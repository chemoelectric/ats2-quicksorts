(*
  Copyright © 2022 Barry Schwartz

  This program is free software: you can redistribute it and/or
  modify it under the terms of the GNU General Public License, as
  published by the Free Software Foundation, either version 3 of the
  License, or (at your option) any later version.

  This program is distributed in the hope that it will be useful, but
  WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
  General Public License for more details.

  You should have received copies of the GNU General Public License
  along with this program. If not, see
  <https://www.gnu.org/licenses/>.
*)

#include "share/atspre_staload.hats"

staload UN = "prelude/SATS/unsafe.sats"
#include "quicksorts/HATS/stable-quicksort.hats"

(*------------------------------------------------------------------*)
(* A simple linear congruential generator.                          *)

(* The multiplier lcg_a comes from Steele, Guy; Vigna, Sebastiano (28
   September 2021). "Computationally easy, spectrally good multipliers
   for congruential pseudorandom number generators".
   arXiv:2001.05304v3 [cs.DS] *)
macdef lcg_a = $UN.cast{uint64} 0xf1357aea2e62a9c5LLU

(* lcg_c must be odd. *)
macdef lcg_c = $UN.cast{uint64} 0x1234567891234567LLU

var seed : uint64 = $UN.cast 0
val p_seed = addr@ seed

fn
random_double ()
    :<!wrt> double =
  let
    val (pf, fpf | p_seed) = $UN.ptr0_vtake{uint64} p_seed
    val old_seed = ptr_get<uint64> (pf | p_seed)

    (* IEEE "binary64" or "double" has 52 bits of precision. We will
       take the high 48 bits of the seed and divide it by 2**48, to
       get a number 0.0 <= randnum < 1.0 *)
    val high_48_bits = $UN.cast{double} (old_seed >> 16)
    val divisor = $UN.cast{double} (1LLU << 48)
    val randnum = high_48_bits / divisor

    (* The following operation is modulo 2**64, by virtue of standard
       C behavior for uint64_t. *)
    val new_seed = (lcg_a * old_seed) + lcg_c

    val () = ptr_set<uint64> (pf | p_seed, new_seed)
    prval () = fpf pf
  in
    randnum
  end

fn
random_int
          {m, n : int | m <= n}
          (m    : int m,
           n    : int n)
    :<!wrt> [i : int | m <= i; i <= n]
            int i =
  m + ($UN.cast{[i : nat | i < n - m + 1] int i}
        (random_double () * (n - m + 1)))

(*------------------------------------------------------------------*)

fn
find_first_letter
          {n            : int}
          (n            : size_t n,
           words_copy   : &array (String1, n),
           first_letter : char)
    : [j : nat | j <= n]
      size_t j =
  let
    prval () = lemma_array_param words_copy

    fun
    loop {i : nat | i <= n}
         .<n - i>.
         (words_copy : &array (String1, n),
          i          : size_t i)
        :<> [j : nat | j <= n]
            size_t j =
      if i = n then
        i
      else if words_copy[i] = "*" then
        loop (words_copy, succ i)
      else if (tolower (string_get_at (words_copy[i], 0)) =
                 first_letter) then
        i
      else
        loop (words_copy, succ i)
  in
    loop (words_copy, i2sz 0)
  end

fn
scramble_words
          {n               : int}
          (n               : size_t n,
           words           : &array (String1, n),
           scrambled_words : &array (String1?, n)
                              >> array (String1, n))
    : void =
  (* Scramble the words, without changing the relative order of words
     that start with the same letter. *)
  let
    prval () = lemma_array_param words

    val () = array_initize_elt<String1> (scrambled_words, n, "*")

    var letters : @[char][26] =
      @[char][26] ('a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i',
                   'j', 'k', 'l', 'm', 'n', 'o', 'p', 'q', 'r',
                   's', 't', 'u', 'v', 'w', 'x', 'y', 'z')

    val @(pf_words_copy, pfgc_words_copy | p_words_copy) =
      array_ptr_alloc<String1> n
    macdef words_copy = !p_words_copy
    val () = array_copy<String1> (words_copy, words, n)

    fun
    loop {i_scrambled : nat | i_scrambled <= n}
         {num_letters : nat | num_letters <= 26}
         .<(n - i_scrambled) + num_letters>.
         (scrambled_words : &array (String1, n) >> _,
          words_copy      : &array (String1, n) >> _,
          letters         : &array (char, 26) >> _,
          i_scrambled     : size_t i_scrambled,
          num_letters     : int num_letters)
        : void =
      if i_scrambled = n then
        ()
      else
        let
          val () = assertloc (num_letters <> 0)
          val i_first_letter = random_int (0, pred num_letters)
          val first_letter = letters[i_first_letter]
          val j = find_first_letter (n, words_copy, first_letter)
        in
          if j <> n then
            begin               (* Move the word. *)
              scrambled_words[i_scrambled] := words_copy[j];
              words_copy[j] := "*";
              loop (scrambled_words, words_copy, letters,
                    succ i_scrambled, num_letters)
            end
          else
            let                 (* Remove the letter. *)
              fun
              move_letters
                        {k : nat | k <= num_letters - 1}
                        .<num_letters - k>.
                        (letters : &array (char, 26) >> _,
                         k       : int k)
                  : void =
                if succ k = num_letters then
                  ()
                else
                  begin
                    letters[k] := letters[succ k];
                    move_letters (letters, succ k)
                  end
            in
              move_letters (letters, i_first_letter);
              loop (scrambled_words, words_copy, letters,
                    i_scrambled, pred num_letters)
            end
        end
  in
    loop (scrambled_words, words_copy, letters, i2sz 0, 26);
    array_ptr_free (pf_words_copy, pfgc_words_copy | p_words_copy)
  end

fn
verify_descrambled
          {n               : int}
          (n               : size_t n,
           words           : &array (String1, n),
           scrambled_words : &array (String1, n))
    : void =
  let
    prval () = lemma_array_param words

    fun
    loop {i : nat | i <= n}
         .<n - i>.
         (words           : &array (String1, n),
          scrambled_words : &array (String1, n),
          i               : size_t i)
        : void =
      if i = n then
        ()
      else
        begin
          if words[i] <> scrambled_words[i] then
            begin
              println! ("Failed");
              exit 1
            end;
          loop (words, scrambled_words, succ i)
        end
  in
    loop (words, scrambled_words, i2sz 0)
  end

fn
print_array
          {n : int}
          (arr : &array (String1, n),
           n   : size_t n)
    : void =
  let
    prval () = lemma_array_param arr

    fun
    loop {i : nat | i <= n}
         (arr : &array (String1, n),
          i   : size_t i)
        : void =
      if i = n then
        ()
      else
        begin
          print! "\"";
          print! (arr[i]);
          print! "\"";
          println! ();
          loop (arr, succ i)
        end
  in
    loop (arr, i2sz 0)
  end

fn
test_stability () : void =
  let
    val words_list =
      $list{String1}
        ("a", "ability", "able", "about", "above", "accept",
         "according", "account", "across", "act", "action",
         "activity", "actually", "add", "address", "administration",
         "admit", "adult", "affect", "after", "again", "against",
         "age", "agency", "agent", "ago", "agree", "agreement",
         "ahead", "air", "all", "allow", "almost", "alone", "along",
         "already", "also", "although", "always", "American", "among",
         "amount", "analysis", "and", "animal", "another", "answer",
         "any", "anyone", "anything", "appear", "apply", "approach",
         "area", "argue", "arm", "around", "arrive", "art", "article",
         "artist", "as", "ask", "assume", "at", "attack", "attention",
         "attorney", "audience", "author", "authority", "available",
         "avoid", "away", "baby", "back", "bad", "bag", "ball",
         "bank", "bar", "base", "be", "beat", "beautiful", "because",
         "become", "bed", "before", "begin", "behavior", "behind",
         "believe", "benefit", "best", "better", "between", "beyond",
         "big", "bill", "billion", "bit", "black", "blood", "blue",
         "board", "body", "book", "born", "both", "box", "boy",
         "break", "bring", "brother", "budget", "build", "building",
         "business", "but", "buy", "by", "call", "camera", "campaign",
         "can", "cancer", "candidate", "capital", "car", "card",
         "care", "career", "carry", "case", "catch", "cause", "cell",
         "center", "central", "century", "certain", "certainly",
         "chair", "challenge", "chance", "change", "character",
         "charge", "check", "child", "choice", "choose", "church",
         "citizen", "city", "civil", "claim", "class", "clear",
         "clearly", "close", "coach", "cold", "collection", "college",
         "color", "come", "commercial", "common", "community",
         "company", "compare", "computer", "concern", "condition",
         "conference", "Congress", "consider", "consumer", "contain",
         "continue", "control", "cost", "could", "country", "couple",
         "course", "court", "cover", "create", "crime", "cultural",
         "culture", "cup", "current", "customer", "cut", "dark",
         "data", "daughter", "day", "dead", "deal", "death", "debate",
         "decade", "decide", "decision", "deep", "defense", "degree",
         "Democrat", "democratic", "describe", "design", "despite",
         "detail", "determine", "develop", "development", "die",
         "difference", "different", "difficult", "dinner",
         "direction", "director", "discover", "discuss", "discussion",
         "disease", "do", "doctor", "dog", "door", "down", "draw",
         "dream", "drive", "drop", "drug", "during", "each", "early",
         "east", "easy", "eat", "economic", "economy", "edge",
         "education", "effect", "effort", "eight", "either",
         "election", "else", "employee", "end", "energy", "enjoy",
         "enough", "enter", "entire", "environment", "environmental",
         "especially", "establish", "even", "evening", "event",
         "ever", "every", "everybody", "everyone", "everything",
         "evidence", "exactly", "example", "executive", "exist",
         "expect", "experience", "expert", "explain", "eye", "face",
         "fact", "factor", "fail", "fall", "family", "far", "fast",
         "father", "fear", "federal", "feel", "feeling", "few",
         "field", "fight", "figure", "fill", "film", "final",
         "finally", "financial", "find", "fine", "finger", "finish",
         "fire", "firm", "first", "fish", "five", "floor", "fly",
         "focus", "follow", "food", "foot", "for", "force", "foreign",
         "forget", "form", "former", "forward", "four", "free",
         "friend", "from", "front", "full", "fund", "future", "game",
         "garden", "gas", "general", "generation", "get", "girl",
         "give", "glass", "go", "goal", "good", "government", "great",
         "green", "ground", "group", "grow", "growth", "guess", "gun",
         "guy", "hair", "half", "hand", "hang", "happen", "happy",
         "hard", "have", "he", "head", "health", "hear", "heart",
         "heat", "heavy", "help", "her", "here", "herself", "high",
         "him", "himself", "his", "history", "hit", "hold", "home",
         "hope", "hospital", "hot", "hotel", "hour", "house", "how",
         "however", "huge", "human", "hundred", "husband", "I",
         "idea", "identify", "if", "image", "imagine", "impact",
         "important", "improve", "in", "include", "including",
         "increase", "indeed", "indicate", "individual", "industry",
         "information", "inside", "instead", "institution",
         "interest", "interesting", "international", "interview",
         "into", "investment", "involve", "issue", "it", "item",
         "its", "itself", "job", "join", "just", "keep", "key", "kid",
         "kill", "kind", "kitchen", "know", "knowledge", "land",
         "language", "large", "last", "late", "later", "laugh", "law",
         "lawyer", "lay", "lead", "leader", "learn", "least", "leave",
         "left", "leg", "legal", "less", "let", "letter", "level",
         "lie", "life", "light", "like", "likely", "line", "list",
         "listen", "little", "live", "local", "long", "look", "lose",
         "loss", "lot", "love", "low", "machine", "magazine", "main",
         "maintain", "major", "majority", "make", "man", "manage",
         "management", "manager", "many", "market", "marriage",
         "material", "matter", "may", "maybe", "me", "mean",
         "measure", "media", "medical", "meet", "meeting", "member",
         "memory", "mention", "message", "method", "middle", "might",
         "military", "million", "mind", "minute", "miss", "mission",
         "model", "modern", "moment", "money", "month", "more",
         "morning", "most", "mother", "mouth", "move", "movement",
         "movie", "Mr", "Mrs", "much", "music", "must", "my",
         "myself", "name", "nation", "national", "natural", "nature",
         "near", "nearly", "necessary", "need", "network", "never",
         "new", "news", "newspaper", "next", "nice", "night", "no",
         "none", "nor", "north", "not", "note", "nothing", "notice",
         "now", "n't", "number", "occur", "of", "off", "offer",
         "office", "officer", "official", "often", "oh", "oil", "ok",
         "old", "on", "once", "one", "only", "onto", "open",
         "operation", "opportunity", "option", "or", "order",
         "organization", "other", "others", "our", "out", "outside",
         "over", "own", "owner", "page", "pain", "painting", "paper",
         "parent", "part", "participant", "particular",
         "particularly", "partner", "party", "pass", "past",
         "patient", "pattern", "pay", "peace", "people", "per",
         "perform", "performance", "perhaps", "period", "person",
         "personal", "phone", "physical", "pick", "picture", "piece",
         "place", "plan", "plant", "play", "player", "PM", "point",
         "police", "policy", "political", "politics", "poor",
         "popular", "population", "position", "positive", "possible",
         "power", "practice", "prepare", "present", "president",
         "pressure", "pretty", "prevent", "price", "private",
         "probably", "problem", "process", "produce", "product",
         "production", "professional", "professor", "program",
         "project", "property", "protect", "prove", "provide",
         "public", "pull", "purpose", "push", "put", "quality",
         "question", "quickly", "quite", "race", "radio", "raise",
         "range", "rate", "rather", "reach", "read", "ready", "real",
         "reality", "realize", "really", "reason", "receive",
         "recent", "recently", "recognize", "record", "red", "reduce",
         "reflect", "region", "relate", "relationship", "religious",
         "remain", "remember", "remove", "report", "represent",
         "Republican", "require", "research", "resource", "respond",
         "response", "responsibility", "rest", "result", "return",
         "reveal", "rich", "right", "rise", "risk", "road", "rock",
         "role", "room", "rule", "run", "safe", "same", "save", "say",
         "scene", "school", "science", "scientist", "score", "sea",
         "season", "seat", "second", "section", "security", "see",
         "seek", "seem", "sell", "send", "senior", "sense", "series",
         "serious", "serve", "service", "set", "seven", "several",
         "sex", "sexual", "shake", "share", "she", "shoot", "short",
         "shot", "should", "shoulder", "show", "side", "sign",
         "significant", "similar", "simple", "simply", "since",
         "sing", "single", "sister", "sit", "site", "situation",
         "six", "size", "skill", "skin", "small", "smile", "so",
         "social", "society", "soldier", "some", "somebody",
         "someone", "something", "sometimes", "son", "song", "soon",
         "sort", "sound", "source", "south", "southern", "space",
         "speak", "special", "specific", "speech", "spend", "sport",
         "spring", "staff", "stage", "stand", "standard", "star",
         "start", "state", "statement", "station", "stay", "step",
         "still", "stock", "stop", "store", "story", "strategy",
         "street", "strong", "structure", "student", "study", "stuff",
         "style", "subject", "success", "successful", "such",
         "suddenly", "suffer", "suggest", "summer", "support", "sure",
         "surface", "system", "table", "take", "talk", "task", "tax",
         "teach", "teacher", "team", "technology", "television",
         "tell", "ten", "tend", "term", "test", "than", "thank",
         "that", "the", "their", "them", "themselves", "then",
         "theory", "there", "these", "they", "thing", "think",
         "third", "this", "those", "though", "thought", "thousand",
         "threat", "three", "through", "throughout", "throw", "thus",
         "time", "to", "today", "together", "tonight", "too", "top",
         "total", "tough", "toward", "town", "trade", "traditional",
         "training", "travel", "treat", "treatment", "tree", "trial",
         "trip", "trouble", "true", "truth", "try", "turn", "TV",
         "two", "type", "under", "understand", "unit", "until", "up",
         "upon", "us", "use", "usually", "value", "various", "very",
         "victim", "view", "violence", "visit", "voice", "vote",
         "wait", "walk", "wall", "want", "war", "watch", "water",
         "way", "we", "weapon", "wear", "week", "weight", "well",
         "west", "western", "what", "whatever", "when", "where",
         "whether", "which", "while", "white", "who", "whole", "whom",
         "whose", "why", "wide", "wife", "will", "win", "wind",
         "window", "wish", "with", "within", "without", "woman",
         "wonder", "word", "work", "worker", "world", "worry",
         "would", "write", "writer", "wrong", "yard", "yeah", "year",
         "yes", "yet", "you", "young", "your", "yourself")

    implement
    array_stable_quicksort$lt<String1> (x, y) =
      (* Lexicographically compare first ASCII letters, in English
         order. *)
      let
        val sx = ptr_get<String1> (view@ x | addr@ x)
        and sy = ptr_get<String1> (view@ y | addr@ y)
      in
        tolower sx[0] < tolower sy[0]
      end

    val n = i2sz (length words_list)

    val @(pf_words, pfgc_words | p_words) =
      array_ptr_alloc<String1> n
    macdef words = !p_words

    val @(pf_scrambled_words, pfgc_scrambled_words |
          p_scrambled_words) =
      array_ptr_alloc<String1> n
    macdef scrambled_words = !p_scrambled_words
  in
    array_initize_list<String1> (words, sz2i n, words_list);
    scramble_words (n, words, scrambled_words);
    // print_array (scrambled_words, n);
    array_stable_quicksort<String1> (scrambled_words, n);
    // print_array (scrambled_words, n);
    verify_descrambled (n, words, scrambled_words);
    array_ptr_free (pf_words, pfgc_words | p_words);
    array_ptr_free (pf_scrambled_words, pfgc_scrambled_words |
                    p_scrambled_words)
  end

(*------------------------------------------------------------------*)

implement
main0 () =
  begin
    test_stability ()
  end

(*------------------------------------------------------------------*)
