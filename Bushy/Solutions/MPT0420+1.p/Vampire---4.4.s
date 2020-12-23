%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : setfam_1__t52_setfam_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n030.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:18 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  453 (1346 expanded)
%              Number of leaves         :  142 ( 572 expanded)
%              Depth                    :   10
%              Number of atoms          : 1219 (3481 expanded)
%              Number of equality atoms :   51 ( 171 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1135,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f71,f78,f85,f92,f103,f110,f125,f126,f156,f169,f182,f192,f194,f206,f214,f228,f235,f256,f264,f274,f284,f299,f307,f317,f329,f337,f345,f355,f372,f383,f390,f404,f418,f426,f437,f445,f459,f466,f485,f498,f534,f550,f563,f571,f591,f601,f617,f631,f639,f649,f663,f677,f695,f712,f726,f745,f755,f768,f781,f785,f798,f802,f809,f820,f834,f843,f853,f863,f877,f890,f900,f910,f915,f925,f936,f943,f957,f964,f972,f981,f991,f1003,f1016,f1029,f1042,f1055,f1059,f1075,f1079,f1088,f1096,f1109,f1122,f1127,f1134])).

fof(f1134,plain,
    ( ~ spl4_4
    | ~ spl4_12
    | spl4_15
    | ~ spl4_234 ),
    inference(avatar_contradiction_clause,[],[f1133])).

fof(f1133,plain,
    ( $false
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_234 ),
    inference(subsumption_resolution,[],[f1132,f121])).

fof(f121,plain,
    ( ~ r1_tarski(sK1,k7_setfam_1(sK0,sK2))
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl4_15
  <=> ~ r1_tarski(sK1,k7_setfam_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f1132,plain,
    ( r1_tarski(sK1,k7_setfam_1(sK0,sK2))
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_234 ),
    inference(subsumption_resolution,[],[f1128,f84])).

fof(f84,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl4_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f1128,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | r1_tarski(sK1,k7_setfam_1(sK0,sK2))
    | ~ spl4_12
    | ~ spl4_234 ),
    inference(resolution,[],[f1126,f118])).

fof(f118,plain,
    ( r1_tarski(k7_setfam_1(sK0,sK1),sK2)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl4_12
  <=> r1_tarski(k7_setfam_1(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f1126,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k7_setfam_1(sK0,X1),sK2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
        | r1_tarski(X1,k7_setfam_1(sK0,sK2)) )
    | ~ spl4_234 ),
    inference(avatar_component_clause,[],[f1125])).

fof(f1125,plain,
    ( spl4_234
  <=> ! [X1] :
        ( ~ r1_tarski(k7_setfam_1(sK0,X1),sK2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
        | r1_tarski(X1,k7_setfam_1(sK0,sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_234])])).

fof(f1127,plain,
    ( ~ spl4_181
    | spl4_234
    | ~ spl4_38 ),
    inference(avatar_split_clause,[],[f321,f233,f1125,f920])).

fof(f920,plain,
    ( spl4_181
  <=> ~ m1_subset_1(k7_setfam_1(sK0,sK2),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_181])])).

fof(f233,plain,
    ( spl4_38
  <=> k7_setfam_1(sK0,k7_setfam_1(sK0,sK2)) = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f321,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k7_setfam_1(sK0,X1),sK2)
        | r1_tarski(X1,k7_setfam_1(sK0,sK2))
        | ~ m1_subset_1(k7_setfam_1(sK0,sK2),k1_zfmisc_1(k1_zfmisc_1(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(sK0))) )
    | ~ spl4_38 ),
    inference(superposition,[],[f57,f234])).

fof(f234,plain,
    ( k7_setfam_1(sK0,k7_setfam_1(sK0,sK2)) = sK2
    | ~ spl4_38 ),
    inference(avatar_component_clause,[],[f233])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
      | r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ~ r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ~ r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
           => r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t52_setfam_1.p',t51_setfam_1)).

fof(f1122,plain,
    ( spl4_230
    | spl4_232
    | ~ spl4_220 ),
    inference(avatar_split_clause,[],[f1081,f1077,f1120,f1114])).

fof(f1114,plain,
    ( spl4_230
  <=> v1_xboole_0(sK3(k1_zfmisc_1(sK3(sK3(k1_zfmisc_1(k7_setfam_1(sK0,sK1))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_230])])).

fof(f1120,plain,
    ( spl4_232
  <=> m1_subset_1(sK3(sK3(k1_zfmisc_1(sK3(sK3(k1_zfmisc_1(k7_setfam_1(sK0,sK1))))))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_232])])).

fof(f1077,plain,
    ( spl4_220
  <=> ! [X0] :
        ( m1_subset_1(X0,sK0)
        | ~ m1_subset_1(X0,sK3(sK3(k1_zfmisc_1(k7_setfam_1(sK0,sK1))))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_220])])).

fof(f1081,plain,
    ( m1_subset_1(sK3(sK3(k1_zfmisc_1(sK3(sK3(k1_zfmisc_1(k7_setfam_1(sK0,sK1))))))),sK0)
    | v1_xboole_0(sK3(k1_zfmisc_1(sK3(sK3(k1_zfmisc_1(k7_setfam_1(sK0,sK1)))))))
    | ~ spl4_220 ),
    inference(resolution,[],[f1078,f509])).

fof(f509,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(sK3(k1_zfmisc_1(X0))),X0)
      | v1_xboole_0(sK3(k1_zfmisc_1(X0))) ) ),
    inference(resolution,[],[f252,f51])).

fof(f51,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f10,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f10,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t52_setfam_1.p',existence_m1_subset_1)).

fof(f252,plain,(
    ! [X10,X9] :
      ( ~ m1_subset_1(X9,sK3(k1_zfmisc_1(X10)))
      | v1_xboole_0(sK3(k1_zfmisc_1(X10)))
      | m1_subset_1(X9,X10) ) ),
    inference(resolution,[],[f133,f51])).

fof(f133,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | m1_subset_1(X2,X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X2,X0) ) ),
    inference(resolution,[],[f62,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t52_setfam_1.p',t2_subset)).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t52_setfam_1.p',t4_subset)).

fof(f1078,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK3(sK3(k1_zfmisc_1(k7_setfam_1(sK0,sK1)))))
        | m1_subset_1(X0,sK0) )
    | ~ spl4_220 ),
    inference(avatar_component_clause,[],[f1077])).

fof(f1109,plain,
    ( ~ spl4_227
    | spl4_88
    | spl4_228
    | ~ spl4_222 ),
    inference(avatar_split_clause,[],[f1089,f1086,f1107,f477,f1101])).

fof(f1101,plain,
    ( spl4_227
  <=> ~ m1_subset_1(sK0,sK3(sK3(sK3(k1_zfmisc_1(k7_setfam_1(sK0,sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_227])])).

fof(f477,plain,
    ( spl4_88
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_88])])).

fof(f1107,plain,
    ( spl4_228
  <=> v1_xboole_0(sK3(sK3(sK3(k1_zfmisc_1(k7_setfam_1(sK0,sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_228])])).

fof(f1086,plain,
    ( spl4_222
  <=> m1_subset_1(sK3(sK3(sK3(k1_zfmisc_1(k7_setfam_1(sK0,sK1))))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_222])])).

fof(f1089,plain,
    ( v1_xboole_0(sK3(sK3(sK3(k1_zfmisc_1(k7_setfam_1(sK0,sK1))))))
    | v1_xboole_0(sK0)
    | ~ m1_subset_1(sK0,sK3(sK3(sK3(k1_zfmisc_1(k7_setfam_1(sK0,sK1))))))
    | ~ spl4_222 ),
    inference(resolution,[],[f1087,f131])).

fof(f131,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(resolution,[],[f128,f54])).

fof(f128,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,X3)
      | ~ m1_subset_1(X3,X2)
      | v1_xboole_0(X2) ) ),
    inference(resolution,[],[f54,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t52_setfam_1.p',antisymmetry_r2_hidden)).

fof(f1087,plain,
    ( m1_subset_1(sK3(sK3(sK3(k1_zfmisc_1(k7_setfam_1(sK0,sK1))))),sK0)
    | ~ spl4_222 ),
    inference(avatar_component_clause,[],[f1086])).

fof(f1096,plain,
    ( ~ spl4_225
    | spl4_82
    | spl4_200
    | ~ spl4_174 ),
    inference(avatar_split_clause,[],[f903,f898,f1014,f457,f1094])).

fof(f1094,plain,
    ( spl4_225
  <=> ~ m1_subset_1(k1_zfmisc_1(sK0),sK3(sK3(k1_zfmisc_1(k7_setfam_1(sK0,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_225])])).

fof(f457,plain,
    ( spl4_82
  <=> v1_xboole_0(k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_82])])).

fof(f1014,plain,
    ( spl4_200
  <=> v1_xboole_0(sK3(sK3(k1_zfmisc_1(k7_setfam_1(sK0,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_200])])).

fof(f898,plain,
    ( spl4_174
  <=> m1_subset_1(sK3(sK3(k1_zfmisc_1(k7_setfam_1(sK0,sK1)))),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_174])])).

fof(f903,plain,
    ( v1_xboole_0(sK3(sK3(k1_zfmisc_1(k7_setfam_1(sK0,sK1)))))
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ m1_subset_1(k1_zfmisc_1(sK0),sK3(sK3(k1_zfmisc_1(k7_setfam_1(sK0,sK1)))))
    | ~ spl4_174 ),
    inference(resolution,[],[f899,f131])).

fof(f899,plain,
    ( m1_subset_1(sK3(sK3(k1_zfmisc_1(k7_setfam_1(sK0,sK1)))),k1_zfmisc_1(sK0))
    | ~ spl4_174 ),
    inference(avatar_component_clause,[],[f898])).

fof(f1088,plain,
    ( spl4_222
    | ~ spl4_220 ),
    inference(avatar_split_clause,[],[f1080,f1077,f1086])).

fof(f1080,plain,
    ( m1_subset_1(sK3(sK3(sK3(k1_zfmisc_1(k7_setfam_1(sK0,sK1))))),sK0)
    | ~ spl4_220 ),
    inference(resolution,[],[f1078,f51])).

fof(f1079,plain,
    ( spl4_200
    | spl4_220
    | ~ spl4_174 ),
    inference(avatar_split_clause,[],[f901,f898,f1077,f1014])).

fof(f901,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,sK0)
        | v1_xboole_0(sK3(sK3(k1_zfmisc_1(k7_setfam_1(sK0,sK1)))))
        | ~ m1_subset_1(X0,sK3(sK3(k1_zfmisc_1(k7_setfam_1(sK0,sK1))))) )
    | ~ spl4_174 ),
    inference(resolution,[],[f899,f133])).

fof(f1075,plain,
    ( spl4_216
    | ~ spl4_181
    | ~ spl4_219
    | ~ spl4_38
    | ~ spl4_182 ),
    inference(avatar_split_clause,[],[f995,f923,f233,f1073,f920,f1067])).

fof(f1067,plain,
    ( spl4_216
  <=> r1_tarski(k7_setfam_1(sK0,sK2),k7_setfam_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_216])])).

fof(f1073,plain,
    ( spl4_219
  <=> ~ r1_tarski(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_219])])).

fof(f923,plain,
    ( spl4_182
  <=> ! [X1] :
        ( ~ r1_tarski(sK2,k7_setfam_1(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
        | r1_tarski(k7_setfam_1(sK0,sK2),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_182])])).

fof(f995,plain,
    ( ~ r1_tarski(sK2,sK2)
    | ~ m1_subset_1(k7_setfam_1(sK0,sK2),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | r1_tarski(k7_setfam_1(sK0,sK2),k7_setfam_1(sK0,sK2))
    | ~ spl4_38
    | ~ spl4_182 ),
    inference(superposition,[],[f924,f234])).

fof(f924,plain,
    ( ! [X1] :
        ( ~ r1_tarski(sK2,k7_setfam_1(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
        | r1_tarski(k7_setfam_1(sK0,sK2),X1) )
    | ~ spl4_182 ),
    inference(avatar_component_clause,[],[f923])).

fof(f1059,plain,
    ( ~ spl4_151
    | spl4_214
    | ~ spl4_36 ),
    inference(avatar_split_clause,[],[f320,f226,f1057,f793])).

fof(f793,plain,
    ( spl4_151
  <=> ~ m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_151])])).

fof(f1057,plain,
    ( spl4_214
  <=> ! [X0] :
        ( ~ r1_tarski(k7_setfam_1(sK0,X0),sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
        | r1_tarski(X0,k7_setfam_1(sK0,sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_214])])).

fof(f226,plain,
    ( spl4_36
  <=> k7_setfam_1(sK0,k7_setfam_1(sK0,sK1)) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f320,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k7_setfam_1(sK0,X0),sK1)
        | r1_tarski(X0,k7_setfam_1(sK0,sK1))
        | ~ m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0))) )
    | ~ spl4_36 ),
    inference(superposition,[],[f57,f227])).

fof(f227,plain,
    ( k7_setfam_1(sK0,k7_setfam_1(sK0,sK1)) = sK1
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f226])).

fof(f1055,plain,
    ( spl4_210
    | ~ spl4_151
    | ~ spl4_213
    | ~ spl4_36
    | ~ spl4_182 ),
    inference(avatar_split_clause,[],[f994,f923,f226,f1053,f793,f1047])).

fof(f1047,plain,
    ( spl4_210
  <=> r1_tarski(k7_setfam_1(sK0,sK2),k7_setfam_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_210])])).

fof(f1053,plain,
    ( spl4_213
  <=> ~ r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_213])])).

fof(f994,plain,
    ( ~ r1_tarski(sK2,sK1)
    | ~ m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | r1_tarski(k7_setfam_1(sK0,sK2),k7_setfam_1(sK0,sK1))
    | ~ spl4_36
    | ~ spl4_182 ),
    inference(superposition,[],[f924,f227])).

fof(f1042,plain,
    ( spl4_206
    | ~ spl4_181
    | ~ spl4_209
    | ~ spl4_38
    | ~ spl4_152 ),
    inference(avatar_split_clause,[],[f805,f796,f233,f1040,f920,f1034])).

fof(f1034,plain,
    ( spl4_206
  <=> r1_tarski(k7_setfam_1(sK0,sK1),k7_setfam_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_206])])).

fof(f1040,plain,
    ( spl4_209
  <=> ~ r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_209])])).

fof(f796,plain,
    ( spl4_152
  <=> ! [X0] :
        ( ~ r1_tarski(sK1,k7_setfam_1(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
        | r1_tarski(k7_setfam_1(sK0,sK1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_152])])).

fof(f805,plain,
    ( ~ r1_tarski(sK1,sK2)
    | ~ m1_subset_1(k7_setfam_1(sK0,sK2),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | r1_tarski(k7_setfam_1(sK0,sK1),k7_setfam_1(sK0,sK2))
    | ~ spl4_38
    | ~ spl4_152 ),
    inference(superposition,[],[f797,f234])).

fof(f797,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK1,k7_setfam_1(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
        | r1_tarski(k7_setfam_1(sK0,sK1),X0) )
    | ~ spl4_152 ),
    inference(avatar_component_clause,[],[f796])).

fof(f1029,plain,
    ( spl4_202
    | ~ spl4_151
    | ~ spl4_205
    | ~ spl4_36
    | ~ spl4_152 ),
    inference(avatar_split_clause,[],[f804,f796,f226,f1027,f793,f1021])).

fof(f1021,plain,
    ( spl4_202
  <=> r1_tarski(k7_setfam_1(sK0,sK1),k7_setfam_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_202])])).

fof(f1027,plain,
    ( spl4_205
  <=> ~ r1_tarski(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_205])])).

fof(f804,plain,
    ( ~ r1_tarski(sK1,sK1)
    | ~ m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | r1_tarski(k7_setfam_1(sK0,sK1),k7_setfam_1(sK0,sK1))
    | ~ spl4_36
    | ~ spl4_152 ),
    inference(superposition,[],[f797,f227])).

fof(f1016,plain,
    ( ~ spl4_199
    | spl4_200
    | spl4_25
    | ~ spl4_172 ),
    inference(avatar_split_clause,[],[f893,f888,f164,f1014,f1008])).

fof(f1008,plain,
    ( spl4_199
  <=> ~ m1_subset_1(sK2,sK3(sK3(k1_zfmisc_1(k7_setfam_1(sK0,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_199])])).

fof(f164,plain,
    ( spl4_25
  <=> ~ v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f888,plain,
    ( spl4_172
  <=> m1_subset_1(sK3(sK3(k1_zfmisc_1(k7_setfam_1(sK0,sK1)))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_172])])).

fof(f893,plain,
    ( v1_xboole_0(sK3(sK3(k1_zfmisc_1(k7_setfam_1(sK0,sK1)))))
    | ~ m1_subset_1(sK2,sK3(sK3(k1_zfmisc_1(k7_setfam_1(sK0,sK1)))))
    | ~ spl4_25
    | ~ spl4_172 ),
    inference(subsumption_resolution,[],[f892,f165])).

fof(f165,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f164])).

fof(f892,plain,
    ( v1_xboole_0(sK3(sK3(k1_zfmisc_1(k7_setfam_1(sK0,sK1)))))
    | v1_xboole_0(sK2)
    | ~ m1_subset_1(sK2,sK3(sK3(k1_zfmisc_1(k7_setfam_1(sK0,sK1)))))
    | ~ spl4_172 ),
    inference(resolution,[],[f889,f131])).

fof(f889,plain,
    ( m1_subset_1(sK3(sK3(k1_zfmisc_1(k7_setfam_1(sK0,sK1)))),sK2)
    | ~ spl4_172 ),
    inference(avatar_component_clause,[],[f888])).

fof(f1003,plain,
    ( ~ spl4_197
    | spl4_82
    | spl4_168
    | ~ spl4_162 ),
    inference(avatar_split_clause,[],[f856,f851,f875,f457,f1001])).

fof(f1001,plain,
    ( spl4_197
  <=> ~ m1_subset_1(k1_zfmisc_1(sK0),sK3(k7_setfam_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_197])])).

fof(f875,plain,
    ( spl4_168
  <=> v1_xboole_0(sK3(k7_setfam_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_168])])).

fof(f851,plain,
    ( spl4_162
  <=> m1_subset_1(sK3(k7_setfam_1(sK0,sK1)),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_162])])).

fof(f856,plain,
    ( v1_xboole_0(sK3(k7_setfam_1(sK0,sK1)))
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ m1_subset_1(k1_zfmisc_1(sK0),sK3(k7_setfam_1(sK0,sK1)))
    | ~ spl4_162 ),
    inference(resolution,[],[f852,f131])).

fof(f852,plain,
    ( m1_subset_1(sK3(k7_setfam_1(sK0,sK1)),k1_zfmisc_1(sK0))
    | ~ spl4_162 ),
    inference(avatar_component_clause,[],[f851])).

fof(f991,plain,
    ( spl4_194
    | ~ spl4_184 ),
    inference(avatar_split_clause,[],[f950,f941,f989])).

fof(f989,plain,
    ( spl4_194
  <=> m1_subset_1(k1_xboole_0,k7_setfam_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_194])])).

fof(f941,plain,
    ( spl4_184
  <=> k1_xboole_0 = sK3(k7_setfam_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_184])])).

fof(f950,plain,
    ( m1_subset_1(k1_xboole_0,k7_setfam_1(sK0,sK1))
    | ~ spl4_184 ),
    inference(superposition,[],[f51,f942])).

fof(f942,plain,
    ( k1_xboole_0 = sK3(k7_setfam_1(sK0,sK1))
    | ~ spl4_184 ),
    inference(avatar_component_clause,[],[f941])).

fof(f981,plain,
    ( spl4_192
    | ~ spl4_162
    | ~ spl4_184 ),
    inference(avatar_split_clause,[],[f947,f941,f851,f979])).

fof(f979,plain,
    ( spl4_192
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_192])])).

fof(f947,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0))
    | ~ spl4_162
    | ~ spl4_184 ),
    inference(superposition,[],[f852,f942])).

fof(f972,plain,
    ( spl4_190
    | ~ spl4_160
    | ~ spl4_184 ),
    inference(avatar_split_clause,[],[f948,f941,f841,f970])).

fof(f970,plain,
    ( spl4_190
  <=> m1_subset_1(k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_190])])).

fof(f841,plain,
    ( spl4_160
  <=> m1_subset_1(sK3(k7_setfam_1(sK0,sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_160])])).

fof(f948,plain,
    ( m1_subset_1(k1_xboole_0,sK2)
    | ~ spl4_160
    | ~ spl4_184 ),
    inference(superposition,[],[f842,f942])).

fof(f842,plain,
    ( m1_subset_1(sK3(k7_setfam_1(sK0,sK1)),sK2)
    | ~ spl4_160 ),
    inference(avatar_component_clause,[],[f841])).

fof(f964,plain,
    ( spl4_188
    | ~ spl4_164
    | ~ spl4_184 ),
    inference(avatar_split_clause,[],[f946,f941,f861,f962])).

fof(f962,plain,
    ( spl4_188
  <=> r1_tarski(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_188])])).

fof(f861,plain,
    ( spl4_164
  <=> r1_tarski(sK3(k7_setfam_1(sK0,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_164])])).

fof(f946,plain,
    ( r1_tarski(k1_xboole_0,sK0)
    | ~ spl4_164
    | ~ spl4_184 ),
    inference(superposition,[],[f862,f942])).

fof(f862,plain,
    ( r1_tarski(sK3(k7_setfam_1(sK0,sK1)),sK0)
    | ~ spl4_164 ),
    inference(avatar_component_clause,[],[f861])).

fof(f957,plain,
    ( ~ spl4_187
    | spl4_167
    | ~ spl4_184 ),
    inference(avatar_split_clause,[],[f945,f941,f869,f955])).

fof(f955,plain,
    ( spl4_187
  <=> ~ m1_subset_1(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_187])])).

fof(f869,plain,
    ( spl4_167
  <=> ~ m1_subset_1(sK2,sK3(k7_setfam_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_167])])).

fof(f945,plain,
    ( ~ m1_subset_1(sK2,k1_xboole_0)
    | ~ spl4_167
    | ~ spl4_184 ),
    inference(superposition,[],[f870,f942])).

fof(f870,plain,
    ( ~ m1_subset_1(sK2,sK3(k7_setfam_1(sK0,sK1)))
    | ~ spl4_167 ),
    inference(avatar_component_clause,[],[f869])).

fof(f943,plain,
    ( spl4_184
    | ~ spl4_98
    | ~ spl4_100
    | ~ spl4_168 ),
    inference(avatar_split_clause,[],[f930,f875,f548,f532,f941])).

fof(f532,plain,
    ( spl4_98
  <=> v1_xboole_0(sK3(k1_zfmisc_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_98])])).

fof(f548,plain,
    ( spl4_100
  <=> k1_xboole_0 = sK3(k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_100])])).

fof(f930,plain,
    ( k1_xboole_0 = sK3(k7_setfam_1(sK0,sK1))
    | ~ spl4_98
    | ~ spl4_100
    | ~ spl4_168 ),
    inference(forward_demodulation,[],[f926,f549])).

fof(f549,plain,
    ( k1_xboole_0 = sK3(k1_zfmisc_1(sK1))
    | ~ spl4_100 ),
    inference(avatar_component_clause,[],[f548])).

fof(f926,plain,
    ( sK3(k1_zfmisc_1(sK1)) = sK3(k7_setfam_1(sK0,sK1))
    | ~ spl4_98
    | ~ spl4_168 ),
    inference(resolution,[],[f876,f536])).

fof(f536,plain,
    ( ! [X2] :
        ( ~ v1_xboole_0(X2)
        | sK3(k1_zfmisc_1(sK1)) = X2 )
    | ~ spl4_98 ),
    inference(resolution,[],[f533,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | X0 = X1
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t52_setfam_1.p',t8_boole)).

fof(f533,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(sK1)))
    | ~ spl4_98 ),
    inference(avatar_component_clause,[],[f532])).

fof(f876,plain,
    ( v1_xboole_0(sK3(k7_setfam_1(sK0,sK1)))
    | ~ spl4_168 ),
    inference(avatar_component_clause,[],[f875])).

fof(f936,plain,
    ( ~ spl4_6
    | spl4_181 ),
    inference(avatar_contradiction_clause,[],[f935])).

fof(f935,plain,
    ( $false
    | ~ spl4_6
    | ~ spl4_181 ),
    inference(subsumption_resolution,[],[f933,f91])).

fof(f91,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl4_6
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f933,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl4_181 ),
    inference(resolution,[],[f921,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t52_setfam_1.p',dt_k7_setfam_1)).

fof(f921,plain,
    ( ~ m1_subset_1(k7_setfam_1(sK0,sK2),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl4_181 ),
    inference(avatar_component_clause,[],[f920])).

fof(f925,plain,
    ( ~ spl4_181
    | spl4_182
    | ~ spl4_38 ),
    inference(avatar_split_clause,[],[f319,f233,f923,f920])).

fof(f319,plain,
    ( ! [X1] :
        ( ~ r1_tarski(sK2,k7_setfam_1(sK0,X1))
        | r1_tarski(k7_setfam_1(sK0,sK2),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
        | ~ m1_subset_1(k7_setfam_1(sK0,sK2),k1_zfmisc_1(k1_zfmisc_1(sK0))) )
    | ~ spl4_38 ),
    inference(superposition,[],[f57,f234])).

fof(f915,plain,
    ( spl4_168
    | spl4_178
    | ~ spl4_162 ),
    inference(avatar_split_clause,[],[f854,f851,f913,f875])).

fof(f913,plain,
    ( spl4_178
  <=> ! [X0] :
        ( m1_subset_1(X0,sK0)
        | ~ m1_subset_1(X0,sK3(k7_setfam_1(sK0,sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_178])])).

fof(f854,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,sK0)
        | v1_xboole_0(sK3(k7_setfam_1(sK0,sK1)))
        | ~ m1_subset_1(X0,sK3(k7_setfam_1(sK0,sK1))) )
    | ~ spl4_162 ),
    inference(resolution,[],[f852,f133])).

fof(f910,plain,
    ( spl4_176
    | ~ spl4_174 ),
    inference(avatar_split_clause,[],[f902,f898,f908])).

fof(f908,plain,
    ( spl4_176
  <=> r1_tarski(sK3(sK3(k1_zfmisc_1(k7_setfam_1(sK0,sK1)))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_176])])).

fof(f902,plain,
    ( r1_tarski(sK3(sK3(k1_zfmisc_1(k7_setfam_1(sK0,sK1)))),sK0)
    | ~ spl4_174 ),
    inference(resolution,[],[f899,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t52_setfam_1.p',t3_subset)).

fof(f900,plain,
    ( spl4_174
    | ~ spl4_50
    | ~ spl4_172 ),
    inference(avatar_split_clause,[],[f891,f888,f305,f898])).

fof(f305,plain,
    ( spl4_50
  <=> ! [X8] :
        ( m1_subset_1(X8,k1_zfmisc_1(sK0))
        | ~ m1_subset_1(X8,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).

fof(f891,plain,
    ( m1_subset_1(sK3(sK3(k1_zfmisc_1(k7_setfam_1(sK0,sK1)))),k1_zfmisc_1(sK0))
    | ~ spl4_50
    | ~ spl4_172 ),
    inference(resolution,[],[f889,f306])).

fof(f306,plain,
    ( ! [X8] :
        ( ~ m1_subset_1(X8,sK2)
        | m1_subset_1(X8,k1_zfmisc_1(sK0)) )
    | ~ spl4_50 ),
    inference(avatar_component_clause,[],[f305])).

fof(f890,plain,
    ( spl4_170
    | spl4_172
    | ~ spl4_154 ),
    inference(avatar_split_clause,[],[f836,f812,f888,f882])).

fof(f882,plain,
    ( spl4_170
  <=> v1_xboole_0(sK3(k1_zfmisc_1(k7_setfam_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_170])])).

fof(f812,plain,
    ( spl4_154
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k7_setfam_1(sK0,sK1))
        | m1_subset_1(X0,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_154])])).

fof(f836,plain,
    ( m1_subset_1(sK3(sK3(k1_zfmisc_1(k7_setfam_1(sK0,sK1)))),sK2)
    | v1_xboole_0(sK3(k1_zfmisc_1(k7_setfam_1(sK0,sK1))))
    | ~ spl4_154 ),
    inference(resolution,[],[f813,f509])).

fof(f813,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k7_setfam_1(sK0,sK1))
        | m1_subset_1(X0,sK2) )
    | ~ spl4_154 ),
    inference(avatar_component_clause,[],[f812])).

fof(f877,plain,
    ( ~ spl4_167
    | spl4_168
    | spl4_25
    | ~ spl4_160 ),
    inference(avatar_split_clause,[],[f846,f841,f164,f875,f869])).

fof(f846,plain,
    ( v1_xboole_0(sK3(k7_setfam_1(sK0,sK1)))
    | ~ m1_subset_1(sK2,sK3(k7_setfam_1(sK0,sK1)))
    | ~ spl4_25
    | ~ spl4_160 ),
    inference(subsumption_resolution,[],[f845,f165])).

fof(f845,plain,
    ( v1_xboole_0(sK3(k7_setfam_1(sK0,sK1)))
    | v1_xboole_0(sK2)
    | ~ m1_subset_1(sK2,sK3(k7_setfam_1(sK0,sK1)))
    | ~ spl4_160 ),
    inference(resolution,[],[f842,f131])).

fof(f863,plain,
    ( spl4_164
    | ~ spl4_162 ),
    inference(avatar_split_clause,[],[f855,f851,f861])).

fof(f855,plain,
    ( r1_tarski(sK3(k7_setfam_1(sK0,sK1)),sK0)
    | ~ spl4_162 ),
    inference(resolution,[],[f852,f58])).

fof(f853,plain,
    ( spl4_162
    | ~ spl4_50
    | ~ spl4_160 ),
    inference(avatar_split_clause,[],[f844,f841,f305,f851])).

fof(f844,plain,
    ( m1_subset_1(sK3(k7_setfam_1(sK0,sK1)),k1_zfmisc_1(sK0))
    | ~ spl4_50
    | ~ spl4_160 ),
    inference(resolution,[],[f842,f306])).

fof(f843,plain,
    ( spl4_160
    | ~ spl4_154 ),
    inference(avatar_split_clause,[],[f835,f812,f841])).

fof(f835,plain,
    ( m1_subset_1(sK3(k7_setfam_1(sK0,sK1)),sK2)
    | ~ spl4_154 ),
    inference(resolution,[],[f813,f51])).

fof(f834,plain,
    ( spl4_158
    | ~ spl4_98
    | ~ spl4_100
    | ~ spl4_156 ),
    inference(avatar_split_clause,[],[f825,f818,f548,f532,f832])).

fof(f832,plain,
    ( spl4_158
  <=> k7_setfam_1(sK0,sK1) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_158])])).

fof(f818,plain,
    ( spl4_156
  <=> v1_xboole_0(k7_setfam_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_156])])).

fof(f825,plain,
    ( k7_setfam_1(sK0,sK1) = k1_xboole_0
    | ~ spl4_98
    | ~ spl4_100
    | ~ spl4_156 ),
    inference(forward_demodulation,[],[f821,f549])).

fof(f821,plain,
    ( k7_setfam_1(sK0,sK1) = sK3(k1_zfmisc_1(sK1))
    | ~ spl4_98
    | ~ spl4_156 ),
    inference(resolution,[],[f819,f536])).

fof(f819,plain,
    ( v1_xboole_0(k7_setfam_1(sK0,sK1))
    | ~ spl4_156 ),
    inference(avatar_component_clause,[],[f818])).

fof(f820,plain,
    ( spl4_154
    | spl4_156
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f810,f117,f818,f812])).

fof(f810,plain,
    ( ! [X0] :
        ( v1_xboole_0(k7_setfam_1(sK0,sK1))
        | ~ m1_subset_1(X0,k7_setfam_1(sK0,sK1))
        | m1_subset_1(X0,sK2) )
    | ~ spl4_12 ),
    inference(resolution,[],[f118,f247])).

fof(f247,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X1)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X0,X2)
      | m1_subset_1(X0,X1) ) ),
    inference(resolution,[],[f133,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f809,plain,
    ( ~ spl4_6
    | spl4_13
    | ~ spl4_14
    | ~ spl4_152 ),
    inference(avatar_contradiction_clause,[],[f808])).

fof(f808,plain,
    ( $false
    | ~ spl4_6
    | ~ spl4_13
    | ~ spl4_14
    | ~ spl4_152 ),
    inference(subsumption_resolution,[],[f807,f115])).

fof(f115,plain,
    ( ~ r1_tarski(k7_setfam_1(sK0,sK1),sK2)
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl4_13
  <=> ~ r1_tarski(k7_setfam_1(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f807,plain,
    ( r1_tarski(k7_setfam_1(sK0,sK1),sK2)
    | ~ spl4_6
    | ~ spl4_14
    | ~ spl4_152 ),
    inference(subsumption_resolution,[],[f803,f91])).

fof(f803,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | r1_tarski(k7_setfam_1(sK0,sK1),sK2)
    | ~ spl4_14
    | ~ spl4_152 ),
    inference(resolution,[],[f797,f124])).

fof(f124,plain,
    ( r1_tarski(sK1,k7_setfam_1(sK0,sK2))
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl4_14
  <=> r1_tarski(sK1,k7_setfam_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f802,plain,
    ( ~ spl4_4
    | spl4_151 ),
    inference(avatar_contradiction_clause,[],[f801])).

fof(f801,plain,
    ( $false
    | ~ spl4_4
    | ~ spl4_151 ),
    inference(subsumption_resolution,[],[f799,f84])).

fof(f799,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl4_151 ),
    inference(resolution,[],[f794,f56])).

fof(f794,plain,
    ( ~ m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl4_151 ),
    inference(avatar_component_clause,[],[f793])).

fof(f798,plain,
    ( ~ spl4_151
    | spl4_152
    | ~ spl4_36 ),
    inference(avatar_split_clause,[],[f318,f226,f796,f793])).

fof(f318,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK1,k7_setfam_1(sK0,X0))
        | r1_tarski(k7_setfam_1(sK0,sK1),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
        | ~ m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) )
    | ~ spl4_36 ),
    inference(superposition,[],[f57,f227])).

fof(f785,plain,
    ( spl4_130
    | spl4_148
    | ~ spl4_14
    | spl4_21 ),
    inference(avatar_split_clause,[],[f698,f151,f123,f783,f707])).

fof(f707,plain,
    ( spl4_130
  <=> v1_xboole_0(k7_setfam_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_130])])).

fof(f783,plain,
    ( spl4_148
  <=> ! [X2] :
        ( v1_xboole_0(k1_zfmisc_1(X2))
        | ~ m1_subset_1(k1_zfmisc_1(X2),sK1)
        | ~ r1_tarski(k7_setfam_1(sK0,sK2),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_148])])).

fof(f151,plain,
    ( spl4_21
  <=> ~ v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f698,plain,
    ( ! [X2] :
        ( v1_xboole_0(k1_zfmisc_1(X2))
        | v1_xboole_0(k7_setfam_1(sK0,sK2))
        | ~ r1_tarski(k7_setfam_1(sK0,sK2),X2)
        | ~ m1_subset_1(k1_zfmisc_1(X2),sK1) )
    | ~ spl4_14
    | ~ spl4_21 ),
    inference(resolution,[],[f134,f507])).

fof(f507,plain,
    ( ! [X7] :
        ( m1_subset_1(X7,k7_setfam_1(sK0,sK2))
        | ~ m1_subset_1(X7,sK1) )
    | ~ spl4_14
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f503,f152])).

fof(f152,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f151])).

fof(f503,plain,
    ( ! [X7] :
        ( v1_xboole_0(sK1)
        | ~ m1_subset_1(X7,sK1)
        | m1_subset_1(X7,k7_setfam_1(sK0,sK2)) )
    | ~ spl4_14 ),
    inference(resolution,[],[f247,f124])).

fof(f134,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k1_zfmisc_1(X1),X0)
      | v1_xboole_0(k1_zfmisc_1(X1))
      | v1_xboole_0(X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f131,f59])).

fof(f781,plain,
    ( ~ spl4_145
    | spl4_88
    | spl4_146
    | ~ spl4_126 ),
    inference(avatar_split_clause,[],[f696,f687,f779,f477,f773])).

fof(f773,plain,
    ( spl4_145
  <=> ~ m1_subset_1(sK0,sK3(sK3(k1_zfmisc_1(sK3(sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_145])])).

fof(f779,plain,
    ( spl4_146
  <=> v1_xboole_0(sK3(sK3(k1_zfmisc_1(sK3(sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_146])])).

fof(f687,plain,
    ( spl4_126
  <=> m1_subset_1(sK3(sK3(k1_zfmisc_1(sK3(sK2)))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_126])])).

fof(f696,plain,
    ( v1_xboole_0(sK3(sK3(k1_zfmisc_1(sK3(sK2)))))
    | v1_xboole_0(sK0)
    | ~ m1_subset_1(sK0,sK3(sK3(k1_zfmisc_1(sK3(sK2)))))
    | ~ spl4_126 ),
    inference(resolution,[],[f688,f131])).

fof(f688,plain,
    ( m1_subset_1(sK3(sK3(k1_zfmisc_1(sK3(sK2)))),sK0)
    | ~ spl4_126 ),
    inference(avatar_component_clause,[],[f687])).

fof(f768,plain,
    ( ~ spl4_141
    | spl4_88
    | spl4_142
    | ~ spl4_120 ),
    inference(avatar_split_clause,[],[f682,f655,f766,f477,f760])).

fof(f760,plain,
    ( spl4_141
  <=> ~ m1_subset_1(sK0,sK3(sK3(k1_zfmisc_1(sK3(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_141])])).

fof(f766,plain,
    ( spl4_142
  <=> v1_xboole_0(sK3(sK3(k1_zfmisc_1(sK3(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_142])])).

fof(f655,plain,
    ( spl4_120
  <=> m1_subset_1(sK3(sK3(k1_zfmisc_1(sK3(sK1)))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_120])])).

fof(f682,plain,
    ( v1_xboole_0(sK3(sK3(k1_zfmisc_1(sK3(sK1)))))
    | v1_xboole_0(sK0)
    | ~ m1_subset_1(sK0,sK3(sK3(k1_zfmisc_1(sK3(sK1)))))
    | ~ spl4_120 ),
    inference(resolution,[],[f656,f131])).

fof(f656,plain,
    ( m1_subset_1(sK3(sK3(k1_zfmisc_1(sK3(sK1)))),sK0)
    | ~ spl4_120 ),
    inference(avatar_component_clause,[],[f655])).

fof(f755,plain,
    ( ~ spl4_139
    | spl4_67
    | ~ spl4_132 ),
    inference(avatar_split_clause,[],[f748,f710,f396,f753])).

fof(f753,plain,
    ( spl4_139
  <=> ~ m1_subset_1(k7_setfam_1(sK0,sK2),sK3(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_139])])).

fof(f396,plain,
    ( spl4_67
  <=> ~ v1_xboole_0(sK3(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_67])])).

fof(f710,plain,
    ( spl4_132
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | ~ m1_subset_1(k7_setfam_1(sK0,sK2),X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_132])])).

fof(f748,plain,
    ( ~ m1_subset_1(k7_setfam_1(sK0,sK2),sK3(sK1))
    | ~ spl4_67
    | ~ spl4_132 ),
    inference(subsumption_resolution,[],[f746,f397])).

fof(f397,plain,
    ( ~ v1_xboole_0(sK3(sK1))
    | ~ spl4_67 ),
    inference(avatar_component_clause,[],[f396])).

fof(f746,plain,
    ( ~ m1_subset_1(k7_setfam_1(sK0,sK2),sK3(sK1))
    | v1_xboole_0(sK3(sK1))
    | ~ spl4_132 ),
    inference(resolution,[],[f711,f51])).

fof(f711,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | ~ m1_subset_1(k7_setfam_1(sK0,sK2),X0)
        | v1_xboole_0(X0) )
    | ~ spl4_132 ),
    inference(avatar_component_clause,[],[f710])).

fof(f745,plain,
    ( spl4_136
    | ~ spl4_14
    | ~ spl4_134 ),
    inference(avatar_split_clause,[],[f730,f724,f123,f743])).

fof(f743,plain,
    ( spl4_136
  <=> r1_tarski(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_136])])).

fof(f724,plain,
    ( spl4_134
  <=> k7_setfam_1(sK0,sK2) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_134])])).

fof(f730,plain,
    ( r1_tarski(sK1,k1_xboole_0)
    | ~ spl4_14
    | ~ spl4_134 ),
    inference(superposition,[],[f124,f725])).

fof(f725,plain,
    ( k7_setfam_1(sK0,sK2) = k1_xboole_0
    | ~ spl4_134 ),
    inference(avatar_component_clause,[],[f724])).

fof(f726,plain,
    ( spl4_134
    | ~ spl4_98
    | ~ spl4_100
    | ~ spl4_130 ),
    inference(avatar_split_clause,[],[f717,f707,f548,f532,f724])).

fof(f717,plain,
    ( k7_setfam_1(sK0,sK2) = k1_xboole_0
    | ~ spl4_98
    | ~ spl4_100
    | ~ spl4_130 ),
    inference(forward_demodulation,[],[f713,f549])).

fof(f713,plain,
    ( k7_setfam_1(sK0,sK2) = sK3(k1_zfmisc_1(sK1))
    | ~ spl4_98
    | ~ spl4_130 ),
    inference(resolution,[],[f708,f536])).

fof(f708,plain,
    ( v1_xboole_0(k7_setfam_1(sK0,sK2))
    | ~ spl4_130 ),
    inference(avatar_component_clause,[],[f707])).

fof(f712,plain,
    ( spl4_130
    | spl4_132
    | ~ spl4_14
    | spl4_21 ),
    inference(avatar_split_clause,[],[f508,f151,f123,f710,f707])).

fof(f508,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | v1_xboole_0(X0)
        | v1_xboole_0(k7_setfam_1(sK0,sK2))
        | ~ m1_subset_1(k7_setfam_1(sK0,sK2),X0) )
    | ~ spl4_14
    | ~ spl4_21 ),
    inference(resolution,[],[f507,f131])).

fof(f695,plain,
    ( spl4_126
    | spl4_128
    | ~ spl4_76 ),
    inference(avatar_split_clause,[],[f520,f435,f693,f687])).

fof(f693,plain,
    ( spl4_128
  <=> v1_xboole_0(sK3(k1_zfmisc_1(sK3(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_128])])).

fof(f435,plain,
    ( spl4_76
  <=> ! [X0] :
        ( m1_subset_1(X0,sK0)
        | ~ m1_subset_1(X0,sK3(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_76])])).

fof(f520,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(sK3(sK2))))
    | m1_subset_1(sK3(sK3(k1_zfmisc_1(sK3(sK2)))),sK0)
    | ~ spl4_76 ),
    inference(resolution,[],[f509,f436])).

fof(f436,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK3(sK2))
        | m1_subset_1(X0,sK0) )
    | ~ spl4_76 ),
    inference(avatar_component_clause,[],[f435])).

fof(f677,plain,
    ( spl4_124
    | ~ spl4_98
    | ~ spl4_100
    | ~ spl4_122 ),
    inference(avatar_split_clause,[],[f668,f661,f548,f532,f675])).

fof(f675,plain,
    ( spl4_124
  <=> k1_xboole_0 = sK3(k1_zfmisc_1(sK3(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_124])])).

fof(f661,plain,
    ( spl4_122
  <=> v1_xboole_0(sK3(k1_zfmisc_1(sK3(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_122])])).

fof(f668,plain,
    ( k1_xboole_0 = sK3(k1_zfmisc_1(sK3(sK1)))
    | ~ spl4_98
    | ~ spl4_100
    | ~ spl4_122 ),
    inference(forward_demodulation,[],[f664,f549])).

fof(f664,plain,
    ( sK3(k1_zfmisc_1(sK1)) = sK3(k1_zfmisc_1(sK3(sK1)))
    | ~ spl4_98
    | ~ spl4_122 ),
    inference(resolution,[],[f662,f536])).

fof(f662,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(sK3(sK1))))
    | ~ spl4_122 ),
    inference(avatar_component_clause,[],[f661])).

fof(f663,plain,
    ( spl4_120
    | spl4_122
    | ~ spl4_68 ),
    inference(avatar_split_clause,[],[f519,f402,f661,f655])).

fof(f402,plain,
    ( spl4_68
  <=> ! [X0] :
        ( m1_subset_1(X0,sK0)
        | ~ m1_subset_1(X0,sK3(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_68])])).

fof(f519,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(sK3(sK1))))
    | m1_subset_1(sK3(sK3(k1_zfmisc_1(sK3(sK1)))),sK0)
    | ~ spl4_68 ),
    inference(resolution,[],[f509,f403])).

fof(f403,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK3(sK1))
        | m1_subset_1(X0,sK0) )
    | ~ spl4_68 ),
    inference(avatar_component_clause,[],[f402])).

fof(f649,plain,
    ( ~ spl4_119
    | spl4_107
    | ~ spl4_112 ),
    inference(avatar_split_clause,[],[f618,f615,f580,f647])).

fof(f647,plain,
    ( spl4_119
  <=> ~ m1_subset_1(sK3(k1_xboole_0),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_119])])).

fof(f580,plain,
    ( spl4_107
  <=> ~ m1_subset_1(sK3(sK3(k1_zfmisc_1(sK2))),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_107])])).

fof(f615,plain,
    ( spl4_112
  <=> k1_xboole_0 = sK3(k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_112])])).

fof(f618,plain,
    ( ~ m1_subset_1(sK3(k1_xboole_0),k1_zfmisc_1(sK0))
    | ~ spl4_107
    | ~ spl4_112 ),
    inference(superposition,[],[f581,f616])).

fof(f616,plain,
    ( k1_xboole_0 = sK3(k1_zfmisc_1(sK2))
    | ~ spl4_112 ),
    inference(avatar_component_clause,[],[f615])).

fof(f581,plain,
    ( ~ m1_subset_1(sK3(sK3(k1_zfmisc_1(sK2))),k1_zfmisc_1(sK0))
    | ~ spl4_107 ),
    inference(avatar_component_clause,[],[f580])).

fof(f639,plain,
    ( spl4_116
    | ~ spl4_112 ),
    inference(avatar_split_clause,[],[f624,f615,f637])).

fof(f637,plain,
    ( spl4_116
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_116])])).

fof(f624,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK2))
    | ~ spl4_112 ),
    inference(superposition,[],[f51,f616])).

fof(f631,plain,
    ( spl4_114
    | ~ spl4_112 ),
    inference(avatar_split_clause,[],[f622,f615,f629])).

fof(f629,plain,
    ( spl4_114
  <=> r1_tarski(k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_114])])).

fof(f622,plain,
    ( r1_tarski(k1_xboole_0,sK2)
    | ~ spl4_112 ),
    inference(superposition,[],[f94,f616])).

fof(f94,plain,(
    ! [X0] : r1_tarski(sK3(k1_zfmisc_1(X0)),X0) ),
    inference(resolution,[],[f58,f51])).

fof(f617,plain,
    ( spl4_112
    | ~ spl4_98
    | ~ spl4_100
    | ~ spl4_108 ),
    inference(avatar_split_clause,[],[f606,f589,f548,f532,f615])).

fof(f589,plain,
    ( spl4_108
  <=> v1_xboole_0(sK3(k1_zfmisc_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_108])])).

fof(f606,plain,
    ( k1_xboole_0 = sK3(k1_zfmisc_1(sK2))
    | ~ spl4_98
    | ~ spl4_100
    | ~ spl4_108 ),
    inference(forward_demodulation,[],[f602,f549])).

fof(f602,plain,
    ( sK3(k1_zfmisc_1(sK1)) = sK3(k1_zfmisc_1(sK2))
    | ~ spl4_98
    | ~ spl4_108 ),
    inference(resolution,[],[f590,f536])).

fof(f590,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(sK2)))
    | ~ spl4_108 ),
    inference(avatar_component_clause,[],[f589])).

fof(f601,plain,
    ( spl4_110
    | ~ spl4_106 ),
    inference(avatar_split_clause,[],[f593,f583,f599])).

fof(f599,plain,
    ( spl4_110
  <=> r1_tarski(sK3(sK3(k1_zfmisc_1(sK2))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_110])])).

fof(f583,plain,
    ( spl4_106
  <=> m1_subset_1(sK3(sK3(k1_zfmisc_1(sK2))),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_106])])).

fof(f593,plain,
    ( r1_tarski(sK3(sK3(k1_zfmisc_1(sK2))),sK0)
    | ~ spl4_106 ),
    inference(resolution,[],[f584,f58])).

fof(f584,plain,
    ( m1_subset_1(sK3(sK3(k1_zfmisc_1(sK2))),k1_zfmisc_1(sK0))
    | ~ spl4_106 ),
    inference(avatar_component_clause,[],[f583])).

fof(f591,plain,
    ( spl4_106
    | spl4_108
    | ~ spl4_50 ),
    inference(avatar_split_clause,[],[f517,f305,f589,f583])).

fof(f517,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(sK2)))
    | m1_subset_1(sK3(sK3(k1_zfmisc_1(sK2))),k1_zfmisc_1(sK0))
    | ~ spl4_50 ),
    inference(resolution,[],[f509,f306])).

fof(f571,plain,
    ( spl4_104
    | ~ spl4_100 ),
    inference(avatar_split_clause,[],[f556,f548,f569])).

fof(f569,plain,
    ( spl4_104
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_104])])).

fof(f556,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1))
    | ~ spl4_100 ),
    inference(superposition,[],[f51,f549])).

fof(f563,plain,
    ( spl4_102
    | ~ spl4_100 ),
    inference(avatar_split_clause,[],[f554,f548,f561])).

fof(f561,plain,
    ( spl4_102
  <=> r1_tarski(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_102])])).

fof(f554,plain,
    ( r1_tarski(k1_xboole_0,sK1)
    | ~ spl4_100 ),
    inference(superposition,[],[f94,f549])).

fof(f550,plain,
    ( spl4_100
    | ~ spl4_98 ),
    inference(avatar_split_clause,[],[f537,f532,f548])).

fof(f537,plain,
    ( k1_xboole_0 = sK3(k1_zfmisc_1(sK1))
    | ~ spl4_98 ),
    inference(resolution,[],[f533,f50])).

fof(f50,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t52_setfam_1.p',t6_boole)).

fof(f534,plain,
    ( spl4_96
    | spl4_98
    | ~ spl4_40 ),
    inference(avatar_split_clause,[],[f516,f254,f532,f526])).

fof(f526,plain,
    ( spl4_96
  <=> m1_subset_1(sK3(sK3(k1_zfmisc_1(sK1))),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_96])])).

fof(f254,plain,
    ( spl4_40
  <=> ! [X7] :
        ( m1_subset_1(X7,k1_zfmisc_1(sK0))
        | ~ m1_subset_1(X7,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f516,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(sK1)))
    | m1_subset_1(sK3(sK3(k1_zfmisc_1(sK1))),k1_zfmisc_1(sK0))
    | ~ spl4_40 ),
    inference(resolution,[],[f509,f255])).

fof(f255,plain,
    ( ! [X7] :
        ( ~ m1_subset_1(X7,sK1)
        | m1_subset_1(X7,k1_zfmisc_1(sK0)) )
    | ~ spl4_40 ),
    inference(avatar_component_clause,[],[f254])).

fof(f498,plain,
    ( ~ spl4_93
    | spl4_88
    | spl4_94
    | ~ spl4_78 ),
    inference(avatar_split_clause,[],[f446,f443,f496,f477,f490])).

fof(f490,plain,
    ( spl4_93
  <=> ~ m1_subset_1(sK0,sK3(sK3(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_93])])).

fof(f496,plain,
    ( spl4_94
  <=> v1_xboole_0(sK3(sK3(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_94])])).

fof(f443,plain,
    ( spl4_78
  <=> m1_subset_1(sK3(sK3(sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_78])])).

fof(f446,plain,
    ( v1_xboole_0(sK3(sK3(sK2)))
    | v1_xboole_0(sK0)
    | ~ m1_subset_1(sK0,sK3(sK3(sK2)))
    | ~ spl4_78 ),
    inference(resolution,[],[f444,f131])).

fof(f444,plain,
    ( m1_subset_1(sK3(sK3(sK2)),sK0)
    | ~ spl4_78 ),
    inference(avatar_component_clause,[],[f443])).

fof(f485,plain,
    ( ~ spl4_87
    | spl4_88
    | spl4_90
    | ~ spl4_72 ),
    inference(avatar_split_clause,[],[f427,f424,f483,f477,f471])).

fof(f471,plain,
    ( spl4_87
  <=> ~ m1_subset_1(sK0,sK3(sK3(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_87])])).

fof(f483,plain,
    ( spl4_90
  <=> v1_xboole_0(sK3(sK3(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_90])])).

fof(f424,plain,
    ( spl4_72
  <=> m1_subset_1(sK3(sK3(sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_72])])).

fof(f427,plain,
    ( v1_xboole_0(sK3(sK3(sK1)))
    | v1_xboole_0(sK0)
    | ~ m1_subset_1(sK0,sK3(sK3(sK1)))
    | ~ spl4_72 ),
    inference(resolution,[],[f425,f131])).

fof(f425,plain,
    ( m1_subset_1(sK3(sK3(sK1)),sK0)
    | ~ spl4_72 ),
    inference(avatar_component_clause,[],[f424])).

fof(f466,plain,
    ( ~ spl4_85
    | spl4_82
    | spl4_74
    | ~ spl4_54 ),
    inference(avatar_split_clause,[],[f393,f327,f432,f457,f464])).

fof(f464,plain,
    ( spl4_85
  <=> ~ m1_subset_1(k1_zfmisc_1(sK0),sK3(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_85])])).

fof(f432,plain,
    ( spl4_74
  <=> v1_xboole_0(sK3(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_74])])).

fof(f327,plain,
    ( spl4_54
  <=> m1_subset_1(sK3(sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).

fof(f393,plain,
    ( v1_xboole_0(sK3(sK2))
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ m1_subset_1(k1_zfmisc_1(sK0),sK3(sK2))
    | ~ spl4_54 ),
    inference(resolution,[],[f328,f131])).

fof(f328,plain,
    ( m1_subset_1(sK3(sK2),k1_zfmisc_1(sK0))
    | ~ spl4_54 ),
    inference(avatar_component_clause,[],[f327])).

fof(f459,plain,
    ( ~ spl4_81
    | spl4_82
    | spl4_66
    | ~ spl4_42 ),
    inference(avatar_split_clause,[],[f302,f262,f399,f457,f451])).

fof(f451,plain,
    ( spl4_81
  <=> ~ m1_subset_1(k1_zfmisc_1(sK0),sK3(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_81])])).

fof(f399,plain,
    ( spl4_66
  <=> v1_xboole_0(sK3(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_66])])).

fof(f262,plain,
    ( spl4_42
  <=> m1_subset_1(sK3(sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).

fof(f302,plain,
    ( v1_xboole_0(sK3(sK1))
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ m1_subset_1(k1_zfmisc_1(sK0),sK3(sK1))
    | ~ spl4_42 ),
    inference(resolution,[],[f263,f131])).

fof(f263,plain,
    ( m1_subset_1(sK3(sK1),k1_zfmisc_1(sK0))
    | ~ spl4_42 ),
    inference(avatar_component_clause,[],[f262])).

fof(f445,plain,
    ( spl4_78
    | ~ spl4_76 ),
    inference(avatar_split_clause,[],[f438,f435,f443])).

fof(f438,plain,
    ( m1_subset_1(sK3(sK3(sK2)),sK0)
    | ~ spl4_76 ),
    inference(resolution,[],[f436,f51])).

fof(f437,plain,
    ( spl4_74
    | spl4_76
    | ~ spl4_54 ),
    inference(avatar_split_clause,[],[f391,f327,f435,f432])).

fof(f391,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,sK0)
        | v1_xboole_0(sK3(sK2))
        | ~ m1_subset_1(X0,sK3(sK2)) )
    | ~ spl4_54 ),
    inference(resolution,[],[f328,f133])).

fof(f426,plain,
    ( spl4_72
    | ~ spl4_68 ),
    inference(avatar_split_clause,[],[f419,f402,f424])).

fof(f419,plain,
    ( m1_subset_1(sK3(sK3(sK1)),sK0)
    | ~ spl4_68 ),
    inference(resolution,[],[f403,f51])).

fof(f418,plain,
    ( spl4_70
    | ~ spl4_66 ),
    inference(avatar_split_clause,[],[f411,f399,f416])).

fof(f416,plain,
    ( spl4_70
  <=> k1_xboole_0 = sK3(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_70])])).

fof(f411,plain,
    ( k1_xboole_0 = sK3(sK1)
    | ~ spl4_66 ),
    inference(resolution,[],[f400,f50])).

fof(f400,plain,
    ( v1_xboole_0(sK3(sK1))
    | ~ spl4_66 ),
    inference(avatar_component_clause,[],[f399])).

fof(f404,plain,
    ( spl4_66
    | spl4_68
    | ~ spl4_42 ),
    inference(avatar_split_clause,[],[f300,f262,f402,f399])).

fof(f300,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,sK0)
        | v1_xboole_0(sK3(sK1))
        | ~ m1_subset_1(X0,sK3(sK1)) )
    | ~ spl4_42 ),
    inference(resolution,[],[f263,f133])).

fof(f390,plain,
    ( spl4_64
    | ~ spl4_14
    | ~ spl4_52 ),
    inference(avatar_split_clause,[],[f360,f315,f123,f388])).

fof(f388,plain,
    ( spl4_64
  <=> r1_tarski(sK1,k7_setfam_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_64])])).

fof(f315,plain,
    ( spl4_52
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).

fof(f360,plain,
    ( r1_tarski(sK1,k7_setfam_1(sK0,k1_xboole_0))
    | ~ spl4_14
    | ~ spl4_52 ),
    inference(superposition,[],[f124,f316])).

fof(f316,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_52 ),
    inference(avatar_component_clause,[],[f315])).

fof(f383,plain,
    ( ~ spl4_63
    | spl4_13
    | ~ spl4_52 ),
    inference(avatar_split_clause,[],[f359,f315,f114,f381])).

fof(f381,plain,
    ( spl4_63
  <=> ~ r1_tarski(k7_setfam_1(sK0,sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_63])])).

fof(f359,plain,
    ( ~ r1_tarski(k7_setfam_1(sK0,sK1),k1_xboole_0)
    | ~ spl4_13
    | ~ spl4_52 ),
    inference(superposition,[],[f115,f316])).

fof(f372,plain,
    ( ~ spl4_61
    | ~ spl4_52
    | spl4_55 ),
    inference(avatar_split_clause,[],[f365,f324,f315,f370])).

fof(f370,plain,
    ( spl4_61
  <=> ~ r1_tarski(sK3(k1_xboole_0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_61])])).

fof(f324,plain,
    ( spl4_55
  <=> ~ m1_subset_1(sK3(sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_55])])).

fof(f365,plain,
    ( ~ r1_tarski(sK3(k1_xboole_0),sK0)
    | ~ spl4_52
    | ~ spl4_55 ),
    inference(forward_demodulation,[],[f363,f316])).

fof(f363,plain,
    ( ~ r1_tarski(sK3(sK2),sK0)
    | ~ spl4_55 ),
    inference(resolution,[],[f325,f59])).

fof(f325,plain,
    ( ~ m1_subset_1(sK3(sK2),k1_zfmisc_1(sK0))
    | ~ spl4_55 ),
    inference(avatar_component_clause,[],[f324])).

fof(f355,plain,
    ( spl4_58
    | ~ spl4_54 ),
    inference(avatar_split_clause,[],[f347,f327,f353])).

fof(f353,plain,
    ( spl4_58
  <=> r1_tarski(sK3(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_58])])).

fof(f347,plain,
    ( r1_tarski(sK3(sK2),sK0)
    | ~ spl4_54 ),
    inference(resolution,[],[f328,f58])).

fof(f345,plain,
    ( spl4_56
    | ~ spl4_6
    | ~ spl4_52 ),
    inference(avatar_split_clause,[],[f331,f315,f90,f343])).

fof(f343,plain,
    ( spl4_56
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).

fof(f331,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl4_6
    | ~ spl4_52 ),
    inference(superposition,[],[f91,f316])).

fof(f337,plain,
    ( spl4_48
    | ~ spl4_10
    | ~ spl4_52 ),
    inference(avatar_split_clause,[],[f332,f315,f108,f297])).

fof(f297,plain,
    ( spl4_48
  <=> r1_tarski(k1_xboole_0,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).

fof(f108,plain,
    ( spl4_10
  <=> r1_tarski(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f332,plain,
    ( r1_tarski(k1_xboole_0,k1_zfmisc_1(sK0))
    | ~ spl4_10
    | ~ spl4_52 ),
    inference(superposition,[],[f109,f316])).

fof(f109,plain,
    ( r1_tarski(sK2,k1_zfmisc_1(sK0))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f108])).

fof(f329,plain,
    ( spl4_54
    | ~ spl4_50 ),
    inference(avatar_split_clause,[],[f322,f305,f327])).

fof(f322,plain,
    ( m1_subset_1(sK3(sK2),k1_zfmisc_1(sK0))
    | ~ spl4_50 ),
    inference(resolution,[],[f306,f51])).

fof(f317,plain,
    ( spl4_52
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f310,f167,f315])).

fof(f167,plain,
    ( spl4_24
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f310,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_24 ),
    inference(resolution,[],[f168,f50])).

fof(f168,plain,
    ( v1_xboole_0(sK2)
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f167])).

fof(f307,plain,
    ( spl4_24
    | spl4_50
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f251,f90,f305,f167])).

fof(f251,plain,
    ( ! [X8] :
        ( m1_subset_1(X8,k1_zfmisc_1(sK0))
        | v1_xboole_0(sK2)
        | ~ m1_subset_1(X8,sK2) )
    | ~ spl4_6 ),
    inference(resolution,[],[f133,f91])).

fof(f299,plain,
    ( spl4_48
    | ~ spl4_8
    | ~ spl4_44 ),
    inference(avatar_split_clause,[],[f288,f272,f101,f297])).

fof(f101,plain,
    ( spl4_8
  <=> r1_tarski(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f272,plain,
    ( spl4_44
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).

fof(f288,plain,
    ( r1_tarski(k1_xboole_0,k1_zfmisc_1(sK0))
    | ~ spl4_8
    | ~ spl4_44 ),
    inference(superposition,[],[f102,f273])).

fof(f273,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_44 ),
    inference(avatar_component_clause,[],[f272])).

fof(f102,plain,
    ( r1_tarski(sK1,k1_zfmisc_1(sK0))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f101])).

fof(f284,plain,
    ( spl4_46
    | ~ spl4_42 ),
    inference(avatar_split_clause,[],[f276,f262,f282])).

fof(f282,plain,
    ( spl4_46
  <=> r1_tarski(sK3(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).

fof(f276,plain,
    ( r1_tarski(sK3(sK1),sK0)
    | ~ spl4_42 ),
    inference(resolution,[],[f263,f58])).

fof(f274,plain,
    ( spl4_44
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f267,f154,f272])).

fof(f154,plain,
    ( spl4_20
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f267,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_20 ),
    inference(resolution,[],[f155,f50])).

fof(f155,plain,
    ( v1_xboole_0(sK1)
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f154])).

fof(f264,plain,
    ( spl4_42
    | ~ spl4_40 ),
    inference(avatar_split_clause,[],[f257,f254,f262])).

fof(f257,plain,
    ( m1_subset_1(sK3(sK1),k1_zfmisc_1(sK0))
    | ~ spl4_40 ),
    inference(resolution,[],[f255,f51])).

fof(f256,plain,
    ( spl4_20
    | spl4_40
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f250,f83,f254,f154])).

fof(f250,plain,
    ( ! [X7] :
        ( m1_subset_1(X7,k1_zfmisc_1(sK0))
        | v1_xboole_0(sK1)
        | ~ m1_subset_1(X7,sK1) )
    | ~ spl4_4 ),
    inference(resolution,[],[f133,f84])).

fof(f235,plain,
    ( spl4_38
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f220,f90,f233])).

fof(f220,plain,
    ( k7_setfam_1(sK0,k7_setfam_1(sK0,sK2)) = sK2
    | ~ spl4_6 ),
    inference(resolution,[],[f55,f91])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t52_setfam_1.p',involutiveness_k7_setfam_1)).

fof(f228,plain,
    ( spl4_36
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f219,f83,f226])).

fof(f219,plain,
    ( k7_setfam_1(sK0,k7_setfam_1(sK0,sK1)) = sK1
    | ~ spl4_4 ),
    inference(resolution,[],[f55,f84])).

fof(f214,plain,
    ( spl4_34
    | ~ spl4_30 ),
    inference(avatar_split_clause,[],[f198,f190,f212])).

fof(f212,plain,
    ( spl4_34
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f190,plain,
    ( spl4_30
  <=> k1_xboole_0 = sK3(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f198,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_30 ),
    inference(superposition,[],[f51,f191])).

fof(f191,plain,
    ( k1_xboole_0 = sK3(k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f190])).

fof(f206,plain,
    ( spl4_32
    | ~ spl4_30 ),
    inference(avatar_split_clause,[],[f196,f190,f204])).

fof(f204,plain,
    ( spl4_32
  <=> r1_tarski(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f196,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl4_30 ),
    inference(superposition,[],[f94,f191])).

fof(f194,plain,(
    ~ spl4_26 ),
    inference(avatar_contradiction_clause,[],[f193])).

fof(f193,plain,
    ( $false
    | ~ spl4_26 ),
    inference(resolution,[],[f175,f51])).

fof(f175,plain,
    ( ! [X2] : ~ m1_subset_1(X2,sK3(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f174])).

fof(f174,plain,
    ( spl4_26
  <=> ! [X2] : ~ m1_subset_1(X2,sK3(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f192,plain,
    ( spl4_30
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f185,f180,f190])).

fof(f180,plain,
    ( spl4_28
  <=> v1_xboole_0(sK3(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f185,plain,
    ( k1_xboole_0 = sK3(k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_28 ),
    inference(resolution,[],[f181,f50])).

fof(f181,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f180])).

fof(f182,plain,
    ( spl4_26
    | spl4_28
    | ~ spl4_0 ),
    inference(avatar_split_clause,[],[f171,f69,f180,f174])).

fof(f69,plain,
    ( spl4_0
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_0])])).

fof(f171,plain,
    ( ! [X2] :
        ( v1_xboole_0(sK3(k1_zfmisc_1(k1_xboole_0)))
        | ~ m1_subset_1(X2,sK3(k1_zfmisc_1(k1_xboole_0))) )
    | ~ spl4_0 ),
    inference(resolution,[],[f132,f51])).

fof(f132,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X1,X0) )
    | ~ spl4_0 ),
    inference(resolution,[],[f130,f54])).

fof(f130,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl4_0 ),
    inference(resolution,[],[f63,f70])).

fof(f70,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_0 ),
    inference(avatar_component_clause,[],[f69])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t52_setfam_1.p',t5_subset)).

fof(f169,plain,
    ( ~ spl4_23
    | spl4_18
    | spl4_24
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f136,f90,f167,f148,f161])).

fof(f161,plain,
    ( spl4_23
  <=> ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(sK0)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f148,plain,
    ( spl4_18
  <=> v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f136,plain,
    ( v1_xboole_0(sK2)
    | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(sK0)),sK2)
    | ~ spl4_6 ),
    inference(resolution,[],[f131,f91])).

fof(f156,plain,
    ( ~ spl4_17
    | spl4_18
    | spl4_20
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f135,f83,f154,f148,f142])).

fof(f142,plain,
    ( spl4_17
  <=> ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f135,plain,
    ( v1_xboole_0(sK1)
    | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(sK0)),sK1)
    | ~ spl4_4 ),
    inference(resolution,[],[f131,f84])).

fof(f126,plain,
    ( ~ spl4_13
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f47,f120,f114])).

fof(f47,plain,
    ( ~ r1_tarski(sK1,k7_setfam_1(sK0,sK2))
    | ~ r1_tarski(k7_setfam_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( ( ~ r1_tarski(sK1,k7_setfam_1(sK0,sK2))
      | ~ r1_tarski(k7_setfam_1(sK0,sK1),sK2) )
    & ( r1_tarski(sK1,k7_setfam_1(sK0,sK2))
      | r1_tarski(k7_setfam_1(sK0,sK1),sK2) )
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f37,f39,f38])).

fof(f38,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ~ r1_tarski(X1,k7_setfam_1(X0,X2))
              | ~ r1_tarski(k7_setfam_1(X0,X1),X2) )
            & ( r1_tarski(X1,k7_setfam_1(X0,X2))
              | r1_tarski(k7_setfam_1(X0,X1),X2) )
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( ? [X2] :
          ( ( ~ r1_tarski(sK1,k7_setfam_1(sK0,X2))
            | ~ r1_tarski(k7_setfam_1(sK0,sK1),X2) )
          & ( r1_tarski(sK1,k7_setfam_1(sK0,X2))
            | r1_tarski(k7_setfam_1(sK0,sK1),X2) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X1,k7_setfam_1(X0,X2))
            | ~ r1_tarski(k7_setfam_1(X0,X1),X2) )
          & ( r1_tarski(X1,k7_setfam_1(X0,X2))
            | r1_tarski(k7_setfam_1(X0,X1),X2) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
     => ( ( ~ r1_tarski(X1,k7_setfam_1(X0,sK2))
          | ~ r1_tarski(k7_setfam_1(X0,X1),sK2) )
        & ( r1_tarski(X1,k7_setfam_1(X0,sK2))
          | r1_tarski(k7_setfam_1(X0,X1),sK2) )
        & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X1,k7_setfam_1(X0,X2))
            | ~ r1_tarski(k7_setfam_1(X0,X1),X2) )
          & ( r1_tarski(X1,k7_setfam_1(X0,X2))
            | r1_tarski(k7_setfam_1(X0,X1),X2) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X1,k7_setfam_1(X0,X2))
            | ~ r1_tarski(k7_setfam_1(X0,X1),X2) )
          & ( r1_tarski(X1,k7_setfam_1(X0,X2))
            | r1_tarski(k7_setfam_1(X0,X1),X2) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_tarski(k7_setfam_1(X0,X1),X2)
          <~> r1_tarski(X1,k7_setfam_1(X0,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
           => ( r1_tarski(k7_setfam_1(X0,X1),X2)
            <=> r1_tarski(X1,k7_setfam_1(X0,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( r1_tarski(k7_setfam_1(X0,X1),X2)
          <=> r1_tarski(X1,k7_setfam_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t52_setfam_1.p',t52_setfam_1)).

fof(f125,plain,
    ( spl4_12
    | spl4_14 ),
    inference(avatar_split_clause,[],[f46,f123,f117])).

fof(f46,plain,
    ( r1_tarski(sK1,k7_setfam_1(sK0,sK2))
    | r1_tarski(k7_setfam_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f110,plain,
    ( spl4_10
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f96,f90,f108])).

fof(f96,plain,
    ( r1_tarski(sK2,k1_zfmisc_1(sK0))
    | ~ spl4_6 ),
    inference(resolution,[],[f58,f91])).

fof(f103,plain,
    ( spl4_8
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f95,f83,f101])).

fof(f95,plain,
    ( r1_tarski(sK1,k1_zfmisc_1(sK0))
    | ~ spl4_4 ),
    inference(resolution,[],[f58,f84])).

fof(f92,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f45,f90])).

fof(f45,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f40])).

fof(f85,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f44,f83])).

fof(f44,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f40])).

fof(f78,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f49,f76])).

fof(f76,plain,
    ( spl4_2
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f49,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t52_setfam_1.p',d2_xboole_0)).

fof(f71,plain,(
    spl4_0 ),
    inference(avatar_split_clause,[],[f64,f69])).

fof(f64,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(forward_demodulation,[],[f48,f49])).

fof(f48,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t52_setfam_1.p',dt_o_0_0_xboole_0)).
%------------------------------------------------------------------------------
