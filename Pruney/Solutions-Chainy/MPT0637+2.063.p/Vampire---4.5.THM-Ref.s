%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:31 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  223 ( 498 expanded)
%              Number of leaves         :   56 ( 236 expanded)
%              Depth                    :   12
%              Number of atoms          :  617 (1219 expanded)
%              Number of equality atoms :  161 ( 361 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    7 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1589,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f77,f81,f89,f93,f101,f117,f121,f132,f136,f140,f149,f162,f169,f175,f179,f187,f201,f206,f210,f218,f275,f337,f397,f410,f562,f768,f784,f788,f796,f812,f821,f875,f1181,f1355,f1472,f1542])).

fof(f1542,plain,
    ( spl2_67
    | ~ spl2_71
    | ~ spl2_90 ),
    inference(avatar_contradiction_clause,[],[f1541])).

fof(f1541,plain,
    ( $false
    | spl2_67
    | ~ spl2_71
    | ~ spl2_90 ),
    inference(subsumption_resolution,[],[f1477,f820])).

fof(f820,plain,
    ( ! [X2,X3] : k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k6_relat_1(X3),X2)
    | ~ spl2_71 ),
    inference(avatar_component_clause,[],[f819])).

fof(f819,plain,
    ( spl2_71
  <=> ! [X3,X2] : k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k6_relat_1(X3),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_71])])).

fof(f1477,plain,
    ( k7_relat_1(k6_relat_1(sK0),sK1) != k7_relat_1(k6_relat_1(sK1),sK0)
    | spl2_67
    | ~ spl2_90 ),
    inference(superposition,[],[f783,f1471])).

fof(f1471,plain,
    ( ! [X2,X3] : k7_relat_1(k6_relat_1(X3),X2) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X2),X3)))
    | ~ spl2_90 ),
    inference(avatar_component_clause,[],[f1470])).

fof(f1470,plain,
    ( spl2_90
  <=> ! [X3,X2] : k7_relat_1(k6_relat_1(X3),X2) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X2),X3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_90])])).

fof(f783,plain,
    ( k7_relat_1(k6_relat_1(sK0),sK1) != k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1)))
    | spl2_67 ),
    inference(avatar_component_clause,[],[f781])).

fof(f781,plain,
    ( spl2_67
  <=> k7_relat_1(k6_relat_1(sK0),sK1) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_67])])).

fof(f1472,plain,
    ( spl2_90
    | ~ spl2_17
    | ~ spl2_21
    | ~ spl2_42
    | ~ spl2_71
    | ~ spl2_72
    | ~ spl2_84
    | ~ spl2_89 ),
    inference(avatar_split_clause,[],[f1411,f1353,f1179,f873,f819,f408,f199,f167,f1470])).

fof(f167,plain,
    ( spl2_17
  <=> ! [X1,X0] :
        ( k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f199,plain,
    ( spl2_21
  <=> ! [X1,X0] : k7_relat_1(k6_relat_1(X0),X1) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).

fof(f408,plain,
    ( spl2_42
  <=> ! [X3,X2] : k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X3),k1_relat_1(k7_relat_1(k6_relat_1(X2),X3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_42])])).

fof(f873,plain,
    ( spl2_72
  <=> ! [X63,X62] : r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X63),X62)),X62) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_72])])).

fof(f1179,plain,
    ( spl2_84
  <=> ! [X18,X20,X19] : k7_relat_1(k7_relat_1(k6_relat_1(X20),X19),X18) = k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X19),X18),X20)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_84])])).

fof(f1353,plain,
    ( spl2_89
  <=> ! [X1,X0] : k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_89])])).

fof(f1411,plain,
    ( ! [X2,X3] : k7_relat_1(k6_relat_1(X3),X2) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X2),X3)))
    | ~ spl2_17
    | ~ spl2_21
    | ~ spl2_42
    | ~ spl2_71
    | ~ spl2_72
    | ~ spl2_84
    | ~ spl2_89 ),
    inference(backward_demodulation,[],[f877,f1410])).

fof(f1410,plain,
    ( ! [X33,X32] : k7_relat_1(k6_relat_1(X33),X32) = k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X32),X33))),X33)
    | ~ spl2_21
    | ~ spl2_42
    | ~ spl2_71
    | ~ spl2_84
    | ~ spl2_89 ),
    inference(backward_demodulation,[],[f1218,f1360])).

fof(f1360,plain,
    ( ! [X2,X3] : k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X2),X3))) = k7_relat_1(k6_relat_1(X2),k1_relat_1(k7_relat_1(k6_relat_1(X2),X3)))
    | ~ spl2_71
    | ~ spl2_89 ),
    inference(superposition,[],[f1354,f820])).

fof(f1354,plain,
    ( ! [X0,X1] : k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X0)
    | ~ spl2_89 ),
    inference(avatar_component_clause,[],[f1353])).

fof(f1218,plain,
    ( ! [X33,X32] : k7_relat_1(k6_relat_1(X33),X32) = k7_relat_1(k7_relat_1(k6_relat_1(X32),k1_relat_1(k7_relat_1(k6_relat_1(X32),X33))),X33)
    | ~ spl2_21
    | ~ spl2_42
    | ~ spl2_71
    | ~ spl2_84 ),
    inference(forward_demodulation,[],[f1217,f820])).

fof(f1217,plain,
    ( ! [X33,X32] : k7_relat_1(k6_relat_1(X33),X32) = k7_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X32),X33))),X32),X33)
    | ~ spl2_21
    | ~ spl2_42
    | ~ spl2_84 ),
    inference(forward_demodulation,[],[f1208,f200])).

fof(f200,plain,
    ( ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0))
    | ~ spl2_21 ),
    inference(avatar_component_clause,[],[f199])).

fof(f1208,plain,
    ( ! [X33,X32] : k7_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X32),X33))),X32),X33) = k4_relat_1(k7_relat_1(k6_relat_1(X32),X33))
    | ~ spl2_42
    | ~ spl2_84 ),
    inference(superposition,[],[f1180,f409])).

fof(f409,plain,
    ( ! [X2,X3] : k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X3),k1_relat_1(k7_relat_1(k6_relat_1(X2),X3)))
    | ~ spl2_42 ),
    inference(avatar_component_clause,[],[f408])).

fof(f1180,plain,
    ( ! [X19,X20,X18] : k7_relat_1(k7_relat_1(k6_relat_1(X20),X19),X18) = k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X19),X18),X20))
    | ~ spl2_84 ),
    inference(avatar_component_clause,[],[f1179])).

fof(f877,plain,
    ( ! [X2,X3] : k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X2),X3))) = k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X2),X3))),X3)
    | ~ spl2_17
    | ~ spl2_72 ),
    inference(resolution,[],[f874,f168])).

fof(f168,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1) )
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f167])).

fof(f874,plain,
    ( ! [X62,X63] : r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X63),X62)),X62)
    | ~ spl2_72 ),
    inference(avatar_component_clause,[],[f873])).

fof(f1355,plain,
    ( spl2_89
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_16
    | ~ spl2_17
    | ~ spl2_55 ),
    inference(avatar_split_clause,[],[f761,f560,f167,f160,f79,f75,f1353])).

fof(f75,plain,
    ( spl2_1
  <=> ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f79,plain,
    ( spl2_2
  <=> ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f160,plain,
    ( spl2_16
  <=> ! [X1,X0] : r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f560,plain,
    ( spl2_55
  <=> ! [X1,X0] :
        ( k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k6_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_55])])).

fof(f761,plain,
    ( ! [X0,X1] : k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X0)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_16
    | ~ spl2_17
    | ~ spl2_55 ),
    inference(backward_demodulation,[],[f170,f759])).

fof(f759,plain,
    ( ! [X4,X3] : k1_relat_1(k7_relat_1(k6_relat_1(X3),X4)) = k1_setfam_1(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_55 ),
    inference(forward_demodulation,[],[f755,f80])).

fof(f80,plain,
    ( ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f79])).

fof(f755,plain,
    ( ! [X4,X3] : k1_relat_1(k7_relat_1(k6_relat_1(X3),X4)) = k1_setfam_1(k6_enumset1(k1_relat_1(k6_relat_1(X3)),k1_relat_1(k6_relat_1(X3)),k1_relat_1(k6_relat_1(X3)),k1_relat_1(k6_relat_1(X3)),k1_relat_1(k6_relat_1(X3)),k1_relat_1(k6_relat_1(X3)),k1_relat_1(k6_relat_1(X3)),X4))
    | ~ spl2_1
    | ~ spl2_55 ),
    inference(resolution,[],[f561,f76])).

fof(f76,plain,
    ( ! [X0] : v1_relat_1(k6_relat_1(X0))
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f75])).

fof(f561,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k6_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0)) )
    | ~ spl2_55 ),
    inference(avatar_component_clause,[],[f560])).

fof(f170,plain,
    ( ! [X0,X1] : k6_relat_1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k7_relat_1(k6_relat_1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X0)
    | ~ spl2_16
    | ~ spl2_17 ),
    inference(resolution,[],[f161,f168])).

fof(f161,plain,
    ( ! [X0,X1] : r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0)
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f160])).

fof(f1181,plain,
    ( spl2_84
    | ~ spl2_35
    | ~ spl2_71 ),
    inference(avatar_split_clause,[],[f829,f819,f335,f1179])).

fof(f335,plain,
    ( spl2_35
  <=> ! [X5,X7,X6] : k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X6),X7),X5)) = k7_relat_1(k7_relat_1(k6_relat_1(X5),X7),X6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_35])])).

fof(f829,plain,
    ( ! [X19,X20,X18] : k7_relat_1(k7_relat_1(k6_relat_1(X20),X19),X18) = k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X19),X18),X20))
    | ~ spl2_35
    | ~ spl2_71 ),
    inference(superposition,[],[f336,f820])).

fof(f336,plain,
    ( ! [X6,X7,X5] : k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X6),X7),X5)) = k7_relat_1(k7_relat_1(k6_relat_1(X5),X7),X6)
    | ~ spl2_35 ),
    inference(avatar_component_clause,[],[f335])).

fof(f875,plain,
    ( spl2_72
    | ~ spl2_65
    | ~ spl2_71 ),
    inference(avatar_split_clause,[],[f843,f819,f766,f873])).

fof(f766,plain,
    ( spl2_65
  <=> ! [X1,X0] : r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_65])])).

fof(f843,plain,
    ( ! [X62,X63] : r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X63),X62)),X62)
    | ~ spl2_65
    | ~ spl2_71 ),
    inference(superposition,[],[f767,f820])).

fof(f767,plain,
    ( ! [X0,X1] : r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0)
    | ~ spl2_65 ),
    inference(avatar_component_clause,[],[f766])).

fof(f821,plain,
    ( spl2_71
    | ~ spl2_21
    | ~ spl2_70 ),
    inference(avatar_split_clause,[],[f814,f810,f199,f819])).

fof(f810,plain,
    ( spl2_70
  <=> ! [X3,X4] : k7_relat_1(k6_relat_1(X3),X4) = k4_relat_1(k7_relat_1(k6_relat_1(X3),X4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_70])])).

fof(f814,plain,
    ( ! [X2,X3] : k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k6_relat_1(X3),X2)
    | ~ spl2_21
    | ~ spl2_70 ),
    inference(superposition,[],[f811,f200])).

fof(f811,plain,
    ( ! [X4,X3] : k7_relat_1(k6_relat_1(X3),X4) = k4_relat_1(k7_relat_1(k6_relat_1(X3),X4))
    | ~ spl2_70 ),
    inference(avatar_component_clause,[],[f810])).

fof(f812,plain,
    ( spl2_70
    | ~ spl2_35
    | ~ spl2_69 ),
    inference(avatar_split_clause,[],[f799,f794,f335,f810])).

fof(f794,plain,
    ( spl2_69
  <=> ! [X1,X0] : k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_69])])).

fof(f799,plain,
    ( ! [X4,X3] : k7_relat_1(k6_relat_1(X3),X4) = k4_relat_1(k7_relat_1(k6_relat_1(X3),X4))
    | ~ spl2_35
    | ~ spl2_69 ),
    inference(superposition,[],[f336,f795])).

fof(f795,plain,
    ( ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0)
    | ~ spl2_69 ),
    inference(avatar_component_clause,[],[f794])).

fof(f796,plain,
    ( spl2_69
    | ~ spl2_22
    | ~ spl2_68 ),
    inference(avatar_split_clause,[],[f790,f786,f204,f794])).

fof(f204,plain,
    ( spl2_22
  <=> ! [X1,X0,X2] : k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k5_relat_1(k6_relat_1(X2),k7_relat_1(k6_relat_1(X0),X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f786,plain,
    ( spl2_68
  <=> ! [X1,X0] : k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X0),X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_68])])).

fof(f790,plain,
    ( ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0)
    | ~ spl2_22
    | ~ spl2_68 ),
    inference(superposition,[],[f787,f205])).

fof(f205,plain,
    ( ! [X2,X0,X1] : k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k5_relat_1(k6_relat_1(X2),k7_relat_1(k6_relat_1(X0),X1))
    | ~ spl2_22 ),
    inference(avatar_component_clause,[],[f204])).

fof(f787,plain,
    ( ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X0),X1))
    | ~ spl2_68 ),
    inference(avatar_component_clause,[],[f786])).

fof(f788,plain,
    ( spl2_68
    | ~ spl2_12
    | ~ spl2_14
    | ~ spl2_65 ),
    inference(avatar_split_clause,[],[f772,f766,f147,f134,f786])).

fof(f134,plain,
    ( spl2_12
  <=> ! [X1,X0] :
        ( k5_relat_1(k6_relat_1(X0),X1) = X1
        | ~ r1_tarski(k1_relat_1(X1),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f147,plain,
    ( spl2_14
  <=> ! [X1,X2] : v1_relat_1(k7_relat_1(k6_relat_1(X2),X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f772,plain,
    ( ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X0),X1))
    | ~ spl2_12
    | ~ spl2_14
    | ~ spl2_65 ),
    inference(subsumption_resolution,[],[f769,f148])).

fof(f148,plain,
    ( ! [X2,X1] : v1_relat_1(k7_relat_1(k6_relat_1(X2),X1))
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f147])).

fof(f769,plain,
    ( ! [X0,X1] :
        ( k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X0),X1))
        | ~ v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) )
    | ~ spl2_12
    | ~ spl2_65 ),
    inference(resolution,[],[f767,f135])).

fof(f135,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k1_relat_1(X1),X0)
        | k5_relat_1(k6_relat_1(X0),X1) = X1
        | ~ v1_relat_1(X1) )
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f134])).

fof(f784,plain,
    ( ~ spl2_67
    | ~ spl2_1
    | ~ spl2_2
    | spl2_18
    | ~ spl2_55 ),
    inference(avatar_split_clause,[],[f760,f560,f172,f79,f75,f781])).

fof(f172,plain,
    ( spl2_18
  <=> k6_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) = k7_relat_1(k6_relat_1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f760,plain,
    ( k7_relat_1(k6_relat_1(sK0),sK1) != k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1)))
    | ~ spl2_1
    | ~ spl2_2
    | spl2_18
    | ~ spl2_55 ),
    inference(backward_demodulation,[],[f174,f759])).

fof(f174,plain,
    ( k6_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1)
    | spl2_18 ),
    inference(avatar_component_clause,[],[f172])).

fof(f768,plain,
    ( spl2_65
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_16
    | ~ spl2_55 ),
    inference(avatar_split_clause,[],[f762,f560,f160,f79,f75,f766])).

fof(f762,plain,
    ( ! [X0,X1] : r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_16
    | ~ spl2_55 ),
    inference(backward_demodulation,[],[f161,f759])).

fof(f562,plain,(
    spl2_55 ),
    inference(avatar_split_clause,[],[f73,f560])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k6_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f55,f70])).

fof(f70,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f51,f69])).

fof(f69,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f52,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f60,f67])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f61,f66])).

fof(f66,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f62,f65])).

fof(f65,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f63,f64])).

fof(f64,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f63,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f62,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f61,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f60,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f52,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f51,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(f410,plain,
    ( spl2_42
    | ~ spl2_22
    | ~ spl2_40 ),
    inference(avatar_split_clause,[],[f403,f395,f204,f408])).

fof(f395,plain,
    ( spl2_40
  <=> ! [X7,X6] : k7_relat_1(k6_relat_1(X6),X7) = k5_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X6),X7))),k7_relat_1(k6_relat_1(X6),X7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_40])])).

fof(f403,plain,
    ( ! [X2,X3] : k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X3),k1_relat_1(k7_relat_1(k6_relat_1(X2),X3)))
    | ~ spl2_22
    | ~ spl2_40 ),
    inference(superposition,[],[f396,f205])).

fof(f396,plain,
    ( ! [X6,X7] : k7_relat_1(k6_relat_1(X6),X7) = k5_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X6),X7))),k7_relat_1(k6_relat_1(X6),X7))
    | ~ spl2_40 ),
    inference(avatar_component_clause,[],[f395])).

fof(f397,plain,
    ( spl2_40
    | ~ spl2_7
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f152,f147,f99,f395])).

fof(f99,plain,
    ( spl2_7
  <=> ! [X0] :
        ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f152,plain,
    ( ! [X6,X7] : k7_relat_1(k6_relat_1(X6),X7) = k5_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X6),X7))),k7_relat_1(k6_relat_1(X6),X7))
    | ~ spl2_7
    | ~ spl2_14 ),
    inference(resolution,[],[f148,f100])).

fof(f100,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f99])).

fof(f337,plain,
    ( spl2_35
    | ~ spl2_1
    | ~ spl2_11
    | ~ spl2_13
    | ~ spl2_22
    | ~ spl2_25
    | ~ spl2_29 ),
    inference(avatar_split_clause,[],[f289,f273,f216,f204,f138,f130,f75,f335])).

fof(f130,plain,
    ( spl2_11
  <=> ! [X1,X0] : k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f138,plain,
    ( spl2_13
  <=> ! [X1,X0] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f216,plain,
    ( spl2_25
  <=> ! [X5,X7,X6] : k8_relat_1(X5,k7_relat_1(k6_relat_1(X7),X6)) = k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X6),X7),X5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).

fof(f273,plain,
    ( spl2_29
  <=> ! [X5,X4,X6] :
        ( ~ v1_relat_1(X4)
        | k8_relat_1(X5,k5_relat_1(k6_relat_1(X6),X4)) = k5_relat_1(k6_relat_1(X6),k8_relat_1(X5,X4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).

fof(f289,plain,
    ( ! [X6,X7,X5] : k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X6),X7),X5)) = k7_relat_1(k7_relat_1(k6_relat_1(X5),X7),X6)
    | ~ spl2_1
    | ~ spl2_11
    | ~ spl2_13
    | ~ spl2_22
    | ~ spl2_25
    | ~ spl2_29 ),
    inference(backward_demodulation,[],[f217,f287])).

fof(f287,plain,
    ( ! [X6,X4,X5] : k7_relat_1(k7_relat_1(k6_relat_1(X4),X6),X5) = k8_relat_1(X4,k7_relat_1(k6_relat_1(X6),X5))
    | ~ spl2_1
    | ~ spl2_11
    | ~ spl2_13
    | ~ spl2_22
    | ~ spl2_29 ),
    inference(forward_demodulation,[],[f286,f139])).

fof(f139,plain,
    ( ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1)
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f138])).

fof(f286,plain,
    ( ! [X6,X4,X5] : k8_relat_1(X4,k5_relat_1(k6_relat_1(X5),k6_relat_1(X6))) = k7_relat_1(k7_relat_1(k6_relat_1(X4),X6),X5)
    | ~ spl2_1
    | ~ spl2_11
    | ~ spl2_22
    | ~ spl2_29 ),
    inference(forward_demodulation,[],[f285,f205])).

fof(f285,plain,
    ( ! [X6,X4,X5] : k8_relat_1(X4,k5_relat_1(k6_relat_1(X5),k6_relat_1(X6))) = k5_relat_1(k6_relat_1(X5),k7_relat_1(k6_relat_1(X4),X6))
    | ~ spl2_1
    | ~ spl2_11
    | ~ spl2_29 ),
    inference(forward_demodulation,[],[f281,f131])).

fof(f131,plain,
    ( ! [X0,X1] : k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),X1)
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f130])).

fof(f281,plain,
    ( ! [X6,X4,X5] : k8_relat_1(X4,k5_relat_1(k6_relat_1(X5),k6_relat_1(X6))) = k5_relat_1(k6_relat_1(X5),k8_relat_1(X4,k6_relat_1(X6)))
    | ~ spl2_1
    | ~ spl2_29 ),
    inference(resolution,[],[f274,f76])).

fof(f274,plain,
    ( ! [X6,X4,X5] :
        ( ~ v1_relat_1(X4)
        | k8_relat_1(X5,k5_relat_1(k6_relat_1(X6),X4)) = k5_relat_1(k6_relat_1(X6),k8_relat_1(X5,X4)) )
    | ~ spl2_29 ),
    inference(avatar_component_clause,[],[f273])).

fof(f217,plain,
    ( ! [X6,X7,X5] : k8_relat_1(X5,k7_relat_1(k6_relat_1(X7),X6)) = k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X6),X7),X5))
    | ~ spl2_25 ),
    inference(avatar_component_clause,[],[f216])).

fof(f275,plain,
    ( spl2_29
    | ~ spl2_1
    | ~ spl2_23 ),
    inference(avatar_split_clause,[],[f263,f208,f75,f273])).

fof(f208,plain,
    ( spl2_23
  <=> ! [X1,X0,X2] :
        ( k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2))
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f263,plain,
    ( ! [X6,X4,X5] :
        ( ~ v1_relat_1(X4)
        | k8_relat_1(X5,k5_relat_1(k6_relat_1(X6),X4)) = k5_relat_1(k6_relat_1(X6),k8_relat_1(X5,X4)) )
    | ~ spl2_1
    | ~ spl2_23 ),
    inference(resolution,[],[f209,f76])).

fof(f209,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X1)
        | ~ v1_relat_1(X2)
        | k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2)) )
    | ~ spl2_23 ),
    inference(avatar_component_clause,[],[f208])).

fof(f218,plain,
    ( spl2_25
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_9
    | ~ spl2_10
    | ~ spl2_13
    | ~ spl2_14
    | ~ spl2_20 ),
    inference(avatar_split_clause,[],[f197,f185,f147,f138,f119,f115,f87,f75,f216])).

fof(f87,plain,
    ( spl2_4
  <=> ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f115,plain,
    ( spl2_9
  <=> ! [X1,X0] :
        ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f119,plain,
    ( spl2_10
  <=> ! [X1,X0] :
        ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f185,plain,
    ( spl2_20
  <=> ! [X1,X0] :
        ( k4_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k5_relat_1(k4_relat_1(X0),k6_relat_1(X1))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f197,plain,
    ( ! [X6,X7,X5] : k8_relat_1(X5,k7_relat_1(k6_relat_1(X7),X6)) = k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X6),X7),X5))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_9
    | ~ spl2_10
    | ~ spl2_13
    | ~ spl2_14
    | ~ spl2_20 ),
    inference(forward_demodulation,[],[f196,f150])).

fof(f150,plain,
    ( ! [X2,X0,X1] : k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k5_relat_1(k6_relat_1(X2),k7_relat_1(k6_relat_1(X0),X1))
    | ~ spl2_10
    | ~ spl2_14 ),
    inference(resolution,[],[f148,f120])).

fof(f120,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) )
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f119])).

fof(f196,plain,
    ( ! [X6,X7,X5] : k4_relat_1(k5_relat_1(k6_relat_1(X5),k7_relat_1(k6_relat_1(X6),X7))) = k8_relat_1(X5,k7_relat_1(k6_relat_1(X7),X6))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_9
    | ~ spl2_13
    | ~ spl2_14
    | ~ spl2_20 ),
    inference(forward_demodulation,[],[f195,f151])).

fof(f151,plain,
    ( ! [X4,X5,X3] : k8_relat_1(X3,k7_relat_1(k6_relat_1(X4),X5)) = k5_relat_1(k7_relat_1(k6_relat_1(X4),X5),k6_relat_1(X3))
    | ~ spl2_9
    | ~ spl2_14 ),
    inference(resolution,[],[f148,f116])).

fof(f116,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) )
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f115])).

fof(f195,plain,
    ( ! [X6,X7,X5] : k4_relat_1(k5_relat_1(k6_relat_1(X5),k7_relat_1(k6_relat_1(X6),X7))) = k5_relat_1(k7_relat_1(k6_relat_1(X7),X6),k6_relat_1(X5))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_13
    | ~ spl2_14
    | ~ spl2_20 ),
    inference(forward_demodulation,[],[f190,f193])).

fof(f193,plain,
    ( ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_13
    | ~ spl2_20 ),
    inference(forward_demodulation,[],[f192,f139])).

fof(f192,plain,
    ( ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_13
    | ~ spl2_20 ),
    inference(forward_demodulation,[],[f191,f139])).

fof(f191,plain,
    ( ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_20 ),
    inference(forward_demodulation,[],[f188,f88])).

fof(f88,plain,
    ( ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f87])).

fof(f188,plain,
    ( ! [X0,X1] : k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k5_relat_1(k4_relat_1(k6_relat_1(X1)),k6_relat_1(X0))
    | ~ spl2_1
    | ~ spl2_20 ),
    inference(resolution,[],[f186,f76])).

fof(f186,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | k4_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k5_relat_1(k4_relat_1(X0),k6_relat_1(X1)) )
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f185])).

fof(f190,plain,
    ( ! [X6,X7,X5] : k4_relat_1(k5_relat_1(k6_relat_1(X5),k7_relat_1(k6_relat_1(X6),X7))) = k5_relat_1(k4_relat_1(k7_relat_1(k6_relat_1(X6),X7)),k6_relat_1(X5))
    | ~ spl2_14
    | ~ spl2_20 ),
    inference(resolution,[],[f186,f148])).

fof(f210,plain,(
    spl2_23 ),
    inference(avatar_split_clause,[],[f57,f208])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_relat_1)).

fof(f206,plain,
    ( spl2_22
    | ~ spl2_10
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f150,f147,f119,f204])).

fof(f201,plain,
    ( spl2_21
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_13
    | ~ spl2_20 ),
    inference(avatar_split_clause,[],[f193,f185,f138,f87,f75,f199])).

fof(f187,plain,
    ( spl2_20
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_19 ),
    inference(avatar_split_clause,[],[f183,f177,f87,f75,f185])).

fof(f177,plain,
    ( spl2_19
  <=> ! [X1,X0] :
        ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f183,plain,
    ( ! [X0,X1] :
        ( k4_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k5_relat_1(k4_relat_1(X0),k6_relat_1(X1))
        | ~ v1_relat_1(X0) )
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_19 ),
    inference(forward_demodulation,[],[f180,f88])).

fof(f180,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | k4_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k5_relat_1(k4_relat_1(X0),k4_relat_1(k6_relat_1(X1))) )
    | ~ spl2_1
    | ~ spl2_19 ),
    inference(resolution,[],[f178,f76])).

fof(f178,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) )
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f177])).

fof(f179,plain,(
    spl2_19 ),
    inference(avatar_split_clause,[],[f48,f177])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).

fof(f175,plain,
    ( ~ spl2_18
    | ~ spl2_1
    | ~ spl2_9
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f128,f119,f115,f75,f172])).

fof(f128,plain,
    ( k6_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1)
    | ~ spl2_1
    | ~ spl2_9
    | ~ spl2_10 ),
    inference(backward_demodulation,[],[f124,f127])).

fof(f127,plain,
    ( ! [X0,X1] : k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),X1)
    | ~ spl2_1
    | ~ spl2_9
    | ~ spl2_10 ),
    inference(backward_demodulation,[],[f122,f125])).

fof(f125,plain,
    ( ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1)
    | ~ spl2_1
    | ~ spl2_10 ),
    inference(resolution,[],[f120,f76])).

fof(f122,plain,
    ( ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k8_relat_1(X0,k6_relat_1(X1))
    | ~ spl2_1
    | ~ spl2_9 ),
    inference(resolution,[],[f116,f76])).

fof(f124,plain,
    ( k6_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) != k8_relat_1(sK0,k6_relat_1(sK1))
    | ~ spl2_1
    | ~ spl2_9 ),
    inference(backward_demodulation,[],[f71,f122])).

fof(f71,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) ),
    inference(definition_unfolding,[],[f41,f70])).

fof(f41,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f39])).

fof(f39,plain,
    ( ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))
   => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

fof(f169,plain,
    ( spl2_17
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_12
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f165,f138,f134,f79,f75,f167])).

fof(f165,plain,
    ( ! [X0,X1] :
        ( k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1)
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_12
    | ~ spl2_13 ),
    inference(forward_demodulation,[],[f164,f139])).

fof(f164,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) )
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_12 ),
    inference(subsumption_resolution,[],[f163,f76])).

fof(f163,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))
        | ~ v1_relat_1(k6_relat_1(X0)) )
    | ~ spl2_2
    | ~ spl2_12 ),
    inference(superposition,[],[f135,f80])).

fof(f162,plain,(
    spl2_16 ),
    inference(avatar_split_clause,[],[f72,f160])).

fof(f72,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f50,f70])).

fof(f50,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f149,plain,
    ( spl2_14
    | ~ spl2_1
    | ~ spl2_5
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f145,f138,f91,f75,f147])).

fof(f91,plain,
    ( spl2_5
  <=> ! [X1,X0] :
        ( v1_relat_1(k5_relat_1(X0,X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f145,plain,
    ( ! [X2,X1] : v1_relat_1(k7_relat_1(k6_relat_1(X2),X1))
    | ~ spl2_1
    | ~ spl2_5
    | ~ spl2_13 ),
    inference(subsumption_resolution,[],[f144,f76])).

fof(f144,plain,
    ( ! [X2,X1] :
        ( v1_relat_1(k7_relat_1(k6_relat_1(X2),X1))
        | ~ v1_relat_1(k6_relat_1(X1)) )
    | ~ spl2_1
    | ~ spl2_5
    | ~ spl2_13 ),
    inference(subsumption_resolution,[],[f143,f76])).

fof(f143,plain,
    ( ! [X2,X1] :
        ( v1_relat_1(k7_relat_1(k6_relat_1(X2),X1))
        | ~ v1_relat_1(k6_relat_1(X2))
        | ~ v1_relat_1(k6_relat_1(X1)) )
    | ~ spl2_5
    | ~ spl2_13 ),
    inference(superposition,[],[f92,f139])).

fof(f92,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(k5_relat_1(X0,X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f91])).

fof(f140,plain,
    ( spl2_13
    | ~ spl2_1
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f125,f119,f75,f138])).

fof(f136,plain,(
    spl2_12 ),
    inference(avatar_split_clause,[],[f56,f134])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

fof(f132,plain,
    ( spl2_11
    | ~ spl2_1
    | ~ spl2_9
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f127,f119,f115,f75,f130])).

fof(f121,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f54,f119])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f117,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f53,f115])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

fof(f101,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f47,f99])).

fof(f47,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

fof(f93,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f59,f91])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f89,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f43,f87])).

fof(f43,plain,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_relat_1)).

fof(f81,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f44,f79])).

fof(f44,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f77,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f42,f75])).

fof(f42,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:55:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.47  % (15931)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.47  % (15936)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.49  % (15939)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.52  % (15928)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.53  % (15929)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.53  % (15927)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.53  % (15926)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.53  % (15938)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.54  % (15935)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.54  % (15937)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.54  % (15935)Refutation not found, incomplete strategy% (15935)------------------------------
% 0.22/0.54  % (15935)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (15935)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (15935)Memory used [KB]: 10618
% 0.22/0.54  % (15935)Time elapsed: 0.093 s
% 0.22/0.54  % (15935)------------------------------
% 0.22/0.54  % (15935)------------------------------
% 0.22/0.54  % (15933)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.54  % (15934)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.54  % (15930)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (15931)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f1589,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(avatar_sat_refutation,[],[f77,f81,f89,f93,f101,f117,f121,f132,f136,f140,f149,f162,f169,f175,f179,f187,f201,f206,f210,f218,f275,f337,f397,f410,f562,f768,f784,f788,f796,f812,f821,f875,f1181,f1355,f1472,f1542])).
% 0.22/0.54  fof(f1542,plain,(
% 0.22/0.54    spl2_67 | ~spl2_71 | ~spl2_90),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f1541])).
% 0.22/0.54  fof(f1541,plain,(
% 0.22/0.54    $false | (spl2_67 | ~spl2_71 | ~spl2_90)),
% 0.22/0.54    inference(subsumption_resolution,[],[f1477,f820])).
% 0.22/0.54  fof(f820,plain,(
% 0.22/0.54    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k6_relat_1(X3),X2)) ) | ~spl2_71),
% 0.22/0.54    inference(avatar_component_clause,[],[f819])).
% 0.22/0.54  fof(f819,plain,(
% 0.22/0.54    spl2_71 <=> ! [X3,X2] : k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k6_relat_1(X3),X2)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_71])])).
% 0.22/0.54  fof(f1477,plain,(
% 0.22/0.54    k7_relat_1(k6_relat_1(sK0),sK1) != k7_relat_1(k6_relat_1(sK1),sK0) | (spl2_67 | ~spl2_90)),
% 0.22/0.54    inference(superposition,[],[f783,f1471])).
% 0.22/0.54  fof(f1471,plain,(
% 0.22/0.54    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X3),X2) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X2),X3)))) ) | ~spl2_90),
% 0.22/0.54    inference(avatar_component_clause,[],[f1470])).
% 0.22/0.54  fof(f1470,plain,(
% 0.22/0.54    spl2_90 <=> ! [X3,X2] : k7_relat_1(k6_relat_1(X3),X2) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X2),X3)))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_90])])).
% 0.22/0.54  fof(f783,plain,(
% 0.22/0.54    k7_relat_1(k6_relat_1(sK0),sK1) != k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1))) | spl2_67),
% 0.22/0.54    inference(avatar_component_clause,[],[f781])).
% 0.22/0.54  fof(f781,plain,(
% 0.22/0.54    spl2_67 <=> k7_relat_1(k6_relat_1(sK0),sK1) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1)))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_67])])).
% 0.22/0.54  fof(f1472,plain,(
% 0.22/0.54    spl2_90 | ~spl2_17 | ~spl2_21 | ~spl2_42 | ~spl2_71 | ~spl2_72 | ~spl2_84 | ~spl2_89),
% 0.22/0.54    inference(avatar_split_clause,[],[f1411,f1353,f1179,f873,f819,f408,f199,f167,f1470])).
% 0.22/0.54  fof(f167,plain,(
% 0.22/0.54    spl2_17 <=> ! [X1,X0] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1) | ~r1_tarski(X0,X1))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.22/0.54  fof(f199,plain,(
% 0.22/0.54    spl2_21 <=> ! [X1,X0] : k7_relat_1(k6_relat_1(X0),X1) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).
% 0.22/0.54  fof(f408,plain,(
% 0.22/0.54    spl2_42 <=> ! [X3,X2] : k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X3),k1_relat_1(k7_relat_1(k6_relat_1(X2),X3)))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_42])])).
% 0.22/0.54  fof(f873,plain,(
% 0.22/0.54    spl2_72 <=> ! [X63,X62] : r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X63),X62)),X62)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_72])])).
% 0.22/0.54  fof(f1179,plain,(
% 0.22/0.54    spl2_84 <=> ! [X18,X20,X19] : k7_relat_1(k7_relat_1(k6_relat_1(X20),X19),X18) = k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X19),X18),X20))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_84])])).
% 0.22/0.54  fof(f1353,plain,(
% 0.22/0.54    spl2_89 <=> ! [X1,X0] : k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_89])])).
% 0.22/0.54  fof(f1411,plain,(
% 0.22/0.54    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X3),X2) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X2),X3)))) ) | (~spl2_17 | ~spl2_21 | ~spl2_42 | ~spl2_71 | ~spl2_72 | ~spl2_84 | ~spl2_89)),
% 0.22/0.54    inference(backward_demodulation,[],[f877,f1410])).
% 0.22/0.54  fof(f1410,plain,(
% 0.22/0.54    ( ! [X33,X32] : (k7_relat_1(k6_relat_1(X33),X32) = k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X32),X33))),X33)) ) | (~spl2_21 | ~spl2_42 | ~spl2_71 | ~spl2_84 | ~spl2_89)),
% 0.22/0.54    inference(backward_demodulation,[],[f1218,f1360])).
% 0.22/0.54  fof(f1360,plain,(
% 0.22/0.54    ( ! [X2,X3] : (k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X2),X3))) = k7_relat_1(k6_relat_1(X2),k1_relat_1(k7_relat_1(k6_relat_1(X2),X3)))) ) | (~spl2_71 | ~spl2_89)),
% 0.22/0.54    inference(superposition,[],[f1354,f820])).
% 0.22/0.54  fof(f1354,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X0)) ) | ~spl2_89),
% 0.22/0.54    inference(avatar_component_clause,[],[f1353])).
% 0.22/0.54  fof(f1218,plain,(
% 0.22/0.54    ( ! [X33,X32] : (k7_relat_1(k6_relat_1(X33),X32) = k7_relat_1(k7_relat_1(k6_relat_1(X32),k1_relat_1(k7_relat_1(k6_relat_1(X32),X33))),X33)) ) | (~spl2_21 | ~spl2_42 | ~spl2_71 | ~spl2_84)),
% 0.22/0.54    inference(forward_demodulation,[],[f1217,f820])).
% 0.22/0.54  fof(f1217,plain,(
% 0.22/0.54    ( ! [X33,X32] : (k7_relat_1(k6_relat_1(X33),X32) = k7_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X32),X33))),X32),X33)) ) | (~spl2_21 | ~spl2_42 | ~spl2_84)),
% 0.22/0.54    inference(forward_demodulation,[],[f1208,f200])).
% 0.22/0.54  fof(f200,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0))) ) | ~spl2_21),
% 0.22/0.54    inference(avatar_component_clause,[],[f199])).
% 0.22/0.54  fof(f1208,plain,(
% 0.22/0.54    ( ! [X33,X32] : (k7_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X32),X33))),X32),X33) = k4_relat_1(k7_relat_1(k6_relat_1(X32),X33))) ) | (~spl2_42 | ~spl2_84)),
% 0.22/0.54    inference(superposition,[],[f1180,f409])).
% 0.22/0.54  fof(f409,plain,(
% 0.22/0.54    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X3),k1_relat_1(k7_relat_1(k6_relat_1(X2),X3)))) ) | ~spl2_42),
% 0.22/0.54    inference(avatar_component_clause,[],[f408])).
% 0.22/0.54  fof(f1180,plain,(
% 0.22/0.54    ( ! [X19,X20,X18] : (k7_relat_1(k7_relat_1(k6_relat_1(X20),X19),X18) = k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X19),X18),X20))) ) | ~spl2_84),
% 0.22/0.54    inference(avatar_component_clause,[],[f1179])).
% 0.22/0.54  fof(f877,plain,(
% 0.22/0.54    ( ! [X2,X3] : (k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X2),X3))) = k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X2),X3))),X3)) ) | (~spl2_17 | ~spl2_72)),
% 0.22/0.54    inference(resolution,[],[f874,f168])).
% 0.22/0.54  fof(f168,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1)) ) | ~spl2_17),
% 0.22/0.54    inference(avatar_component_clause,[],[f167])).
% 0.22/0.54  fof(f874,plain,(
% 0.22/0.54    ( ! [X62,X63] : (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X63),X62)),X62)) ) | ~spl2_72),
% 0.22/0.54    inference(avatar_component_clause,[],[f873])).
% 0.22/0.54  fof(f1355,plain,(
% 0.22/0.54    spl2_89 | ~spl2_1 | ~spl2_2 | ~spl2_16 | ~spl2_17 | ~spl2_55),
% 0.22/0.54    inference(avatar_split_clause,[],[f761,f560,f167,f160,f79,f75,f1353])).
% 0.22/0.54  fof(f75,plain,(
% 0.22/0.54    spl2_1 <=> ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.54  fof(f79,plain,(
% 0.22/0.54    spl2_2 <=> ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.54  fof(f160,plain,(
% 0.22/0.54    spl2_16 <=> ! [X1,X0] : r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.22/0.54  fof(f560,plain,(
% 0.22/0.54    spl2_55 <=> ! [X1,X0] : (k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k6_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_55])])).
% 0.22/0.54  fof(f761,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X0)) ) | (~spl2_1 | ~spl2_2 | ~spl2_16 | ~spl2_17 | ~spl2_55)),
% 0.22/0.54    inference(backward_demodulation,[],[f170,f759])).
% 0.22/0.54  fof(f759,plain,(
% 0.22/0.54    ( ! [X4,X3] : (k1_relat_1(k7_relat_1(k6_relat_1(X3),X4)) = k1_setfam_1(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4))) ) | (~spl2_1 | ~spl2_2 | ~spl2_55)),
% 0.22/0.54    inference(forward_demodulation,[],[f755,f80])).
% 0.22/0.54  fof(f80,plain,(
% 0.22/0.54    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) ) | ~spl2_2),
% 0.22/0.54    inference(avatar_component_clause,[],[f79])).
% 0.22/0.54  fof(f755,plain,(
% 0.22/0.54    ( ! [X4,X3] : (k1_relat_1(k7_relat_1(k6_relat_1(X3),X4)) = k1_setfam_1(k6_enumset1(k1_relat_1(k6_relat_1(X3)),k1_relat_1(k6_relat_1(X3)),k1_relat_1(k6_relat_1(X3)),k1_relat_1(k6_relat_1(X3)),k1_relat_1(k6_relat_1(X3)),k1_relat_1(k6_relat_1(X3)),k1_relat_1(k6_relat_1(X3)),X4))) ) | (~spl2_1 | ~spl2_55)),
% 0.22/0.54    inference(resolution,[],[f561,f76])).
% 0.22/0.54  fof(f76,plain,(
% 0.22/0.54    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) ) | ~spl2_1),
% 0.22/0.54    inference(avatar_component_clause,[],[f75])).
% 0.22/0.54  fof(f561,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k6_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0))) ) | ~spl2_55),
% 0.22/0.54    inference(avatar_component_clause,[],[f560])).
% 0.22/0.54  fof(f170,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k6_relat_1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k7_relat_1(k6_relat_1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X0)) ) | (~spl2_16 | ~spl2_17)),
% 0.22/0.54    inference(resolution,[],[f161,f168])).
% 0.22/0.54  fof(f161,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0)) ) | ~spl2_16),
% 0.22/0.54    inference(avatar_component_clause,[],[f160])).
% 0.22/0.54  fof(f1181,plain,(
% 0.22/0.54    spl2_84 | ~spl2_35 | ~spl2_71),
% 0.22/0.54    inference(avatar_split_clause,[],[f829,f819,f335,f1179])).
% 0.22/0.54  fof(f335,plain,(
% 0.22/0.54    spl2_35 <=> ! [X5,X7,X6] : k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X6),X7),X5)) = k7_relat_1(k7_relat_1(k6_relat_1(X5),X7),X6)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_35])])).
% 0.22/0.54  fof(f829,plain,(
% 0.22/0.54    ( ! [X19,X20,X18] : (k7_relat_1(k7_relat_1(k6_relat_1(X20),X19),X18) = k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X19),X18),X20))) ) | (~spl2_35 | ~spl2_71)),
% 0.22/0.54    inference(superposition,[],[f336,f820])).
% 0.22/0.54  fof(f336,plain,(
% 0.22/0.54    ( ! [X6,X7,X5] : (k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X6),X7),X5)) = k7_relat_1(k7_relat_1(k6_relat_1(X5),X7),X6)) ) | ~spl2_35),
% 0.22/0.54    inference(avatar_component_clause,[],[f335])).
% 0.22/0.54  fof(f875,plain,(
% 0.22/0.54    spl2_72 | ~spl2_65 | ~spl2_71),
% 0.22/0.54    inference(avatar_split_clause,[],[f843,f819,f766,f873])).
% 0.22/0.54  fof(f766,plain,(
% 0.22/0.54    spl2_65 <=> ! [X1,X0] : r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_65])])).
% 0.22/0.54  fof(f843,plain,(
% 0.22/0.54    ( ! [X62,X63] : (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X63),X62)),X62)) ) | (~spl2_65 | ~spl2_71)),
% 0.22/0.54    inference(superposition,[],[f767,f820])).
% 0.22/0.54  fof(f767,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0)) ) | ~spl2_65),
% 0.22/0.54    inference(avatar_component_clause,[],[f766])).
% 0.22/0.54  fof(f821,plain,(
% 0.22/0.54    spl2_71 | ~spl2_21 | ~spl2_70),
% 0.22/0.54    inference(avatar_split_clause,[],[f814,f810,f199,f819])).
% 0.22/0.54  fof(f810,plain,(
% 0.22/0.54    spl2_70 <=> ! [X3,X4] : k7_relat_1(k6_relat_1(X3),X4) = k4_relat_1(k7_relat_1(k6_relat_1(X3),X4))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_70])])).
% 0.22/0.54  fof(f814,plain,(
% 0.22/0.54    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k6_relat_1(X3),X2)) ) | (~spl2_21 | ~spl2_70)),
% 0.22/0.54    inference(superposition,[],[f811,f200])).
% 0.22/0.54  fof(f811,plain,(
% 0.22/0.54    ( ! [X4,X3] : (k7_relat_1(k6_relat_1(X3),X4) = k4_relat_1(k7_relat_1(k6_relat_1(X3),X4))) ) | ~spl2_70),
% 0.22/0.54    inference(avatar_component_clause,[],[f810])).
% 0.22/0.54  fof(f812,plain,(
% 0.22/0.54    spl2_70 | ~spl2_35 | ~spl2_69),
% 0.22/0.54    inference(avatar_split_clause,[],[f799,f794,f335,f810])).
% 0.22/0.54  fof(f794,plain,(
% 0.22/0.54    spl2_69 <=> ! [X1,X0] : k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_69])])).
% 0.22/0.54  fof(f799,plain,(
% 0.22/0.54    ( ! [X4,X3] : (k7_relat_1(k6_relat_1(X3),X4) = k4_relat_1(k7_relat_1(k6_relat_1(X3),X4))) ) | (~spl2_35 | ~spl2_69)),
% 0.22/0.54    inference(superposition,[],[f336,f795])).
% 0.22/0.54  fof(f795,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0)) ) | ~spl2_69),
% 0.22/0.54    inference(avatar_component_clause,[],[f794])).
% 0.22/0.54  fof(f796,plain,(
% 0.22/0.54    spl2_69 | ~spl2_22 | ~spl2_68),
% 0.22/0.54    inference(avatar_split_clause,[],[f790,f786,f204,f794])).
% 0.22/0.54  fof(f204,plain,(
% 0.22/0.54    spl2_22 <=> ! [X1,X0,X2] : k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k5_relat_1(k6_relat_1(X2),k7_relat_1(k6_relat_1(X0),X1))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 0.22/0.54  fof(f786,plain,(
% 0.22/0.54    spl2_68 <=> ! [X1,X0] : k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X0),X1))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_68])])).
% 0.22/0.54  fof(f790,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0)) ) | (~spl2_22 | ~spl2_68)),
% 0.22/0.54    inference(superposition,[],[f787,f205])).
% 0.22/0.54  fof(f205,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k5_relat_1(k6_relat_1(X2),k7_relat_1(k6_relat_1(X0),X1))) ) | ~spl2_22),
% 0.22/0.54    inference(avatar_component_clause,[],[f204])).
% 0.22/0.54  fof(f787,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X0),X1))) ) | ~spl2_68),
% 0.22/0.54    inference(avatar_component_clause,[],[f786])).
% 0.22/0.54  fof(f788,plain,(
% 0.22/0.54    spl2_68 | ~spl2_12 | ~spl2_14 | ~spl2_65),
% 0.22/0.54    inference(avatar_split_clause,[],[f772,f766,f147,f134,f786])).
% 0.22/0.54  fof(f134,plain,(
% 0.22/0.54    spl2_12 <=> ! [X1,X0] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.22/0.54  fof(f147,plain,(
% 0.22/0.54    spl2_14 <=> ! [X1,X2] : v1_relat_1(k7_relat_1(k6_relat_1(X2),X1))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.22/0.54  fof(f772,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X0),X1))) ) | (~spl2_12 | ~spl2_14 | ~spl2_65)),
% 0.22/0.54    inference(subsumption_resolution,[],[f769,f148])).
% 0.22/0.54  fof(f148,plain,(
% 0.22/0.54    ( ! [X2,X1] : (v1_relat_1(k7_relat_1(k6_relat_1(X2),X1))) ) | ~spl2_14),
% 0.22/0.54    inference(avatar_component_clause,[],[f147])).
% 0.22/0.54  fof(f769,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X0),X1)) | ~v1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ) | (~spl2_12 | ~spl2_65)),
% 0.22/0.54    inference(resolution,[],[f767,f135])).
% 0.22/0.54  fof(f135,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | k5_relat_1(k6_relat_1(X0),X1) = X1 | ~v1_relat_1(X1)) ) | ~spl2_12),
% 0.22/0.54    inference(avatar_component_clause,[],[f134])).
% 0.22/0.54  fof(f784,plain,(
% 0.22/0.54    ~spl2_67 | ~spl2_1 | ~spl2_2 | spl2_18 | ~spl2_55),
% 0.22/0.54    inference(avatar_split_clause,[],[f760,f560,f172,f79,f75,f781])).
% 0.22/0.54  fof(f172,plain,(
% 0.22/0.54    spl2_18 <=> k6_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) = k7_relat_1(k6_relat_1(sK0),sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.22/0.54  fof(f760,plain,(
% 0.22/0.54    k7_relat_1(k6_relat_1(sK0),sK1) != k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1))) | (~spl2_1 | ~spl2_2 | spl2_18 | ~spl2_55)),
% 0.22/0.54    inference(backward_demodulation,[],[f174,f759])).
% 0.22/0.54  fof(f174,plain,(
% 0.22/0.54    k6_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1) | spl2_18),
% 0.22/0.54    inference(avatar_component_clause,[],[f172])).
% 0.22/0.54  fof(f768,plain,(
% 0.22/0.54    spl2_65 | ~spl2_1 | ~spl2_2 | ~spl2_16 | ~spl2_55),
% 0.22/0.54    inference(avatar_split_clause,[],[f762,f560,f160,f79,f75,f766])).
% 0.22/0.55  fof(f762,plain,(
% 0.22/0.55    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0)) ) | (~spl2_1 | ~spl2_2 | ~spl2_16 | ~spl2_55)),
% 0.22/0.55    inference(backward_demodulation,[],[f161,f759])).
% 0.22/0.55  fof(f562,plain,(
% 0.22/0.55    spl2_55),
% 0.22/0.55    inference(avatar_split_clause,[],[f73,f560])).
% 0.22/0.55  fof(f73,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k6_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 0.22/0.55    inference(definition_unfolding,[],[f55,f70])).
% 0.22/0.55  fof(f70,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 0.22/0.55    inference(definition_unfolding,[],[f51,f69])).
% 0.22/0.55  fof(f69,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.22/0.55    inference(definition_unfolding,[],[f52,f68])).
% 0.22/0.55  fof(f68,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.22/0.55    inference(definition_unfolding,[],[f60,f67])).
% 0.22/0.55  fof(f67,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.22/0.55    inference(definition_unfolding,[],[f61,f66])).
% 0.22/0.55  fof(f66,plain,(
% 0.22/0.55    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.22/0.55    inference(definition_unfolding,[],[f62,f65])).
% 0.22/0.55  fof(f65,plain,(
% 0.22/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.22/0.55    inference(definition_unfolding,[],[f63,f64])).
% 0.22/0.55  fof(f64,plain,(
% 0.22/0.55    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f7])).
% 0.22/0.55  fof(f7,axiom,(
% 0.22/0.55    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 0.22/0.55  fof(f63,plain,(
% 0.22/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f6])).
% 0.22/0.55  fof(f6,axiom,(
% 0.22/0.55    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 0.22/0.55  fof(f62,plain,(
% 0.22/0.55    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f5])).
% 0.22/0.55  fof(f5,axiom,(
% 0.22/0.55    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.22/0.55  fof(f61,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f4])).
% 0.22/0.55  fof(f4,axiom,(
% 0.22/0.55    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.22/0.55  fof(f60,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f3])).
% 0.22/0.55  fof(f3,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.55  fof(f52,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f2])).
% 0.22/0.55  fof(f2,axiom,(
% 0.22/0.55    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.55  fof(f51,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f8])).
% 0.22/0.55  fof(f8,axiom,(
% 0.22/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.22/0.55  fof(f55,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f32])).
% 0.22/0.55  fof(f32,plain,(
% 0.22/0.55    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.55    inference(ennf_transformation,[],[f21])).
% 0.22/0.55  fof(f21,axiom,(
% 0.22/0.55    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).
% 0.22/0.55  fof(f410,plain,(
% 0.22/0.55    spl2_42 | ~spl2_22 | ~spl2_40),
% 0.22/0.55    inference(avatar_split_clause,[],[f403,f395,f204,f408])).
% 0.22/0.55  fof(f395,plain,(
% 0.22/0.55    spl2_40 <=> ! [X7,X6] : k7_relat_1(k6_relat_1(X6),X7) = k5_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X6),X7))),k7_relat_1(k6_relat_1(X6),X7))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_40])])).
% 0.22/0.55  fof(f403,plain,(
% 0.22/0.55    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X3),k1_relat_1(k7_relat_1(k6_relat_1(X2),X3)))) ) | (~spl2_22 | ~spl2_40)),
% 0.22/0.55    inference(superposition,[],[f396,f205])).
% 0.22/0.55  fof(f396,plain,(
% 0.22/0.55    ( ! [X6,X7] : (k7_relat_1(k6_relat_1(X6),X7) = k5_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X6),X7))),k7_relat_1(k6_relat_1(X6),X7))) ) | ~spl2_40),
% 0.22/0.55    inference(avatar_component_clause,[],[f395])).
% 0.22/0.55  fof(f397,plain,(
% 0.22/0.55    spl2_40 | ~spl2_7 | ~spl2_14),
% 0.22/0.55    inference(avatar_split_clause,[],[f152,f147,f99,f395])).
% 0.22/0.55  fof(f99,plain,(
% 0.22/0.55    spl2_7 <=> ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.22/0.55  fof(f152,plain,(
% 0.22/0.55    ( ! [X6,X7] : (k7_relat_1(k6_relat_1(X6),X7) = k5_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X6),X7))),k7_relat_1(k6_relat_1(X6),X7))) ) | (~spl2_7 | ~spl2_14)),
% 0.22/0.55    inference(resolution,[],[f148,f100])).
% 0.22/0.55  fof(f100,plain,(
% 0.22/0.55    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0) ) | ~spl2_7),
% 0.22/0.55    inference(avatar_component_clause,[],[f99])).
% 0.22/0.55  fof(f337,plain,(
% 0.22/0.55    spl2_35 | ~spl2_1 | ~spl2_11 | ~spl2_13 | ~spl2_22 | ~spl2_25 | ~spl2_29),
% 0.22/0.55    inference(avatar_split_clause,[],[f289,f273,f216,f204,f138,f130,f75,f335])).
% 0.22/0.55  fof(f130,plain,(
% 0.22/0.55    spl2_11 <=> ! [X1,X0] : k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),X1)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.22/0.55  fof(f138,plain,(
% 0.22/0.55    spl2_13 <=> ! [X1,X0] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.22/0.55  fof(f216,plain,(
% 0.22/0.55    spl2_25 <=> ! [X5,X7,X6] : k8_relat_1(X5,k7_relat_1(k6_relat_1(X7),X6)) = k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X6),X7),X5))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).
% 0.22/0.55  fof(f273,plain,(
% 0.22/0.55    spl2_29 <=> ! [X5,X4,X6] : (~v1_relat_1(X4) | k8_relat_1(X5,k5_relat_1(k6_relat_1(X6),X4)) = k5_relat_1(k6_relat_1(X6),k8_relat_1(X5,X4)))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).
% 0.22/0.55  fof(f289,plain,(
% 0.22/0.55    ( ! [X6,X7,X5] : (k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X6),X7),X5)) = k7_relat_1(k7_relat_1(k6_relat_1(X5),X7),X6)) ) | (~spl2_1 | ~spl2_11 | ~spl2_13 | ~spl2_22 | ~spl2_25 | ~spl2_29)),
% 0.22/0.55    inference(backward_demodulation,[],[f217,f287])).
% 0.22/0.55  fof(f287,plain,(
% 0.22/0.55    ( ! [X6,X4,X5] : (k7_relat_1(k7_relat_1(k6_relat_1(X4),X6),X5) = k8_relat_1(X4,k7_relat_1(k6_relat_1(X6),X5))) ) | (~spl2_1 | ~spl2_11 | ~spl2_13 | ~spl2_22 | ~spl2_29)),
% 0.22/0.55    inference(forward_demodulation,[],[f286,f139])).
% 0.22/0.55  fof(f139,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1)) ) | ~spl2_13),
% 0.22/0.55    inference(avatar_component_clause,[],[f138])).
% 0.22/0.55  fof(f286,plain,(
% 0.22/0.55    ( ! [X6,X4,X5] : (k8_relat_1(X4,k5_relat_1(k6_relat_1(X5),k6_relat_1(X6))) = k7_relat_1(k7_relat_1(k6_relat_1(X4),X6),X5)) ) | (~spl2_1 | ~spl2_11 | ~spl2_22 | ~spl2_29)),
% 0.22/0.55    inference(forward_demodulation,[],[f285,f205])).
% 0.22/0.55  fof(f285,plain,(
% 0.22/0.55    ( ! [X6,X4,X5] : (k8_relat_1(X4,k5_relat_1(k6_relat_1(X5),k6_relat_1(X6))) = k5_relat_1(k6_relat_1(X5),k7_relat_1(k6_relat_1(X4),X6))) ) | (~spl2_1 | ~spl2_11 | ~spl2_29)),
% 0.22/0.55    inference(forward_demodulation,[],[f281,f131])).
% 0.22/0.55  fof(f131,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),X1)) ) | ~spl2_11),
% 0.22/0.55    inference(avatar_component_clause,[],[f130])).
% 0.22/0.55  fof(f281,plain,(
% 0.22/0.55    ( ! [X6,X4,X5] : (k8_relat_1(X4,k5_relat_1(k6_relat_1(X5),k6_relat_1(X6))) = k5_relat_1(k6_relat_1(X5),k8_relat_1(X4,k6_relat_1(X6)))) ) | (~spl2_1 | ~spl2_29)),
% 0.22/0.55    inference(resolution,[],[f274,f76])).
% 0.22/0.55  fof(f274,plain,(
% 0.22/0.55    ( ! [X6,X4,X5] : (~v1_relat_1(X4) | k8_relat_1(X5,k5_relat_1(k6_relat_1(X6),X4)) = k5_relat_1(k6_relat_1(X6),k8_relat_1(X5,X4))) ) | ~spl2_29),
% 0.22/0.55    inference(avatar_component_clause,[],[f273])).
% 0.22/0.55  fof(f217,plain,(
% 0.22/0.55    ( ! [X6,X7,X5] : (k8_relat_1(X5,k7_relat_1(k6_relat_1(X7),X6)) = k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X6),X7),X5))) ) | ~spl2_25),
% 0.22/0.55    inference(avatar_component_clause,[],[f216])).
% 0.22/0.55  fof(f275,plain,(
% 0.22/0.55    spl2_29 | ~spl2_1 | ~spl2_23),
% 0.22/0.55    inference(avatar_split_clause,[],[f263,f208,f75,f273])).
% 0.22/0.55  fof(f208,plain,(
% 0.22/0.55    spl2_23 <=> ! [X1,X0,X2] : (k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2)) | ~v1_relat_1(X2) | ~v1_relat_1(X1))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 0.22/0.55  fof(f263,plain,(
% 0.22/0.55    ( ! [X6,X4,X5] : (~v1_relat_1(X4) | k8_relat_1(X5,k5_relat_1(k6_relat_1(X6),X4)) = k5_relat_1(k6_relat_1(X6),k8_relat_1(X5,X4))) ) | (~spl2_1 | ~spl2_23)),
% 0.22/0.55    inference(resolution,[],[f209,f76])).
% 0.22/0.55  fof(f209,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X2) | k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2))) ) | ~spl2_23),
% 0.22/0.55    inference(avatar_component_clause,[],[f208])).
% 0.22/0.55  fof(f218,plain,(
% 0.22/0.55    spl2_25 | ~spl2_1 | ~spl2_4 | ~spl2_9 | ~spl2_10 | ~spl2_13 | ~spl2_14 | ~spl2_20),
% 0.22/0.55    inference(avatar_split_clause,[],[f197,f185,f147,f138,f119,f115,f87,f75,f216])).
% 0.22/0.55  fof(f87,plain,(
% 0.22/0.55    spl2_4 <=> ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.55  fof(f115,plain,(
% 0.22/0.55    spl2_9 <=> ! [X1,X0] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.22/0.55  fof(f119,plain,(
% 0.22/0.55    spl2_10 <=> ! [X1,X0] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.22/0.55  fof(f185,plain,(
% 0.22/0.55    spl2_20 <=> ! [X1,X0] : (k4_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k5_relat_1(k4_relat_1(X0),k6_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 0.22/0.55  fof(f197,plain,(
% 0.22/0.55    ( ! [X6,X7,X5] : (k8_relat_1(X5,k7_relat_1(k6_relat_1(X7),X6)) = k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X6),X7),X5))) ) | (~spl2_1 | ~spl2_4 | ~spl2_9 | ~spl2_10 | ~spl2_13 | ~spl2_14 | ~spl2_20)),
% 0.22/0.55    inference(forward_demodulation,[],[f196,f150])).
% 0.22/0.55  fof(f150,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k5_relat_1(k6_relat_1(X2),k7_relat_1(k6_relat_1(X0),X1))) ) | (~spl2_10 | ~spl2_14)),
% 0.22/0.55    inference(resolution,[],[f148,f120])).
% 0.22/0.55  fof(f120,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) ) | ~spl2_10),
% 0.22/0.55    inference(avatar_component_clause,[],[f119])).
% 0.22/0.55  fof(f196,plain,(
% 0.22/0.55    ( ! [X6,X7,X5] : (k4_relat_1(k5_relat_1(k6_relat_1(X5),k7_relat_1(k6_relat_1(X6),X7))) = k8_relat_1(X5,k7_relat_1(k6_relat_1(X7),X6))) ) | (~spl2_1 | ~spl2_4 | ~spl2_9 | ~spl2_13 | ~spl2_14 | ~spl2_20)),
% 0.22/0.55    inference(forward_demodulation,[],[f195,f151])).
% 0.22/0.55  fof(f151,plain,(
% 0.22/0.55    ( ! [X4,X5,X3] : (k8_relat_1(X3,k7_relat_1(k6_relat_1(X4),X5)) = k5_relat_1(k7_relat_1(k6_relat_1(X4),X5),k6_relat_1(X3))) ) | (~spl2_9 | ~spl2_14)),
% 0.22/0.55    inference(resolution,[],[f148,f116])).
% 0.22/0.55  fof(f116,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))) ) | ~spl2_9),
% 0.22/0.55    inference(avatar_component_clause,[],[f115])).
% 0.22/0.55  fof(f195,plain,(
% 0.22/0.55    ( ! [X6,X7,X5] : (k4_relat_1(k5_relat_1(k6_relat_1(X5),k7_relat_1(k6_relat_1(X6),X7))) = k5_relat_1(k7_relat_1(k6_relat_1(X7),X6),k6_relat_1(X5))) ) | (~spl2_1 | ~spl2_4 | ~spl2_13 | ~spl2_14 | ~spl2_20)),
% 0.22/0.55    inference(forward_demodulation,[],[f190,f193])).
% 0.22/0.55  fof(f193,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0))) ) | (~spl2_1 | ~spl2_4 | ~spl2_13 | ~spl2_20)),
% 0.22/0.55    inference(forward_demodulation,[],[f192,f139])).
% 0.22/0.55  fof(f192,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0))) ) | (~spl2_1 | ~spl2_4 | ~spl2_13 | ~spl2_20)),
% 0.22/0.55    inference(forward_demodulation,[],[f191,f139])).
% 0.22/0.55  fof(f191,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)))) ) | (~spl2_1 | ~spl2_4 | ~spl2_20)),
% 0.22/0.55    inference(forward_demodulation,[],[f188,f88])).
% 0.22/0.55  fof(f88,plain,(
% 0.22/0.55    ( ! [X0] : (k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))) ) | ~spl2_4),
% 0.22/0.55    inference(avatar_component_clause,[],[f87])).
% 0.22/0.55  fof(f188,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k5_relat_1(k4_relat_1(k6_relat_1(X1)),k6_relat_1(X0))) ) | (~spl2_1 | ~spl2_20)),
% 0.22/0.55    inference(resolution,[],[f186,f76])).
% 0.22/0.55  fof(f186,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~v1_relat_1(X0) | k4_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k5_relat_1(k4_relat_1(X0),k6_relat_1(X1))) ) | ~spl2_20),
% 0.22/0.55    inference(avatar_component_clause,[],[f185])).
% 0.22/0.55  fof(f190,plain,(
% 0.22/0.55    ( ! [X6,X7,X5] : (k4_relat_1(k5_relat_1(k6_relat_1(X5),k7_relat_1(k6_relat_1(X6),X7))) = k5_relat_1(k4_relat_1(k7_relat_1(k6_relat_1(X6),X7)),k6_relat_1(X5))) ) | (~spl2_14 | ~spl2_20)),
% 0.22/0.55    inference(resolution,[],[f186,f148])).
% 0.22/0.55  fof(f210,plain,(
% 0.22/0.55    spl2_23),
% 0.22/0.55    inference(avatar_split_clause,[],[f57,f208])).
% 0.22/0.55  fof(f57,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2)) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f35])).
% 0.22/0.55  fof(f35,plain,(
% 0.22/0.55    ! [X0,X1] : (! [X2] : (k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.22/0.55    inference(ennf_transformation,[],[f13])).
% 0.22/0.55  fof(f13,axiom,(
% 0.22/0.55    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2))))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_relat_1)).
% 0.22/0.55  fof(f206,plain,(
% 0.22/0.55    spl2_22 | ~spl2_10 | ~spl2_14),
% 0.22/0.55    inference(avatar_split_clause,[],[f150,f147,f119,f204])).
% 0.22/0.55  fof(f201,plain,(
% 0.22/0.55    spl2_21 | ~spl2_1 | ~spl2_4 | ~spl2_13 | ~spl2_20),
% 0.22/0.55    inference(avatar_split_clause,[],[f193,f185,f138,f87,f75,f199])).
% 0.22/0.55  fof(f187,plain,(
% 0.22/0.55    spl2_20 | ~spl2_1 | ~spl2_4 | ~spl2_19),
% 0.22/0.55    inference(avatar_split_clause,[],[f183,f177,f87,f75,f185])).
% 0.22/0.55  fof(f177,plain,(
% 0.22/0.55    spl2_19 <=> ! [X1,X0] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 0.22/0.55  fof(f183,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k4_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k5_relat_1(k4_relat_1(X0),k6_relat_1(X1)) | ~v1_relat_1(X0)) ) | (~spl2_1 | ~spl2_4 | ~spl2_19)),
% 0.22/0.55    inference(forward_demodulation,[],[f180,f88])).
% 0.22/0.55  fof(f180,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~v1_relat_1(X0) | k4_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k5_relat_1(k4_relat_1(X0),k4_relat_1(k6_relat_1(X1)))) ) | (~spl2_1 | ~spl2_19)),
% 0.22/0.55    inference(resolution,[],[f178,f76])).
% 0.22/0.55  fof(f178,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))) ) | ~spl2_19),
% 0.22/0.55    inference(avatar_component_clause,[],[f177])).
% 0.22/0.55  fof(f179,plain,(
% 0.22/0.55    spl2_19),
% 0.22/0.55    inference(avatar_split_clause,[],[f48,f177])).
% 0.22/0.55  fof(f48,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f28])).
% 0.22/0.55  fof(f28,plain,(
% 0.22/0.55    ! [X0] : (! [X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.55    inference(ennf_transformation,[],[f14])).
% 0.22/0.55  fof(f14,axiom,(
% 0.22/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).
% 0.22/0.55  fof(f175,plain,(
% 0.22/0.55    ~spl2_18 | ~spl2_1 | ~spl2_9 | ~spl2_10),
% 0.22/0.55    inference(avatar_split_clause,[],[f128,f119,f115,f75,f172])).
% 0.22/0.55  fof(f128,plain,(
% 0.22/0.55    k6_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1) | (~spl2_1 | ~spl2_9 | ~spl2_10)),
% 0.22/0.55    inference(backward_demodulation,[],[f124,f127])).
% 0.22/0.55  fof(f127,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),X1)) ) | (~spl2_1 | ~spl2_9 | ~spl2_10)),
% 0.22/0.55    inference(backward_demodulation,[],[f122,f125])).
% 0.22/0.55  fof(f125,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1)) ) | (~spl2_1 | ~spl2_10)),
% 0.22/0.55    inference(resolution,[],[f120,f76])).
% 0.22/0.55  fof(f122,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k8_relat_1(X0,k6_relat_1(X1))) ) | (~spl2_1 | ~spl2_9)),
% 0.22/0.55    inference(resolution,[],[f116,f76])).
% 0.22/0.55  fof(f124,plain,(
% 0.22/0.55    k6_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) != k8_relat_1(sK0,k6_relat_1(sK1)) | (~spl2_1 | ~spl2_9)),
% 0.22/0.55    inference(backward_demodulation,[],[f71,f122])).
% 0.22/0.55  fof(f71,plain,(
% 0.22/0.55    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),
% 0.22/0.55    inference(definition_unfolding,[],[f41,f70])).
% 0.22/0.55  fof(f41,plain,(
% 0.22/0.55    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 0.22/0.55    inference(cnf_transformation,[],[f40])).
% 0.22/0.55  fof(f40,plain,(
% 0.22/0.55    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 0.22/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f39])).
% 0.22/0.55  fof(f39,plain,(
% 0.22/0.55    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f25,plain,(
% 0.22/0.55    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))),
% 0.22/0.55    inference(ennf_transformation,[],[f24])).
% 0.22/0.55  fof(f24,negated_conjecture,(
% 0.22/0.55    ~! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.22/0.55    inference(negated_conjecture,[],[f23])).
% 0.22/0.55  fof(f23,conjecture,(
% 0.22/0.55    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).
% 0.22/0.55  fof(f169,plain,(
% 0.22/0.55    spl2_17 | ~spl2_1 | ~spl2_2 | ~spl2_12 | ~spl2_13),
% 0.22/0.55    inference(avatar_split_clause,[],[f165,f138,f134,f79,f75,f167])).
% 0.22/0.55  fof(f165,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1) | ~r1_tarski(X0,X1)) ) | (~spl2_1 | ~spl2_2 | ~spl2_12 | ~spl2_13)),
% 0.22/0.55    inference(forward_demodulation,[],[f164,f139])).
% 0.22/0.55  fof(f164,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) ) | (~spl2_1 | ~spl2_2 | ~spl2_12)),
% 0.22/0.55    inference(subsumption_resolution,[],[f163,f76])).
% 0.22/0.55  fof(f163,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) ) | (~spl2_2 | ~spl2_12)),
% 0.22/0.55    inference(superposition,[],[f135,f80])).
% 0.22/0.55  fof(f162,plain,(
% 0.22/0.55    spl2_16),
% 0.22/0.55    inference(avatar_split_clause,[],[f72,f160])).
% 0.22/0.55  fof(f72,plain,(
% 0.22/0.55    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0)) )),
% 0.22/0.55    inference(definition_unfolding,[],[f50,f70])).
% 0.22/0.55  fof(f50,plain,(
% 0.22/0.55    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f1])).
% 0.22/0.55  fof(f1,axiom,(
% 0.22/0.55    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.22/0.55  fof(f149,plain,(
% 0.22/0.55    spl2_14 | ~spl2_1 | ~spl2_5 | ~spl2_13),
% 0.22/0.55    inference(avatar_split_clause,[],[f145,f138,f91,f75,f147])).
% 0.22/0.55  fof(f91,plain,(
% 0.22/0.55    spl2_5 <=> ! [X1,X0] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.22/0.55  fof(f145,plain,(
% 0.22/0.55    ( ! [X2,X1] : (v1_relat_1(k7_relat_1(k6_relat_1(X2),X1))) ) | (~spl2_1 | ~spl2_5 | ~spl2_13)),
% 0.22/0.55    inference(subsumption_resolution,[],[f144,f76])).
% 0.22/0.55  fof(f144,plain,(
% 0.22/0.55    ( ! [X2,X1] : (v1_relat_1(k7_relat_1(k6_relat_1(X2),X1)) | ~v1_relat_1(k6_relat_1(X1))) ) | (~spl2_1 | ~spl2_5 | ~spl2_13)),
% 0.22/0.55    inference(subsumption_resolution,[],[f143,f76])).
% 0.22/0.55  fof(f143,plain,(
% 0.22/0.55    ( ! [X2,X1] : (v1_relat_1(k7_relat_1(k6_relat_1(X2),X1)) | ~v1_relat_1(k6_relat_1(X2)) | ~v1_relat_1(k6_relat_1(X1))) ) | (~spl2_5 | ~spl2_13)),
% 0.22/0.55    inference(superposition,[],[f92,f139])).
% 0.22/0.55  fof(f92,plain,(
% 0.22/0.55    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl2_5),
% 0.22/0.55    inference(avatar_component_clause,[],[f91])).
% 0.22/0.55  fof(f140,plain,(
% 0.22/0.55    spl2_13 | ~spl2_1 | ~spl2_10),
% 0.22/0.55    inference(avatar_split_clause,[],[f125,f119,f75,f138])).
% 0.22/0.55  fof(f136,plain,(
% 0.22/0.55    spl2_12),
% 0.22/0.55    inference(avatar_split_clause,[],[f56,f134])).
% 0.22/0.55  fof(f56,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f34])).
% 0.22/0.55  fof(f34,plain,(
% 0.22/0.55    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.55    inference(flattening,[],[f33])).
% 0.22/0.55  fof(f33,plain,(
% 0.22/0.55    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.55    inference(ennf_transformation,[],[f18])).
% 0.22/0.55  fof(f18,axiom,(
% 0.22/0.55    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).
% 0.22/0.55  fof(f132,plain,(
% 0.22/0.55    spl2_11 | ~spl2_1 | ~spl2_9 | ~spl2_10),
% 0.22/0.55    inference(avatar_split_clause,[],[f127,f119,f115,f75,f130])).
% 0.22/0.55  fof(f121,plain,(
% 0.22/0.55    spl2_10),
% 0.22/0.55    inference(avatar_split_clause,[],[f54,f119])).
% 0.22/0.55  fof(f54,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f31])).
% 0.22/0.55  fof(f31,plain,(
% 0.22/0.55    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.22/0.55    inference(ennf_transformation,[],[f22])).
% 0.22/0.55  fof(f22,axiom,(
% 0.22/0.55    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 0.22/0.55  fof(f117,plain,(
% 0.22/0.55    spl2_9),
% 0.22/0.55    inference(avatar_split_clause,[],[f53,f115])).
% 0.22/0.55  fof(f53,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f30])).
% 0.22/0.55  fof(f30,plain,(
% 0.22/0.55    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 0.22/0.55    inference(ennf_transformation,[],[f12])).
% 0.22/0.55  fof(f12,axiom,(
% 0.22/0.55    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).
% 0.22/0.55  fof(f101,plain,(
% 0.22/0.55    spl2_7),
% 0.22/0.55    inference(avatar_split_clause,[],[f47,f99])).
% 0.22/0.55  fof(f47,plain,(
% 0.22/0.55    ( ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f27])).
% 0.22/0.55  fof(f27,plain,(
% 0.22/0.55    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 0.22/0.55    inference(ennf_transformation,[],[f19])).
% 0.22/0.55  fof(f19,axiom,(
% 0.22/0.55    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).
% 0.22/0.55  fof(f93,plain,(
% 0.22/0.55    spl2_5),
% 0.22/0.55    inference(avatar_split_clause,[],[f59,f91])).
% 0.22/0.55  fof(f59,plain,(
% 0.22/0.55    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f38])).
% 0.22/0.55  fof(f38,plain,(
% 0.22/0.55    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.22/0.55    inference(flattening,[],[f37])).
% 0.22/0.55  fof(f37,plain,(
% 0.22/0.55    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 0.22/0.55    inference(ennf_transformation,[],[f9])).
% 0.22/0.55  fof(f9,axiom,(
% 0.22/0.55    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 0.22/0.55  fof(f89,plain,(
% 0.22/0.55    spl2_4),
% 0.22/0.55    inference(avatar_split_clause,[],[f43,f87])).
% 0.22/0.55  fof(f43,plain,(
% 0.22/0.55    ( ! [X0] : (k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f17])).
% 0.22/0.55  fof(f17,axiom,(
% 0.22/0.55    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_relat_1)).
% 0.22/0.55  fof(f81,plain,(
% 0.22/0.55    spl2_2),
% 0.22/0.55    inference(avatar_split_clause,[],[f44,f79])).
% 0.22/0.55  fof(f44,plain,(
% 0.22/0.55    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.22/0.55    inference(cnf_transformation,[],[f16])).
% 0.22/0.55  fof(f16,axiom,(
% 0.22/0.55    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.22/0.55  fof(f77,plain,(
% 0.22/0.55    spl2_1),
% 0.22/0.55    inference(avatar_split_clause,[],[f42,f75])).
% 0.22/0.55  fof(f42,plain,(
% 0.22/0.55    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f10])).
% 0.22/0.55  fof(f10,axiom,(
% 0.22/0.55    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.22/0.55  % SZS output end Proof for theBenchmark
% 0.22/0.55  % (15931)------------------------------
% 0.22/0.55  % (15931)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (15931)Termination reason: Refutation
% 0.22/0.55  
% 0.22/0.55  % (15931)Memory used [KB]: 7675
% 0.22/0.55  % (15931)Time elapsed: 0.082 s
% 0.22/0.55  % (15931)------------------------------
% 0.22/0.55  % (15931)------------------------------
% 0.22/0.55  % (15941)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.55  % (15923)Success in time 0.19 s
%------------------------------------------------------------------------------
