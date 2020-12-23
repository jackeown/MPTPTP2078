%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:02 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  227 ( 424 expanded)
%              Number of leaves         :   60 ( 211 expanded)
%              Depth                    :    8
%              Number of atoms          :  622 (1089 expanded)
%              Number of equality atoms :  114 ( 217 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2014,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f63,f67,f71,f75,f79,f84,f94,f99,f126,f135,f144,f158,f162,f178,f195,f259,f284,f296,f300,f329,f349,f358,f396,f412,f506,f543,f558,f565,f580,f588,f651,f657,f665,f714,f845,f849,f857,f937,f1745,f1964,f1974,f1994,f2010])).

fof(f2010,plain,
    ( ~ spl2_1
    | ~ spl2_5
    | spl2_79
    | ~ spl2_199 ),
    inference(avatar_contradiction_clause,[],[f2009])).

fof(f2009,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_5
    | spl2_79
    | ~ spl2_199 ),
    inference(subsumption_resolution,[],[f664,f2008])).

fof(f2008,plain,
    ( ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k9_relat_1(k4_relat_1(sK1),k9_relat_1(sK1,X0)))
    | ~ spl2_1
    | ~ spl2_5
    | ~ spl2_199 ),
    inference(subsumption_resolution,[],[f2006,f62])).

fof(f62,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl2_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f2006,plain,
    ( ! [X0] :
        ( r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k9_relat_1(k4_relat_1(sK1),k9_relat_1(sK1,X0)))
        | ~ v1_relat_1(sK1) )
    | ~ spl2_5
    | ~ spl2_199 ),
    inference(resolution,[],[f1993,f78])).

fof(f78,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(k7_relat_1(X0,X1))
        | ~ v1_relat_1(X0) )
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl2_5
  <=> ! [X1,X0] :
        ( v1_relat_1(k7_relat_1(X0,X1))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f1993,plain,
    ( ! [X1] :
        ( ~ v1_relat_1(k7_relat_1(sK1,X1))
        | r1_tarski(k1_relat_1(k7_relat_1(sK1,X1)),k9_relat_1(k4_relat_1(sK1),k9_relat_1(sK1,X1))) )
    | ~ spl2_199 ),
    inference(avatar_component_clause,[],[f1992])).

fof(f1992,plain,
    ( spl2_199
  <=> ! [X1] :
        ( r1_tarski(k1_relat_1(k7_relat_1(sK1,X1)),k9_relat_1(k4_relat_1(sK1),k9_relat_1(sK1,X1)))
        | ~ v1_relat_1(k7_relat_1(sK1,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_199])])).

fof(f664,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK1,sK0)),k9_relat_1(k4_relat_1(sK1),k9_relat_1(sK1,sK0)))
    | spl2_79 ),
    inference(avatar_component_clause,[],[f662])).

fof(f662,plain,
    ( spl2_79
  <=> r1_tarski(k1_relat_1(k7_relat_1(sK1,sK0)),k9_relat_1(k4_relat_1(sK1),k9_relat_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_79])])).

fof(f1994,plain,
    ( spl2_199
    | ~ spl2_34
    | ~ spl2_100
    | ~ spl2_103
    | ~ spl2_197 ),
    inference(avatar_split_clause,[],[f1982,f1972,f935,f847,f257,f1992])).

fof(f257,plain,
    ( spl2_34
  <=> ! [X1,X0] :
        ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).

fof(f847,plain,
    ( spl2_100
  <=> ! [X3] : k9_relat_1(k4_relat_1(sK1),X3) = k1_relat_1(k5_relat_1(sK1,k6_relat_1(X3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_100])])).

fof(f935,plain,
    ( spl2_103
  <=> ! [X0] : v1_relat_1(k5_relat_1(sK1,k6_relat_1(X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_103])])).

fof(f1972,plain,
    ( spl2_197
  <=> ! [X0] : r1_tarski(k7_relat_1(sK1,X0),k5_relat_1(sK1,k6_relat_1(k9_relat_1(sK1,X0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_197])])).

fof(f1982,plain,
    ( ! [X1] :
        ( r1_tarski(k1_relat_1(k7_relat_1(sK1,X1)),k9_relat_1(k4_relat_1(sK1),k9_relat_1(sK1,X1)))
        | ~ v1_relat_1(k7_relat_1(sK1,X1)) )
    | ~ spl2_34
    | ~ spl2_100
    | ~ spl2_103
    | ~ spl2_197 ),
    inference(forward_demodulation,[],[f1981,f848])).

fof(f848,plain,
    ( ! [X3] : k9_relat_1(k4_relat_1(sK1),X3) = k1_relat_1(k5_relat_1(sK1,k6_relat_1(X3)))
    | ~ spl2_100 ),
    inference(avatar_component_clause,[],[f847])).

fof(f1981,plain,
    ( ! [X1] :
        ( r1_tarski(k1_relat_1(k7_relat_1(sK1,X1)),k1_relat_1(k5_relat_1(sK1,k6_relat_1(k9_relat_1(sK1,X1)))))
        | ~ v1_relat_1(k7_relat_1(sK1,X1)) )
    | ~ spl2_34
    | ~ spl2_103
    | ~ spl2_197 ),
    inference(subsumption_resolution,[],[f1976,f936])).

fof(f936,plain,
    ( ! [X0] : v1_relat_1(k5_relat_1(sK1,k6_relat_1(X0)))
    | ~ spl2_103 ),
    inference(avatar_component_clause,[],[f935])).

fof(f1976,plain,
    ( ! [X1] :
        ( r1_tarski(k1_relat_1(k7_relat_1(sK1,X1)),k1_relat_1(k5_relat_1(sK1,k6_relat_1(k9_relat_1(sK1,X1)))))
        | ~ v1_relat_1(k5_relat_1(sK1,k6_relat_1(k9_relat_1(sK1,X1))))
        | ~ v1_relat_1(k7_relat_1(sK1,X1)) )
    | ~ spl2_34
    | ~ spl2_197 ),
    inference(resolution,[],[f1973,f258])).

fof(f258,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl2_34 ),
    inference(avatar_component_clause,[],[f257])).

fof(f1973,plain,
    ( ! [X0] : r1_tarski(k7_relat_1(sK1,X0),k5_relat_1(sK1,k6_relat_1(k9_relat_1(sK1,X0))))
    | ~ spl2_197 ),
    inference(avatar_component_clause,[],[f1972])).

fof(f1974,plain,
    ( spl2_197
    | ~ spl2_2
    | ~ spl2_52
    | ~ spl2_196 ),
    inference(avatar_split_clause,[],[f1970,f1962,f394,f65,f1972])).

fof(f65,plain,
    ( spl2_2
  <=> ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f394,plain,
    ( spl2_52
  <=> ! [X11,X10] :
        ( ~ v1_relat_1(X10)
        | r1_tarski(k5_relat_1(k7_relat_1(sK1,X11),X10),k5_relat_1(sK1,X10)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_52])])).

fof(f1962,plain,
    ( spl2_196
  <=> ! [X15] : k7_relat_1(sK1,X15) = k5_relat_1(k7_relat_1(sK1,X15),k6_relat_1(k9_relat_1(sK1,X15))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_196])])).

fof(f1970,plain,
    ( ! [X0] : r1_tarski(k7_relat_1(sK1,X0),k5_relat_1(sK1,k6_relat_1(k9_relat_1(sK1,X0))))
    | ~ spl2_2
    | ~ spl2_52
    | ~ spl2_196 ),
    inference(subsumption_resolution,[],[f1967,f66])).

fof(f66,plain,
    ( ! [X0] : v1_relat_1(k6_relat_1(X0))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f65])).

fof(f1967,plain,
    ( ! [X0] :
        ( r1_tarski(k7_relat_1(sK1,X0),k5_relat_1(sK1,k6_relat_1(k9_relat_1(sK1,X0))))
        | ~ v1_relat_1(k6_relat_1(k9_relat_1(sK1,X0))) )
    | ~ spl2_52
    | ~ spl2_196 ),
    inference(superposition,[],[f395,f1963])).

fof(f1963,plain,
    ( ! [X15] : k7_relat_1(sK1,X15) = k5_relat_1(k7_relat_1(sK1,X15),k6_relat_1(k9_relat_1(sK1,X15)))
    | ~ spl2_196 ),
    inference(avatar_component_clause,[],[f1962])).

fof(f395,plain,
    ( ! [X10,X11] :
        ( r1_tarski(k5_relat_1(k7_relat_1(sK1,X11),X10),k5_relat_1(sK1,X10))
        | ~ v1_relat_1(X10) )
    | ~ spl2_52 ),
    inference(avatar_component_clause,[],[f394])).

fof(f1964,plain,
    ( spl2_196
    | ~ spl2_1
    | ~ spl2_20
    | ~ spl2_174 ),
    inference(avatar_split_clause,[],[f1960,f1743,f176,f60,f1962])).

fof(f176,plain,
    ( spl2_20
  <=> ! [X7] : k2_relat_1(k7_relat_1(sK1,X7)) = k9_relat_1(sK1,X7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f1743,plain,
    ( spl2_174
  <=> ! [X3,X2] :
        ( k7_relat_1(X2,X3) = k5_relat_1(k7_relat_1(X2,X3),k6_relat_1(k2_relat_1(k7_relat_1(X2,X3))))
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_174])])).

fof(f1960,plain,
    ( ! [X15] : k7_relat_1(sK1,X15) = k5_relat_1(k7_relat_1(sK1,X15),k6_relat_1(k9_relat_1(sK1,X15)))
    | ~ spl2_1
    | ~ spl2_20
    | ~ spl2_174 ),
    inference(forward_demodulation,[],[f1954,f177])).

fof(f177,plain,
    ( ! [X7] : k2_relat_1(k7_relat_1(sK1,X7)) = k9_relat_1(sK1,X7)
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f176])).

fof(f1954,plain,
    ( ! [X15] : k7_relat_1(sK1,X15) = k5_relat_1(k7_relat_1(sK1,X15),k6_relat_1(k2_relat_1(k7_relat_1(sK1,X15))))
    | ~ spl2_1
    | ~ spl2_174 ),
    inference(resolution,[],[f1744,f62])).

fof(f1744,plain,
    ( ! [X2,X3] :
        ( ~ v1_relat_1(X2)
        | k7_relat_1(X2,X3) = k5_relat_1(k7_relat_1(X2,X3),k6_relat_1(k2_relat_1(k7_relat_1(X2,X3)))) )
    | ~ spl2_174 ),
    inference(avatar_component_clause,[],[f1743])).

fof(f1745,plain,
    ( spl2_174
    | ~ spl2_5
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f138,f124,f77,f1743])).

fof(f124,plain,
    ( spl2_12
  <=> ! [X0] :
        ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f138,plain,
    ( ! [X2,X3] :
        ( k7_relat_1(X2,X3) = k5_relat_1(k7_relat_1(X2,X3),k6_relat_1(k2_relat_1(k7_relat_1(X2,X3))))
        | ~ v1_relat_1(X2) )
    | ~ spl2_5
    | ~ spl2_12 ),
    inference(resolution,[],[f125,f78])).

fof(f125,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 )
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f124])).

fof(f937,plain,
    ( spl2_103
    | ~ spl2_5
    | ~ spl2_75
    | ~ spl2_101 ),
    inference(avatar_split_clause,[],[f860,f855,f585,f77,f935])).

fof(f585,plain,
    ( spl2_75
  <=> v1_relat_1(k4_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_75])])).

fof(f855,plain,
    ( spl2_101
  <=> ! [X0] :
        ( v1_relat_1(k5_relat_1(sK1,k6_relat_1(X0)))
        | ~ v1_relat_1(k7_relat_1(k4_relat_1(sK1),X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_101])])).

fof(f860,plain,
    ( ! [X0] : v1_relat_1(k5_relat_1(sK1,k6_relat_1(X0)))
    | ~ spl2_5
    | ~ spl2_75
    | ~ spl2_101 ),
    inference(subsumption_resolution,[],[f858,f587])).

fof(f587,plain,
    ( v1_relat_1(k4_relat_1(sK1))
    | ~ spl2_75 ),
    inference(avatar_component_clause,[],[f585])).

fof(f858,plain,
    ( ! [X0] :
        ( v1_relat_1(k5_relat_1(sK1,k6_relat_1(X0)))
        | ~ v1_relat_1(k4_relat_1(sK1)) )
    | ~ spl2_5
    | ~ spl2_101 ),
    inference(resolution,[],[f856,f78])).

fof(f856,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(k7_relat_1(k4_relat_1(sK1),X0))
        | v1_relat_1(k5_relat_1(sK1,k6_relat_1(X0))) )
    | ~ spl2_101 ),
    inference(avatar_component_clause,[],[f855])).

fof(f857,plain,
    ( spl2_101
    | ~ spl2_3
    | ~ spl2_99 ),
    inference(avatar_split_clause,[],[f851,f843,f69,f855])).

fof(f69,plain,
    ( spl2_3
  <=> ! [X0] :
        ( v1_relat_1(k4_relat_1(X0))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f843,plain,
    ( spl2_99
  <=> ! [X2] : k4_relat_1(k7_relat_1(k4_relat_1(sK1),X2)) = k5_relat_1(sK1,k6_relat_1(X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_99])])).

fof(f851,plain,
    ( ! [X0] :
        ( v1_relat_1(k5_relat_1(sK1,k6_relat_1(X0)))
        | ~ v1_relat_1(k7_relat_1(k4_relat_1(sK1),X0)) )
    | ~ spl2_3
    | ~ spl2_99 ),
    inference(superposition,[],[f70,f844])).

fof(f844,plain,
    ( ! [X2] : k4_relat_1(k7_relat_1(k4_relat_1(sK1),X2)) = k5_relat_1(sK1,k6_relat_1(X2))
    | ~ spl2_99 ),
    inference(avatar_component_clause,[],[f843])).

fof(f70,plain,
    ( ! [X0] :
        ( v1_relat_1(k4_relat_1(X0))
        | ~ v1_relat_1(X0) )
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f69])).

fof(f849,plain,
    ( spl2_100
    | ~ spl2_7
    | ~ spl2_47
    | ~ spl2_75
    | ~ spl2_77
    | ~ spl2_87 ),
    inference(avatar_split_clause,[],[f806,f712,f649,f585,f347,f91,f847])).

fof(f91,plain,
    ( spl2_7
  <=> sK1 = k4_relat_1(k4_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f347,plain,
    ( spl2_47
  <=> ! [X7] : k7_relat_1(k4_relat_1(sK1),X7) = k5_relat_1(k6_relat_1(X7),k4_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_47])])).

fof(f649,plain,
    ( spl2_77
  <=> ! [X3] : k1_relat_1(k4_relat_1(k7_relat_1(k4_relat_1(sK1),X3))) = k9_relat_1(k4_relat_1(sK1),X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_77])])).

fof(f712,plain,
    ( spl2_87
  <=> ! [X3,X2] :
        ( k4_relat_1(k5_relat_1(k6_relat_1(X3),X2)) = k5_relat_1(k4_relat_1(X2),k6_relat_1(X3))
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_87])])).

fof(f806,plain,
    ( ! [X3] : k9_relat_1(k4_relat_1(sK1),X3) = k1_relat_1(k5_relat_1(sK1,k6_relat_1(X3)))
    | ~ spl2_7
    | ~ spl2_47
    | ~ spl2_75
    | ~ spl2_77
    | ~ spl2_87 ),
    inference(backward_demodulation,[],[f650,f804])).

fof(f804,plain,
    ( ! [X2] : k4_relat_1(k7_relat_1(k4_relat_1(sK1),X2)) = k5_relat_1(sK1,k6_relat_1(X2))
    | ~ spl2_7
    | ~ spl2_47
    | ~ spl2_75
    | ~ spl2_87 ),
    inference(forward_demodulation,[],[f803,f348])).

fof(f348,plain,
    ( ! [X7] : k7_relat_1(k4_relat_1(sK1),X7) = k5_relat_1(k6_relat_1(X7),k4_relat_1(sK1))
    | ~ spl2_47 ),
    inference(avatar_component_clause,[],[f347])).

fof(f803,plain,
    ( ! [X2] : k4_relat_1(k5_relat_1(k6_relat_1(X2),k4_relat_1(sK1))) = k5_relat_1(sK1,k6_relat_1(X2))
    | ~ spl2_7
    | ~ spl2_75
    | ~ spl2_87 ),
    inference(forward_demodulation,[],[f799,f93])).

fof(f93,plain,
    ( sK1 = k4_relat_1(k4_relat_1(sK1))
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f91])).

fof(f799,plain,
    ( ! [X2] : k4_relat_1(k5_relat_1(k6_relat_1(X2),k4_relat_1(sK1))) = k5_relat_1(k4_relat_1(k4_relat_1(sK1)),k6_relat_1(X2))
    | ~ spl2_75
    | ~ spl2_87 ),
    inference(resolution,[],[f713,f587])).

fof(f713,plain,
    ( ! [X2,X3] :
        ( ~ v1_relat_1(X2)
        | k4_relat_1(k5_relat_1(k6_relat_1(X3),X2)) = k5_relat_1(k4_relat_1(X2),k6_relat_1(X3)) )
    | ~ spl2_87 ),
    inference(avatar_component_clause,[],[f712])).

fof(f650,plain,
    ( ! [X3] : k1_relat_1(k4_relat_1(k7_relat_1(k4_relat_1(sK1),X3))) = k9_relat_1(k4_relat_1(sK1),X3)
    | ~ spl2_77 ),
    inference(avatar_component_clause,[],[f649])).

fof(f845,plain,
    ( spl2_99
    | ~ spl2_7
    | ~ spl2_47
    | ~ spl2_75
    | ~ spl2_87 ),
    inference(avatar_split_clause,[],[f804,f712,f585,f347,f91,f843])).

fof(f714,plain,
    ( spl2_87
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_54 ),
    inference(avatar_split_clause,[],[f539,f410,f73,f65,f712])).

fof(f73,plain,
    ( spl2_4
  <=> ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f410,plain,
    ( spl2_54
  <=> ! [X1,X0] :
        ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_54])])).

fof(f539,plain,
    ( ! [X2,X3] :
        ( k4_relat_1(k5_relat_1(k6_relat_1(X3),X2)) = k5_relat_1(k4_relat_1(X2),k6_relat_1(X3))
        | ~ v1_relat_1(X2) )
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_54 ),
    inference(forward_demodulation,[],[f536,f74])).

fof(f74,plain,
    ( ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f73])).

fof(f536,plain,
    ( ! [X2,X3] :
        ( ~ v1_relat_1(X2)
        | k4_relat_1(k5_relat_1(k6_relat_1(X3),X2)) = k5_relat_1(k4_relat_1(X2),k4_relat_1(k6_relat_1(X3))) )
    | ~ spl2_2
    | ~ spl2_54 ),
    inference(resolution,[],[f411,f66])).

fof(f411,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) )
    | ~ spl2_54 ),
    inference(avatar_component_clause,[],[f410])).

fof(f665,plain,
    ( ~ spl2_79
    | ~ spl2_14
    | spl2_24
    | ~ spl2_78 ),
    inference(avatar_split_clause,[],[f660,f655,f192,f133,f662])).

fof(f133,plain,
    ( spl2_14
  <=> ! [X1,X0] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f192,plain,
    ( spl2_24
  <=> r1_tarski(k1_setfam_1(k1_enumset1(sK0,sK0,k1_relat_1(sK1))),k9_relat_1(k4_relat_1(sK1),k9_relat_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).

fof(f655,plain,
    ( spl2_78
  <=> ! [X7] : k1_relat_1(k7_relat_1(sK1,X7)) = k1_setfam_1(k1_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),X7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_78])])).

fof(f660,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK1,sK0)),k9_relat_1(k4_relat_1(sK1),k9_relat_1(sK1,sK0)))
    | ~ spl2_14
    | spl2_24
    | ~ spl2_78 ),
    inference(backward_demodulation,[],[f194,f658])).

fof(f658,plain,
    ( ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k1_enumset1(X0,X0,k1_relat_1(sK1)))
    | ~ spl2_14
    | ~ spl2_78 ),
    inference(superposition,[],[f656,f134])).

fof(f134,plain,
    ( ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f133])).

fof(f656,plain,
    ( ! [X7] : k1_relat_1(k7_relat_1(sK1,X7)) = k1_setfam_1(k1_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),X7))
    | ~ spl2_78 ),
    inference(avatar_component_clause,[],[f655])).

fof(f194,plain,
    ( ~ r1_tarski(k1_setfam_1(k1_enumset1(sK0,sK0,k1_relat_1(sK1))),k9_relat_1(k4_relat_1(sK1),k9_relat_1(sK1,sK0)))
    | spl2_24 ),
    inference(avatar_component_clause,[],[f192])).

fof(f657,plain,
    ( spl2_78
    | ~ spl2_1
    | ~ spl2_65 ),
    inference(avatar_split_clause,[],[f592,f504,f60,f655])).

fof(f504,plain,
    ( spl2_65
  <=> ! [X1,X0] :
        ( k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X0))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_65])])).

fof(f592,plain,
    ( ! [X7] : k1_relat_1(k7_relat_1(sK1,X7)) = k1_setfam_1(k1_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),X7))
    | ~ spl2_1
    | ~ spl2_65 ),
    inference(resolution,[],[f505,f62])).

fof(f505,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X0)) )
    | ~ spl2_65 ),
    inference(avatar_component_clause,[],[f504])).

fof(f651,plain,
    ( spl2_77
    | ~ spl2_37
    | ~ spl2_48
    | ~ spl2_75 ),
    inference(avatar_split_clause,[],[f627,f585,f356,f282,f649])).

fof(f282,plain,
    ( spl2_37
  <=> ! [X3,X2] :
        ( k2_relat_1(k7_relat_1(X2,X3)) = k1_relat_1(k4_relat_1(k7_relat_1(X2,X3)))
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_37])])).

fof(f356,plain,
    ( spl2_48
  <=> ! [X7] : k2_relat_1(k7_relat_1(k4_relat_1(sK1),X7)) = k9_relat_1(k4_relat_1(sK1),X7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_48])])).

fof(f627,plain,
    ( ! [X3] : k1_relat_1(k4_relat_1(k7_relat_1(k4_relat_1(sK1),X3))) = k9_relat_1(k4_relat_1(sK1),X3)
    | ~ spl2_37
    | ~ spl2_48
    | ~ spl2_75 ),
    inference(forward_demodulation,[],[f605,f357])).

fof(f357,plain,
    ( ! [X7] : k2_relat_1(k7_relat_1(k4_relat_1(sK1),X7)) = k9_relat_1(k4_relat_1(sK1),X7)
    | ~ spl2_48 ),
    inference(avatar_component_clause,[],[f356])).

fof(f605,plain,
    ( ! [X3] : k2_relat_1(k7_relat_1(k4_relat_1(sK1),X3)) = k1_relat_1(k4_relat_1(k7_relat_1(k4_relat_1(sK1),X3)))
    | ~ spl2_37
    | ~ spl2_75 ),
    inference(resolution,[],[f587,f283])).

fof(f283,plain,
    ( ! [X2,X3] :
        ( ~ v1_relat_1(X2)
        | k2_relat_1(k7_relat_1(X2,X3)) = k1_relat_1(k4_relat_1(k7_relat_1(X2,X3))) )
    | ~ spl2_37 ),
    inference(avatar_component_clause,[],[f282])).

fof(f588,plain,
    ( spl2_75
    | ~ spl2_1
    | ~ spl2_15
    | ~ spl2_72
    | ~ spl2_74 ),
    inference(avatar_split_clause,[],[f583,f578,f562,f141,f60,f585])).

fof(f141,plain,
    ( spl2_15
  <=> sK1 = k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f562,plain,
    ( spl2_72
  <=> k4_relat_1(sK1) = k7_relat_1(k4_relat_1(sK1),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_72])])).

fof(f578,plain,
    ( spl2_74
  <=> ! [X0] :
        ( v1_relat_1(k7_relat_1(k4_relat_1(sK1),X0))
        | ~ v1_relat_1(k5_relat_1(sK1,k6_relat_1(X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_74])])).

fof(f583,plain,
    ( v1_relat_1(k4_relat_1(sK1))
    | ~ spl2_1
    | ~ spl2_15
    | ~ spl2_72
    | ~ spl2_74 ),
    inference(forward_demodulation,[],[f582,f564])).

fof(f564,plain,
    ( k4_relat_1(sK1) = k7_relat_1(k4_relat_1(sK1),k2_relat_1(sK1))
    | ~ spl2_72 ),
    inference(avatar_component_clause,[],[f562])).

fof(f582,plain,
    ( v1_relat_1(k7_relat_1(k4_relat_1(sK1),k2_relat_1(sK1)))
    | ~ spl2_1
    | ~ spl2_15
    | ~ spl2_74 ),
    inference(subsumption_resolution,[],[f581,f62])).

fof(f581,plain,
    ( ~ v1_relat_1(sK1)
    | v1_relat_1(k7_relat_1(k4_relat_1(sK1),k2_relat_1(sK1)))
    | ~ spl2_15
    | ~ spl2_74 ),
    inference(superposition,[],[f579,f143])).

fof(f143,plain,
    ( sK1 = k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1)))
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f141])).

fof(f579,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(k5_relat_1(sK1,k6_relat_1(X0)))
        | v1_relat_1(k7_relat_1(k4_relat_1(sK1),X0)) )
    | ~ spl2_74 ),
    inference(avatar_component_clause,[],[f578])).

fof(f580,plain,
    ( spl2_74
    | ~ spl2_3
    | ~ spl2_71 ),
    inference(avatar_split_clause,[],[f560,f556,f69,f578])).

fof(f556,plain,
    ( spl2_71
  <=> ! [X1] : k4_relat_1(k5_relat_1(sK1,k6_relat_1(X1))) = k7_relat_1(k4_relat_1(sK1),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_71])])).

fof(f560,plain,
    ( ! [X0] :
        ( v1_relat_1(k7_relat_1(k4_relat_1(sK1),X0))
        | ~ v1_relat_1(k5_relat_1(sK1,k6_relat_1(X0))) )
    | ~ spl2_3
    | ~ spl2_71 ),
    inference(superposition,[],[f70,f557])).

fof(f557,plain,
    ( ! [X1] : k4_relat_1(k5_relat_1(sK1,k6_relat_1(X1))) = k7_relat_1(k4_relat_1(sK1),X1)
    | ~ spl2_71 ),
    inference(avatar_component_clause,[],[f556])).

fof(f565,plain,
    ( spl2_72
    | ~ spl2_15
    | ~ spl2_71 ),
    inference(avatar_split_clause,[],[f559,f556,f141,f562])).

fof(f559,plain,
    ( k4_relat_1(sK1) = k7_relat_1(k4_relat_1(sK1),k2_relat_1(sK1))
    | ~ spl2_15
    | ~ spl2_71 ),
    inference(superposition,[],[f557,f143])).

fof(f558,plain,
    ( spl2_71
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_47
    | ~ spl2_69 ),
    inference(avatar_split_clause,[],[f549,f541,f347,f73,f65,f556])).

fof(f541,plain,
    ( spl2_69
  <=> ! [X7] :
        ( ~ v1_relat_1(X7)
        | k4_relat_1(k5_relat_1(sK1,X7)) = k5_relat_1(k4_relat_1(X7),k4_relat_1(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_69])])).

fof(f549,plain,
    ( ! [X1] : k4_relat_1(k5_relat_1(sK1,k6_relat_1(X1))) = k7_relat_1(k4_relat_1(sK1),X1)
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_47
    | ~ spl2_69 ),
    inference(forward_demodulation,[],[f548,f348])).

fof(f548,plain,
    ( ! [X1] : k4_relat_1(k5_relat_1(sK1,k6_relat_1(X1))) = k5_relat_1(k6_relat_1(X1),k4_relat_1(sK1))
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_69 ),
    inference(forward_demodulation,[],[f545,f74])).

fof(f545,plain,
    ( ! [X1] : k4_relat_1(k5_relat_1(sK1,k6_relat_1(X1))) = k5_relat_1(k4_relat_1(k6_relat_1(X1)),k4_relat_1(sK1))
    | ~ spl2_2
    | ~ spl2_69 ),
    inference(resolution,[],[f542,f66])).

fof(f542,plain,
    ( ! [X7] :
        ( ~ v1_relat_1(X7)
        | k4_relat_1(k5_relat_1(sK1,X7)) = k5_relat_1(k4_relat_1(X7),k4_relat_1(sK1)) )
    | ~ spl2_69 ),
    inference(avatar_component_clause,[],[f541])).

fof(f543,plain,
    ( spl2_69
    | ~ spl2_1
    | ~ spl2_54 ),
    inference(avatar_split_clause,[],[f538,f410,f60,f541])).

fof(f538,plain,
    ( ! [X7] :
        ( ~ v1_relat_1(X7)
        | k4_relat_1(k5_relat_1(sK1,X7)) = k5_relat_1(k4_relat_1(X7),k4_relat_1(sK1)) )
    | ~ spl2_1
    | ~ spl2_54 ),
    inference(resolution,[],[f411,f62])).

fof(f506,plain,(
    spl2_65 ),
    inference(avatar_split_clause,[],[f57,f504])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f52,f54])).

fof(f54,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f48,f47])).

fof(f47,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f48,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(f412,plain,(
    spl2_54 ),
    inference(avatar_split_clause,[],[f43,f410])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relat_1)).

fof(f396,plain,
    ( spl2_52
    | ~ spl2_1
    | ~ spl2_45 ),
    inference(avatar_split_clause,[],[f392,f327,f60,f394])).

fof(f327,plain,
    ( spl2_45
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k5_relat_1(k7_relat_1(X1,X0),X2),k5_relat_1(X1,X2))
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_45])])).

fof(f392,plain,
    ( ! [X10,X11] :
        ( ~ v1_relat_1(X10)
        | r1_tarski(k5_relat_1(k7_relat_1(sK1,X11),X10),k5_relat_1(sK1,X10)) )
    | ~ spl2_1
    | ~ spl2_45 ),
    inference(resolution,[],[f328,f62])).

fof(f328,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X1)
        | ~ v1_relat_1(X2)
        | r1_tarski(k5_relat_1(k7_relat_1(X1,X0),X2),k5_relat_1(X1,X2)) )
    | ~ spl2_45 ),
    inference(avatar_component_clause,[],[f327])).

fof(f358,plain,
    ( spl2_48
    | ~ spl2_1
    | ~ spl2_41 ),
    inference(avatar_split_clause,[],[f353,f298,f60,f356])).

fof(f298,plain,
    ( spl2_41
  <=> ! [X1,X0] :
        ( k2_relat_1(k7_relat_1(k4_relat_1(X0),X1)) = k9_relat_1(k4_relat_1(X0),X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_41])])).

fof(f353,plain,
    ( ! [X7] : k2_relat_1(k7_relat_1(k4_relat_1(sK1),X7)) = k9_relat_1(k4_relat_1(sK1),X7)
    | ~ spl2_1
    | ~ spl2_41 ),
    inference(resolution,[],[f299,f62])).

fof(f299,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | k2_relat_1(k7_relat_1(k4_relat_1(X0),X1)) = k9_relat_1(k4_relat_1(X0),X1) )
    | ~ spl2_41 ),
    inference(avatar_component_clause,[],[f298])).

fof(f349,plain,
    ( spl2_47
    | ~ spl2_1
    | ~ spl2_40 ),
    inference(avatar_split_clause,[],[f344,f294,f60,f347])).

fof(f294,plain,
    ( spl2_40
  <=> ! [X1,X0] :
        ( k7_relat_1(k4_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X1),k4_relat_1(X0))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_40])])).

fof(f344,plain,
    ( ! [X7] : k7_relat_1(k4_relat_1(sK1),X7) = k5_relat_1(k6_relat_1(X7),k4_relat_1(sK1))
    | ~ spl2_1
    | ~ spl2_40 ),
    inference(resolution,[],[f295,f62])).

fof(f295,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | k7_relat_1(k4_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X1),k4_relat_1(X0)) )
    | ~ spl2_40 ),
    inference(avatar_component_clause,[],[f294])).

fof(f329,plain,(
    spl2_45 ),
    inference(avatar_split_clause,[],[f53,f327])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_relat_1(k7_relat_1(X1,X0),X2),k5_relat_1(X1,X2))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k5_relat_1(k7_relat_1(X1,X0),X2),k5_relat_1(X1,X2))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => r1_tarski(k5_relat_1(k7_relat_1(X1,X0),X2),k5_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_relat_1)).

fof(f300,plain,
    ( spl2_41
    | ~ spl2_3
    | ~ spl2_18 ),
    inference(avatar_split_clause,[],[f171,f160,f69,f298])).

fof(f160,plain,
    ( spl2_18
  <=> ! [X1,X0] :
        ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f171,plain,
    ( ! [X0,X1] :
        ( k2_relat_1(k7_relat_1(k4_relat_1(X0),X1)) = k9_relat_1(k4_relat_1(X0),X1)
        | ~ v1_relat_1(X0) )
    | ~ spl2_3
    | ~ spl2_18 ),
    inference(resolution,[],[f161,f70])).

fof(f161,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) )
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f160])).

fof(f296,plain,
    ( spl2_40
    | ~ spl2_3
    | ~ spl2_17 ),
    inference(avatar_split_clause,[],[f163,f156,f69,f294])).

fof(f156,plain,
    ( spl2_17
  <=> ! [X1,X0] :
        ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f163,plain,
    ( ! [X0,X1] :
        ( k7_relat_1(k4_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X1),k4_relat_1(X0))
        | ~ v1_relat_1(X0) )
    | ~ spl2_3
    | ~ spl2_17 ),
    inference(resolution,[],[f157,f70])).

fof(f157,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) )
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f156])).

fof(f284,plain,
    ( spl2_37
    | ~ spl2_5
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f106,f97,f77,f282])).

fof(f97,plain,
    ( spl2_8
  <=> ! [X0] :
        ( k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f106,plain,
    ( ! [X2,X3] :
        ( k2_relat_1(k7_relat_1(X2,X3)) = k1_relat_1(k4_relat_1(k7_relat_1(X2,X3)))
        | ~ v1_relat_1(X2) )
    | ~ spl2_5
    | ~ spl2_8 ),
    inference(resolution,[],[f98,f78])).

fof(f98,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f97])).

fof(f259,plain,(
    spl2_34 ),
    inference(avatar_split_clause,[],[f44,f257])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

fof(f195,plain,(
    ~ spl2_24 ),
    inference(avatar_split_clause,[],[f58,f192])).

fof(f58,plain,(
    ~ r1_tarski(k1_setfam_1(k1_enumset1(sK0,sK0,k1_relat_1(sK1))),k9_relat_1(k4_relat_1(sK1),k9_relat_1(sK1,sK0))) ),
    inference(backward_demodulation,[],[f55,f56])).

fof(f56,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f46,f47,f47])).

fof(f46,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f55,plain,(
    ~ r1_tarski(k1_setfam_1(k1_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),sK0)),k9_relat_1(k4_relat_1(sK1),k9_relat_1(sK1,sK0))) ),
    inference(definition_unfolding,[],[f35,f54])).

fof(f35,plain,(
    ~ r1_tarski(k3_xboole_0(k1_relat_1(sK1),sK0),k9_relat_1(k4_relat_1(sK1),k9_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ~ r1_tarski(k3_xboole_0(k1_relat_1(sK1),sK0),k9_relat_1(k4_relat_1(sK1),k9_relat_1(sK1,sK0)))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f32])).

fof(f32,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k3_xboole_0(k1_relat_1(X1),X0),k9_relat_1(k4_relat_1(X1),k9_relat_1(X1,X0)))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k3_xboole_0(k1_relat_1(sK1),sK0),k9_relat_1(k4_relat_1(sK1),k9_relat_1(sK1,sK0)))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k3_xboole_0(k1_relat_1(X1),X0),k9_relat_1(k4_relat_1(X1),k9_relat_1(X1,X0)))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => r1_tarski(k3_xboole_0(k1_relat_1(X1),X0),k9_relat_1(k4_relat_1(X1),k9_relat_1(X1,X0))) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k3_xboole_0(k1_relat_1(X1),X0),k9_relat_1(k4_relat_1(X1),k9_relat_1(X1,X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_relat_1)).

fof(f178,plain,
    ( spl2_20
    | ~ spl2_1
    | ~ spl2_18 ),
    inference(avatar_split_clause,[],[f174,f160,f60,f176])).

fof(f174,plain,
    ( ! [X7] : k2_relat_1(k7_relat_1(sK1,X7)) = k9_relat_1(sK1,X7)
    | ~ spl2_1
    | ~ spl2_18 ),
    inference(resolution,[],[f161,f62])).

fof(f162,plain,(
    spl2_18 ),
    inference(avatar_split_clause,[],[f51,f160])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f158,plain,(
    spl2_17 ),
    inference(avatar_split_clause,[],[f50,f156])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f144,plain,
    ( spl2_15
    | ~ spl2_1
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f139,f124,f60,f141])).

fof(f139,plain,
    ( sK1 = k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1)))
    | ~ spl2_1
    | ~ spl2_12 ),
    inference(resolution,[],[f125,f62])).

fof(f135,plain,(
    spl2_14 ),
    inference(avatar_split_clause,[],[f56,f133])).

fof(f126,plain,(
    spl2_12 ),
    inference(avatar_split_clause,[],[f40,f124])).

fof(f40,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

fof(f99,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f41,f97])).

fof(f41,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

fof(f94,plain,
    ( spl2_7
    | ~ spl2_1
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f88,f82,f60,f91])).

fof(f82,plain,
    ( spl2_6
  <=> ! [X0] :
        ( k4_relat_1(k4_relat_1(X0)) = X0
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f88,plain,
    ( sK1 = k4_relat_1(k4_relat_1(sK1))
    | ~ spl2_1
    | ~ spl2_6 ),
    inference(resolution,[],[f83,f62])).

fof(f83,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k4_relat_1(k4_relat_1(X0)) = X0 )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f82])).

fof(f84,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f39,f82])).

fof(f39,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

fof(f79,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f49,f77])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f75,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f37,f73])).

fof(f37,plain,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_relat_1)).

fof(f71,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f38,f69])).

fof(f38,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f67,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f36,f65])).

fof(f36,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f63,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f34,f60])).

fof(f34,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:03:02 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (24318)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.46  % (24316)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.47  % (24328)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.47  % (24319)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.47  % (24317)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (24324)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.47  % (24320)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.48  % (24326)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.48  % (24325)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.49  % (24315)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.50  % (24313)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.50  % (24330)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.50  % (24323)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.51  % (24314)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.51  % (24321)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.51  % (24327)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.51  % (24329)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.52  % (24322)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.54  % (24320)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f2014,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(avatar_sat_refutation,[],[f63,f67,f71,f75,f79,f84,f94,f99,f126,f135,f144,f158,f162,f178,f195,f259,f284,f296,f300,f329,f349,f358,f396,f412,f506,f543,f558,f565,f580,f588,f651,f657,f665,f714,f845,f849,f857,f937,f1745,f1964,f1974,f1994,f2010])).
% 0.21/0.54  fof(f2010,plain,(
% 0.21/0.54    ~spl2_1 | ~spl2_5 | spl2_79 | ~spl2_199),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f2009])).
% 0.21/0.54  fof(f2009,plain,(
% 0.21/0.54    $false | (~spl2_1 | ~spl2_5 | spl2_79 | ~spl2_199)),
% 0.21/0.54    inference(subsumption_resolution,[],[f664,f2008])).
% 0.21/0.54  fof(f2008,plain,(
% 0.21/0.54    ( ! [X0] : (r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k9_relat_1(k4_relat_1(sK1),k9_relat_1(sK1,X0)))) ) | (~spl2_1 | ~spl2_5 | ~spl2_199)),
% 0.21/0.54    inference(subsumption_resolution,[],[f2006,f62])).
% 0.21/0.54  fof(f62,plain,(
% 0.21/0.54    v1_relat_1(sK1) | ~spl2_1),
% 0.21/0.54    inference(avatar_component_clause,[],[f60])).
% 0.21/0.54  fof(f60,plain,(
% 0.21/0.54    spl2_1 <=> v1_relat_1(sK1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.54  fof(f2006,plain,(
% 0.21/0.54    ( ! [X0] : (r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k9_relat_1(k4_relat_1(sK1),k9_relat_1(sK1,X0))) | ~v1_relat_1(sK1)) ) | (~spl2_5 | ~spl2_199)),
% 0.21/0.54    inference(resolution,[],[f1993,f78])).
% 0.21/0.54  fof(f78,plain,(
% 0.21/0.54    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) ) | ~spl2_5),
% 0.21/0.54    inference(avatar_component_clause,[],[f77])).
% 0.21/0.54  fof(f77,plain,(
% 0.21/0.54    spl2_5 <=> ! [X1,X0] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.54  fof(f1993,plain,(
% 0.21/0.54    ( ! [X1] : (~v1_relat_1(k7_relat_1(sK1,X1)) | r1_tarski(k1_relat_1(k7_relat_1(sK1,X1)),k9_relat_1(k4_relat_1(sK1),k9_relat_1(sK1,X1)))) ) | ~spl2_199),
% 0.21/0.54    inference(avatar_component_clause,[],[f1992])).
% 0.21/0.54  fof(f1992,plain,(
% 0.21/0.54    spl2_199 <=> ! [X1] : (r1_tarski(k1_relat_1(k7_relat_1(sK1,X1)),k9_relat_1(k4_relat_1(sK1),k9_relat_1(sK1,X1))) | ~v1_relat_1(k7_relat_1(sK1,X1)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_199])])).
% 0.21/0.54  fof(f664,plain,(
% 0.21/0.54    ~r1_tarski(k1_relat_1(k7_relat_1(sK1,sK0)),k9_relat_1(k4_relat_1(sK1),k9_relat_1(sK1,sK0))) | spl2_79),
% 0.21/0.54    inference(avatar_component_clause,[],[f662])).
% 0.21/0.54  fof(f662,plain,(
% 0.21/0.54    spl2_79 <=> r1_tarski(k1_relat_1(k7_relat_1(sK1,sK0)),k9_relat_1(k4_relat_1(sK1),k9_relat_1(sK1,sK0)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_79])])).
% 0.21/0.54  fof(f1994,plain,(
% 0.21/0.54    spl2_199 | ~spl2_34 | ~spl2_100 | ~spl2_103 | ~spl2_197),
% 0.21/0.54    inference(avatar_split_clause,[],[f1982,f1972,f935,f847,f257,f1992])).
% 0.21/0.54  fof(f257,plain,(
% 0.21/0.54    spl2_34 <=> ! [X1,X0] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).
% 0.21/0.54  fof(f847,plain,(
% 0.21/0.54    spl2_100 <=> ! [X3] : k9_relat_1(k4_relat_1(sK1),X3) = k1_relat_1(k5_relat_1(sK1,k6_relat_1(X3)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_100])])).
% 0.21/0.54  fof(f935,plain,(
% 0.21/0.54    spl2_103 <=> ! [X0] : v1_relat_1(k5_relat_1(sK1,k6_relat_1(X0)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_103])])).
% 0.21/0.54  fof(f1972,plain,(
% 0.21/0.54    spl2_197 <=> ! [X0] : r1_tarski(k7_relat_1(sK1,X0),k5_relat_1(sK1,k6_relat_1(k9_relat_1(sK1,X0))))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_197])])).
% 0.21/0.54  fof(f1982,plain,(
% 0.21/0.54    ( ! [X1] : (r1_tarski(k1_relat_1(k7_relat_1(sK1,X1)),k9_relat_1(k4_relat_1(sK1),k9_relat_1(sK1,X1))) | ~v1_relat_1(k7_relat_1(sK1,X1))) ) | (~spl2_34 | ~spl2_100 | ~spl2_103 | ~spl2_197)),
% 0.21/0.54    inference(forward_demodulation,[],[f1981,f848])).
% 0.21/0.54  fof(f848,plain,(
% 0.21/0.54    ( ! [X3] : (k9_relat_1(k4_relat_1(sK1),X3) = k1_relat_1(k5_relat_1(sK1,k6_relat_1(X3)))) ) | ~spl2_100),
% 0.21/0.54    inference(avatar_component_clause,[],[f847])).
% 0.21/0.54  fof(f1981,plain,(
% 0.21/0.54    ( ! [X1] : (r1_tarski(k1_relat_1(k7_relat_1(sK1,X1)),k1_relat_1(k5_relat_1(sK1,k6_relat_1(k9_relat_1(sK1,X1))))) | ~v1_relat_1(k7_relat_1(sK1,X1))) ) | (~spl2_34 | ~spl2_103 | ~spl2_197)),
% 0.21/0.54    inference(subsumption_resolution,[],[f1976,f936])).
% 0.21/0.54  fof(f936,plain,(
% 0.21/0.54    ( ! [X0] : (v1_relat_1(k5_relat_1(sK1,k6_relat_1(X0)))) ) | ~spl2_103),
% 0.21/0.54    inference(avatar_component_clause,[],[f935])).
% 0.21/0.54  fof(f1976,plain,(
% 0.21/0.54    ( ! [X1] : (r1_tarski(k1_relat_1(k7_relat_1(sK1,X1)),k1_relat_1(k5_relat_1(sK1,k6_relat_1(k9_relat_1(sK1,X1))))) | ~v1_relat_1(k5_relat_1(sK1,k6_relat_1(k9_relat_1(sK1,X1)))) | ~v1_relat_1(k7_relat_1(sK1,X1))) ) | (~spl2_34 | ~spl2_197)),
% 0.21/0.54    inference(resolution,[],[f1973,f258])).
% 0.21/0.54  fof(f258,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl2_34),
% 0.21/0.54    inference(avatar_component_clause,[],[f257])).
% 0.21/0.54  fof(f1973,plain,(
% 0.21/0.54    ( ! [X0] : (r1_tarski(k7_relat_1(sK1,X0),k5_relat_1(sK1,k6_relat_1(k9_relat_1(sK1,X0))))) ) | ~spl2_197),
% 0.21/0.54    inference(avatar_component_clause,[],[f1972])).
% 0.21/0.54  fof(f1974,plain,(
% 0.21/0.54    spl2_197 | ~spl2_2 | ~spl2_52 | ~spl2_196),
% 0.21/0.54    inference(avatar_split_clause,[],[f1970,f1962,f394,f65,f1972])).
% 0.21/0.54  fof(f65,plain,(
% 0.21/0.54    spl2_2 <=> ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.54  fof(f394,plain,(
% 0.21/0.54    spl2_52 <=> ! [X11,X10] : (~v1_relat_1(X10) | r1_tarski(k5_relat_1(k7_relat_1(sK1,X11),X10),k5_relat_1(sK1,X10)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_52])])).
% 0.21/0.54  fof(f1962,plain,(
% 0.21/0.54    spl2_196 <=> ! [X15] : k7_relat_1(sK1,X15) = k5_relat_1(k7_relat_1(sK1,X15),k6_relat_1(k9_relat_1(sK1,X15)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_196])])).
% 0.21/0.54  fof(f1970,plain,(
% 0.21/0.54    ( ! [X0] : (r1_tarski(k7_relat_1(sK1,X0),k5_relat_1(sK1,k6_relat_1(k9_relat_1(sK1,X0))))) ) | (~spl2_2 | ~spl2_52 | ~spl2_196)),
% 0.21/0.54    inference(subsumption_resolution,[],[f1967,f66])).
% 0.21/0.54  fof(f66,plain,(
% 0.21/0.54    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) ) | ~spl2_2),
% 0.21/0.54    inference(avatar_component_clause,[],[f65])).
% 0.21/0.54  fof(f1967,plain,(
% 0.21/0.54    ( ! [X0] : (r1_tarski(k7_relat_1(sK1,X0),k5_relat_1(sK1,k6_relat_1(k9_relat_1(sK1,X0)))) | ~v1_relat_1(k6_relat_1(k9_relat_1(sK1,X0)))) ) | (~spl2_52 | ~spl2_196)),
% 0.21/0.54    inference(superposition,[],[f395,f1963])).
% 0.21/0.54  fof(f1963,plain,(
% 0.21/0.54    ( ! [X15] : (k7_relat_1(sK1,X15) = k5_relat_1(k7_relat_1(sK1,X15),k6_relat_1(k9_relat_1(sK1,X15)))) ) | ~spl2_196),
% 0.21/0.54    inference(avatar_component_clause,[],[f1962])).
% 0.21/0.54  fof(f395,plain,(
% 0.21/0.54    ( ! [X10,X11] : (r1_tarski(k5_relat_1(k7_relat_1(sK1,X11),X10),k5_relat_1(sK1,X10)) | ~v1_relat_1(X10)) ) | ~spl2_52),
% 0.21/0.54    inference(avatar_component_clause,[],[f394])).
% 0.21/0.54  fof(f1964,plain,(
% 0.21/0.54    spl2_196 | ~spl2_1 | ~spl2_20 | ~spl2_174),
% 0.21/0.54    inference(avatar_split_clause,[],[f1960,f1743,f176,f60,f1962])).
% 0.21/0.54  fof(f176,plain,(
% 0.21/0.54    spl2_20 <=> ! [X7] : k2_relat_1(k7_relat_1(sK1,X7)) = k9_relat_1(sK1,X7)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 0.21/0.54  fof(f1743,plain,(
% 0.21/0.54    spl2_174 <=> ! [X3,X2] : (k7_relat_1(X2,X3) = k5_relat_1(k7_relat_1(X2,X3),k6_relat_1(k2_relat_1(k7_relat_1(X2,X3)))) | ~v1_relat_1(X2))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_174])])).
% 0.21/0.54  fof(f1960,plain,(
% 0.21/0.54    ( ! [X15] : (k7_relat_1(sK1,X15) = k5_relat_1(k7_relat_1(sK1,X15),k6_relat_1(k9_relat_1(sK1,X15)))) ) | (~spl2_1 | ~spl2_20 | ~spl2_174)),
% 0.21/0.54    inference(forward_demodulation,[],[f1954,f177])).
% 0.21/0.54  fof(f177,plain,(
% 0.21/0.54    ( ! [X7] : (k2_relat_1(k7_relat_1(sK1,X7)) = k9_relat_1(sK1,X7)) ) | ~spl2_20),
% 0.21/0.54    inference(avatar_component_clause,[],[f176])).
% 0.21/0.54  fof(f1954,plain,(
% 0.21/0.54    ( ! [X15] : (k7_relat_1(sK1,X15) = k5_relat_1(k7_relat_1(sK1,X15),k6_relat_1(k2_relat_1(k7_relat_1(sK1,X15))))) ) | (~spl2_1 | ~spl2_174)),
% 0.21/0.54    inference(resolution,[],[f1744,f62])).
% 0.21/0.54  fof(f1744,plain,(
% 0.21/0.54    ( ! [X2,X3] : (~v1_relat_1(X2) | k7_relat_1(X2,X3) = k5_relat_1(k7_relat_1(X2,X3),k6_relat_1(k2_relat_1(k7_relat_1(X2,X3))))) ) | ~spl2_174),
% 0.21/0.54    inference(avatar_component_clause,[],[f1743])).
% 0.21/0.54  fof(f1745,plain,(
% 0.21/0.54    spl2_174 | ~spl2_5 | ~spl2_12),
% 0.21/0.54    inference(avatar_split_clause,[],[f138,f124,f77,f1743])).
% 0.21/0.54  fof(f124,plain,(
% 0.21/0.54    spl2_12 <=> ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.21/0.54  fof(f138,plain,(
% 0.21/0.54    ( ! [X2,X3] : (k7_relat_1(X2,X3) = k5_relat_1(k7_relat_1(X2,X3),k6_relat_1(k2_relat_1(k7_relat_1(X2,X3)))) | ~v1_relat_1(X2)) ) | (~spl2_5 | ~spl2_12)),
% 0.21/0.54    inference(resolution,[],[f125,f78])).
% 0.21/0.54  fof(f125,plain,(
% 0.21/0.54    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0) ) | ~spl2_12),
% 0.21/0.54    inference(avatar_component_clause,[],[f124])).
% 0.21/0.54  fof(f937,plain,(
% 0.21/0.54    spl2_103 | ~spl2_5 | ~spl2_75 | ~spl2_101),
% 0.21/0.54    inference(avatar_split_clause,[],[f860,f855,f585,f77,f935])).
% 0.21/0.54  fof(f585,plain,(
% 0.21/0.54    spl2_75 <=> v1_relat_1(k4_relat_1(sK1))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_75])])).
% 0.21/0.54  fof(f855,plain,(
% 0.21/0.54    spl2_101 <=> ! [X0] : (v1_relat_1(k5_relat_1(sK1,k6_relat_1(X0))) | ~v1_relat_1(k7_relat_1(k4_relat_1(sK1),X0)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_101])])).
% 0.21/0.54  fof(f860,plain,(
% 0.21/0.54    ( ! [X0] : (v1_relat_1(k5_relat_1(sK1,k6_relat_1(X0)))) ) | (~spl2_5 | ~spl2_75 | ~spl2_101)),
% 0.21/0.54    inference(subsumption_resolution,[],[f858,f587])).
% 0.21/0.54  fof(f587,plain,(
% 0.21/0.54    v1_relat_1(k4_relat_1(sK1)) | ~spl2_75),
% 0.21/0.54    inference(avatar_component_clause,[],[f585])).
% 0.21/0.54  fof(f858,plain,(
% 0.21/0.54    ( ! [X0] : (v1_relat_1(k5_relat_1(sK1,k6_relat_1(X0))) | ~v1_relat_1(k4_relat_1(sK1))) ) | (~spl2_5 | ~spl2_101)),
% 0.21/0.54    inference(resolution,[],[f856,f78])).
% 0.21/0.54  fof(f856,plain,(
% 0.21/0.54    ( ! [X0] : (~v1_relat_1(k7_relat_1(k4_relat_1(sK1),X0)) | v1_relat_1(k5_relat_1(sK1,k6_relat_1(X0)))) ) | ~spl2_101),
% 0.21/0.54    inference(avatar_component_clause,[],[f855])).
% 0.21/0.54  fof(f857,plain,(
% 0.21/0.54    spl2_101 | ~spl2_3 | ~spl2_99),
% 0.21/0.54    inference(avatar_split_clause,[],[f851,f843,f69,f855])).
% 0.21/0.54  fof(f69,plain,(
% 0.21/0.54    spl2_3 <=> ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.54  fof(f843,plain,(
% 0.21/0.54    spl2_99 <=> ! [X2] : k4_relat_1(k7_relat_1(k4_relat_1(sK1),X2)) = k5_relat_1(sK1,k6_relat_1(X2))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_99])])).
% 0.21/0.54  fof(f851,plain,(
% 0.21/0.54    ( ! [X0] : (v1_relat_1(k5_relat_1(sK1,k6_relat_1(X0))) | ~v1_relat_1(k7_relat_1(k4_relat_1(sK1),X0))) ) | (~spl2_3 | ~spl2_99)),
% 0.21/0.54    inference(superposition,[],[f70,f844])).
% 0.21/0.54  fof(f844,plain,(
% 0.21/0.54    ( ! [X2] : (k4_relat_1(k7_relat_1(k4_relat_1(sK1),X2)) = k5_relat_1(sK1,k6_relat_1(X2))) ) | ~spl2_99),
% 0.21/0.54    inference(avatar_component_clause,[],[f843])).
% 0.21/0.54  fof(f70,plain,(
% 0.21/0.54    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) ) | ~spl2_3),
% 0.21/0.54    inference(avatar_component_clause,[],[f69])).
% 0.21/0.54  fof(f849,plain,(
% 0.21/0.54    spl2_100 | ~spl2_7 | ~spl2_47 | ~spl2_75 | ~spl2_77 | ~spl2_87),
% 0.21/0.54    inference(avatar_split_clause,[],[f806,f712,f649,f585,f347,f91,f847])).
% 0.21/0.54  fof(f91,plain,(
% 0.21/0.54    spl2_7 <=> sK1 = k4_relat_1(k4_relat_1(sK1))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.54  fof(f347,plain,(
% 0.21/0.54    spl2_47 <=> ! [X7] : k7_relat_1(k4_relat_1(sK1),X7) = k5_relat_1(k6_relat_1(X7),k4_relat_1(sK1))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_47])])).
% 0.21/0.54  fof(f649,plain,(
% 0.21/0.54    spl2_77 <=> ! [X3] : k1_relat_1(k4_relat_1(k7_relat_1(k4_relat_1(sK1),X3))) = k9_relat_1(k4_relat_1(sK1),X3)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_77])])).
% 0.21/0.54  fof(f712,plain,(
% 0.21/0.54    spl2_87 <=> ! [X3,X2] : (k4_relat_1(k5_relat_1(k6_relat_1(X3),X2)) = k5_relat_1(k4_relat_1(X2),k6_relat_1(X3)) | ~v1_relat_1(X2))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_87])])).
% 0.21/0.54  fof(f806,plain,(
% 0.21/0.54    ( ! [X3] : (k9_relat_1(k4_relat_1(sK1),X3) = k1_relat_1(k5_relat_1(sK1,k6_relat_1(X3)))) ) | (~spl2_7 | ~spl2_47 | ~spl2_75 | ~spl2_77 | ~spl2_87)),
% 0.21/0.54    inference(backward_demodulation,[],[f650,f804])).
% 0.21/0.54  fof(f804,plain,(
% 0.21/0.54    ( ! [X2] : (k4_relat_1(k7_relat_1(k4_relat_1(sK1),X2)) = k5_relat_1(sK1,k6_relat_1(X2))) ) | (~spl2_7 | ~spl2_47 | ~spl2_75 | ~spl2_87)),
% 0.21/0.54    inference(forward_demodulation,[],[f803,f348])).
% 0.21/0.54  fof(f348,plain,(
% 0.21/0.54    ( ! [X7] : (k7_relat_1(k4_relat_1(sK1),X7) = k5_relat_1(k6_relat_1(X7),k4_relat_1(sK1))) ) | ~spl2_47),
% 0.21/0.54    inference(avatar_component_clause,[],[f347])).
% 0.21/0.54  fof(f803,plain,(
% 0.21/0.54    ( ! [X2] : (k4_relat_1(k5_relat_1(k6_relat_1(X2),k4_relat_1(sK1))) = k5_relat_1(sK1,k6_relat_1(X2))) ) | (~spl2_7 | ~spl2_75 | ~spl2_87)),
% 0.21/0.54    inference(forward_demodulation,[],[f799,f93])).
% 0.21/0.54  fof(f93,plain,(
% 0.21/0.54    sK1 = k4_relat_1(k4_relat_1(sK1)) | ~spl2_7),
% 0.21/0.54    inference(avatar_component_clause,[],[f91])).
% 0.21/0.54  fof(f799,plain,(
% 0.21/0.54    ( ! [X2] : (k4_relat_1(k5_relat_1(k6_relat_1(X2),k4_relat_1(sK1))) = k5_relat_1(k4_relat_1(k4_relat_1(sK1)),k6_relat_1(X2))) ) | (~spl2_75 | ~spl2_87)),
% 0.21/0.54    inference(resolution,[],[f713,f587])).
% 0.21/0.54  fof(f713,plain,(
% 0.21/0.54    ( ! [X2,X3] : (~v1_relat_1(X2) | k4_relat_1(k5_relat_1(k6_relat_1(X3),X2)) = k5_relat_1(k4_relat_1(X2),k6_relat_1(X3))) ) | ~spl2_87),
% 0.21/0.54    inference(avatar_component_clause,[],[f712])).
% 0.21/0.54  fof(f650,plain,(
% 0.21/0.54    ( ! [X3] : (k1_relat_1(k4_relat_1(k7_relat_1(k4_relat_1(sK1),X3))) = k9_relat_1(k4_relat_1(sK1),X3)) ) | ~spl2_77),
% 0.21/0.54    inference(avatar_component_clause,[],[f649])).
% 0.21/0.54  fof(f845,plain,(
% 0.21/0.54    spl2_99 | ~spl2_7 | ~spl2_47 | ~spl2_75 | ~spl2_87),
% 0.21/0.54    inference(avatar_split_clause,[],[f804,f712,f585,f347,f91,f843])).
% 0.21/0.54  fof(f714,plain,(
% 0.21/0.54    spl2_87 | ~spl2_2 | ~spl2_4 | ~spl2_54),
% 0.21/0.54    inference(avatar_split_clause,[],[f539,f410,f73,f65,f712])).
% 0.21/0.54  fof(f73,plain,(
% 0.21/0.54    spl2_4 <=> ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.54  fof(f410,plain,(
% 0.21/0.54    spl2_54 <=> ! [X1,X0] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_54])])).
% 0.21/0.54  fof(f539,plain,(
% 0.21/0.54    ( ! [X2,X3] : (k4_relat_1(k5_relat_1(k6_relat_1(X3),X2)) = k5_relat_1(k4_relat_1(X2),k6_relat_1(X3)) | ~v1_relat_1(X2)) ) | (~spl2_2 | ~spl2_4 | ~spl2_54)),
% 0.21/0.54    inference(forward_demodulation,[],[f536,f74])).
% 0.21/0.54  fof(f74,plain,(
% 0.21/0.54    ( ! [X0] : (k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))) ) | ~spl2_4),
% 0.21/0.54    inference(avatar_component_clause,[],[f73])).
% 0.21/0.54  fof(f536,plain,(
% 0.21/0.54    ( ! [X2,X3] : (~v1_relat_1(X2) | k4_relat_1(k5_relat_1(k6_relat_1(X3),X2)) = k5_relat_1(k4_relat_1(X2),k4_relat_1(k6_relat_1(X3)))) ) | (~spl2_2 | ~spl2_54)),
% 0.21/0.54    inference(resolution,[],[f411,f66])).
% 0.21/0.54  fof(f411,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))) ) | ~spl2_54),
% 0.21/0.54    inference(avatar_component_clause,[],[f410])).
% 0.21/0.54  fof(f665,plain,(
% 0.21/0.54    ~spl2_79 | ~spl2_14 | spl2_24 | ~spl2_78),
% 0.21/0.54    inference(avatar_split_clause,[],[f660,f655,f192,f133,f662])).
% 0.21/0.54  fof(f133,plain,(
% 0.21/0.54    spl2_14 <=> ! [X1,X0] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.21/0.54  fof(f192,plain,(
% 0.21/0.54    spl2_24 <=> r1_tarski(k1_setfam_1(k1_enumset1(sK0,sK0,k1_relat_1(sK1))),k9_relat_1(k4_relat_1(sK1),k9_relat_1(sK1,sK0)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).
% 0.21/0.54  fof(f655,plain,(
% 0.21/0.54    spl2_78 <=> ! [X7] : k1_relat_1(k7_relat_1(sK1,X7)) = k1_setfam_1(k1_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),X7))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_78])])).
% 0.21/0.54  fof(f660,plain,(
% 0.21/0.54    ~r1_tarski(k1_relat_1(k7_relat_1(sK1,sK0)),k9_relat_1(k4_relat_1(sK1),k9_relat_1(sK1,sK0))) | (~spl2_14 | spl2_24 | ~spl2_78)),
% 0.21/0.54    inference(backward_demodulation,[],[f194,f658])).
% 0.21/0.54  fof(f658,plain,(
% 0.21/0.54    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k1_enumset1(X0,X0,k1_relat_1(sK1)))) ) | (~spl2_14 | ~spl2_78)),
% 0.21/0.54    inference(superposition,[],[f656,f134])).
% 0.21/0.54  fof(f134,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) ) | ~spl2_14),
% 0.21/0.54    inference(avatar_component_clause,[],[f133])).
% 0.21/0.54  fof(f656,plain,(
% 0.21/0.54    ( ! [X7] : (k1_relat_1(k7_relat_1(sK1,X7)) = k1_setfam_1(k1_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),X7))) ) | ~spl2_78),
% 0.21/0.54    inference(avatar_component_clause,[],[f655])).
% 0.21/0.54  fof(f194,plain,(
% 0.21/0.54    ~r1_tarski(k1_setfam_1(k1_enumset1(sK0,sK0,k1_relat_1(sK1))),k9_relat_1(k4_relat_1(sK1),k9_relat_1(sK1,sK0))) | spl2_24),
% 0.21/0.54    inference(avatar_component_clause,[],[f192])).
% 0.21/0.54  fof(f657,plain,(
% 0.21/0.54    spl2_78 | ~spl2_1 | ~spl2_65),
% 0.21/0.54    inference(avatar_split_clause,[],[f592,f504,f60,f655])).
% 0.21/0.54  fof(f504,plain,(
% 0.21/0.54    spl2_65 <=> ! [X1,X0] : (k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_65])])).
% 0.21/0.54  fof(f592,plain,(
% 0.21/0.54    ( ! [X7] : (k1_relat_1(k7_relat_1(sK1,X7)) = k1_setfam_1(k1_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),X7))) ) | (~spl2_1 | ~spl2_65)),
% 0.21/0.54    inference(resolution,[],[f505,f62])).
% 0.21/0.54  fof(f505,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X0))) ) | ~spl2_65),
% 0.21/0.54    inference(avatar_component_clause,[],[f504])).
% 0.21/0.54  fof(f651,plain,(
% 0.21/0.54    spl2_77 | ~spl2_37 | ~spl2_48 | ~spl2_75),
% 0.21/0.54    inference(avatar_split_clause,[],[f627,f585,f356,f282,f649])).
% 0.21/0.54  fof(f282,plain,(
% 0.21/0.54    spl2_37 <=> ! [X3,X2] : (k2_relat_1(k7_relat_1(X2,X3)) = k1_relat_1(k4_relat_1(k7_relat_1(X2,X3))) | ~v1_relat_1(X2))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_37])])).
% 0.21/0.54  fof(f356,plain,(
% 0.21/0.54    spl2_48 <=> ! [X7] : k2_relat_1(k7_relat_1(k4_relat_1(sK1),X7)) = k9_relat_1(k4_relat_1(sK1),X7)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_48])])).
% 0.21/0.54  fof(f627,plain,(
% 0.21/0.54    ( ! [X3] : (k1_relat_1(k4_relat_1(k7_relat_1(k4_relat_1(sK1),X3))) = k9_relat_1(k4_relat_1(sK1),X3)) ) | (~spl2_37 | ~spl2_48 | ~spl2_75)),
% 0.21/0.54    inference(forward_demodulation,[],[f605,f357])).
% 0.21/0.54  fof(f357,plain,(
% 0.21/0.54    ( ! [X7] : (k2_relat_1(k7_relat_1(k4_relat_1(sK1),X7)) = k9_relat_1(k4_relat_1(sK1),X7)) ) | ~spl2_48),
% 0.21/0.54    inference(avatar_component_clause,[],[f356])).
% 0.21/0.54  fof(f605,plain,(
% 0.21/0.54    ( ! [X3] : (k2_relat_1(k7_relat_1(k4_relat_1(sK1),X3)) = k1_relat_1(k4_relat_1(k7_relat_1(k4_relat_1(sK1),X3)))) ) | (~spl2_37 | ~spl2_75)),
% 0.21/0.54    inference(resolution,[],[f587,f283])).
% 0.21/0.54  fof(f283,plain,(
% 0.21/0.54    ( ! [X2,X3] : (~v1_relat_1(X2) | k2_relat_1(k7_relat_1(X2,X3)) = k1_relat_1(k4_relat_1(k7_relat_1(X2,X3)))) ) | ~spl2_37),
% 0.21/0.54    inference(avatar_component_clause,[],[f282])).
% 0.21/0.54  fof(f588,plain,(
% 0.21/0.54    spl2_75 | ~spl2_1 | ~spl2_15 | ~spl2_72 | ~spl2_74),
% 0.21/0.54    inference(avatar_split_clause,[],[f583,f578,f562,f141,f60,f585])).
% 0.21/0.54  fof(f141,plain,(
% 0.21/0.54    spl2_15 <=> sK1 = k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.21/0.54  fof(f562,plain,(
% 0.21/0.54    spl2_72 <=> k4_relat_1(sK1) = k7_relat_1(k4_relat_1(sK1),k2_relat_1(sK1))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_72])])).
% 0.21/0.54  fof(f578,plain,(
% 0.21/0.54    spl2_74 <=> ! [X0] : (v1_relat_1(k7_relat_1(k4_relat_1(sK1),X0)) | ~v1_relat_1(k5_relat_1(sK1,k6_relat_1(X0))))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_74])])).
% 0.21/0.54  fof(f583,plain,(
% 0.21/0.54    v1_relat_1(k4_relat_1(sK1)) | (~spl2_1 | ~spl2_15 | ~spl2_72 | ~spl2_74)),
% 0.21/0.54    inference(forward_demodulation,[],[f582,f564])).
% 0.21/0.54  fof(f564,plain,(
% 0.21/0.54    k4_relat_1(sK1) = k7_relat_1(k4_relat_1(sK1),k2_relat_1(sK1)) | ~spl2_72),
% 0.21/0.54    inference(avatar_component_clause,[],[f562])).
% 0.21/0.54  fof(f582,plain,(
% 0.21/0.54    v1_relat_1(k7_relat_1(k4_relat_1(sK1),k2_relat_1(sK1))) | (~spl2_1 | ~spl2_15 | ~spl2_74)),
% 0.21/0.54    inference(subsumption_resolution,[],[f581,f62])).
% 0.21/0.54  fof(f581,plain,(
% 0.21/0.54    ~v1_relat_1(sK1) | v1_relat_1(k7_relat_1(k4_relat_1(sK1),k2_relat_1(sK1))) | (~spl2_15 | ~spl2_74)),
% 0.21/0.54    inference(superposition,[],[f579,f143])).
% 0.21/0.54  fof(f143,plain,(
% 0.21/0.54    sK1 = k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1))) | ~spl2_15),
% 0.21/0.54    inference(avatar_component_clause,[],[f141])).
% 0.21/0.54  fof(f579,plain,(
% 0.21/0.54    ( ! [X0] : (~v1_relat_1(k5_relat_1(sK1,k6_relat_1(X0))) | v1_relat_1(k7_relat_1(k4_relat_1(sK1),X0))) ) | ~spl2_74),
% 0.21/0.54    inference(avatar_component_clause,[],[f578])).
% 0.21/0.54  fof(f580,plain,(
% 0.21/0.54    spl2_74 | ~spl2_3 | ~spl2_71),
% 0.21/0.54    inference(avatar_split_clause,[],[f560,f556,f69,f578])).
% 0.21/0.54  fof(f556,plain,(
% 0.21/0.54    spl2_71 <=> ! [X1] : k4_relat_1(k5_relat_1(sK1,k6_relat_1(X1))) = k7_relat_1(k4_relat_1(sK1),X1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_71])])).
% 0.21/0.54  fof(f560,plain,(
% 0.21/0.54    ( ! [X0] : (v1_relat_1(k7_relat_1(k4_relat_1(sK1),X0)) | ~v1_relat_1(k5_relat_1(sK1,k6_relat_1(X0)))) ) | (~spl2_3 | ~spl2_71)),
% 0.21/0.54    inference(superposition,[],[f70,f557])).
% 0.21/0.54  fof(f557,plain,(
% 0.21/0.54    ( ! [X1] : (k4_relat_1(k5_relat_1(sK1,k6_relat_1(X1))) = k7_relat_1(k4_relat_1(sK1),X1)) ) | ~spl2_71),
% 0.21/0.54    inference(avatar_component_clause,[],[f556])).
% 0.21/0.54  fof(f565,plain,(
% 0.21/0.54    spl2_72 | ~spl2_15 | ~spl2_71),
% 0.21/0.54    inference(avatar_split_clause,[],[f559,f556,f141,f562])).
% 0.21/0.54  fof(f559,plain,(
% 0.21/0.54    k4_relat_1(sK1) = k7_relat_1(k4_relat_1(sK1),k2_relat_1(sK1)) | (~spl2_15 | ~spl2_71)),
% 0.21/0.54    inference(superposition,[],[f557,f143])).
% 0.21/0.54  fof(f558,plain,(
% 0.21/0.54    spl2_71 | ~spl2_2 | ~spl2_4 | ~spl2_47 | ~spl2_69),
% 0.21/0.54    inference(avatar_split_clause,[],[f549,f541,f347,f73,f65,f556])).
% 0.21/0.54  fof(f541,plain,(
% 0.21/0.54    spl2_69 <=> ! [X7] : (~v1_relat_1(X7) | k4_relat_1(k5_relat_1(sK1,X7)) = k5_relat_1(k4_relat_1(X7),k4_relat_1(sK1)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_69])])).
% 0.21/0.54  fof(f549,plain,(
% 0.21/0.54    ( ! [X1] : (k4_relat_1(k5_relat_1(sK1,k6_relat_1(X1))) = k7_relat_1(k4_relat_1(sK1),X1)) ) | (~spl2_2 | ~spl2_4 | ~spl2_47 | ~spl2_69)),
% 0.21/0.54    inference(forward_demodulation,[],[f548,f348])).
% 0.21/0.54  fof(f548,plain,(
% 0.21/0.54    ( ! [X1] : (k4_relat_1(k5_relat_1(sK1,k6_relat_1(X1))) = k5_relat_1(k6_relat_1(X1),k4_relat_1(sK1))) ) | (~spl2_2 | ~spl2_4 | ~spl2_69)),
% 0.21/0.54    inference(forward_demodulation,[],[f545,f74])).
% 0.21/0.54  fof(f545,plain,(
% 0.21/0.54    ( ! [X1] : (k4_relat_1(k5_relat_1(sK1,k6_relat_1(X1))) = k5_relat_1(k4_relat_1(k6_relat_1(X1)),k4_relat_1(sK1))) ) | (~spl2_2 | ~spl2_69)),
% 0.21/0.54    inference(resolution,[],[f542,f66])).
% 0.21/0.54  fof(f542,plain,(
% 0.21/0.54    ( ! [X7] : (~v1_relat_1(X7) | k4_relat_1(k5_relat_1(sK1,X7)) = k5_relat_1(k4_relat_1(X7),k4_relat_1(sK1))) ) | ~spl2_69),
% 0.21/0.54    inference(avatar_component_clause,[],[f541])).
% 0.21/0.54  fof(f543,plain,(
% 0.21/0.54    spl2_69 | ~spl2_1 | ~spl2_54),
% 0.21/0.54    inference(avatar_split_clause,[],[f538,f410,f60,f541])).
% 0.21/0.54  fof(f538,plain,(
% 0.21/0.54    ( ! [X7] : (~v1_relat_1(X7) | k4_relat_1(k5_relat_1(sK1,X7)) = k5_relat_1(k4_relat_1(X7),k4_relat_1(sK1))) ) | (~spl2_1 | ~spl2_54)),
% 0.21/0.54    inference(resolution,[],[f411,f62])).
% 0.21/0.54  fof(f506,plain,(
% 0.21/0.54    spl2_65),
% 0.21/0.54    inference(avatar_split_clause,[],[f57,f504])).
% 0.21/0.54  fof(f57,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f52,f54])).
% 0.21/0.54  fof(f54,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 0.21/0.54    inference(definition_unfolding,[],[f48,f47])).
% 0.21/0.54  fof(f47,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.54  fof(f48,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.54  fof(f52,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f30])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f14])).
% 0.21/0.54  fof(f14,axiom,(
% 0.21/0.54    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).
% 0.21/0.54  fof(f412,plain,(
% 0.21/0.54    spl2_54),
% 0.21/0.54    inference(avatar_split_clause,[],[f43,f410])).
% 0.21/0.54  fof(f43,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f24])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f11])).
% 0.21/0.54  fof(f11,axiom,(
% 0.21/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relat_1)).
% 0.21/0.54  fof(f396,plain,(
% 0.21/0.54    spl2_52 | ~spl2_1 | ~spl2_45),
% 0.21/0.54    inference(avatar_split_clause,[],[f392,f327,f60,f394])).
% 0.21/0.54  fof(f327,plain,(
% 0.21/0.54    spl2_45 <=> ! [X1,X0,X2] : (r1_tarski(k5_relat_1(k7_relat_1(X1,X0),X2),k5_relat_1(X1,X2)) | ~v1_relat_1(X2) | ~v1_relat_1(X1))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_45])])).
% 0.21/0.54  fof(f392,plain,(
% 0.21/0.54    ( ! [X10,X11] : (~v1_relat_1(X10) | r1_tarski(k5_relat_1(k7_relat_1(sK1,X11),X10),k5_relat_1(sK1,X10))) ) | (~spl2_1 | ~spl2_45)),
% 0.21/0.54    inference(resolution,[],[f328,f62])).
% 0.21/0.54  fof(f328,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X2) | r1_tarski(k5_relat_1(k7_relat_1(X1,X0),X2),k5_relat_1(X1,X2))) ) | ~spl2_45),
% 0.21/0.54    inference(avatar_component_clause,[],[f327])).
% 0.21/0.54  fof(f358,plain,(
% 0.21/0.54    spl2_48 | ~spl2_1 | ~spl2_41),
% 0.21/0.54    inference(avatar_split_clause,[],[f353,f298,f60,f356])).
% 0.21/0.54  fof(f298,plain,(
% 0.21/0.54    spl2_41 <=> ! [X1,X0] : (k2_relat_1(k7_relat_1(k4_relat_1(X0),X1)) = k9_relat_1(k4_relat_1(X0),X1) | ~v1_relat_1(X0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_41])])).
% 0.21/0.54  fof(f353,plain,(
% 0.21/0.54    ( ! [X7] : (k2_relat_1(k7_relat_1(k4_relat_1(sK1),X7)) = k9_relat_1(k4_relat_1(sK1),X7)) ) | (~spl2_1 | ~spl2_41)),
% 0.21/0.54    inference(resolution,[],[f299,f62])).
% 0.21/0.54  fof(f299,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~v1_relat_1(X0) | k2_relat_1(k7_relat_1(k4_relat_1(X0),X1)) = k9_relat_1(k4_relat_1(X0),X1)) ) | ~spl2_41),
% 0.21/0.54    inference(avatar_component_clause,[],[f298])).
% 0.21/0.54  fof(f349,plain,(
% 0.21/0.54    spl2_47 | ~spl2_1 | ~spl2_40),
% 0.21/0.54    inference(avatar_split_clause,[],[f344,f294,f60,f347])).
% 0.21/0.54  fof(f294,plain,(
% 0.21/0.54    spl2_40 <=> ! [X1,X0] : (k7_relat_1(k4_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_40])])).
% 0.21/0.54  fof(f344,plain,(
% 0.21/0.54    ( ! [X7] : (k7_relat_1(k4_relat_1(sK1),X7) = k5_relat_1(k6_relat_1(X7),k4_relat_1(sK1))) ) | (~spl2_1 | ~spl2_40)),
% 0.21/0.54    inference(resolution,[],[f295,f62])).
% 0.21/0.54  fof(f295,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~v1_relat_1(X0) | k7_relat_1(k4_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X1),k4_relat_1(X0))) ) | ~spl2_40),
% 0.21/0.54    inference(avatar_component_clause,[],[f294])).
% 0.21/0.54  fof(f329,plain,(
% 0.21/0.54    spl2_45),
% 0.21/0.54    inference(avatar_split_clause,[],[f53,f327])).
% 0.21/0.54  fof(f53,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (r1_tarski(k5_relat_1(k7_relat_1(X1,X0),X2),k5_relat_1(X1,X2)) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f31])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ! [X0,X1] : (! [X2] : (r1_tarski(k5_relat_1(k7_relat_1(X1,X0),X2),k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f15])).
% 0.21/0.54  fof(f15,axiom,(
% 0.21/0.54    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => r1_tarski(k5_relat_1(k7_relat_1(X1,X0),X2),k5_relat_1(X1,X2))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_relat_1)).
% 0.21/0.54  fof(f300,plain,(
% 0.21/0.54    spl2_41 | ~spl2_3 | ~spl2_18),
% 0.21/0.54    inference(avatar_split_clause,[],[f171,f160,f69,f298])).
% 0.21/0.54  fof(f160,plain,(
% 0.21/0.54    spl2_18 <=> ! [X1,X0] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.21/0.54  fof(f171,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(k4_relat_1(X0),X1)) = k9_relat_1(k4_relat_1(X0),X1) | ~v1_relat_1(X0)) ) | (~spl2_3 | ~spl2_18)),
% 0.21/0.54    inference(resolution,[],[f161,f70])).
% 0.21/0.54  fof(f161,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) ) | ~spl2_18),
% 0.21/0.54    inference(avatar_component_clause,[],[f160])).
% 0.21/0.54  fof(f296,plain,(
% 0.21/0.54    spl2_40 | ~spl2_3 | ~spl2_17),
% 0.21/0.54    inference(avatar_split_clause,[],[f163,f156,f69,f294])).
% 0.21/0.54  fof(f156,plain,(
% 0.21/0.54    spl2_17 <=> ! [X1,X0] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.21/0.54  fof(f163,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k7_relat_1(k4_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X0)) ) | (~spl2_3 | ~spl2_17)),
% 0.21/0.54    inference(resolution,[],[f157,f70])).
% 0.21/0.54  fof(f157,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) ) | ~spl2_17),
% 0.21/0.54    inference(avatar_component_clause,[],[f156])).
% 0.21/0.54  fof(f284,plain,(
% 0.21/0.54    spl2_37 | ~spl2_5 | ~spl2_8),
% 0.21/0.54    inference(avatar_split_clause,[],[f106,f97,f77,f282])).
% 0.21/0.54  fof(f97,plain,(
% 0.21/0.54    spl2_8 <=> ! [X0] : (k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.54  fof(f106,plain,(
% 0.21/0.54    ( ! [X2,X3] : (k2_relat_1(k7_relat_1(X2,X3)) = k1_relat_1(k4_relat_1(k7_relat_1(X2,X3))) | ~v1_relat_1(X2)) ) | (~spl2_5 | ~spl2_8)),
% 0.21/0.54    inference(resolution,[],[f98,f78])).
% 0.21/0.54  fof(f98,plain,(
% 0.21/0.54    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) ) | ~spl2_8),
% 0.21/0.54    inference(avatar_component_clause,[],[f97])).
% 0.21/0.54  fof(f259,plain,(
% 0.21/0.54    spl2_34),
% 0.21/0.54    inference(avatar_split_clause,[],[f44,f257])).
% 0.21/0.54  fof(f44,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f26])).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(flattening,[],[f25])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f9])).
% 0.21/0.54  fof(f9,axiom,(
% 0.21/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).
% 0.21/0.54  fof(f195,plain,(
% 0.21/0.54    ~spl2_24),
% 0.21/0.54    inference(avatar_split_clause,[],[f58,f192])).
% 0.21/0.54  fof(f58,plain,(
% 0.21/0.54    ~r1_tarski(k1_setfam_1(k1_enumset1(sK0,sK0,k1_relat_1(sK1))),k9_relat_1(k4_relat_1(sK1),k9_relat_1(sK1,sK0)))),
% 0.21/0.54    inference(backward_demodulation,[],[f55,f56])).
% 0.21/0.54  fof(f56,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f46,f47,f47])).
% 0.21/0.54  fof(f46,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.21/0.54  fof(f55,plain,(
% 0.21/0.54    ~r1_tarski(k1_setfam_1(k1_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),sK0)),k9_relat_1(k4_relat_1(sK1),k9_relat_1(sK1,sK0)))),
% 0.21/0.54    inference(definition_unfolding,[],[f35,f54])).
% 0.21/0.54  fof(f35,plain,(
% 0.21/0.54    ~r1_tarski(k3_xboole_0(k1_relat_1(sK1),sK0),k9_relat_1(k4_relat_1(sK1),k9_relat_1(sK1,sK0)))),
% 0.21/0.54    inference(cnf_transformation,[],[f33])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    ~r1_tarski(k3_xboole_0(k1_relat_1(sK1),sK0),k9_relat_1(k4_relat_1(sK1),k9_relat_1(sK1,sK0))) & v1_relat_1(sK1)),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f32])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    ? [X0,X1] : (~r1_tarski(k3_xboole_0(k1_relat_1(X1),X0),k9_relat_1(k4_relat_1(X1),k9_relat_1(X1,X0))) & v1_relat_1(X1)) => (~r1_tarski(k3_xboole_0(k1_relat_1(sK1),sK0),k9_relat_1(k4_relat_1(sK1),k9_relat_1(sK1,sK0))) & v1_relat_1(sK1))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    ? [X0,X1] : (~r1_tarski(k3_xboole_0(k1_relat_1(X1),X0),k9_relat_1(k4_relat_1(X1),k9_relat_1(X1,X0))) & v1_relat_1(X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f18])).
% 0.21/0.54  fof(f18,negated_conjecture,(
% 0.21/0.54    ~! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k3_xboole_0(k1_relat_1(X1),X0),k9_relat_1(k4_relat_1(X1),k9_relat_1(X1,X0))))),
% 0.21/0.54    inference(negated_conjecture,[],[f17])).
% 0.21/0.54  fof(f17,conjecture,(
% 0.21/0.54    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k3_xboole_0(k1_relat_1(X1),X0),k9_relat_1(k4_relat_1(X1),k9_relat_1(X1,X0))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_relat_1)).
% 0.21/0.54  fof(f178,plain,(
% 0.21/0.54    spl2_20 | ~spl2_1 | ~spl2_18),
% 0.21/0.54    inference(avatar_split_clause,[],[f174,f160,f60,f176])).
% 0.21/0.54  fof(f174,plain,(
% 0.21/0.54    ( ! [X7] : (k2_relat_1(k7_relat_1(sK1,X7)) = k9_relat_1(sK1,X7)) ) | (~spl2_1 | ~spl2_18)),
% 0.21/0.54    inference(resolution,[],[f161,f62])).
% 0.21/0.54  fof(f162,plain,(
% 0.21/0.54    spl2_18),
% 0.21/0.54    inference(avatar_split_clause,[],[f51,f160])).
% 0.21/0.54  fof(f51,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f29])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,axiom,(
% 0.21/0.54    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.21/0.54  fof(f158,plain,(
% 0.21/0.54    spl2_17),
% 0.21/0.54    inference(avatar_split_clause,[],[f50,f156])).
% 0.21/0.54  fof(f50,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f28])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f16])).
% 0.21/0.54  fof(f16,axiom,(
% 0.21/0.54    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 0.21/0.54  fof(f144,plain,(
% 0.21/0.54    spl2_15 | ~spl2_1 | ~spl2_12),
% 0.21/0.54    inference(avatar_split_clause,[],[f139,f124,f60,f141])).
% 0.21/0.54  fof(f139,plain,(
% 0.21/0.54    sK1 = k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1))) | (~spl2_1 | ~spl2_12)),
% 0.21/0.54    inference(resolution,[],[f125,f62])).
% 0.21/0.54  fof(f135,plain,(
% 0.21/0.54    spl2_14),
% 0.21/0.54    inference(avatar_split_clause,[],[f56,f133])).
% 0.21/0.54  fof(f126,plain,(
% 0.21/0.54    spl2_12),
% 0.21/0.54    inference(avatar_split_clause,[],[f40,f124])).
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f22])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f13])).
% 0.21/0.54  fof(f13,axiom,(
% 0.21/0.54    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).
% 0.21/0.54  fof(f99,plain,(
% 0.21/0.54    spl2_8),
% 0.21/0.54    inference(avatar_split_clause,[],[f41,f97])).
% 0.21/0.54  fof(f41,plain,(
% 0.21/0.54    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f23])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f10])).
% 0.21/0.54  fof(f10,axiom,(
% 0.21/0.54    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).
% 0.21/0.54  fof(f94,plain,(
% 0.21/0.54    spl2_7 | ~spl2_1 | ~spl2_6),
% 0.21/0.54    inference(avatar_split_clause,[],[f88,f82,f60,f91])).
% 0.21/0.54  fof(f82,plain,(
% 0.21/0.54    spl2_6 <=> ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.54  fof(f88,plain,(
% 0.21/0.54    sK1 = k4_relat_1(k4_relat_1(sK1)) | (~spl2_1 | ~spl2_6)),
% 0.21/0.54    inference(resolution,[],[f83,f62])).
% 0.21/0.54  fof(f83,plain,(
% 0.21/0.54    ( ! [X0] : (~v1_relat_1(X0) | k4_relat_1(k4_relat_1(X0)) = X0) ) | ~spl2_6),
% 0.21/0.54    inference(avatar_component_clause,[],[f82])).
% 0.21/0.54  fof(f84,plain,(
% 0.21/0.54    spl2_6),
% 0.21/0.54    inference(avatar_split_clause,[],[f39,f82])).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    ( ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f21])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,axiom,(
% 0.21/0.54    ! [X0] : (v1_relat_1(X0) => k4_relat_1(k4_relat_1(X0)) = X0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).
% 0.21/0.54  fof(f79,plain,(
% 0.21/0.54    spl2_5),
% 0.21/0.54    inference(avatar_split_clause,[],[f49,f77])).
% 0.21/0.54  fof(f49,plain,(
% 0.21/0.54    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f27])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.21/0.54  fof(f75,plain,(
% 0.21/0.54    spl2_4),
% 0.21/0.54    inference(avatar_split_clause,[],[f37,f73])).
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    ( ! [X0] : (k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f12])).
% 0.21/0.54  fof(f12,axiom,(
% 0.21/0.54    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_relat_1)).
% 0.21/0.54  fof(f71,plain,(
% 0.21/0.54    spl2_3),
% 0.21/0.54    inference(avatar_split_clause,[],[f38,f69])).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f20])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 0.21/0.54  fof(f67,plain,(
% 0.21/0.54    spl2_2),
% 0.21/0.54    inference(avatar_split_clause,[],[f36,f65])).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.21/0.54  fof(f63,plain,(
% 0.21/0.54    spl2_1),
% 0.21/0.54    inference(avatar_split_clause,[],[f34,f60])).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    v1_relat_1(sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f33])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (24320)------------------------------
% 0.21/0.54  % (24320)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (24320)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (24320)Memory used [KB]: 7675
% 0.21/0.54  % (24320)Time elapsed: 0.070 s
% 0.21/0.54  % (24320)------------------------------
% 0.21/0.54  % (24320)------------------------------
% 0.21/0.54  % (24312)Success in time 0.184 s
%------------------------------------------------------------------------------
