%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:02 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  224 ( 418 expanded)
%              Number of leaves         :   59 ( 209 expanded)
%              Depth                    :    8
%              Number of atoms          :  619 (1083 expanded)
%              Number of equality atoms :  111 ( 211 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2063,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f60,f64,f68,f72,f76,f81,f91,f96,f123,f137,f151,f155,f171,f196,f226,f256,f281,f293,f297,f326,f346,f355,f393,f409,f503,f540,f555,f562,f577,f585,f648,f654,f669,f721,f852,f856,f864,f944,f1776,f2013,f2023,f2043,f2059])).

fof(f2059,plain,
    ( ~ spl2_1
    | ~ spl2_5
    | spl2_79
    | ~ spl2_199 ),
    inference(avatar_contradiction_clause,[],[f2058])).

fof(f2058,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_5
    | spl2_79
    | ~ spl2_199 ),
    inference(subsumption_resolution,[],[f668,f2057])).

fof(f2057,plain,
    ( ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k9_relat_1(k4_relat_1(sK1),k9_relat_1(sK1,X0)))
    | ~ spl2_1
    | ~ spl2_5
    | ~ spl2_199 ),
    inference(subsumption_resolution,[],[f2055,f59])).

fof(f59,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl2_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f2055,plain,
    ( ! [X0] :
        ( r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k9_relat_1(k4_relat_1(sK1),k9_relat_1(sK1,X0)))
        | ~ v1_relat_1(sK1) )
    | ~ spl2_5
    | ~ spl2_199 ),
    inference(resolution,[],[f2042,f75])).

fof(f75,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(k7_relat_1(X0,X1))
        | ~ v1_relat_1(X0) )
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl2_5
  <=> ! [X1,X0] :
        ( v1_relat_1(k7_relat_1(X0,X1))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f2042,plain,
    ( ! [X1] :
        ( ~ v1_relat_1(k7_relat_1(sK1,X1))
        | r1_tarski(k1_relat_1(k7_relat_1(sK1,X1)),k9_relat_1(k4_relat_1(sK1),k9_relat_1(sK1,X1))) )
    | ~ spl2_199 ),
    inference(avatar_component_clause,[],[f2041])).

fof(f2041,plain,
    ( spl2_199
  <=> ! [X1] :
        ( r1_tarski(k1_relat_1(k7_relat_1(sK1,X1)),k9_relat_1(k4_relat_1(sK1),k9_relat_1(sK1,X1)))
        | ~ v1_relat_1(k7_relat_1(sK1,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_199])])).

fof(f668,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK1,sK0)),k9_relat_1(k4_relat_1(sK1),k9_relat_1(sK1,sK0)))
    | spl2_79 ),
    inference(avatar_component_clause,[],[f666])).

fof(f666,plain,
    ( spl2_79
  <=> r1_tarski(k1_relat_1(k7_relat_1(sK1,sK0)),k9_relat_1(k4_relat_1(sK1),k9_relat_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_79])])).

fof(f2043,plain,
    ( spl2_199
    | ~ spl2_34
    | ~ spl2_100
    | ~ spl2_103
    | ~ spl2_197 ),
    inference(avatar_split_clause,[],[f2031,f2021,f942,f854,f254,f2041])).

fof(f254,plain,
    ( spl2_34
  <=> ! [X1,X0] :
        ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).

fof(f854,plain,
    ( spl2_100
  <=> ! [X3] : k9_relat_1(k4_relat_1(sK1),X3) = k1_relat_1(k5_relat_1(sK1,k6_relat_1(X3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_100])])).

fof(f942,plain,
    ( spl2_103
  <=> ! [X0] : v1_relat_1(k5_relat_1(sK1,k6_relat_1(X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_103])])).

fof(f2021,plain,
    ( spl2_197
  <=> ! [X0] : r1_tarski(k7_relat_1(sK1,X0),k5_relat_1(sK1,k6_relat_1(k9_relat_1(sK1,X0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_197])])).

fof(f2031,plain,
    ( ! [X1] :
        ( r1_tarski(k1_relat_1(k7_relat_1(sK1,X1)),k9_relat_1(k4_relat_1(sK1),k9_relat_1(sK1,X1)))
        | ~ v1_relat_1(k7_relat_1(sK1,X1)) )
    | ~ spl2_34
    | ~ spl2_100
    | ~ spl2_103
    | ~ spl2_197 ),
    inference(forward_demodulation,[],[f2030,f855])).

fof(f855,plain,
    ( ! [X3] : k9_relat_1(k4_relat_1(sK1),X3) = k1_relat_1(k5_relat_1(sK1,k6_relat_1(X3)))
    | ~ spl2_100 ),
    inference(avatar_component_clause,[],[f854])).

fof(f2030,plain,
    ( ! [X1] :
        ( r1_tarski(k1_relat_1(k7_relat_1(sK1,X1)),k1_relat_1(k5_relat_1(sK1,k6_relat_1(k9_relat_1(sK1,X1)))))
        | ~ v1_relat_1(k7_relat_1(sK1,X1)) )
    | ~ spl2_34
    | ~ spl2_103
    | ~ spl2_197 ),
    inference(subsumption_resolution,[],[f2025,f943])).

fof(f943,plain,
    ( ! [X0] : v1_relat_1(k5_relat_1(sK1,k6_relat_1(X0)))
    | ~ spl2_103 ),
    inference(avatar_component_clause,[],[f942])).

fof(f2025,plain,
    ( ! [X1] :
        ( r1_tarski(k1_relat_1(k7_relat_1(sK1,X1)),k1_relat_1(k5_relat_1(sK1,k6_relat_1(k9_relat_1(sK1,X1)))))
        | ~ v1_relat_1(k5_relat_1(sK1,k6_relat_1(k9_relat_1(sK1,X1))))
        | ~ v1_relat_1(k7_relat_1(sK1,X1)) )
    | ~ spl2_34
    | ~ spl2_197 ),
    inference(resolution,[],[f2022,f255])).

fof(f255,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl2_34 ),
    inference(avatar_component_clause,[],[f254])).

fof(f2022,plain,
    ( ! [X0] : r1_tarski(k7_relat_1(sK1,X0),k5_relat_1(sK1,k6_relat_1(k9_relat_1(sK1,X0))))
    | ~ spl2_197 ),
    inference(avatar_component_clause,[],[f2021])).

fof(f2023,plain,
    ( spl2_197
    | ~ spl2_2
    | ~ spl2_52
    | ~ spl2_196 ),
    inference(avatar_split_clause,[],[f2019,f2011,f391,f62,f2021])).

fof(f62,plain,
    ( spl2_2
  <=> ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f391,plain,
    ( spl2_52
  <=> ! [X11,X10] :
        ( ~ v1_relat_1(X10)
        | r1_tarski(k5_relat_1(k7_relat_1(sK1,X11),X10),k5_relat_1(sK1,X10)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_52])])).

fof(f2011,plain,
    ( spl2_196
  <=> ! [X15] : k7_relat_1(sK1,X15) = k5_relat_1(k7_relat_1(sK1,X15),k6_relat_1(k9_relat_1(sK1,X15))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_196])])).

fof(f2019,plain,
    ( ! [X0] : r1_tarski(k7_relat_1(sK1,X0),k5_relat_1(sK1,k6_relat_1(k9_relat_1(sK1,X0))))
    | ~ spl2_2
    | ~ spl2_52
    | ~ spl2_196 ),
    inference(subsumption_resolution,[],[f2016,f63])).

fof(f63,plain,
    ( ! [X0] : v1_relat_1(k6_relat_1(X0))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f2016,plain,
    ( ! [X0] :
        ( r1_tarski(k7_relat_1(sK1,X0),k5_relat_1(sK1,k6_relat_1(k9_relat_1(sK1,X0))))
        | ~ v1_relat_1(k6_relat_1(k9_relat_1(sK1,X0))) )
    | ~ spl2_52
    | ~ spl2_196 ),
    inference(superposition,[],[f392,f2012])).

fof(f2012,plain,
    ( ! [X15] : k7_relat_1(sK1,X15) = k5_relat_1(k7_relat_1(sK1,X15),k6_relat_1(k9_relat_1(sK1,X15)))
    | ~ spl2_196 ),
    inference(avatar_component_clause,[],[f2011])).

fof(f392,plain,
    ( ! [X10,X11] :
        ( r1_tarski(k5_relat_1(k7_relat_1(sK1,X11),X10),k5_relat_1(sK1,X10))
        | ~ v1_relat_1(X10) )
    | ~ spl2_52 ),
    inference(avatar_component_clause,[],[f391])).

fof(f2013,plain,
    ( spl2_196
    | ~ spl2_1
    | ~ spl2_19
    | ~ spl2_174 ),
    inference(avatar_split_clause,[],[f2009,f1774,f169,f57,f2011])).

fof(f169,plain,
    ( spl2_19
  <=> ! [X7] : k2_relat_1(k7_relat_1(sK1,X7)) = k9_relat_1(sK1,X7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f1774,plain,
    ( spl2_174
  <=> ! [X3,X2] :
        ( k7_relat_1(X2,X3) = k5_relat_1(k7_relat_1(X2,X3),k6_relat_1(k2_relat_1(k7_relat_1(X2,X3))))
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_174])])).

fof(f2009,plain,
    ( ! [X15] : k7_relat_1(sK1,X15) = k5_relat_1(k7_relat_1(sK1,X15),k6_relat_1(k9_relat_1(sK1,X15)))
    | ~ spl2_1
    | ~ spl2_19
    | ~ spl2_174 ),
    inference(forward_demodulation,[],[f2003,f170])).

fof(f170,plain,
    ( ! [X7] : k2_relat_1(k7_relat_1(sK1,X7)) = k9_relat_1(sK1,X7)
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f169])).

fof(f2003,plain,
    ( ! [X15] : k7_relat_1(sK1,X15) = k5_relat_1(k7_relat_1(sK1,X15),k6_relat_1(k2_relat_1(k7_relat_1(sK1,X15))))
    | ~ spl2_1
    | ~ spl2_174 ),
    inference(resolution,[],[f1775,f59])).

fof(f1775,plain,
    ( ! [X2,X3] :
        ( ~ v1_relat_1(X2)
        | k7_relat_1(X2,X3) = k5_relat_1(k7_relat_1(X2,X3),k6_relat_1(k2_relat_1(k7_relat_1(X2,X3)))) )
    | ~ spl2_174 ),
    inference(avatar_component_clause,[],[f1774])).

fof(f1776,plain,
    ( spl2_174
    | ~ spl2_5
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f131,f121,f74,f1774])).

fof(f121,plain,
    ( spl2_12
  <=> ! [X0] :
        ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f131,plain,
    ( ! [X2,X3] :
        ( k7_relat_1(X2,X3) = k5_relat_1(k7_relat_1(X2,X3),k6_relat_1(k2_relat_1(k7_relat_1(X2,X3))))
        | ~ v1_relat_1(X2) )
    | ~ spl2_5
    | ~ spl2_12 ),
    inference(resolution,[],[f122,f75])).

fof(f122,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 )
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f121])).

fof(f944,plain,
    ( spl2_103
    | ~ spl2_5
    | ~ spl2_75
    | ~ spl2_101 ),
    inference(avatar_split_clause,[],[f867,f862,f582,f74,f942])).

fof(f582,plain,
    ( spl2_75
  <=> v1_relat_1(k4_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_75])])).

fof(f862,plain,
    ( spl2_101
  <=> ! [X0] :
        ( v1_relat_1(k5_relat_1(sK1,k6_relat_1(X0)))
        | ~ v1_relat_1(k7_relat_1(k4_relat_1(sK1),X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_101])])).

fof(f867,plain,
    ( ! [X0] : v1_relat_1(k5_relat_1(sK1,k6_relat_1(X0)))
    | ~ spl2_5
    | ~ spl2_75
    | ~ spl2_101 ),
    inference(subsumption_resolution,[],[f865,f584])).

fof(f584,plain,
    ( v1_relat_1(k4_relat_1(sK1))
    | ~ spl2_75 ),
    inference(avatar_component_clause,[],[f582])).

fof(f865,plain,
    ( ! [X0] :
        ( v1_relat_1(k5_relat_1(sK1,k6_relat_1(X0)))
        | ~ v1_relat_1(k4_relat_1(sK1)) )
    | ~ spl2_5
    | ~ spl2_101 ),
    inference(resolution,[],[f863,f75])).

fof(f863,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(k7_relat_1(k4_relat_1(sK1),X0))
        | v1_relat_1(k5_relat_1(sK1,k6_relat_1(X0))) )
    | ~ spl2_101 ),
    inference(avatar_component_clause,[],[f862])).

fof(f864,plain,
    ( spl2_101
    | ~ spl2_3
    | ~ spl2_99 ),
    inference(avatar_split_clause,[],[f858,f850,f66,f862])).

fof(f66,plain,
    ( spl2_3
  <=> ! [X0] :
        ( v1_relat_1(k4_relat_1(X0))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f850,plain,
    ( spl2_99
  <=> ! [X2] : k4_relat_1(k7_relat_1(k4_relat_1(sK1),X2)) = k5_relat_1(sK1,k6_relat_1(X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_99])])).

fof(f858,plain,
    ( ! [X0] :
        ( v1_relat_1(k5_relat_1(sK1,k6_relat_1(X0)))
        | ~ v1_relat_1(k7_relat_1(k4_relat_1(sK1),X0)) )
    | ~ spl2_3
    | ~ spl2_99 ),
    inference(superposition,[],[f67,f851])).

fof(f851,plain,
    ( ! [X2] : k4_relat_1(k7_relat_1(k4_relat_1(sK1),X2)) = k5_relat_1(sK1,k6_relat_1(X2))
    | ~ spl2_99 ),
    inference(avatar_component_clause,[],[f850])).

fof(f67,plain,
    ( ! [X0] :
        ( v1_relat_1(k4_relat_1(X0))
        | ~ v1_relat_1(X0) )
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f66])).

fof(f856,plain,
    ( spl2_100
    | ~ spl2_7
    | ~ spl2_47
    | ~ spl2_75
    | ~ spl2_77
    | ~ spl2_87 ),
    inference(avatar_split_clause,[],[f813,f719,f646,f582,f344,f88,f854])).

fof(f88,plain,
    ( spl2_7
  <=> sK1 = k4_relat_1(k4_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f344,plain,
    ( spl2_47
  <=> ! [X7] : k7_relat_1(k4_relat_1(sK1),X7) = k5_relat_1(k6_relat_1(X7),k4_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_47])])).

fof(f646,plain,
    ( spl2_77
  <=> ! [X3] : k1_relat_1(k4_relat_1(k7_relat_1(k4_relat_1(sK1),X3))) = k9_relat_1(k4_relat_1(sK1),X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_77])])).

fof(f719,plain,
    ( spl2_87
  <=> ! [X3,X2] :
        ( k4_relat_1(k5_relat_1(k6_relat_1(X3),X2)) = k5_relat_1(k4_relat_1(X2),k6_relat_1(X3))
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_87])])).

fof(f813,plain,
    ( ! [X3] : k9_relat_1(k4_relat_1(sK1),X3) = k1_relat_1(k5_relat_1(sK1,k6_relat_1(X3)))
    | ~ spl2_7
    | ~ spl2_47
    | ~ spl2_75
    | ~ spl2_77
    | ~ spl2_87 ),
    inference(backward_demodulation,[],[f647,f811])).

fof(f811,plain,
    ( ! [X2] : k4_relat_1(k7_relat_1(k4_relat_1(sK1),X2)) = k5_relat_1(sK1,k6_relat_1(X2))
    | ~ spl2_7
    | ~ spl2_47
    | ~ spl2_75
    | ~ spl2_87 ),
    inference(forward_demodulation,[],[f810,f345])).

fof(f345,plain,
    ( ! [X7] : k7_relat_1(k4_relat_1(sK1),X7) = k5_relat_1(k6_relat_1(X7),k4_relat_1(sK1))
    | ~ spl2_47 ),
    inference(avatar_component_clause,[],[f344])).

fof(f810,plain,
    ( ! [X2] : k4_relat_1(k5_relat_1(k6_relat_1(X2),k4_relat_1(sK1))) = k5_relat_1(sK1,k6_relat_1(X2))
    | ~ spl2_7
    | ~ spl2_75
    | ~ spl2_87 ),
    inference(forward_demodulation,[],[f806,f90])).

fof(f90,plain,
    ( sK1 = k4_relat_1(k4_relat_1(sK1))
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f88])).

fof(f806,plain,
    ( ! [X2] : k4_relat_1(k5_relat_1(k6_relat_1(X2),k4_relat_1(sK1))) = k5_relat_1(k4_relat_1(k4_relat_1(sK1)),k6_relat_1(X2))
    | ~ spl2_75
    | ~ spl2_87 ),
    inference(resolution,[],[f720,f584])).

fof(f720,plain,
    ( ! [X2,X3] :
        ( ~ v1_relat_1(X2)
        | k4_relat_1(k5_relat_1(k6_relat_1(X3),X2)) = k5_relat_1(k4_relat_1(X2),k6_relat_1(X3)) )
    | ~ spl2_87 ),
    inference(avatar_component_clause,[],[f719])).

fof(f647,plain,
    ( ! [X3] : k1_relat_1(k4_relat_1(k7_relat_1(k4_relat_1(sK1),X3))) = k9_relat_1(k4_relat_1(sK1),X3)
    | ~ spl2_77 ),
    inference(avatar_component_clause,[],[f646])).

fof(f852,plain,
    ( spl2_99
    | ~ spl2_7
    | ~ spl2_47
    | ~ spl2_75
    | ~ spl2_87 ),
    inference(avatar_split_clause,[],[f811,f719,f582,f344,f88,f850])).

fof(f721,plain,
    ( spl2_87
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_54 ),
    inference(avatar_split_clause,[],[f536,f407,f70,f62,f719])).

fof(f70,plain,
    ( spl2_4
  <=> ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f407,plain,
    ( spl2_54
  <=> ! [X1,X0] :
        ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_54])])).

fof(f536,plain,
    ( ! [X2,X3] :
        ( k4_relat_1(k5_relat_1(k6_relat_1(X3),X2)) = k5_relat_1(k4_relat_1(X2),k6_relat_1(X3))
        | ~ v1_relat_1(X2) )
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_54 ),
    inference(forward_demodulation,[],[f533,f71])).

fof(f71,plain,
    ( ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f70])).

fof(f533,plain,
    ( ! [X2,X3] :
        ( ~ v1_relat_1(X2)
        | k4_relat_1(k5_relat_1(k6_relat_1(X3),X2)) = k5_relat_1(k4_relat_1(X2),k4_relat_1(k6_relat_1(X3))) )
    | ~ spl2_2
    | ~ spl2_54 ),
    inference(resolution,[],[f408,f63])).

fof(f408,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) )
    | ~ spl2_54 ),
    inference(avatar_component_clause,[],[f407])).

fof(f669,plain,
    ( ~ spl2_79
    | spl2_25
    | ~ spl2_28
    | ~ spl2_78 ),
    inference(avatar_split_clause,[],[f664,f652,f224,f193,f666])).

fof(f193,plain,
    ( spl2_25
  <=> r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,k1_relat_1(sK1))),k9_relat_1(k4_relat_1(sK1),k9_relat_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).

fof(f224,plain,
    ( spl2_28
  <=> ! [X1,X0] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).

fof(f652,plain,
    ( spl2_78
  <=> ! [X7] : k1_relat_1(k7_relat_1(sK1,X7)) = k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),X7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_78])])).

fof(f664,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK1,sK0)),k9_relat_1(k4_relat_1(sK1),k9_relat_1(sK1,sK0)))
    | spl2_25
    | ~ spl2_28
    | ~ spl2_78 ),
    inference(backward_demodulation,[],[f195,f658])).

fof(f658,plain,
    ( ! [X1] : k1_relat_1(k7_relat_1(sK1,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,k1_relat_1(sK1)))
    | ~ spl2_28
    | ~ spl2_78 ),
    inference(superposition,[],[f653,f225])).

fof(f225,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))
    | ~ spl2_28 ),
    inference(avatar_component_clause,[],[f224])).

fof(f653,plain,
    ( ! [X7] : k1_relat_1(k7_relat_1(sK1,X7)) = k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),X7))
    | ~ spl2_78 ),
    inference(avatar_component_clause,[],[f652])).

fof(f195,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,k1_relat_1(sK1))),k9_relat_1(k4_relat_1(sK1),k9_relat_1(sK1,sK0)))
    | spl2_25 ),
    inference(avatar_component_clause,[],[f193])).

fof(f654,plain,
    ( spl2_78
    | ~ spl2_1
    | ~ spl2_65 ),
    inference(avatar_split_clause,[],[f589,f501,f57,f652])).

fof(f501,plain,
    ( spl2_65
  <=> ! [X1,X0] :
        ( k1_relat_1(k7_relat_1(X1,X0)) = k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X0))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_65])])).

fof(f589,plain,
    ( ! [X7] : k1_relat_1(k7_relat_1(sK1,X7)) = k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),X7))
    | ~ spl2_1
    | ~ spl2_65 ),
    inference(resolution,[],[f502,f59])).

fof(f502,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k1_relat_1(k7_relat_1(X1,X0)) = k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X0)) )
    | ~ spl2_65 ),
    inference(avatar_component_clause,[],[f501])).

fof(f648,plain,
    ( spl2_77
    | ~ spl2_37
    | ~ spl2_48
    | ~ spl2_75 ),
    inference(avatar_split_clause,[],[f624,f582,f353,f279,f646])).

fof(f279,plain,
    ( spl2_37
  <=> ! [X3,X2] :
        ( k2_relat_1(k7_relat_1(X2,X3)) = k1_relat_1(k4_relat_1(k7_relat_1(X2,X3)))
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_37])])).

fof(f353,plain,
    ( spl2_48
  <=> ! [X7] : k2_relat_1(k7_relat_1(k4_relat_1(sK1),X7)) = k9_relat_1(k4_relat_1(sK1),X7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_48])])).

fof(f624,plain,
    ( ! [X3] : k1_relat_1(k4_relat_1(k7_relat_1(k4_relat_1(sK1),X3))) = k9_relat_1(k4_relat_1(sK1),X3)
    | ~ spl2_37
    | ~ spl2_48
    | ~ spl2_75 ),
    inference(forward_demodulation,[],[f602,f354])).

fof(f354,plain,
    ( ! [X7] : k2_relat_1(k7_relat_1(k4_relat_1(sK1),X7)) = k9_relat_1(k4_relat_1(sK1),X7)
    | ~ spl2_48 ),
    inference(avatar_component_clause,[],[f353])).

fof(f602,plain,
    ( ! [X3] : k2_relat_1(k7_relat_1(k4_relat_1(sK1),X3)) = k1_relat_1(k4_relat_1(k7_relat_1(k4_relat_1(sK1),X3)))
    | ~ spl2_37
    | ~ spl2_75 ),
    inference(resolution,[],[f584,f280])).

fof(f280,plain,
    ( ! [X2,X3] :
        ( ~ v1_relat_1(X2)
        | k2_relat_1(k7_relat_1(X2,X3)) = k1_relat_1(k4_relat_1(k7_relat_1(X2,X3))) )
    | ~ spl2_37 ),
    inference(avatar_component_clause,[],[f279])).

fof(f585,plain,
    ( spl2_75
    | ~ spl2_1
    | ~ spl2_14
    | ~ spl2_72
    | ~ spl2_74 ),
    inference(avatar_split_clause,[],[f580,f575,f559,f134,f57,f582])).

fof(f134,plain,
    ( spl2_14
  <=> sK1 = k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f559,plain,
    ( spl2_72
  <=> k4_relat_1(sK1) = k7_relat_1(k4_relat_1(sK1),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_72])])).

fof(f575,plain,
    ( spl2_74
  <=> ! [X0] :
        ( v1_relat_1(k7_relat_1(k4_relat_1(sK1),X0))
        | ~ v1_relat_1(k5_relat_1(sK1,k6_relat_1(X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_74])])).

fof(f580,plain,
    ( v1_relat_1(k4_relat_1(sK1))
    | ~ spl2_1
    | ~ spl2_14
    | ~ spl2_72
    | ~ spl2_74 ),
    inference(forward_demodulation,[],[f579,f561])).

fof(f561,plain,
    ( k4_relat_1(sK1) = k7_relat_1(k4_relat_1(sK1),k2_relat_1(sK1))
    | ~ spl2_72 ),
    inference(avatar_component_clause,[],[f559])).

fof(f579,plain,
    ( v1_relat_1(k7_relat_1(k4_relat_1(sK1),k2_relat_1(sK1)))
    | ~ spl2_1
    | ~ spl2_14
    | ~ spl2_74 ),
    inference(subsumption_resolution,[],[f578,f59])).

fof(f578,plain,
    ( ~ v1_relat_1(sK1)
    | v1_relat_1(k7_relat_1(k4_relat_1(sK1),k2_relat_1(sK1)))
    | ~ spl2_14
    | ~ spl2_74 ),
    inference(superposition,[],[f576,f136])).

fof(f136,plain,
    ( sK1 = k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1)))
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f134])).

fof(f576,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(k5_relat_1(sK1,k6_relat_1(X0)))
        | v1_relat_1(k7_relat_1(k4_relat_1(sK1),X0)) )
    | ~ spl2_74 ),
    inference(avatar_component_clause,[],[f575])).

fof(f577,plain,
    ( spl2_74
    | ~ spl2_3
    | ~ spl2_71 ),
    inference(avatar_split_clause,[],[f557,f553,f66,f575])).

fof(f553,plain,
    ( spl2_71
  <=> ! [X1] : k4_relat_1(k5_relat_1(sK1,k6_relat_1(X1))) = k7_relat_1(k4_relat_1(sK1),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_71])])).

fof(f557,plain,
    ( ! [X0] :
        ( v1_relat_1(k7_relat_1(k4_relat_1(sK1),X0))
        | ~ v1_relat_1(k5_relat_1(sK1,k6_relat_1(X0))) )
    | ~ spl2_3
    | ~ spl2_71 ),
    inference(superposition,[],[f67,f554])).

fof(f554,plain,
    ( ! [X1] : k4_relat_1(k5_relat_1(sK1,k6_relat_1(X1))) = k7_relat_1(k4_relat_1(sK1),X1)
    | ~ spl2_71 ),
    inference(avatar_component_clause,[],[f553])).

fof(f562,plain,
    ( spl2_72
    | ~ spl2_14
    | ~ spl2_71 ),
    inference(avatar_split_clause,[],[f556,f553,f134,f559])).

fof(f556,plain,
    ( k4_relat_1(sK1) = k7_relat_1(k4_relat_1(sK1),k2_relat_1(sK1))
    | ~ spl2_14
    | ~ spl2_71 ),
    inference(superposition,[],[f554,f136])).

fof(f555,plain,
    ( spl2_71
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_47
    | ~ spl2_69 ),
    inference(avatar_split_clause,[],[f546,f538,f344,f70,f62,f553])).

fof(f538,plain,
    ( spl2_69
  <=> ! [X7] :
        ( ~ v1_relat_1(X7)
        | k4_relat_1(k5_relat_1(sK1,X7)) = k5_relat_1(k4_relat_1(X7),k4_relat_1(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_69])])).

fof(f546,plain,
    ( ! [X1] : k4_relat_1(k5_relat_1(sK1,k6_relat_1(X1))) = k7_relat_1(k4_relat_1(sK1),X1)
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_47
    | ~ spl2_69 ),
    inference(forward_demodulation,[],[f545,f345])).

fof(f545,plain,
    ( ! [X1] : k4_relat_1(k5_relat_1(sK1,k6_relat_1(X1))) = k5_relat_1(k6_relat_1(X1),k4_relat_1(sK1))
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_69 ),
    inference(forward_demodulation,[],[f542,f71])).

fof(f542,plain,
    ( ! [X1] : k4_relat_1(k5_relat_1(sK1,k6_relat_1(X1))) = k5_relat_1(k4_relat_1(k6_relat_1(X1)),k4_relat_1(sK1))
    | ~ spl2_2
    | ~ spl2_69 ),
    inference(resolution,[],[f539,f63])).

fof(f539,plain,
    ( ! [X7] :
        ( ~ v1_relat_1(X7)
        | k4_relat_1(k5_relat_1(sK1,X7)) = k5_relat_1(k4_relat_1(X7),k4_relat_1(sK1)) )
    | ~ spl2_69 ),
    inference(avatar_component_clause,[],[f538])).

fof(f540,plain,
    ( spl2_69
    | ~ spl2_1
    | ~ spl2_54 ),
    inference(avatar_split_clause,[],[f535,f407,f57,f538])).

fof(f535,plain,
    ( ! [X7] :
        ( ~ v1_relat_1(X7)
        | k4_relat_1(k5_relat_1(sK1,X7)) = k5_relat_1(k4_relat_1(X7),k4_relat_1(sK1)) )
    | ~ spl2_1
    | ~ spl2_54 ),
    inference(resolution,[],[f408,f59])).

fof(f503,plain,(
    spl2_65 ),
    inference(avatar_split_clause,[],[f54,f501])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f50,f46])).

fof(f46,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(f409,plain,(
    spl2_54 ),
    inference(avatar_split_clause,[],[f42,f407])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).

fof(f393,plain,
    ( spl2_52
    | ~ spl2_1
    | ~ spl2_45 ),
    inference(avatar_split_clause,[],[f389,f324,f57,f391])).

fof(f324,plain,
    ( spl2_45
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k5_relat_1(k7_relat_1(X1,X0),X2),k5_relat_1(X1,X2))
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_45])])).

fof(f389,plain,
    ( ! [X10,X11] :
        ( ~ v1_relat_1(X10)
        | r1_tarski(k5_relat_1(k7_relat_1(sK1,X11),X10),k5_relat_1(sK1,X10)) )
    | ~ spl2_1
    | ~ spl2_45 ),
    inference(resolution,[],[f325,f59])).

fof(f325,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X1)
        | ~ v1_relat_1(X2)
        | r1_tarski(k5_relat_1(k7_relat_1(X1,X0),X2),k5_relat_1(X1,X2)) )
    | ~ spl2_45 ),
    inference(avatar_component_clause,[],[f324])).

fof(f355,plain,
    ( spl2_48
    | ~ spl2_1
    | ~ spl2_41 ),
    inference(avatar_split_clause,[],[f350,f295,f57,f353])).

fof(f295,plain,
    ( spl2_41
  <=> ! [X1,X0] :
        ( k2_relat_1(k7_relat_1(k4_relat_1(X0),X1)) = k9_relat_1(k4_relat_1(X0),X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_41])])).

fof(f350,plain,
    ( ! [X7] : k2_relat_1(k7_relat_1(k4_relat_1(sK1),X7)) = k9_relat_1(k4_relat_1(sK1),X7)
    | ~ spl2_1
    | ~ spl2_41 ),
    inference(resolution,[],[f296,f59])).

fof(f296,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | k2_relat_1(k7_relat_1(k4_relat_1(X0),X1)) = k9_relat_1(k4_relat_1(X0),X1) )
    | ~ spl2_41 ),
    inference(avatar_component_clause,[],[f295])).

fof(f346,plain,
    ( spl2_47
    | ~ spl2_1
    | ~ spl2_40 ),
    inference(avatar_split_clause,[],[f341,f291,f57,f344])).

fof(f291,plain,
    ( spl2_40
  <=> ! [X1,X0] :
        ( k7_relat_1(k4_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X1),k4_relat_1(X0))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_40])])).

fof(f341,plain,
    ( ! [X7] : k7_relat_1(k4_relat_1(sK1),X7) = k5_relat_1(k6_relat_1(X7),k4_relat_1(sK1))
    | ~ spl2_1
    | ~ spl2_40 ),
    inference(resolution,[],[f292,f59])).

fof(f292,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | k7_relat_1(k4_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X1),k4_relat_1(X0)) )
    | ~ spl2_40 ),
    inference(avatar_component_clause,[],[f291])).

fof(f326,plain,(
    spl2_45 ),
    inference(avatar_split_clause,[],[f51,f324])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_relat_1(k7_relat_1(X1,X0),X2),k5_relat_1(X1,X2))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k5_relat_1(k7_relat_1(X1,X0),X2),k5_relat_1(X1,X2))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => r1_tarski(k5_relat_1(k7_relat_1(X1,X0),X2),k5_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_relat_1)).

fof(f297,plain,
    ( spl2_41
    | ~ spl2_3
    | ~ spl2_17 ),
    inference(avatar_split_clause,[],[f164,f153,f66,f295])).

fof(f153,plain,
    ( spl2_17
  <=> ! [X1,X0] :
        ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f164,plain,
    ( ! [X0,X1] :
        ( k2_relat_1(k7_relat_1(k4_relat_1(X0),X1)) = k9_relat_1(k4_relat_1(X0),X1)
        | ~ v1_relat_1(X0) )
    | ~ spl2_3
    | ~ spl2_17 ),
    inference(resolution,[],[f154,f67])).

fof(f154,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) )
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f153])).

fof(f293,plain,
    ( spl2_40
    | ~ spl2_3
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f156,f149,f66,f291])).

fof(f149,plain,
    ( spl2_16
  <=> ! [X1,X0] :
        ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f156,plain,
    ( ! [X0,X1] :
        ( k7_relat_1(k4_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X1),k4_relat_1(X0))
        | ~ v1_relat_1(X0) )
    | ~ spl2_3
    | ~ spl2_16 ),
    inference(resolution,[],[f150,f67])).

fof(f150,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) )
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f149])).

fof(f281,plain,
    ( spl2_37
    | ~ spl2_5
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f103,f94,f74,f279])).

fof(f94,plain,
    ( spl2_8
  <=> ! [X0] :
        ( k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f103,plain,
    ( ! [X2,X3] :
        ( k2_relat_1(k7_relat_1(X2,X3)) = k1_relat_1(k4_relat_1(k7_relat_1(X2,X3)))
        | ~ v1_relat_1(X2) )
    | ~ spl2_5
    | ~ spl2_8 ),
    inference(resolution,[],[f95,f75])).

fof(f95,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f94])).

fof(f256,plain,(
    spl2_34 ),
    inference(avatar_split_clause,[],[f43,f254])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(f226,plain,(
    spl2_28 ),
    inference(avatar_split_clause,[],[f53,f224])).

fof(f53,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f45,f46,f46])).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f196,plain,(
    ~ spl2_25 ),
    inference(avatar_split_clause,[],[f55,f193])).

fof(f55,plain,(
    ~ r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,k1_relat_1(sK1))),k9_relat_1(k4_relat_1(sK1),k9_relat_1(sK1,sK0))) ),
    inference(backward_demodulation,[],[f52,f53])).

fof(f52,plain,(
    ~ r1_tarski(k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),sK0)),k9_relat_1(k4_relat_1(sK1),k9_relat_1(sK1,sK0))) ),
    inference(definition_unfolding,[],[f34,f46])).

fof(f34,plain,(
    ~ r1_tarski(k3_xboole_0(k1_relat_1(sK1),sK0),k9_relat_1(k4_relat_1(sK1),k9_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ~ r1_tarski(k3_xboole_0(k1_relat_1(sK1),sK0),k9_relat_1(k4_relat_1(sK1),k9_relat_1(sK1,sK0)))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f31])).

fof(f31,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k3_xboole_0(k1_relat_1(X1),X0),k9_relat_1(k4_relat_1(X1),k9_relat_1(X1,X0)))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k3_xboole_0(k1_relat_1(sK1),sK0),k9_relat_1(k4_relat_1(sK1),k9_relat_1(sK1,sK0)))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k3_xboole_0(k1_relat_1(X1),X0),k9_relat_1(k4_relat_1(X1),k9_relat_1(X1,X0)))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => r1_tarski(k3_xboole_0(k1_relat_1(X1),X0),k9_relat_1(k4_relat_1(X1),k9_relat_1(X1,X0))) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k3_xboole_0(k1_relat_1(X1),X0),k9_relat_1(k4_relat_1(X1),k9_relat_1(X1,X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t163_relat_1)).

fof(f171,plain,
    ( spl2_19
    | ~ spl2_1
    | ~ spl2_17 ),
    inference(avatar_split_clause,[],[f167,f153,f57,f169])).

fof(f167,plain,
    ( ! [X7] : k2_relat_1(k7_relat_1(sK1,X7)) = k9_relat_1(sK1,X7)
    | ~ spl2_1
    | ~ spl2_17 ),
    inference(resolution,[],[f154,f59])).

fof(f155,plain,(
    spl2_17 ),
    inference(avatar_split_clause,[],[f49,f153])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f151,plain,(
    spl2_16 ),
    inference(avatar_split_clause,[],[f48,f149])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f137,plain,
    ( spl2_14
    | ~ spl2_1
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f132,f121,f57,f134])).

fof(f132,plain,
    ( sK1 = k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1)))
    | ~ spl2_1
    | ~ spl2_12 ),
    inference(resolution,[],[f122,f59])).

fof(f123,plain,(
    spl2_12 ),
    inference(avatar_split_clause,[],[f39,f121])).

fof(f39,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

fof(f96,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f40,f94])).

fof(f40,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

fof(f91,plain,
    ( spl2_7
    | ~ spl2_1
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f85,f79,f57,f88])).

fof(f79,plain,
    ( spl2_6
  <=> ! [X0] :
        ( k4_relat_1(k4_relat_1(X0)) = X0
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f85,plain,
    ( sK1 = k4_relat_1(k4_relat_1(sK1))
    | ~ spl2_1
    | ~ spl2_6 ),
    inference(resolution,[],[f80,f59])).

fof(f80,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k4_relat_1(k4_relat_1(X0)) = X0 )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f79])).

fof(f81,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f38,f79])).

fof(f38,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

fof(f76,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f47,f74])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f72,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f36,f70])).

fof(f36,plain,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_relat_1)).

fof(f68,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f37,f66])).

fof(f37,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f64,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f35,f62])).

fof(f35,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f60,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f33,f57])).

fof(f33,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:43:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (28904)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.46  % (28895)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.46  % (28905)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.46  % (28893)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.46  % (28897)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.46  % (28896)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.47  % (28894)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (28903)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.47  % (28901)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.47  % (28907)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.47  % (28899)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.47  % (28900)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.48  % (28892)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.48  % (28891)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.49  % (28890)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.49  % (28906)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.49  % (28898)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.49  % (28902)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.57  % (28897)Refutation found. Thanks to Tanya!
% 0.21/0.57  % SZS status Theorem for theBenchmark
% 0.21/0.57  % SZS output start Proof for theBenchmark
% 0.21/0.57  fof(f2063,plain,(
% 0.21/0.57    $false),
% 0.21/0.57    inference(avatar_sat_refutation,[],[f60,f64,f68,f72,f76,f81,f91,f96,f123,f137,f151,f155,f171,f196,f226,f256,f281,f293,f297,f326,f346,f355,f393,f409,f503,f540,f555,f562,f577,f585,f648,f654,f669,f721,f852,f856,f864,f944,f1776,f2013,f2023,f2043,f2059])).
% 0.21/0.57  fof(f2059,plain,(
% 0.21/0.57    ~spl2_1 | ~spl2_5 | spl2_79 | ~spl2_199),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f2058])).
% 0.21/0.57  fof(f2058,plain,(
% 0.21/0.57    $false | (~spl2_1 | ~spl2_5 | spl2_79 | ~spl2_199)),
% 0.21/0.57    inference(subsumption_resolution,[],[f668,f2057])).
% 0.21/0.57  fof(f2057,plain,(
% 0.21/0.57    ( ! [X0] : (r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k9_relat_1(k4_relat_1(sK1),k9_relat_1(sK1,X0)))) ) | (~spl2_1 | ~spl2_5 | ~spl2_199)),
% 0.21/0.57    inference(subsumption_resolution,[],[f2055,f59])).
% 0.21/0.57  fof(f59,plain,(
% 0.21/0.57    v1_relat_1(sK1) | ~spl2_1),
% 0.21/0.57    inference(avatar_component_clause,[],[f57])).
% 0.21/0.57  fof(f57,plain,(
% 0.21/0.57    spl2_1 <=> v1_relat_1(sK1)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.57  fof(f2055,plain,(
% 0.21/0.57    ( ! [X0] : (r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k9_relat_1(k4_relat_1(sK1),k9_relat_1(sK1,X0))) | ~v1_relat_1(sK1)) ) | (~spl2_5 | ~spl2_199)),
% 0.21/0.57    inference(resolution,[],[f2042,f75])).
% 0.21/0.57  fof(f75,plain,(
% 0.21/0.57    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) ) | ~spl2_5),
% 0.21/0.57    inference(avatar_component_clause,[],[f74])).
% 0.21/0.57  fof(f74,plain,(
% 0.21/0.57    spl2_5 <=> ! [X1,X0] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.57  fof(f2042,plain,(
% 0.21/0.57    ( ! [X1] : (~v1_relat_1(k7_relat_1(sK1,X1)) | r1_tarski(k1_relat_1(k7_relat_1(sK1,X1)),k9_relat_1(k4_relat_1(sK1),k9_relat_1(sK1,X1)))) ) | ~spl2_199),
% 0.21/0.57    inference(avatar_component_clause,[],[f2041])).
% 0.21/0.57  fof(f2041,plain,(
% 0.21/0.57    spl2_199 <=> ! [X1] : (r1_tarski(k1_relat_1(k7_relat_1(sK1,X1)),k9_relat_1(k4_relat_1(sK1),k9_relat_1(sK1,X1))) | ~v1_relat_1(k7_relat_1(sK1,X1)))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_199])])).
% 0.21/0.57  fof(f668,plain,(
% 0.21/0.57    ~r1_tarski(k1_relat_1(k7_relat_1(sK1,sK0)),k9_relat_1(k4_relat_1(sK1),k9_relat_1(sK1,sK0))) | spl2_79),
% 0.21/0.57    inference(avatar_component_clause,[],[f666])).
% 0.21/0.57  fof(f666,plain,(
% 0.21/0.57    spl2_79 <=> r1_tarski(k1_relat_1(k7_relat_1(sK1,sK0)),k9_relat_1(k4_relat_1(sK1),k9_relat_1(sK1,sK0)))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_79])])).
% 0.21/0.57  fof(f2043,plain,(
% 0.21/0.57    spl2_199 | ~spl2_34 | ~spl2_100 | ~spl2_103 | ~spl2_197),
% 0.21/0.57    inference(avatar_split_clause,[],[f2031,f2021,f942,f854,f254,f2041])).
% 0.21/0.57  fof(f254,plain,(
% 0.21/0.57    spl2_34 <=> ! [X1,X0] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).
% 0.21/0.57  fof(f854,plain,(
% 0.21/0.57    spl2_100 <=> ! [X3] : k9_relat_1(k4_relat_1(sK1),X3) = k1_relat_1(k5_relat_1(sK1,k6_relat_1(X3)))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_100])])).
% 0.21/0.57  fof(f942,plain,(
% 0.21/0.57    spl2_103 <=> ! [X0] : v1_relat_1(k5_relat_1(sK1,k6_relat_1(X0)))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_103])])).
% 0.21/0.57  fof(f2021,plain,(
% 0.21/0.57    spl2_197 <=> ! [X0] : r1_tarski(k7_relat_1(sK1,X0),k5_relat_1(sK1,k6_relat_1(k9_relat_1(sK1,X0))))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_197])])).
% 0.21/0.57  fof(f2031,plain,(
% 0.21/0.57    ( ! [X1] : (r1_tarski(k1_relat_1(k7_relat_1(sK1,X1)),k9_relat_1(k4_relat_1(sK1),k9_relat_1(sK1,X1))) | ~v1_relat_1(k7_relat_1(sK1,X1))) ) | (~spl2_34 | ~spl2_100 | ~spl2_103 | ~spl2_197)),
% 0.21/0.57    inference(forward_demodulation,[],[f2030,f855])).
% 0.21/0.57  fof(f855,plain,(
% 0.21/0.57    ( ! [X3] : (k9_relat_1(k4_relat_1(sK1),X3) = k1_relat_1(k5_relat_1(sK1,k6_relat_1(X3)))) ) | ~spl2_100),
% 0.21/0.57    inference(avatar_component_clause,[],[f854])).
% 0.21/0.57  fof(f2030,plain,(
% 0.21/0.57    ( ! [X1] : (r1_tarski(k1_relat_1(k7_relat_1(sK1,X1)),k1_relat_1(k5_relat_1(sK1,k6_relat_1(k9_relat_1(sK1,X1))))) | ~v1_relat_1(k7_relat_1(sK1,X1))) ) | (~spl2_34 | ~spl2_103 | ~spl2_197)),
% 0.21/0.57    inference(subsumption_resolution,[],[f2025,f943])).
% 0.21/0.57  fof(f943,plain,(
% 0.21/0.57    ( ! [X0] : (v1_relat_1(k5_relat_1(sK1,k6_relat_1(X0)))) ) | ~spl2_103),
% 0.21/0.57    inference(avatar_component_clause,[],[f942])).
% 0.21/0.57  fof(f2025,plain,(
% 0.21/0.57    ( ! [X1] : (r1_tarski(k1_relat_1(k7_relat_1(sK1,X1)),k1_relat_1(k5_relat_1(sK1,k6_relat_1(k9_relat_1(sK1,X1))))) | ~v1_relat_1(k5_relat_1(sK1,k6_relat_1(k9_relat_1(sK1,X1)))) | ~v1_relat_1(k7_relat_1(sK1,X1))) ) | (~spl2_34 | ~spl2_197)),
% 0.21/0.57    inference(resolution,[],[f2022,f255])).
% 0.21/0.57  fof(f255,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl2_34),
% 0.21/0.57    inference(avatar_component_clause,[],[f254])).
% 0.21/0.57  fof(f2022,plain,(
% 0.21/0.57    ( ! [X0] : (r1_tarski(k7_relat_1(sK1,X0),k5_relat_1(sK1,k6_relat_1(k9_relat_1(sK1,X0))))) ) | ~spl2_197),
% 0.21/0.57    inference(avatar_component_clause,[],[f2021])).
% 0.21/0.57  fof(f2023,plain,(
% 0.21/0.57    spl2_197 | ~spl2_2 | ~spl2_52 | ~spl2_196),
% 0.21/0.57    inference(avatar_split_clause,[],[f2019,f2011,f391,f62,f2021])).
% 0.21/0.57  fof(f62,plain,(
% 0.21/0.57    spl2_2 <=> ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.57  fof(f391,plain,(
% 0.21/0.57    spl2_52 <=> ! [X11,X10] : (~v1_relat_1(X10) | r1_tarski(k5_relat_1(k7_relat_1(sK1,X11),X10),k5_relat_1(sK1,X10)))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_52])])).
% 0.21/0.57  fof(f2011,plain,(
% 0.21/0.57    spl2_196 <=> ! [X15] : k7_relat_1(sK1,X15) = k5_relat_1(k7_relat_1(sK1,X15),k6_relat_1(k9_relat_1(sK1,X15)))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_196])])).
% 0.21/0.57  fof(f2019,plain,(
% 0.21/0.57    ( ! [X0] : (r1_tarski(k7_relat_1(sK1,X0),k5_relat_1(sK1,k6_relat_1(k9_relat_1(sK1,X0))))) ) | (~spl2_2 | ~spl2_52 | ~spl2_196)),
% 0.21/0.57    inference(subsumption_resolution,[],[f2016,f63])).
% 0.21/0.57  fof(f63,plain,(
% 0.21/0.57    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) ) | ~spl2_2),
% 0.21/0.57    inference(avatar_component_clause,[],[f62])).
% 0.21/0.57  fof(f2016,plain,(
% 0.21/0.57    ( ! [X0] : (r1_tarski(k7_relat_1(sK1,X0),k5_relat_1(sK1,k6_relat_1(k9_relat_1(sK1,X0)))) | ~v1_relat_1(k6_relat_1(k9_relat_1(sK1,X0)))) ) | (~spl2_52 | ~spl2_196)),
% 0.21/0.57    inference(superposition,[],[f392,f2012])).
% 0.21/0.57  fof(f2012,plain,(
% 0.21/0.57    ( ! [X15] : (k7_relat_1(sK1,X15) = k5_relat_1(k7_relat_1(sK1,X15),k6_relat_1(k9_relat_1(sK1,X15)))) ) | ~spl2_196),
% 0.21/0.57    inference(avatar_component_clause,[],[f2011])).
% 0.21/0.57  fof(f392,plain,(
% 0.21/0.57    ( ! [X10,X11] : (r1_tarski(k5_relat_1(k7_relat_1(sK1,X11),X10),k5_relat_1(sK1,X10)) | ~v1_relat_1(X10)) ) | ~spl2_52),
% 0.21/0.57    inference(avatar_component_clause,[],[f391])).
% 0.21/0.57  fof(f2013,plain,(
% 0.21/0.57    spl2_196 | ~spl2_1 | ~spl2_19 | ~spl2_174),
% 0.21/0.57    inference(avatar_split_clause,[],[f2009,f1774,f169,f57,f2011])).
% 0.21/0.57  fof(f169,plain,(
% 0.21/0.57    spl2_19 <=> ! [X7] : k2_relat_1(k7_relat_1(sK1,X7)) = k9_relat_1(sK1,X7)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 0.21/0.57  fof(f1774,plain,(
% 0.21/0.57    spl2_174 <=> ! [X3,X2] : (k7_relat_1(X2,X3) = k5_relat_1(k7_relat_1(X2,X3),k6_relat_1(k2_relat_1(k7_relat_1(X2,X3)))) | ~v1_relat_1(X2))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_174])])).
% 0.21/0.57  fof(f2009,plain,(
% 0.21/0.57    ( ! [X15] : (k7_relat_1(sK1,X15) = k5_relat_1(k7_relat_1(sK1,X15),k6_relat_1(k9_relat_1(sK1,X15)))) ) | (~spl2_1 | ~spl2_19 | ~spl2_174)),
% 0.21/0.57    inference(forward_demodulation,[],[f2003,f170])).
% 0.21/0.57  fof(f170,plain,(
% 0.21/0.57    ( ! [X7] : (k2_relat_1(k7_relat_1(sK1,X7)) = k9_relat_1(sK1,X7)) ) | ~spl2_19),
% 0.21/0.57    inference(avatar_component_clause,[],[f169])).
% 0.21/0.57  fof(f2003,plain,(
% 0.21/0.57    ( ! [X15] : (k7_relat_1(sK1,X15) = k5_relat_1(k7_relat_1(sK1,X15),k6_relat_1(k2_relat_1(k7_relat_1(sK1,X15))))) ) | (~spl2_1 | ~spl2_174)),
% 0.21/0.57    inference(resolution,[],[f1775,f59])).
% 0.21/0.57  fof(f1775,plain,(
% 0.21/0.57    ( ! [X2,X3] : (~v1_relat_1(X2) | k7_relat_1(X2,X3) = k5_relat_1(k7_relat_1(X2,X3),k6_relat_1(k2_relat_1(k7_relat_1(X2,X3))))) ) | ~spl2_174),
% 0.21/0.57    inference(avatar_component_clause,[],[f1774])).
% 0.21/0.57  fof(f1776,plain,(
% 0.21/0.57    spl2_174 | ~spl2_5 | ~spl2_12),
% 0.21/0.57    inference(avatar_split_clause,[],[f131,f121,f74,f1774])).
% 0.21/0.57  fof(f121,plain,(
% 0.21/0.57    spl2_12 <=> ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.21/0.57  fof(f131,plain,(
% 0.21/0.57    ( ! [X2,X3] : (k7_relat_1(X2,X3) = k5_relat_1(k7_relat_1(X2,X3),k6_relat_1(k2_relat_1(k7_relat_1(X2,X3)))) | ~v1_relat_1(X2)) ) | (~spl2_5 | ~spl2_12)),
% 0.21/0.57    inference(resolution,[],[f122,f75])).
% 0.21/0.57  fof(f122,plain,(
% 0.21/0.57    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0) ) | ~spl2_12),
% 0.21/0.57    inference(avatar_component_clause,[],[f121])).
% 0.21/0.57  fof(f944,plain,(
% 0.21/0.57    spl2_103 | ~spl2_5 | ~spl2_75 | ~spl2_101),
% 0.21/0.57    inference(avatar_split_clause,[],[f867,f862,f582,f74,f942])).
% 0.21/0.57  fof(f582,plain,(
% 0.21/0.57    spl2_75 <=> v1_relat_1(k4_relat_1(sK1))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_75])])).
% 0.21/0.57  fof(f862,plain,(
% 0.21/0.57    spl2_101 <=> ! [X0] : (v1_relat_1(k5_relat_1(sK1,k6_relat_1(X0))) | ~v1_relat_1(k7_relat_1(k4_relat_1(sK1),X0)))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_101])])).
% 0.21/0.57  fof(f867,plain,(
% 0.21/0.57    ( ! [X0] : (v1_relat_1(k5_relat_1(sK1,k6_relat_1(X0)))) ) | (~spl2_5 | ~spl2_75 | ~spl2_101)),
% 0.21/0.57    inference(subsumption_resolution,[],[f865,f584])).
% 0.21/0.57  fof(f584,plain,(
% 0.21/0.57    v1_relat_1(k4_relat_1(sK1)) | ~spl2_75),
% 0.21/0.57    inference(avatar_component_clause,[],[f582])).
% 0.21/0.57  fof(f865,plain,(
% 0.21/0.57    ( ! [X0] : (v1_relat_1(k5_relat_1(sK1,k6_relat_1(X0))) | ~v1_relat_1(k4_relat_1(sK1))) ) | (~spl2_5 | ~spl2_101)),
% 0.21/0.57    inference(resolution,[],[f863,f75])).
% 0.21/0.57  fof(f863,plain,(
% 0.21/0.57    ( ! [X0] : (~v1_relat_1(k7_relat_1(k4_relat_1(sK1),X0)) | v1_relat_1(k5_relat_1(sK1,k6_relat_1(X0)))) ) | ~spl2_101),
% 0.21/0.57    inference(avatar_component_clause,[],[f862])).
% 0.21/0.57  fof(f864,plain,(
% 0.21/0.57    spl2_101 | ~spl2_3 | ~spl2_99),
% 0.21/0.57    inference(avatar_split_clause,[],[f858,f850,f66,f862])).
% 0.21/0.57  fof(f66,plain,(
% 0.21/0.57    spl2_3 <=> ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.57  fof(f850,plain,(
% 0.21/0.57    spl2_99 <=> ! [X2] : k4_relat_1(k7_relat_1(k4_relat_1(sK1),X2)) = k5_relat_1(sK1,k6_relat_1(X2))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_99])])).
% 0.21/0.57  fof(f858,plain,(
% 0.21/0.57    ( ! [X0] : (v1_relat_1(k5_relat_1(sK1,k6_relat_1(X0))) | ~v1_relat_1(k7_relat_1(k4_relat_1(sK1),X0))) ) | (~spl2_3 | ~spl2_99)),
% 0.21/0.57    inference(superposition,[],[f67,f851])).
% 0.21/0.57  fof(f851,plain,(
% 0.21/0.57    ( ! [X2] : (k4_relat_1(k7_relat_1(k4_relat_1(sK1),X2)) = k5_relat_1(sK1,k6_relat_1(X2))) ) | ~spl2_99),
% 0.21/0.57    inference(avatar_component_clause,[],[f850])).
% 0.21/0.57  fof(f67,plain,(
% 0.21/0.57    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) ) | ~spl2_3),
% 0.21/0.57    inference(avatar_component_clause,[],[f66])).
% 0.21/0.57  fof(f856,plain,(
% 0.21/0.57    spl2_100 | ~spl2_7 | ~spl2_47 | ~spl2_75 | ~spl2_77 | ~spl2_87),
% 0.21/0.57    inference(avatar_split_clause,[],[f813,f719,f646,f582,f344,f88,f854])).
% 0.21/0.57  fof(f88,plain,(
% 0.21/0.57    spl2_7 <=> sK1 = k4_relat_1(k4_relat_1(sK1))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.57  fof(f344,plain,(
% 0.21/0.57    spl2_47 <=> ! [X7] : k7_relat_1(k4_relat_1(sK1),X7) = k5_relat_1(k6_relat_1(X7),k4_relat_1(sK1))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_47])])).
% 0.21/0.57  fof(f646,plain,(
% 0.21/0.57    spl2_77 <=> ! [X3] : k1_relat_1(k4_relat_1(k7_relat_1(k4_relat_1(sK1),X3))) = k9_relat_1(k4_relat_1(sK1),X3)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_77])])).
% 0.21/0.57  fof(f719,plain,(
% 0.21/0.57    spl2_87 <=> ! [X3,X2] : (k4_relat_1(k5_relat_1(k6_relat_1(X3),X2)) = k5_relat_1(k4_relat_1(X2),k6_relat_1(X3)) | ~v1_relat_1(X2))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_87])])).
% 0.21/0.57  fof(f813,plain,(
% 0.21/0.57    ( ! [X3] : (k9_relat_1(k4_relat_1(sK1),X3) = k1_relat_1(k5_relat_1(sK1,k6_relat_1(X3)))) ) | (~spl2_7 | ~spl2_47 | ~spl2_75 | ~spl2_77 | ~spl2_87)),
% 0.21/0.57    inference(backward_demodulation,[],[f647,f811])).
% 0.21/0.57  fof(f811,plain,(
% 0.21/0.57    ( ! [X2] : (k4_relat_1(k7_relat_1(k4_relat_1(sK1),X2)) = k5_relat_1(sK1,k6_relat_1(X2))) ) | (~spl2_7 | ~spl2_47 | ~spl2_75 | ~spl2_87)),
% 0.21/0.57    inference(forward_demodulation,[],[f810,f345])).
% 0.21/0.57  fof(f345,plain,(
% 0.21/0.57    ( ! [X7] : (k7_relat_1(k4_relat_1(sK1),X7) = k5_relat_1(k6_relat_1(X7),k4_relat_1(sK1))) ) | ~spl2_47),
% 0.21/0.57    inference(avatar_component_clause,[],[f344])).
% 0.21/0.57  fof(f810,plain,(
% 0.21/0.57    ( ! [X2] : (k4_relat_1(k5_relat_1(k6_relat_1(X2),k4_relat_1(sK1))) = k5_relat_1(sK1,k6_relat_1(X2))) ) | (~spl2_7 | ~spl2_75 | ~spl2_87)),
% 0.21/0.57    inference(forward_demodulation,[],[f806,f90])).
% 0.21/0.57  fof(f90,plain,(
% 0.21/0.57    sK1 = k4_relat_1(k4_relat_1(sK1)) | ~spl2_7),
% 0.21/0.57    inference(avatar_component_clause,[],[f88])).
% 0.21/0.57  fof(f806,plain,(
% 0.21/0.57    ( ! [X2] : (k4_relat_1(k5_relat_1(k6_relat_1(X2),k4_relat_1(sK1))) = k5_relat_1(k4_relat_1(k4_relat_1(sK1)),k6_relat_1(X2))) ) | (~spl2_75 | ~spl2_87)),
% 0.21/0.57    inference(resolution,[],[f720,f584])).
% 0.21/0.57  fof(f720,plain,(
% 0.21/0.57    ( ! [X2,X3] : (~v1_relat_1(X2) | k4_relat_1(k5_relat_1(k6_relat_1(X3),X2)) = k5_relat_1(k4_relat_1(X2),k6_relat_1(X3))) ) | ~spl2_87),
% 0.21/0.57    inference(avatar_component_clause,[],[f719])).
% 0.21/0.57  fof(f647,plain,(
% 0.21/0.57    ( ! [X3] : (k1_relat_1(k4_relat_1(k7_relat_1(k4_relat_1(sK1),X3))) = k9_relat_1(k4_relat_1(sK1),X3)) ) | ~spl2_77),
% 0.21/0.57    inference(avatar_component_clause,[],[f646])).
% 0.21/0.57  fof(f852,plain,(
% 0.21/0.57    spl2_99 | ~spl2_7 | ~spl2_47 | ~spl2_75 | ~spl2_87),
% 0.21/0.57    inference(avatar_split_clause,[],[f811,f719,f582,f344,f88,f850])).
% 0.21/0.57  fof(f721,plain,(
% 0.21/0.57    spl2_87 | ~spl2_2 | ~spl2_4 | ~spl2_54),
% 0.21/0.57    inference(avatar_split_clause,[],[f536,f407,f70,f62,f719])).
% 0.21/0.57  fof(f70,plain,(
% 0.21/0.57    spl2_4 <=> ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.57  fof(f407,plain,(
% 0.21/0.57    spl2_54 <=> ! [X1,X0] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_54])])).
% 0.21/0.57  fof(f536,plain,(
% 0.21/0.57    ( ! [X2,X3] : (k4_relat_1(k5_relat_1(k6_relat_1(X3),X2)) = k5_relat_1(k4_relat_1(X2),k6_relat_1(X3)) | ~v1_relat_1(X2)) ) | (~spl2_2 | ~spl2_4 | ~spl2_54)),
% 0.21/0.57    inference(forward_demodulation,[],[f533,f71])).
% 0.21/0.57  fof(f71,plain,(
% 0.21/0.57    ( ! [X0] : (k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))) ) | ~spl2_4),
% 0.21/0.57    inference(avatar_component_clause,[],[f70])).
% 0.21/0.57  fof(f533,plain,(
% 0.21/0.57    ( ! [X2,X3] : (~v1_relat_1(X2) | k4_relat_1(k5_relat_1(k6_relat_1(X3),X2)) = k5_relat_1(k4_relat_1(X2),k4_relat_1(k6_relat_1(X3)))) ) | (~spl2_2 | ~spl2_54)),
% 0.21/0.57    inference(resolution,[],[f408,f63])).
% 0.21/0.57  fof(f408,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))) ) | ~spl2_54),
% 0.21/0.57    inference(avatar_component_clause,[],[f407])).
% 0.21/0.57  fof(f669,plain,(
% 0.21/0.57    ~spl2_79 | spl2_25 | ~spl2_28 | ~spl2_78),
% 0.21/0.57    inference(avatar_split_clause,[],[f664,f652,f224,f193,f666])).
% 0.21/0.57  fof(f193,plain,(
% 0.21/0.57    spl2_25 <=> r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,k1_relat_1(sK1))),k9_relat_1(k4_relat_1(sK1),k9_relat_1(sK1,sK0)))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).
% 0.21/0.57  fof(f224,plain,(
% 0.21/0.57    spl2_28 <=> ! [X1,X0] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).
% 0.21/0.57  fof(f652,plain,(
% 0.21/0.57    spl2_78 <=> ! [X7] : k1_relat_1(k7_relat_1(sK1,X7)) = k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),X7))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_78])])).
% 0.21/0.57  fof(f664,plain,(
% 0.21/0.57    ~r1_tarski(k1_relat_1(k7_relat_1(sK1,sK0)),k9_relat_1(k4_relat_1(sK1),k9_relat_1(sK1,sK0))) | (spl2_25 | ~spl2_28 | ~spl2_78)),
% 0.21/0.57    inference(backward_demodulation,[],[f195,f658])).
% 0.21/0.57  fof(f658,plain,(
% 0.21/0.57    ( ! [X1] : (k1_relat_1(k7_relat_1(sK1,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,k1_relat_1(sK1)))) ) | (~spl2_28 | ~spl2_78)),
% 0.21/0.57    inference(superposition,[],[f653,f225])).
% 0.21/0.57  fof(f225,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) ) | ~spl2_28),
% 0.21/0.57    inference(avatar_component_clause,[],[f224])).
% 0.21/0.57  fof(f653,plain,(
% 0.21/0.57    ( ! [X7] : (k1_relat_1(k7_relat_1(sK1,X7)) = k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),X7))) ) | ~spl2_78),
% 0.21/0.57    inference(avatar_component_clause,[],[f652])).
% 0.21/0.57  fof(f195,plain,(
% 0.21/0.57    ~r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,k1_relat_1(sK1))),k9_relat_1(k4_relat_1(sK1),k9_relat_1(sK1,sK0))) | spl2_25),
% 0.21/0.57    inference(avatar_component_clause,[],[f193])).
% 0.21/0.57  fof(f654,plain,(
% 0.21/0.57    spl2_78 | ~spl2_1 | ~spl2_65),
% 0.21/0.57    inference(avatar_split_clause,[],[f589,f501,f57,f652])).
% 0.21/0.57  fof(f501,plain,(
% 0.21/0.57    spl2_65 <=> ! [X1,X0] : (k1_relat_1(k7_relat_1(X1,X0)) = k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_65])])).
% 0.21/0.57  fof(f589,plain,(
% 0.21/0.57    ( ! [X7] : (k1_relat_1(k7_relat_1(sK1,X7)) = k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),X7))) ) | (~spl2_1 | ~spl2_65)),
% 0.21/0.57    inference(resolution,[],[f502,f59])).
% 0.21/0.57  fof(f502,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X0))) ) | ~spl2_65),
% 0.21/0.57    inference(avatar_component_clause,[],[f501])).
% 0.21/0.57  fof(f648,plain,(
% 0.21/0.57    spl2_77 | ~spl2_37 | ~spl2_48 | ~spl2_75),
% 0.21/0.57    inference(avatar_split_clause,[],[f624,f582,f353,f279,f646])).
% 0.21/0.57  fof(f279,plain,(
% 0.21/0.57    spl2_37 <=> ! [X3,X2] : (k2_relat_1(k7_relat_1(X2,X3)) = k1_relat_1(k4_relat_1(k7_relat_1(X2,X3))) | ~v1_relat_1(X2))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_37])])).
% 0.21/0.57  fof(f353,plain,(
% 0.21/0.57    spl2_48 <=> ! [X7] : k2_relat_1(k7_relat_1(k4_relat_1(sK1),X7)) = k9_relat_1(k4_relat_1(sK1),X7)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_48])])).
% 0.21/0.57  fof(f624,plain,(
% 0.21/0.57    ( ! [X3] : (k1_relat_1(k4_relat_1(k7_relat_1(k4_relat_1(sK1),X3))) = k9_relat_1(k4_relat_1(sK1),X3)) ) | (~spl2_37 | ~spl2_48 | ~spl2_75)),
% 0.21/0.57    inference(forward_demodulation,[],[f602,f354])).
% 0.21/0.57  fof(f354,plain,(
% 0.21/0.57    ( ! [X7] : (k2_relat_1(k7_relat_1(k4_relat_1(sK1),X7)) = k9_relat_1(k4_relat_1(sK1),X7)) ) | ~spl2_48),
% 0.21/0.57    inference(avatar_component_clause,[],[f353])).
% 0.21/0.57  fof(f602,plain,(
% 0.21/0.57    ( ! [X3] : (k2_relat_1(k7_relat_1(k4_relat_1(sK1),X3)) = k1_relat_1(k4_relat_1(k7_relat_1(k4_relat_1(sK1),X3)))) ) | (~spl2_37 | ~spl2_75)),
% 0.21/0.57    inference(resolution,[],[f584,f280])).
% 0.21/0.57  fof(f280,plain,(
% 0.21/0.57    ( ! [X2,X3] : (~v1_relat_1(X2) | k2_relat_1(k7_relat_1(X2,X3)) = k1_relat_1(k4_relat_1(k7_relat_1(X2,X3)))) ) | ~spl2_37),
% 0.21/0.57    inference(avatar_component_clause,[],[f279])).
% 0.21/0.57  fof(f585,plain,(
% 0.21/0.57    spl2_75 | ~spl2_1 | ~spl2_14 | ~spl2_72 | ~spl2_74),
% 0.21/0.57    inference(avatar_split_clause,[],[f580,f575,f559,f134,f57,f582])).
% 0.21/0.57  fof(f134,plain,(
% 0.21/0.57    spl2_14 <=> sK1 = k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1)))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.21/0.57  fof(f559,plain,(
% 0.21/0.57    spl2_72 <=> k4_relat_1(sK1) = k7_relat_1(k4_relat_1(sK1),k2_relat_1(sK1))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_72])])).
% 0.21/0.57  fof(f575,plain,(
% 0.21/0.57    spl2_74 <=> ! [X0] : (v1_relat_1(k7_relat_1(k4_relat_1(sK1),X0)) | ~v1_relat_1(k5_relat_1(sK1,k6_relat_1(X0))))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_74])])).
% 0.21/0.57  fof(f580,plain,(
% 0.21/0.57    v1_relat_1(k4_relat_1(sK1)) | (~spl2_1 | ~spl2_14 | ~spl2_72 | ~spl2_74)),
% 0.21/0.57    inference(forward_demodulation,[],[f579,f561])).
% 0.21/0.57  fof(f561,plain,(
% 0.21/0.57    k4_relat_1(sK1) = k7_relat_1(k4_relat_1(sK1),k2_relat_1(sK1)) | ~spl2_72),
% 0.21/0.57    inference(avatar_component_clause,[],[f559])).
% 0.21/0.57  fof(f579,plain,(
% 0.21/0.57    v1_relat_1(k7_relat_1(k4_relat_1(sK1),k2_relat_1(sK1))) | (~spl2_1 | ~spl2_14 | ~spl2_74)),
% 0.21/0.57    inference(subsumption_resolution,[],[f578,f59])).
% 0.21/0.57  fof(f578,plain,(
% 0.21/0.57    ~v1_relat_1(sK1) | v1_relat_1(k7_relat_1(k4_relat_1(sK1),k2_relat_1(sK1))) | (~spl2_14 | ~spl2_74)),
% 0.21/0.57    inference(superposition,[],[f576,f136])).
% 0.21/0.57  fof(f136,plain,(
% 0.21/0.57    sK1 = k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1))) | ~spl2_14),
% 0.21/0.57    inference(avatar_component_clause,[],[f134])).
% 0.21/0.57  fof(f576,plain,(
% 0.21/0.57    ( ! [X0] : (~v1_relat_1(k5_relat_1(sK1,k6_relat_1(X0))) | v1_relat_1(k7_relat_1(k4_relat_1(sK1),X0))) ) | ~spl2_74),
% 0.21/0.57    inference(avatar_component_clause,[],[f575])).
% 0.21/0.57  fof(f577,plain,(
% 0.21/0.57    spl2_74 | ~spl2_3 | ~spl2_71),
% 0.21/0.57    inference(avatar_split_clause,[],[f557,f553,f66,f575])).
% 0.21/0.57  fof(f553,plain,(
% 0.21/0.57    spl2_71 <=> ! [X1] : k4_relat_1(k5_relat_1(sK1,k6_relat_1(X1))) = k7_relat_1(k4_relat_1(sK1),X1)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_71])])).
% 0.21/0.57  fof(f557,plain,(
% 0.21/0.57    ( ! [X0] : (v1_relat_1(k7_relat_1(k4_relat_1(sK1),X0)) | ~v1_relat_1(k5_relat_1(sK1,k6_relat_1(X0)))) ) | (~spl2_3 | ~spl2_71)),
% 0.21/0.57    inference(superposition,[],[f67,f554])).
% 0.21/0.57  fof(f554,plain,(
% 0.21/0.57    ( ! [X1] : (k4_relat_1(k5_relat_1(sK1,k6_relat_1(X1))) = k7_relat_1(k4_relat_1(sK1),X1)) ) | ~spl2_71),
% 0.21/0.57    inference(avatar_component_clause,[],[f553])).
% 0.21/0.57  fof(f562,plain,(
% 0.21/0.57    spl2_72 | ~spl2_14 | ~spl2_71),
% 0.21/0.57    inference(avatar_split_clause,[],[f556,f553,f134,f559])).
% 0.21/0.57  fof(f556,plain,(
% 0.21/0.57    k4_relat_1(sK1) = k7_relat_1(k4_relat_1(sK1),k2_relat_1(sK1)) | (~spl2_14 | ~spl2_71)),
% 0.21/0.57    inference(superposition,[],[f554,f136])).
% 0.21/0.57  fof(f555,plain,(
% 0.21/0.57    spl2_71 | ~spl2_2 | ~spl2_4 | ~spl2_47 | ~spl2_69),
% 0.21/0.57    inference(avatar_split_clause,[],[f546,f538,f344,f70,f62,f553])).
% 0.21/0.57  fof(f538,plain,(
% 0.21/0.57    spl2_69 <=> ! [X7] : (~v1_relat_1(X7) | k4_relat_1(k5_relat_1(sK1,X7)) = k5_relat_1(k4_relat_1(X7),k4_relat_1(sK1)))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_69])])).
% 0.21/0.57  fof(f546,plain,(
% 0.21/0.57    ( ! [X1] : (k4_relat_1(k5_relat_1(sK1,k6_relat_1(X1))) = k7_relat_1(k4_relat_1(sK1),X1)) ) | (~spl2_2 | ~spl2_4 | ~spl2_47 | ~spl2_69)),
% 0.21/0.57    inference(forward_demodulation,[],[f545,f345])).
% 0.21/0.57  fof(f545,plain,(
% 0.21/0.57    ( ! [X1] : (k4_relat_1(k5_relat_1(sK1,k6_relat_1(X1))) = k5_relat_1(k6_relat_1(X1),k4_relat_1(sK1))) ) | (~spl2_2 | ~spl2_4 | ~spl2_69)),
% 0.21/0.57    inference(forward_demodulation,[],[f542,f71])).
% 0.21/0.57  fof(f542,plain,(
% 0.21/0.57    ( ! [X1] : (k4_relat_1(k5_relat_1(sK1,k6_relat_1(X1))) = k5_relat_1(k4_relat_1(k6_relat_1(X1)),k4_relat_1(sK1))) ) | (~spl2_2 | ~spl2_69)),
% 0.21/0.57    inference(resolution,[],[f539,f63])).
% 0.21/0.57  fof(f539,plain,(
% 0.21/0.57    ( ! [X7] : (~v1_relat_1(X7) | k4_relat_1(k5_relat_1(sK1,X7)) = k5_relat_1(k4_relat_1(X7),k4_relat_1(sK1))) ) | ~spl2_69),
% 0.21/0.57    inference(avatar_component_clause,[],[f538])).
% 0.21/0.57  fof(f540,plain,(
% 0.21/0.57    spl2_69 | ~spl2_1 | ~spl2_54),
% 0.21/0.57    inference(avatar_split_clause,[],[f535,f407,f57,f538])).
% 0.21/0.57  fof(f535,plain,(
% 0.21/0.57    ( ! [X7] : (~v1_relat_1(X7) | k4_relat_1(k5_relat_1(sK1,X7)) = k5_relat_1(k4_relat_1(X7),k4_relat_1(sK1))) ) | (~spl2_1 | ~spl2_54)),
% 0.21/0.57    inference(resolution,[],[f408,f59])).
% 0.21/0.57  fof(f503,plain,(
% 0.21/0.57    spl2_65),
% 0.21/0.57    inference(avatar_split_clause,[],[f54,f501])).
% 0.21/0.57  fof(f54,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 0.21/0.57    inference(definition_unfolding,[],[f50,f46])).
% 0.21/0.57  fof(f46,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f2])).
% 0.21/0.57  fof(f2,axiom,(
% 0.21/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.57  fof(f50,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f29])).
% 0.21/0.57  fof(f29,plain,(
% 0.21/0.57    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.57    inference(ennf_transformation,[],[f13])).
% 0.21/0.57  fof(f13,axiom,(
% 0.21/0.57    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).
% 0.21/0.57  fof(f409,plain,(
% 0.21/0.57    spl2_54),
% 0.21/0.57    inference(avatar_split_clause,[],[f42,f407])).
% 0.21/0.57  fof(f42,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f23])).
% 0.21/0.57  fof(f23,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f10])).
% 0.21/0.57  fof(f10,axiom,(
% 0.21/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).
% 0.21/0.57  fof(f393,plain,(
% 0.21/0.57    spl2_52 | ~spl2_1 | ~spl2_45),
% 0.21/0.57    inference(avatar_split_clause,[],[f389,f324,f57,f391])).
% 0.21/0.57  fof(f324,plain,(
% 0.21/0.57    spl2_45 <=> ! [X1,X0,X2] : (r1_tarski(k5_relat_1(k7_relat_1(X1,X0),X2),k5_relat_1(X1,X2)) | ~v1_relat_1(X2) | ~v1_relat_1(X1))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_45])])).
% 0.21/0.57  fof(f389,plain,(
% 0.21/0.57    ( ! [X10,X11] : (~v1_relat_1(X10) | r1_tarski(k5_relat_1(k7_relat_1(sK1,X11),X10),k5_relat_1(sK1,X10))) ) | (~spl2_1 | ~spl2_45)),
% 0.21/0.57    inference(resolution,[],[f325,f59])).
% 0.21/0.57  fof(f325,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X2) | r1_tarski(k5_relat_1(k7_relat_1(X1,X0),X2),k5_relat_1(X1,X2))) ) | ~spl2_45),
% 0.21/0.57    inference(avatar_component_clause,[],[f324])).
% 0.21/0.57  fof(f355,plain,(
% 0.21/0.57    spl2_48 | ~spl2_1 | ~spl2_41),
% 0.21/0.57    inference(avatar_split_clause,[],[f350,f295,f57,f353])).
% 0.21/0.57  fof(f295,plain,(
% 0.21/0.57    spl2_41 <=> ! [X1,X0] : (k2_relat_1(k7_relat_1(k4_relat_1(X0),X1)) = k9_relat_1(k4_relat_1(X0),X1) | ~v1_relat_1(X0))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_41])])).
% 0.21/0.57  fof(f350,plain,(
% 0.21/0.57    ( ! [X7] : (k2_relat_1(k7_relat_1(k4_relat_1(sK1),X7)) = k9_relat_1(k4_relat_1(sK1),X7)) ) | (~spl2_1 | ~spl2_41)),
% 0.21/0.57    inference(resolution,[],[f296,f59])).
% 0.21/0.57  fof(f296,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~v1_relat_1(X0) | k2_relat_1(k7_relat_1(k4_relat_1(X0),X1)) = k9_relat_1(k4_relat_1(X0),X1)) ) | ~spl2_41),
% 0.21/0.57    inference(avatar_component_clause,[],[f295])).
% 0.21/0.57  fof(f346,plain,(
% 0.21/0.57    spl2_47 | ~spl2_1 | ~spl2_40),
% 0.21/0.57    inference(avatar_split_clause,[],[f341,f291,f57,f344])).
% 0.21/0.57  fof(f291,plain,(
% 0.21/0.57    spl2_40 <=> ! [X1,X0] : (k7_relat_1(k4_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_40])])).
% 0.21/0.57  fof(f341,plain,(
% 0.21/0.57    ( ! [X7] : (k7_relat_1(k4_relat_1(sK1),X7) = k5_relat_1(k6_relat_1(X7),k4_relat_1(sK1))) ) | (~spl2_1 | ~spl2_40)),
% 0.21/0.57    inference(resolution,[],[f292,f59])).
% 0.21/0.57  fof(f292,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~v1_relat_1(X0) | k7_relat_1(k4_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X1),k4_relat_1(X0))) ) | ~spl2_40),
% 0.21/0.57    inference(avatar_component_clause,[],[f291])).
% 0.21/0.57  fof(f326,plain,(
% 0.21/0.57    spl2_45),
% 0.21/0.57    inference(avatar_split_clause,[],[f51,f324])).
% 0.21/0.57  fof(f51,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (r1_tarski(k5_relat_1(k7_relat_1(X1,X0),X2),k5_relat_1(X1,X2)) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f30])).
% 0.21/0.57  fof(f30,plain,(
% 0.21/0.57    ! [X0,X1] : (! [X2] : (r1_tarski(k5_relat_1(k7_relat_1(X1,X0),X2),k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.21/0.57    inference(ennf_transformation,[],[f14])).
% 0.21/0.57  fof(f14,axiom,(
% 0.21/0.57    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => r1_tarski(k5_relat_1(k7_relat_1(X1,X0),X2),k5_relat_1(X1,X2))))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_relat_1)).
% 0.21/0.57  fof(f297,plain,(
% 0.21/0.57    spl2_41 | ~spl2_3 | ~spl2_17),
% 0.21/0.57    inference(avatar_split_clause,[],[f164,f153,f66,f295])).
% 0.21/0.57  fof(f153,plain,(
% 0.21/0.57    spl2_17 <=> ! [X1,X0] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.21/0.57  fof(f164,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(k4_relat_1(X0),X1)) = k9_relat_1(k4_relat_1(X0),X1) | ~v1_relat_1(X0)) ) | (~spl2_3 | ~spl2_17)),
% 0.21/0.57    inference(resolution,[],[f154,f67])).
% 0.21/0.57  fof(f154,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) ) | ~spl2_17),
% 0.21/0.57    inference(avatar_component_clause,[],[f153])).
% 0.21/0.57  fof(f293,plain,(
% 0.21/0.57    spl2_40 | ~spl2_3 | ~spl2_16),
% 0.21/0.57    inference(avatar_split_clause,[],[f156,f149,f66,f291])).
% 0.21/0.57  fof(f149,plain,(
% 0.21/0.57    spl2_16 <=> ! [X1,X0] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.21/0.57  fof(f156,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k7_relat_1(k4_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X0)) ) | (~spl2_3 | ~spl2_16)),
% 0.21/0.57    inference(resolution,[],[f150,f67])).
% 0.21/0.57  fof(f150,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) ) | ~spl2_16),
% 0.21/0.57    inference(avatar_component_clause,[],[f149])).
% 0.21/0.57  fof(f281,plain,(
% 0.21/0.57    spl2_37 | ~spl2_5 | ~spl2_8),
% 0.21/0.57    inference(avatar_split_clause,[],[f103,f94,f74,f279])).
% 0.21/0.57  fof(f94,plain,(
% 0.21/0.57    spl2_8 <=> ! [X0] : (k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.57  fof(f103,plain,(
% 0.21/0.57    ( ! [X2,X3] : (k2_relat_1(k7_relat_1(X2,X3)) = k1_relat_1(k4_relat_1(k7_relat_1(X2,X3))) | ~v1_relat_1(X2)) ) | (~spl2_5 | ~spl2_8)),
% 0.21/0.57    inference(resolution,[],[f95,f75])).
% 0.21/0.57  fof(f95,plain,(
% 0.21/0.57    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) ) | ~spl2_8),
% 0.21/0.57    inference(avatar_component_clause,[],[f94])).
% 0.21/0.57  fof(f256,plain,(
% 0.21/0.57    spl2_34),
% 0.21/0.57    inference(avatar_split_clause,[],[f43,f254])).
% 0.21/0.57  fof(f43,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f25])).
% 0.21/0.57  fof(f25,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.57    inference(flattening,[],[f24])).
% 0.21/0.57  fof(f24,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f8])).
% 0.21/0.57  fof(f8,axiom,(
% 0.21/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).
% 0.21/0.57  fof(f226,plain,(
% 0.21/0.57    spl2_28),
% 0.21/0.57    inference(avatar_split_clause,[],[f53,f224])).
% 0.21/0.57  fof(f53,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.21/0.57    inference(definition_unfolding,[],[f45,f46,f46])).
% 0.21/0.57  fof(f45,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f1])).
% 0.21/0.57  fof(f1,axiom,(
% 0.21/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.57  fof(f196,plain,(
% 0.21/0.57    ~spl2_25),
% 0.21/0.57    inference(avatar_split_clause,[],[f55,f193])).
% 0.21/0.57  fof(f55,plain,(
% 0.21/0.57    ~r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,k1_relat_1(sK1))),k9_relat_1(k4_relat_1(sK1),k9_relat_1(sK1,sK0)))),
% 0.21/0.57    inference(backward_demodulation,[],[f52,f53])).
% 0.21/0.57  fof(f52,plain,(
% 0.21/0.57    ~r1_tarski(k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),sK0)),k9_relat_1(k4_relat_1(sK1),k9_relat_1(sK1,sK0)))),
% 0.21/0.57    inference(definition_unfolding,[],[f34,f46])).
% 0.21/0.57  fof(f34,plain,(
% 0.21/0.57    ~r1_tarski(k3_xboole_0(k1_relat_1(sK1),sK0),k9_relat_1(k4_relat_1(sK1),k9_relat_1(sK1,sK0)))),
% 0.21/0.57    inference(cnf_transformation,[],[f32])).
% 0.21/0.57  fof(f32,plain,(
% 0.21/0.57    ~r1_tarski(k3_xboole_0(k1_relat_1(sK1),sK0),k9_relat_1(k4_relat_1(sK1),k9_relat_1(sK1,sK0))) & v1_relat_1(sK1)),
% 0.21/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f31])).
% 0.21/0.57  fof(f31,plain,(
% 0.21/0.57    ? [X0,X1] : (~r1_tarski(k3_xboole_0(k1_relat_1(X1),X0),k9_relat_1(k4_relat_1(X1),k9_relat_1(X1,X0))) & v1_relat_1(X1)) => (~r1_tarski(k3_xboole_0(k1_relat_1(sK1),sK0),k9_relat_1(k4_relat_1(sK1),k9_relat_1(sK1,sK0))) & v1_relat_1(sK1))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f18,plain,(
% 0.21/0.57    ? [X0,X1] : (~r1_tarski(k3_xboole_0(k1_relat_1(X1),X0),k9_relat_1(k4_relat_1(X1),k9_relat_1(X1,X0))) & v1_relat_1(X1))),
% 0.21/0.57    inference(ennf_transformation,[],[f17])).
% 0.21/0.57  fof(f17,negated_conjecture,(
% 0.21/0.57    ~! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k3_xboole_0(k1_relat_1(X1),X0),k9_relat_1(k4_relat_1(X1),k9_relat_1(X1,X0))))),
% 0.21/0.57    inference(negated_conjecture,[],[f16])).
% 0.21/0.57  fof(f16,conjecture,(
% 0.21/0.57    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k3_xboole_0(k1_relat_1(X1),X0),k9_relat_1(k4_relat_1(X1),k9_relat_1(X1,X0))))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t163_relat_1)).
% 0.21/0.57  fof(f171,plain,(
% 0.21/0.57    spl2_19 | ~spl2_1 | ~spl2_17),
% 0.21/0.57    inference(avatar_split_clause,[],[f167,f153,f57,f169])).
% 0.21/0.57  fof(f167,plain,(
% 0.21/0.57    ( ! [X7] : (k2_relat_1(k7_relat_1(sK1,X7)) = k9_relat_1(sK1,X7)) ) | (~spl2_1 | ~spl2_17)),
% 0.21/0.57    inference(resolution,[],[f154,f59])).
% 0.21/0.57  fof(f155,plain,(
% 0.21/0.57    spl2_17),
% 0.21/0.57    inference(avatar_split_clause,[],[f49,f153])).
% 0.21/0.57  fof(f49,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f28])).
% 0.21/0.57  fof(f28,plain,(
% 0.21/0.57    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.57    inference(ennf_transformation,[],[f7])).
% 0.21/0.57  fof(f7,axiom,(
% 0.21/0.57    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.21/0.57  fof(f151,plain,(
% 0.21/0.57    spl2_16),
% 0.21/0.57    inference(avatar_split_clause,[],[f48,f149])).
% 0.21/0.57  fof(f48,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f27])).
% 0.21/0.57  fof(f27,plain,(
% 0.21/0.57    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.21/0.57    inference(ennf_transformation,[],[f15])).
% 0.21/0.57  fof(f15,axiom,(
% 0.21/0.57    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 0.21/0.57  fof(f137,plain,(
% 0.21/0.57    spl2_14 | ~spl2_1 | ~spl2_12),
% 0.21/0.57    inference(avatar_split_clause,[],[f132,f121,f57,f134])).
% 0.21/0.57  fof(f132,plain,(
% 0.21/0.57    sK1 = k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1))) | (~spl2_1 | ~spl2_12)),
% 0.21/0.57    inference(resolution,[],[f122,f59])).
% 0.21/0.57  fof(f123,plain,(
% 0.21/0.57    spl2_12),
% 0.21/0.57    inference(avatar_split_clause,[],[f39,f121])).
% 0.21/0.57  fof(f39,plain,(
% 0.21/0.57    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f21])).
% 0.21/0.57  fof(f21,plain,(
% 0.21/0.57    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f12])).
% 0.21/0.57  fof(f12,axiom,(
% 0.21/0.57    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).
% 0.21/0.57  fof(f96,plain,(
% 0.21/0.57    spl2_8),
% 0.21/0.57    inference(avatar_split_clause,[],[f40,f94])).
% 0.21/0.57  fof(f40,plain,(
% 0.21/0.57    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f22])).
% 0.21/0.57  fof(f22,plain,(
% 0.21/0.57    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f9])).
% 0.21/0.57  fof(f9,axiom,(
% 0.21/0.57    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).
% 0.21/0.57  fof(f91,plain,(
% 0.21/0.57    spl2_7 | ~spl2_1 | ~spl2_6),
% 0.21/0.57    inference(avatar_split_clause,[],[f85,f79,f57,f88])).
% 0.21/0.57  fof(f79,plain,(
% 0.21/0.57    spl2_6 <=> ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.57  fof(f85,plain,(
% 0.21/0.57    sK1 = k4_relat_1(k4_relat_1(sK1)) | (~spl2_1 | ~spl2_6)),
% 0.21/0.57    inference(resolution,[],[f80,f59])).
% 0.21/0.57  fof(f80,plain,(
% 0.21/0.57    ( ! [X0] : (~v1_relat_1(X0) | k4_relat_1(k4_relat_1(X0)) = X0) ) | ~spl2_6),
% 0.21/0.57    inference(avatar_component_clause,[],[f79])).
% 0.21/0.57  fof(f81,plain,(
% 0.21/0.57    spl2_6),
% 0.21/0.57    inference(avatar_split_clause,[],[f38,f79])).
% 0.21/0.57  fof(f38,plain,(
% 0.21/0.57    ( ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f20])).
% 0.21/0.57  fof(f20,plain,(
% 0.21/0.57    ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f6])).
% 0.21/0.57  fof(f6,axiom,(
% 0.21/0.57    ! [X0] : (v1_relat_1(X0) => k4_relat_1(k4_relat_1(X0)) = X0)),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).
% 0.21/0.57  fof(f76,plain,(
% 0.21/0.57    spl2_5),
% 0.21/0.57    inference(avatar_split_clause,[],[f47,f74])).
% 0.21/0.57  fof(f47,plain,(
% 0.21/0.57    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f26])).
% 0.21/0.57  fof(f26,plain,(
% 0.21/0.57    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f5])).
% 0.21/0.57  fof(f5,axiom,(
% 0.21/0.57    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.21/0.57  fof(f72,plain,(
% 0.21/0.57    spl2_4),
% 0.21/0.57    inference(avatar_split_clause,[],[f36,f70])).
% 0.21/0.57  fof(f36,plain,(
% 0.21/0.57    ( ! [X0] : (k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f11])).
% 0.21/0.57  fof(f11,axiom,(
% 0.21/0.57    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_relat_1)).
% 0.21/0.57  fof(f68,plain,(
% 0.21/0.57    spl2_3),
% 0.21/0.57    inference(avatar_split_clause,[],[f37,f66])).
% 0.21/0.57  fof(f37,plain,(
% 0.21/0.57    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f19])).
% 0.21/0.57  fof(f19,plain,(
% 0.21/0.57    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f3])).
% 0.21/0.57  fof(f3,axiom,(
% 0.21/0.57    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 0.21/0.57  fof(f64,plain,(
% 0.21/0.57    spl2_2),
% 0.21/0.57    inference(avatar_split_clause,[],[f35,f62])).
% 0.21/0.57  fof(f35,plain,(
% 0.21/0.57    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f4])).
% 0.21/0.57  fof(f4,axiom,(
% 0.21/0.57    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.21/0.57  fof(f60,plain,(
% 0.21/0.57    spl2_1),
% 0.21/0.57    inference(avatar_split_clause,[],[f33,f57])).
% 0.21/0.57  fof(f33,plain,(
% 0.21/0.57    v1_relat_1(sK1)),
% 0.21/0.57    inference(cnf_transformation,[],[f32])).
% 0.21/0.57  % SZS output end Proof for theBenchmark
% 0.21/0.57  % (28897)------------------------------
% 0.21/0.57  % (28897)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (28897)Termination reason: Refutation
% 0.21/0.57  
% 0.21/0.57  % (28897)Memory used [KB]: 7675
% 0.21/0.57  % (28897)Time elapsed: 0.118 s
% 0.21/0.57  % (28897)------------------------------
% 0.21/0.57  % (28897)------------------------------
% 0.21/0.58  % (28889)Success in time 0.219 s
%------------------------------------------------------------------------------
