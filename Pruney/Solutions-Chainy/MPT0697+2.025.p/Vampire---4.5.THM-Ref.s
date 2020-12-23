%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:09 EST 2020

% Result     : Theorem 3.74s
% Output     : Refutation 3.74s
% Verified   : 
% Statistics : Number of formulae       :  210 ( 358 expanded)
%              Number of leaves         :   54 ( 169 expanded)
%              Depth                    :    7
%              Number of atoms          :  574 ( 968 expanded)
%              Number of equality atoms :   81 ( 140 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11543,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f83,f88,f93,f105,f109,f114,f119,f123,f135,f139,f143,f152,f178,f191,f205,f212,f435,f473,f540,f628,f716,f857,f876,f1004,f1330,f1624,f1800,f1805,f1862,f2000,f2205,f2355,f3232,f3514,f5158,f6759,f11427,f11472,f11506])).

fof(f11506,plain,
    ( ~ spl3_10
    | spl3_18
    | ~ spl3_244 ),
    inference(avatar_contradiction_clause,[],[f11500])).

fof(f11500,plain,
    ( $false
    | ~ spl3_10
    | spl3_18
    | ~ spl3_244 ),
    inference(subsumption_resolution,[],[f177,f11474])).

fof(f11474,plain,
    ( ! [X1] : k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X1)),X1)
    | ~ spl3_10
    | ~ spl3_244 ),
    inference(resolution,[],[f11471,f122])).

fof(f122,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_xboole_0)
        | k1_xboole_0 = X0 )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl3_10
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_xboole_0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f11471,plain,
    ( ! [X11] : r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X11)),X11),k1_xboole_0)
    | ~ spl3_244 ),
    inference(avatar_component_clause,[],[f11470])).

fof(f11470,plain,
    ( spl3_244
  <=> ! [X11] : r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X11)),X11),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_244])])).

fof(f177,plain,
    ( k1_xboole_0 != k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)
    | spl3_18 ),
    inference(avatar_component_clause,[],[f175])).

fof(f175,plain,
    ( spl3_18
  <=> k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f11472,plain,
    ( spl3_244
    | ~ spl3_96
    | ~ spl3_116
    | ~ spl3_155
    | ~ spl3_241 ),
    inference(avatar_split_clause,[],[f11468,f11425,f3511,f2203,f1860,f11470])).

fof(f1860,plain,
    ( spl3_96
  <=> ! [X32,X33] : r1_tarski(k6_subset_1(k10_relat_1(sK1,X32),X33),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_96])])).

fof(f2203,plain,
    ( spl3_116
  <=> ! [X0] :
        ( ~ r1_tarski(X0,k1_relat_1(sK1))
        | r1_tarski(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_116])])).

fof(f3511,plain,
    ( spl3_155
  <=> k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_155])])).

fof(f11425,plain,
    ( spl3_241
  <=> ! [X0] : k1_xboole_0 = k9_relat_1(sK1,k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_241])])).

fof(f11468,plain,
    ( ! [X11] : r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X11)),X11),k1_xboole_0)
    | ~ spl3_96
    | ~ spl3_116
    | ~ spl3_155
    | ~ spl3_241 ),
    inference(forward_demodulation,[],[f11467,f3513])).

fof(f3513,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0)
    | ~ spl3_155 ),
    inference(avatar_component_clause,[],[f3511])).

fof(f11467,plain,
    ( ! [X11] : r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X11)),X11),k10_relat_1(sK1,k1_xboole_0))
    | ~ spl3_96
    | ~ spl3_116
    | ~ spl3_241 ),
    inference(subsumption_resolution,[],[f11451,f1861])).

fof(f1861,plain,
    ( ! [X33,X32] : r1_tarski(k6_subset_1(k10_relat_1(sK1,X32),X33),k1_relat_1(sK1))
    | ~ spl3_96 ),
    inference(avatar_component_clause,[],[f1860])).

fof(f11451,plain,
    ( ! [X11] :
        ( r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X11)),X11),k10_relat_1(sK1,k1_xboole_0))
        | ~ r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X11)),X11),k1_relat_1(sK1)) )
    | ~ spl3_116
    | ~ spl3_241 ),
    inference(superposition,[],[f2204,f11426])).

fof(f11426,plain,
    ( ! [X0] : k1_xboole_0 = k9_relat_1(sK1,k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0))
    | ~ spl3_241 ),
    inference(avatar_component_clause,[],[f11425])).

fof(f2204,plain,
    ( ! [X0] :
        ( r1_tarski(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0)))
        | ~ r1_tarski(X0,k1_relat_1(sK1)) )
    | ~ spl3_116 ),
    inference(avatar_component_clause,[],[f2203])).

fof(f11427,plain,
    ( spl3_241
    | ~ spl3_58
    | ~ spl3_229 ),
    inference(avatar_split_clause,[],[f11098,f6757,f874,f11425])).

fof(f874,plain,
    ( spl3_58
  <=> ! [X5] : k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X5)),X5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_58])])).

fof(f6757,plain,
    ( spl3_229
  <=> ! [X1,X0] : k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_229])])).

fof(f11098,plain,
    ( ! [X0] : k1_xboole_0 = k9_relat_1(sK1,k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0))
    | ~ spl3_58
    | ~ spl3_229 ),
    inference(superposition,[],[f6758,f875])).

fof(f875,plain,
    ( ! [X5] : k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X5)),X5)
    | ~ spl3_58 ),
    inference(avatar_component_clause,[],[f874])).

fof(f6758,plain,
    ( ! [X0,X1] : k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))
    | ~ spl3_229 ),
    inference(avatar_component_clause,[],[f6757])).

fof(f6759,plain,
    ( spl3_229
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_196 ),
    inference(avatar_split_clause,[],[f5238,f5156,f90,f85,f80,f6757])).

fof(f80,plain,
    ( spl3_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f85,plain,
    ( spl3_2
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f90,plain,
    ( spl3_3
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f5156,plain,
    ( spl3_196
  <=> ! [X1,X0,X2] :
        ( k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
        | ~ v2_funct_1(X2)
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_196])])).

fof(f5238,plain,
    ( ! [X0,X1] : k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_196 ),
    inference(subsumption_resolution,[],[f5237,f82])).

fof(f82,plain,
    ( v1_relat_1(sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f80])).

fof(f5237,plain,
    ( ! [X0,X1] :
        ( k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))
        | ~ v1_relat_1(sK1) )
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_196 ),
    inference(subsumption_resolution,[],[f5236,f87])).

fof(f87,plain,
    ( v1_funct_1(sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f85])).

fof(f5236,plain,
    ( ! [X0,X1] :
        ( k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl3_3
    | ~ spl3_196 ),
    inference(resolution,[],[f5157,f92])).

fof(f92,plain,
    ( v2_funct_1(sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f90])).

fof(f5157,plain,
    ( ! [X2,X0,X1] :
        ( ~ v2_funct_1(X2)
        | k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
    | ~ spl3_196 ),
    inference(avatar_component_clause,[],[f5156])).

fof(f5158,plain,(
    spl3_196 ),
    inference(avatar_split_clause,[],[f67,f5156])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( v2_funct_1(X2)
       => k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_funct_1)).

fof(f3514,plain,
    ( spl3_155
    | ~ spl3_8
    | ~ spl3_15
    | ~ spl3_153 ),
    inference(avatar_split_clause,[],[f3316,f3230,f150,f112,f3511])).

fof(f112,plain,
    ( spl3_8
  <=> ! [X0] : r1_tarski(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f150,plain,
    ( spl3_15
  <=> ! [X2] : k1_xboole_0 = k6_subset_1(X2,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f3230,plain,
    ( spl3_153
  <=> ! [X9,X8] :
        ( k1_xboole_0 = k10_relat_1(sK1,k6_subset_1(X8,X9))
        | ~ r1_tarski(X8,X9) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_153])])).

fof(f3316,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0)
    | ~ spl3_8
    | ~ spl3_15
    | ~ spl3_153 ),
    inference(forward_demodulation,[],[f3233,f151])).

fof(f151,plain,
    ( ! [X2] : k1_xboole_0 = k6_subset_1(X2,X2)
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f150])).

fof(f3233,plain,
    ( ! [X0] : k1_xboole_0 = k10_relat_1(sK1,k6_subset_1(X0,X0))
    | ~ spl3_8
    | ~ spl3_153 ),
    inference(resolution,[],[f3231,f113])).

fof(f113,plain,
    ( ! [X0] : r1_tarski(X0,X0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f112])).

fof(f3231,plain,
    ( ! [X8,X9] :
        ( ~ r1_tarski(X8,X9)
        | k1_xboole_0 = k10_relat_1(sK1,k6_subset_1(X8,X9)) )
    | ~ spl3_153 ),
    inference(avatar_component_clause,[],[f3230])).

fof(f3232,plain,
    ( spl3_153
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_108
    | ~ spl3_125 ),
    inference(avatar_split_clause,[],[f3212,f2353,f1998,f85,f80,f3230])).

fof(f1998,plain,
    ( spl3_108
  <=> ! [X1,X0,X2] :
        ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_108])])).

fof(f2353,plain,
    ( spl3_125
  <=> ! [X9,X8] :
        ( ~ r1_tarski(X8,X9)
        | k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,X8),k10_relat_1(sK1,X9)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_125])])).

fof(f3212,plain,
    ( ! [X8,X9] :
        ( k1_xboole_0 = k10_relat_1(sK1,k6_subset_1(X8,X9))
        | ~ r1_tarski(X8,X9) )
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_108
    | ~ spl3_125 ),
    inference(backward_demodulation,[],[f2354,f3211])).

fof(f3211,plain,
    ( ! [X0,X1] : k10_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_108 ),
    inference(subsumption_resolution,[],[f3210,f82])).

fof(f3210,plain,
    ( ! [X0,X1] :
        ( k10_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1))
        | ~ v1_relat_1(sK1) )
    | ~ spl3_2
    | ~ spl3_108 ),
    inference(resolution,[],[f1999,f87])).

fof(f1999,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_1(X2)
        | k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
        | ~ v1_relat_1(X2) )
    | ~ spl3_108 ),
    inference(avatar_component_clause,[],[f1998])).

fof(f2354,plain,
    ( ! [X8,X9] :
        ( ~ r1_tarski(X8,X9)
        | k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,X8),k10_relat_1(sK1,X9)) )
    | ~ spl3_125 ),
    inference(avatar_component_clause,[],[f2353])).

fof(f2355,plain,
    ( spl3_125
    | ~ spl3_13
    | ~ spl3_76 ),
    inference(avatar_split_clause,[],[f1334,f1328,f137,f2353])).

fof(f137,plain,
    ( spl3_13
  <=> ! [X1,X0] :
        ( k1_xboole_0 = k6_subset_1(X0,X1)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f1328,plain,
    ( spl3_76
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,X1)
        | r1_tarski(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_76])])).

fof(f1334,plain,
    ( ! [X8,X9] :
        ( ~ r1_tarski(X8,X9)
        | k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,X8),k10_relat_1(sK1,X9)) )
    | ~ spl3_13
    | ~ spl3_76 ),
    inference(resolution,[],[f1329,f138])).

fof(f138,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k1_xboole_0 = k6_subset_1(X0,X1) )
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f137])).

fof(f1329,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1))
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_76 ),
    inference(avatar_component_clause,[],[f1328])).

fof(f2205,plain,
    ( spl3_116
    | ~ spl3_1
    | ~ spl3_87 ),
    inference(avatar_split_clause,[],[f1863,f1622,f80,f2203])).

fof(f1622,plain,
    ( spl3_87
  <=> ! [X1,X0] :
        ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
        | ~ r1_tarski(X0,k1_relat_1(X1))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_87])])).

fof(f1863,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_relat_1(sK1))
        | r1_tarski(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0))) )
    | ~ spl3_1
    | ~ spl3_87 ),
    inference(resolution,[],[f1623,f82])).

fof(f1623,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | ~ r1_tarski(X0,k1_relat_1(X1))
        | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) )
    | ~ spl3_87 ),
    inference(avatar_component_clause,[],[f1622])).

fof(f2000,plain,(
    spl3_108 ),
    inference(avatar_split_clause,[],[f66,f1998])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_funct_1)).

fof(f1862,plain,
    ( spl3_96
    | ~ spl3_37
    | ~ spl3_49
    | ~ spl3_93 ),
    inference(avatar_split_clause,[],[f1837,f1803,f714,f471,f1860])).

fof(f471,plain,
    ( spl3_37
  <=> ! [X9] : k2_xboole_0(X9,k1_xboole_0) = X9 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).

fof(f714,plain,
    ( spl3_49
  <=> ! [X3,X2,X4] : r1_tarski(k6_subset_1(X2,X3),k2_xboole_0(X4,k6_subset_1(X2,X4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).

fof(f1803,plain,
    ( spl3_93
  <=> ! [X0] : k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,X0),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_93])])).

fof(f1837,plain,
    ( ! [X33,X32] : r1_tarski(k6_subset_1(k10_relat_1(sK1,X32),X33),k1_relat_1(sK1))
    | ~ spl3_37
    | ~ spl3_49
    | ~ spl3_93 ),
    inference(forward_demodulation,[],[f1822,f472])).

fof(f472,plain,
    ( ! [X9] : k2_xboole_0(X9,k1_xboole_0) = X9
    | ~ spl3_37 ),
    inference(avatar_component_clause,[],[f471])).

fof(f1822,plain,
    ( ! [X33,X32] : r1_tarski(k6_subset_1(k10_relat_1(sK1,X32),X33),k2_xboole_0(k1_relat_1(sK1),k1_xboole_0))
    | ~ spl3_49
    | ~ spl3_93 ),
    inference(superposition,[],[f715,f1804])).

fof(f1804,plain,
    ( ! [X0] : k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,X0),k1_relat_1(sK1))
    | ~ spl3_93 ),
    inference(avatar_component_clause,[],[f1803])).

fof(f715,plain,
    ( ! [X4,X2,X3] : r1_tarski(k6_subset_1(X2,X3),k2_xboole_0(X4,k6_subset_1(X2,X4)))
    | ~ spl3_49 ),
    inference(avatar_component_clause,[],[f714])).

fof(f1805,plain,
    ( spl3_93
    | ~ spl3_1
    | ~ spl3_92 ),
    inference(avatar_split_clause,[],[f1801,f1798,f80,f1803])).

fof(f1798,plain,
    ( spl3_92
  <=> ! [X7,X6] :
        ( k1_xboole_0 = k6_subset_1(k10_relat_1(X6,X7),k1_relat_1(X6))
        | ~ v1_relat_1(X6) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_92])])).

fof(f1801,plain,
    ( ! [X0] : k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,X0),k1_relat_1(sK1))
    | ~ spl3_1
    | ~ spl3_92 ),
    inference(resolution,[],[f1799,f82])).

fof(f1799,plain,
    ( ! [X6,X7] :
        ( ~ v1_relat_1(X6)
        | k1_xboole_0 = k6_subset_1(k10_relat_1(X6,X7),k1_relat_1(X6)) )
    | ~ spl3_92 ),
    inference(avatar_component_clause,[],[f1798])).

fof(f1800,plain,
    ( spl3_92
    | ~ spl3_12
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f148,f137,f133,f1798])).

fof(f133,plain,
    ( spl3_12
  <=> ! [X1,X0] :
        ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f148,plain,
    ( ! [X6,X7] :
        ( k1_xboole_0 = k6_subset_1(k10_relat_1(X6,X7),k1_relat_1(X6))
        | ~ v1_relat_1(X6) )
    | ~ spl3_12
    | ~ spl3_13 ),
    inference(resolution,[],[f138,f134])).

fof(f134,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
        | ~ v1_relat_1(X1) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f133])).

fof(f1624,plain,(
    spl3_87 ),
    inference(avatar_split_clause,[],[f58,f1622])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

fof(f1330,plain,
    ( spl3_76
    | ~ spl3_1
    | ~ spl3_66 ),
    inference(avatar_split_clause,[],[f1326,f1002,f80,f1328])).

fof(f1002,plain,
    ( spl3_66
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_66])])).

fof(f1326,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | r1_tarski(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1)) )
    | ~ spl3_1
    | ~ spl3_66 ),
    inference(resolution,[],[f1003,f82])).

fof(f1003,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X2)
        | ~ r1_tarski(X0,X1)
        | r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
    | ~ spl3_66 ),
    inference(avatar_component_clause,[],[f1002])).

fof(f1004,plain,(
    spl3_66 ),
    inference(avatar_split_clause,[],[f63,f1002])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_relat_1)).

fof(f876,plain,
    ( spl3_58
    | ~ spl3_13
    | ~ spl3_55 ),
    inference(avatar_split_clause,[],[f862,f855,f137,f874])).

fof(f855,plain,
    ( spl3_55
  <=> ! [X0] : r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_55])])).

fof(f862,plain,
    ( ! [X5] : k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X5)),X5)
    | ~ spl3_13
    | ~ spl3_55 ),
    inference(resolution,[],[f856,f138])).

fof(f856,plain,
    ( ! [X0] : r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0)
    | ~ spl3_55 ),
    inference(avatar_component_clause,[],[f855])).

fof(f857,plain,
    ( spl3_55
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_44 ),
    inference(avatar_split_clause,[],[f853,f626,f85,f80,f855])).

fof(f626,plain,
    ( spl3_44
  <=> ! [X1,X0] :
        ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).

fof(f853,plain,
    ( ! [X0] : r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_44 ),
    inference(subsumption_resolution,[],[f852,f82])).

fof(f852,plain,
    ( ! [X0] :
        ( r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0)
        | ~ v1_relat_1(sK1) )
    | ~ spl3_2
    | ~ spl3_44 ),
    inference(resolution,[],[f627,f87])).

fof(f627,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_1(X1)
        | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
        | ~ v1_relat_1(X1) )
    | ~ spl3_44 ),
    inference(avatar_component_clause,[],[f626])).

fof(f716,plain,
    ( spl3_49
    | ~ spl3_22
    | ~ spl3_39 ),
    inference(avatar_split_clause,[],[f546,f538,f203,f714])).

fof(f203,plain,
    ( spl3_22
  <=> ! [X11,X10,X12] :
        ( ~ r1_tarski(X10,X11)
        | r1_tarski(k6_subset_1(X10,X12),X11) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f538,plain,
    ( spl3_39
  <=> ! [X36,X35] : r1_tarski(X35,k2_xboole_0(X36,k6_subset_1(X35,X36))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).

fof(f546,plain,
    ( ! [X4,X2,X3] : r1_tarski(k6_subset_1(X2,X3),k2_xboole_0(X4,k6_subset_1(X2,X4)))
    | ~ spl3_22
    | ~ spl3_39 ),
    inference(resolution,[],[f539,f204])).

fof(f204,plain,
    ( ! [X12,X10,X11] :
        ( ~ r1_tarski(X10,X11)
        | r1_tarski(k6_subset_1(X10,X12),X11) )
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f203])).

fof(f539,plain,
    ( ! [X35,X36] : r1_tarski(X35,k2_xboole_0(X36,k6_subset_1(X35,X36)))
    | ~ spl3_39 ),
    inference(avatar_component_clause,[],[f538])).

fof(f628,plain,(
    spl3_44 ),
    inference(avatar_split_clause,[],[f60,f626])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

fof(f540,plain,
    ( spl3_39
    | ~ spl3_8
    | ~ spl3_35 ),
    inference(avatar_split_clause,[],[f514,f433,f112,f538])).

fof(f433,plain,
    ( spl3_35
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,k2_xboole_0(X1,X2))
        | ~ r1_tarski(k6_subset_1(X0,X1),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).

fof(f514,plain,
    ( ! [X35,X36] : r1_tarski(X35,k2_xboole_0(X36,k6_subset_1(X35,X36)))
    | ~ spl3_8
    | ~ spl3_35 ),
    inference(resolution,[],[f434,f113])).

fof(f434,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(k6_subset_1(X0,X1),X2)
        | r1_tarski(X0,k2_xboole_0(X1,X2)) )
    | ~ spl3_35 ),
    inference(avatar_component_clause,[],[f433])).

fof(f473,plain,
    ( spl3_37
    | ~ spl3_8
    | ~ spl3_15
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f449,f210,f150,f112,f471])).

fof(f210,plain,
    ( spl3_23
  <=> ! [X1,X0] :
        ( k2_xboole_0(X0,k6_subset_1(X1,X0)) = X1
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f449,plain,
    ( ! [X9] : k2_xboole_0(X9,k1_xboole_0) = X9
    | ~ spl3_8
    | ~ spl3_15
    | ~ spl3_23 ),
    inference(forward_demodulation,[],[f439,f151])).

fof(f439,plain,
    ( ! [X9] : k2_xboole_0(X9,k6_subset_1(X9,X9)) = X9
    | ~ spl3_8
    | ~ spl3_23 ),
    inference(resolution,[],[f211,f113])).

fof(f211,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k2_xboole_0(X0,k6_subset_1(X1,X0)) = X1 )
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f210])).

fof(f435,plain,(
    spl3_35 ),
    inference(avatar_split_clause,[],[f78,f433])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k6_subset_1(X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f65,f56])).

fof(f56,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f212,plain,(
    spl3_23 ),
    inference(avatar_split_clause,[],[f74,f210])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k6_subset_1(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f59,f56])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).

fof(f205,plain,
    ( spl3_22
    | ~ spl3_7
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f196,f189,f107,f203])).

fof(f107,plain,
    ( spl3_7
  <=> ! [X1,X0] : r1_tarski(k6_subset_1(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f189,plain,
    ( spl3_20
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,X2)
        | ~ r1_tarski(X1,X2)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f196,plain,
    ( ! [X12,X10,X11] :
        ( ~ r1_tarski(X10,X11)
        | r1_tarski(k6_subset_1(X10,X12),X11) )
    | ~ spl3_7
    | ~ spl3_20 ),
    inference(resolution,[],[f190,f108])).

fof(f108,plain,
    ( ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f107])).

fof(f190,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ r1_tarski(X1,X2)
        | r1_tarski(X0,X2) )
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f189])).

fof(f191,plain,(
    spl3_20 ),
    inference(avatar_split_clause,[],[f68,f189])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f178,plain,
    ( ~ spl3_18
    | spl3_9
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f171,f141,f116,f175])).

fof(f116,plain,
    ( spl3_9
  <=> r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f141,plain,
    ( spl3_14
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | k1_xboole_0 != k6_subset_1(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f171,plain,
    ( k1_xboole_0 != k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)
    | spl3_9
    | ~ spl3_14 ),
    inference(resolution,[],[f142,f118])).

fof(f118,plain,
    ( ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)
    | spl3_9 ),
    inference(avatar_component_clause,[],[f116])).

fof(f142,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X0,X1)
        | k1_xboole_0 != k6_subset_1(X0,X1) )
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f141])).

fof(f152,plain,
    ( spl3_15
    | ~ spl3_8
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f145,f137,f112,f150])).

fof(f145,plain,
    ( ! [X2] : k1_xboole_0 = k6_subset_1(X2,X2)
    | ~ spl3_8
    | ~ spl3_13 ),
    inference(resolution,[],[f138,f113])).

fof(f143,plain,(
    spl3_14 ),
    inference(avatar_split_clause,[],[f76,f141])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k6_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f61,f56])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f139,plain,(
    spl3_13 ),
    inference(avatar_split_clause,[],[f75,f137])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k6_subset_1(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f62,f56])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f135,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f57,f133])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

fof(f123,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f53,f121])).

fof(f53,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f119,plain,(
    ~ spl3_9 ),
    inference(avatar_split_clause,[],[f50,f116])).

fof(f50,plain,(
    ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,
    ( ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)
    & v2_funct_1(sK1)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f42])).

fof(f42,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
        & v2_funct_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)
      & v2_funct_1(sK1)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( v2_funct_1(X1)
         => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_funct_1)).

fof(f114,plain,
    ( spl3_8
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f110,f107,f103,f112])).

fof(f103,plain,
    ( spl3_6
  <=> ! [X0] : k6_subset_1(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f110,plain,
    ( ! [X0] : r1_tarski(X0,X0)
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(superposition,[],[f108,f104])).

fof(f104,plain,
    ( ! [X0] : k6_subset_1(X0,k1_xboole_0) = X0
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f103])).

fof(f109,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f73,f107])).

fof(f73,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(definition_unfolding,[],[f55,f56])).

fof(f55,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f105,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f72,f103])).

fof(f72,plain,(
    ! [X0] : k6_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f52,f56])).

fof(f52,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f93,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f49,f90])).

fof(f49,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f88,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f48,f85])).

fof(f48,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f83,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f47,f80])).

fof(f47,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f43])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:19:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.43  % (26399)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.45  % (26396)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.47  % (26401)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.47  % (26410)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.47  % (26406)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.48  % (26402)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.48  % (26409)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.48  % (26400)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.49  % (26405)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.50  % (26408)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.50  % (26395)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.51  % (26397)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 1.24/0.51  % (26398)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 1.24/0.51  % (26411)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 1.24/0.52  % (26404)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 1.24/0.52  % (26403)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 1.24/0.52  % (26413)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 1.24/0.52  % (26414)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 3.74/0.86  % (26402)Refutation found. Thanks to Tanya!
% 3.74/0.86  % SZS status Theorem for theBenchmark
% 3.74/0.86  % SZS output start Proof for theBenchmark
% 3.74/0.86  fof(f11543,plain,(
% 3.74/0.86    $false),
% 3.74/0.86    inference(avatar_sat_refutation,[],[f83,f88,f93,f105,f109,f114,f119,f123,f135,f139,f143,f152,f178,f191,f205,f212,f435,f473,f540,f628,f716,f857,f876,f1004,f1330,f1624,f1800,f1805,f1862,f2000,f2205,f2355,f3232,f3514,f5158,f6759,f11427,f11472,f11506])).
% 3.74/0.86  fof(f11506,plain,(
% 3.74/0.86    ~spl3_10 | spl3_18 | ~spl3_244),
% 3.74/0.86    inference(avatar_contradiction_clause,[],[f11500])).
% 3.74/0.86  fof(f11500,plain,(
% 3.74/0.86    $false | (~spl3_10 | spl3_18 | ~spl3_244)),
% 3.74/0.86    inference(subsumption_resolution,[],[f177,f11474])).
% 3.74/0.86  fof(f11474,plain,(
% 3.74/0.86    ( ! [X1] : (k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X1)),X1)) ) | (~spl3_10 | ~spl3_244)),
% 3.74/0.86    inference(resolution,[],[f11471,f122])).
% 3.74/0.86  fof(f122,plain,(
% 3.74/0.86    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) ) | ~spl3_10),
% 3.74/0.86    inference(avatar_component_clause,[],[f121])).
% 3.74/0.86  fof(f121,plain,(
% 3.74/0.86    spl3_10 <=> ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 3.74/0.86    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 3.74/0.86  fof(f11471,plain,(
% 3.74/0.86    ( ! [X11] : (r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X11)),X11),k1_xboole_0)) ) | ~spl3_244),
% 3.74/0.86    inference(avatar_component_clause,[],[f11470])).
% 3.74/0.86  fof(f11470,plain,(
% 3.74/0.86    spl3_244 <=> ! [X11] : r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X11)),X11),k1_xboole_0)),
% 3.74/0.86    introduced(avatar_definition,[new_symbols(naming,[spl3_244])])).
% 3.74/0.86  fof(f177,plain,(
% 3.74/0.86    k1_xboole_0 != k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) | spl3_18),
% 3.74/0.86    inference(avatar_component_clause,[],[f175])).
% 3.74/0.86  fof(f175,plain,(
% 3.74/0.86    spl3_18 <=> k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)),
% 3.74/0.86    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 3.74/0.86  fof(f11472,plain,(
% 3.74/0.86    spl3_244 | ~spl3_96 | ~spl3_116 | ~spl3_155 | ~spl3_241),
% 3.74/0.86    inference(avatar_split_clause,[],[f11468,f11425,f3511,f2203,f1860,f11470])).
% 3.74/0.86  fof(f1860,plain,(
% 3.74/0.86    spl3_96 <=> ! [X32,X33] : r1_tarski(k6_subset_1(k10_relat_1(sK1,X32),X33),k1_relat_1(sK1))),
% 3.74/0.86    introduced(avatar_definition,[new_symbols(naming,[spl3_96])])).
% 3.74/0.86  fof(f2203,plain,(
% 3.74/0.86    spl3_116 <=> ! [X0] : (~r1_tarski(X0,k1_relat_1(sK1)) | r1_tarski(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0))))),
% 3.74/0.86    introduced(avatar_definition,[new_symbols(naming,[spl3_116])])).
% 3.74/0.86  fof(f3511,plain,(
% 3.74/0.86    spl3_155 <=> k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0)),
% 3.74/0.86    introduced(avatar_definition,[new_symbols(naming,[spl3_155])])).
% 3.74/0.86  fof(f11425,plain,(
% 3.74/0.86    spl3_241 <=> ! [X0] : k1_xboole_0 = k9_relat_1(sK1,k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0))),
% 3.74/0.86    introduced(avatar_definition,[new_symbols(naming,[spl3_241])])).
% 3.74/0.86  fof(f11468,plain,(
% 3.74/0.86    ( ! [X11] : (r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X11)),X11),k1_xboole_0)) ) | (~spl3_96 | ~spl3_116 | ~spl3_155 | ~spl3_241)),
% 3.74/0.86    inference(forward_demodulation,[],[f11467,f3513])).
% 3.74/0.86  fof(f3513,plain,(
% 3.74/0.86    k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0) | ~spl3_155),
% 3.74/0.86    inference(avatar_component_clause,[],[f3511])).
% 3.74/0.86  fof(f11467,plain,(
% 3.74/0.86    ( ! [X11] : (r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X11)),X11),k10_relat_1(sK1,k1_xboole_0))) ) | (~spl3_96 | ~spl3_116 | ~spl3_241)),
% 3.74/0.86    inference(subsumption_resolution,[],[f11451,f1861])).
% 3.74/0.86  fof(f1861,plain,(
% 3.74/0.86    ( ! [X33,X32] : (r1_tarski(k6_subset_1(k10_relat_1(sK1,X32),X33),k1_relat_1(sK1))) ) | ~spl3_96),
% 3.74/0.86    inference(avatar_component_clause,[],[f1860])).
% 3.74/0.86  fof(f11451,plain,(
% 3.74/0.86    ( ! [X11] : (r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X11)),X11),k10_relat_1(sK1,k1_xboole_0)) | ~r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X11)),X11),k1_relat_1(sK1))) ) | (~spl3_116 | ~spl3_241)),
% 3.74/0.86    inference(superposition,[],[f2204,f11426])).
% 3.74/0.86  fof(f11426,plain,(
% 3.74/0.86    ( ! [X0] : (k1_xboole_0 = k9_relat_1(sK1,k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0))) ) | ~spl3_241),
% 3.74/0.86    inference(avatar_component_clause,[],[f11425])).
% 3.74/0.86  fof(f2204,plain,(
% 3.74/0.86    ( ! [X0] : (r1_tarski(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0))) | ~r1_tarski(X0,k1_relat_1(sK1))) ) | ~spl3_116),
% 3.74/0.86    inference(avatar_component_clause,[],[f2203])).
% 3.74/0.86  fof(f11427,plain,(
% 3.74/0.86    spl3_241 | ~spl3_58 | ~spl3_229),
% 3.74/0.86    inference(avatar_split_clause,[],[f11098,f6757,f874,f11425])).
% 3.74/0.86  fof(f874,plain,(
% 3.74/0.86    spl3_58 <=> ! [X5] : k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X5)),X5)),
% 3.74/0.86    introduced(avatar_definition,[new_symbols(naming,[spl3_58])])).
% 3.74/0.86  fof(f6757,plain,(
% 3.74/0.86    spl3_229 <=> ! [X1,X0] : k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))),
% 3.74/0.86    introduced(avatar_definition,[new_symbols(naming,[spl3_229])])).
% 3.74/0.86  fof(f11098,plain,(
% 3.74/0.86    ( ! [X0] : (k1_xboole_0 = k9_relat_1(sK1,k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0))) ) | (~spl3_58 | ~spl3_229)),
% 3.74/0.86    inference(superposition,[],[f6758,f875])).
% 3.74/0.86  fof(f875,plain,(
% 3.74/0.86    ( ! [X5] : (k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X5)),X5)) ) | ~spl3_58),
% 3.74/0.86    inference(avatar_component_clause,[],[f874])).
% 3.74/0.86  fof(f6758,plain,(
% 3.74/0.86    ( ! [X0,X1] : (k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))) ) | ~spl3_229),
% 3.74/0.86    inference(avatar_component_clause,[],[f6757])).
% 3.74/0.86  fof(f6759,plain,(
% 3.74/0.86    spl3_229 | ~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_196),
% 3.74/0.86    inference(avatar_split_clause,[],[f5238,f5156,f90,f85,f80,f6757])).
% 3.74/0.86  fof(f80,plain,(
% 3.74/0.86    spl3_1 <=> v1_relat_1(sK1)),
% 3.74/0.86    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 3.74/0.86  fof(f85,plain,(
% 3.74/0.86    spl3_2 <=> v1_funct_1(sK1)),
% 3.74/0.86    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 3.74/0.86  fof(f90,plain,(
% 3.74/0.86    spl3_3 <=> v2_funct_1(sK1)),
% 3.74/0.86    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 3.74/0.86  fof(f5156,plain,(
% 3.74/0.86    spl3_196 <=> ! [X1,X0,X2] : (k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.74/0.86    introduced(avatar_definition,[new_symbols(naming,[spl3_196])])).
% 3.74/0.86  fof(f5238,plain,(
% 3.74/0.86    ( ! [X0,X1] : (k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))) ) | (~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_196)),
% 3.74/0.86    inference(subsumption_resolution,[],[f5237,f82])).
% 3.74/0.86  fof(f82,plain,(
% 3.74/0.86    v1_relat_1(sK1) | ~spl3_1),
% 3.74/0.86    inference(avatar_component_clause,[],[f80])).
% 3.74/0.86  fof(f5237,plain,(
% 3.74/0.86    ( ! [X0,X1] : (k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) | ~v1_relat_1(sK1)) ) | (~spl3_2 | ~spl3_3 | ~spl3_196)),
% 3.74/0.86    inference(subsumption_resolution,[],[f5236,f87])).
% 3.74/0.86  fof(f87,plain,(
% 3.74/0.86    v1_funct_1(sK1) | ~spl3_2),
% 3.74/0.86    inference(avatar_component_clause,[],[f85])).
% 3.74/0.86  fof(f5236,plain,(
% 3.74/0.86    ( ! [X0,X1] : (k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) ) | (~spl3_3 | ~spl3_196)),
% 3.74/0.86    inference(resolution,[],[f5157,f92])).
% 3.74/0.86  fof(f92,plain,(
% 3.74/0.86    v2_funct_1(sK1) | ~spl3_3),
% 3.74/0.86    inference(avatar_component_clause,[],[f90])).
% 3.74/0.86  fof(f5157,plain,(
% 3.74/0.86    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) ) | ~spl3_196),
% 3.74/0.86    inference(avatar_component_clause,[],[f5156])).
% 3.74/0.86  fof(f5158,plain,(
% 3.74/0.86    spl3_196),
% 3.74/0.86    inference(avatar_split_clause,[],[f67,f5156])).
% 3.74/0.86  fof(f67,plain,(
% 3.74/0.86    ( ! [X2,X0,X1] : (k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.74/0.86    inference(cnf_transformation,[],[f37])).
% 3.74/0.86  fof(f37,plain,(
% 3.74/0.86    ! [X0,X1,X2] : (k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.74/0.86    inference(flattening,[],[f36])).
% 3.74/0.86  fof(f36,plain,(
% 3.74/0.86    ! [X0,X1,X2] : ((k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 3.74/0.86    inference(ennf_transformation,[],[f15])).
% 3.74/0.86  fof(f15,axiom,(
% 3.74/0.86    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (v2_funct_1(X2) => k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 3.74/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_funct_1)).
% 3.74/0.86  fof(f3514,plain,(
% 3.74/0.86    spl3_155 | ~spl3_8 | ~spl3_15 | ~spl3_153),
% 3.74/0.86    inference(avatar_split_clause,[],[f3316,f3230,f150,f112,f3511])).
% 3.74/0.86  fof(f112,plain,(
% 3.74/0.86    spl3_8 <=> ! [X0] : r1_tarski(X0,X0)),
% 3.74/0.86    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 3.74/0.86  fof(f150,plain,(
% 3.74/0.86    spl3_15 <=> ! [X2] : k1_xboole_0 = k6_subset_1(X2,X2)),
% 3.74/0.86    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 3.74/0.86  fof(f3230,plain,(
% 3.74/0.86    spl3_153 <=> ! [X9,X8] : (k1_xboole_0 = k10_relat_1(sK1,k6_subset_1(X8,X9)) | ~r1_tarski(X8,X9))),
% 3.74/0.86    introduced(avatar_definition,[new_symbols(naming,[spl3_153])])).
% 3.74/0.86  fof(f3316,plain,(
% 3.74/0.86    k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0) | (~spl3_8 | ~spl3_15 | ~spl3_153)),
% 3.74/0.86    inference(forward_demodulation,[],[f3233,f151])).
% 3.74/0.86  fof(f151,plain,(
% 3.74/0.86    ( ! [X2] : (k1_xboole_0 = k6_subset_1(X2,X2)) ) | ~spl3_15),
% 3.74/0.86    inference(avatar_component_clause,[],[f150])).
% 3.74/0.86  fof(f3233,plain,(
% 3.74/0.86    ( ! [X0] : (k1_xboole_0 = k10_relat_1(sK1,k6_subset_1(X0,X0))) ) | (~spl3_8 | ~spl3_153)),
% 3.74/0.86    inference(resolution,[],[f3231,f113])).
% 3.74/0.86  fof(f113,plain,(
% 3.74/0.86    ( ! [X0] : (r1_tarski(X0,X0)) ) | ~spl3_8),
% 3.74/0.86    inference(avatar_component_clause,[],[f112])).
% 3.74/0.86  fof(f3231,plain,(
% 3.74/0.86    ( ! [X8,X9] : (~r1_tarski(X8,X9) | k1_xboole_0 = k10_relat_1(sK1,k6_subset_1(X8,X9))) ) | ~spl3_153),
% 3.74/0.86    inference(avatar_component_clause,[],[f3230])).
% 3.74/0.86  fof(f3232,plain,(
% 3.74/0.86    spl3_153 | ~spl3_1 | ~spl3_2 | ~spl3_108 | ~spl3_125),
% 3.74/0.86    inference(avatar_split_clause,[],[f3212,f2353,f1998,f85,f80,f3230])).
% 3.74/0.86  fof(f1998,plain,(
% 3.74/0.86    spl3_108 <=> ! [X1,X0,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.74/0.86    introduced(avatar_definition,[new_symbols(naming,[spl3_108])])).
% 3.74/0.86  fof(f2353,plain,(
% 3.74/0.86    spl3_125 <=> ! [X9,X8] : (~r1_tarski(X8,X9) | k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,X8),k10_relat_1(sK1,X9)))),
% 3.74/0.86    introduced(avatar_definition,[new_symbols(naming,[spl3_125])])).
% 3.74/0.86  fof(f3212,plain,(
% 3.74/0.86    ( ! [X8,X9] : (k1_xboole_0 = k10_relat_1(sK1,k6_subset_1(X8,X9)) | ~r1_tarski(X8,X9)) ) | (~spl3_1 | ~spl3_2 | ~spl3_108 | ~spl3_125)),
% 3.74/0.86    inference(backward_demodulation,[],[f2354,f3211])).
% 3.74/0.86  fof(f3211,plain,(
% 3.74/0.86    ( ! [X0,X1] : (k10_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1))) ) | (~spl3_1 | ~spl3_2 | ~spl3_108)),
% 3.74/0.86    inference(subsumption_resolution,[],[f3210,f82])).
% 3.74/0.86  fof(f3210,plain,(
% 3.74/0.86    ( ! [X0,X1] : (k10_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1)) | ~v1_relat_1(sK1)) ) | (~spl3_2 | ~spl3_108)),
% 3.74/0.86    inference(resolution,[],[f1999,f87])).
% 3.74/0.86  fof(f1999,plain,(
% 3.74/0.86    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) ) | ~spl3_108),
% 3.74/0.86    inference(avatar_component_clause,[],[f1998])).
% 3.74/0.86  fof(f2354,plain,(
% 3.74/0.86    ( ! [X8,X9] : (~r1_tarski(X8,X9) | k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,X8),k10_relat_1(sK1,X9))) ) | ~spl3_125),
% 3.74/0.86    inference(avatar_component_clause,[],[f2353])).
% 3.74/0.86  fof(f2355,plain,(
% 3.74/0.86    spl3_125 | ~spl3_13 | ~spl3_76),
% 3.74/0.86    inference(avatar_split_clause,[],[f1334,f1328,f137,f2353])).
% 3.74/0.86  fof(f137,plain,(
% 3.74/0.86    spl3_13 <=> ! [X1,X0] : (k1_xboole_0 = k6_subset_1(X0,X1) | ~r1_tarski(X0,X1))),
% 3.74/0.86    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 3.74/0.86  fof(f1328,plain,(
% 3.74/0.86    spl3_76 <=> ! [X1,X0] : (~r1_tarski(X0,X1) | r1_tarski(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1)))),
% 3.74/0.86    introduced(avatar_definition,[new_symbols(naming,[spl3_76])])).
% 3.74/0.86  fof(f1334,plain,(
% 3.74/0.86    ( ! [X8,X9] : (~r1_tarski(X8,X9) | k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,X8),k10_relat_1(sK1,X9))) ) | (~spl3_13 | ~spl3_76)),
% 3.74/0.86    inference(resolution,[],[f1329,f138])).
% 3.74/0.86  fof(f138,plain,(
% 3.74/0.86    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k6_subset_1(X0,X1)) ) | ~spl3_13),
% 3.74/0.86    inference(avatar_component_clause,[],[f137])).
% 3.74/0.86  fof(f1329,plain,(
% 3.74/0.86    ( ! [X0,X1] : (r1_tarski(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1)) | ~r1_tarski(X0,X1)) ) | ~spl3_76),
% 3.74/0.86    inference(avatar_component_clause,[],[f1328])).
% 3.74/0.86  fof(f2205,plain,(
% 3.74/0.86    spl3_116 | ~spl3_1 | ~spl3_87),
% 3.74/0.86    inference(avatar_split_clause,[],[f1863,f1622,f80,f2203])).
% 3.74/0.86  fof(f1622,plain,(
% 3.74/0.86    spl3_87 <=> ! [X1,X0] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 3.74/0.86    introduced(avatar_definition,[new_symbols(naming,[spl3_87])])).
% 3.74/0.86  fof(f1863,plain,(
% 3.74/0.86    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(sK1)) | r1_tarski(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0)))) ) | (~spl3_1 | ~spl3_87)),
% 3.74/0.86    inference(resolution,[],[f1623,f82])).
% 3.74/0.86  fof(f1623,plain,(
% 3.74/0.86    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))) ) | ~spl3_87),
% 3.74/0.86    inference(avatar_component_clause,[],[f1622])).
% 3.74/0.86  fof(f2000,plain,(
% 3.74/0.86    spl3_108),
% 3.74/0.86    inference(avatar_split_clause,[],[f66,f1998])).
% 3.74/0.86  fof(f66,plain,(
% 3.74/0.86    ( ! [X2,X0,X1] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.74/0.86    inference(cnf_transformation,[],[f35])).
% 3.74/0.86  fof(f35,plain,(
% 3.74/0.86    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.74/0.86    inference(flattening,[],[f34])).
% 3.74/0.86  fof(f34,plain,(
% 3.74/0.86    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 3.74/0.86    inference(ennf_transformation,[],[f16])).
% 3.74/0.86  fof(f16,axiom,(
% 3.74/0.86    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 3.74/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_funct_1)).
% 3.74/0.86  fof(f1862,plain,(
% 3.74/0.86    spl3_96 | ~spl3_37 | ~spl3_49 | ~spl3_93),
% 3.74/0.86    inference(avatar_split_clause,[],[f1837,f1803,f714,f471,f1860])).
% 3.74/0.86  fof(f471,plain,(
% 3.74/0.86    spl3_37 <=> ! [X9] : k2_xboole_0(X9,k1_xboole_0) = X9),
% 3.74/0.86    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).
% 3.74/0.86  fof(f714,plain,(
% 3.74/0.86    spl3_49 <=> ! [X3,X2,X4] : r1_tarski(k6_subset_1(X2,X3),k2_xboole_0(X4,k6_subset_1(X2,X4)))),
% 3.74/0.86    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).
% 3.74/0.86  fof(f1803,plain,(
% 3.74/0.86    spl3_93 <=> ! [X0] : k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,X0),k1_relat_1(sK1))),
% 3.74/0.86    introduced(avatar_definition,[new_symbols(naming,[spl3_93])])).
% 3.74/0.86  fof(f1837,plain,(
% 3.74/0.86    ( ! [X33,X32] : (r1_tarski(k6_subset_1(k10_relat_1(sK1,X32),X33),k1_relat_1(sK1))) ) | (~spl3_37 | ~spl3_49 | ~spl3_93)),
% 3.74/0.86    inference(forward_demodulation,[],[f1822,f472])).
% 3.74/0.86  fof(f472,plain,(
% 3.74/0.86    ( ! [X9] : (k2_xboole_0(X9,k1_xboole_0) = X9) ) | ~spl3_37),
% 3.74/0.86    inference(avatar_component_clause,[],[f471])).
% 3.74/0.86  fof(f1822,plain,(
% 3.74/0.86    ( ! [X33,X32] : (r1_tarski(k6_subset_1(k10_relat_1(sK1,X32),X33),k2_xboole_0(k1_relat_1(sK1),k1_xboole_0))) ) | (~spl3_49 | ~spl3_93)),
% 3.74/0.86    inference(superposition,[],[f715,f1804])).
% 3.74/0.86  fof(f1804,plain,(
% 3.74/0.86    ( ! [X0] : (k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,X0),k1_relat_1(sK1))) ) | ~spl3_93),
% 3.74/0.86    inference(avatar_component_clause,[],[f1803])).
% 3.74/0.86  fof(f715,plain,(
% 3.74/0.86    ( ! [X4,X2,X3] : (r1_tarski(k6_subset_1(X2,X3),k2_xboole_0(X4,k6_subset_1(X2,X4)))) ) | ~spl3_49),
% 3.74/0.86    inference(avatar_component_clause,[],[f714])).
% 3.74/0.86  fof(f1805,plain,(
% 3.74/0.86    spl3_93 | ~spl3_1 | ~spl3_92),
% 3.74/0.86    inference(avatar_split_clause,[],[f1801,f1798,f80,f1803])).
% 3.74/0.86  fof(f1798,plain,(
% 3.74/0.86    spl3_92 <=> ! [X7,X6] : (k1_xboole_0 = k6_subset_1(k10_relat_1(X6,X7),k1_relat_1(X6)) | ~v1_relat_1(X6))),
% 3.74/0.86    introduced(avatar_definition,[new_symbols(naming,[spl3_92])])).
% 3.74/0.86  fof(f1801,plain,(
% 3.74/0.86    ( ! [X0] : (k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,X0),k1_relat_1(sK1))) ) | (~spl3_1 | ~spl3_92)),
% 3.74/0.86    inference(resolution,[],[f1799,f82])).
% 3.74/0.86  fof(f1799,plain,(
% 3.74/0.86    ( ! [X6,X7] : (~v1_relat_1(X6) | k1_xboole_0 = k6_subset_1(k10_relat_1(X6,X7),k1_relat_1(X6))) ) | ~spl3_92),
% 3.74/0.86    inference(avatar_component_clause,[],[f1798])).
% 3.74/0.86  fof(f1800,plain,(
% 3.74/0.86    spl3_92 | ~spl3_12 | ~spl3_13),
% 3.74/0.86    inference(avatar_split_clause,[],[f148,f137,f133,f1798])).
% 3.74/0.86  fof(f133,plain,(
% 3.74/0.86    spl3_12 <=> ! [X1,X0] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 3.74/0.86    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 3.74/0.86  fof(f148,plain,(
% 3.74/0.86    ( ! [X6,X7] : (k1_xboole_0 = k6_subset_1(k10_relat_1(X6,X7),k1_relat_1(X6)) | ~v1_relat_1(X6)) ) | (~spl3_12 | ~spl3_13)),
% 3.74/0.86    inference(resolution,[],[f138,f134])).
% 3.74/0.86  fof(f134,plain,(
% 3.74/0.86    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) ) | ~spl3_12),
% 3.74/0.86    inference(avatar_component_clause,[],[f133])).
% 3.74/0.86  fof(f1624,plain,(
% 3.74/0.86    spl3_87),
% 3.74/0.86    inference(avatar_split_clause,[],[f58,f1622])).
% 3.74/0.86  fof(f58,plain,(
% 3.74/0.86    ( ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.74/0.86    inference(cnf_transformation,[],[f26])).
% 3.74/0.86  fof(f26,plain,(
% 3.74/0.86    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 3.74/0.86    inference(flattening,[],[f25])).
% 3.74/0.86  fof(f25,plain,(
% 3.74/0.86    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 3.74/0.86    inference(ennf_transformation,[],[f18])).
% 3.74/0.86  fof(f18,axiom,(
% 3.74/0.86    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 3.74/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).
% 3.74/0.86  fof(f1330,plain,(
% 3.74/0.86    spl3_76 | ~spl3_1 | ~spl3_66),
% 3.74/0.86    inference(avatar_split_clause,[],[f1326,f1002,f80,f1328])).
% 3.74/0.86  fof(f1002,plain,(
% 3.74/0.86    spl3_66 <=> ! [X1,X0,X2] : (r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 3.74/0.86    introduced(avatar_definition,[new_symbols(naming,[spl3_66])])).
% 3.74/0.86  fof(f1326,plain,(
% 3.74/0.86    ( ! [X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1))) ) | (~spl3_1 | ~spl3_66)),
% 3.74/0.86    inference(resolution,[],[f1003,f82])).
% 3.74/0.86  fof(f1003,plain,(
% 3.74/0.86    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(X0,X1) | r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) ) | ~spl3_66),
% 3.74/0.86    inference(avatar_component_clause,[],[f1002])).
% 3.74/0.86  fof(f1004,plain,(
% 3.74/0.86    spl3_66),
% 3.74/0.86    inference(avatar_split_clause,[],[f63,f1002])).
% 3.74/0.86  fof(f63,plain,(
% 3.74/0.86    ( ! [X2,X0,X1] : (r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 3.74/0.86    inference(cnf_transformation,[],[f31])).
% 3.74/0.86  fof(f31,plain,(
% 3.74/0.86    ! [X0,X1,X2] : (r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 3.74/0.86    inference(flattening,[],[f30])).
% 3.74/0.86  fof(f30,plain,(
% 3.74/0.86    ! [X0,X1,X2] : ((r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 3.74/0.86    inference(ennf_transformation,[],[f14])).
% 3.74/0.86  fof(f14,axiom,(
% 3.74/0.86    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))))),
% 3.74/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_relat_1)).
% 3.74/0.86  fof(f876,plain,(
% 3.74/0.86    spl3_58 | ~spl3_13 | ~spl3_55),
% 3.74/0.86    inference(avatar_split_clause,[],[f862,f855,f137,f874])).
% 3.74/0.86  fof(f855,plain,(
% 3.74/0.86    spl3_55 <=> ! [X0] : r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0)),
% 3.74/0.86    introduced(avatar_definition,[new_symbols(naming,[spl3_55])])).
% 3.74/0.86  fof(f862,plain,(
% 3.74/0.86    ( ! [X5] : (k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X5)),X5)) ) | (~spl3_13 | ~spl3_55)),
% 3.74/0.86    inference(resolution,[],[f856,f138])).
% 3.74/0.86  fof(f856,plain,(
% 3.74/0.86    ( ! [X0] : (r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0)) ) | ~spl3_55),
% 3.74/0.86    inference(avatar_component_clause,[],[f855])).
% 3.74/0.86  fof(f857,plain,(
% 3.74/0.86    spl3_55 | ~spl3_1 | ~spl3_2 | ~spl3_44),
% 3.74/0.86    inference(avatar_split_clause,[],[f853,f626,f85,f80,f855])).
% 3.74/0.86  fof(f626,plain,(
% 3.74/0.86    spl3_44 <=> ! [X1,X0] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.74/0.86    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).
% 3.74/0.86  fof(f853,plain,(
% 3.74/0.86    ( ! [X0] : (r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0)) ) | (~spl3_1 | ~spl3_2 | ~spl3_44)),
% 3.74/0.86    inference(subsumption_resolution,[],[f852,f82])).
% 3.74/0.86  fof(f852,plain,(
% 3.74/0.86    ( ! [X0] : (r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0) | ~v1_relat_1(sK1)) ) | (~spl3_2 | ~spl3_44)),
% 3.74/0.86    inference(resolution,[],[f627,f87])).
% 3.74/0.86  fof(f627,plain,(
% 3.74/0.86    ( ! [X0,X1] : (~v1_funct_1(X1) | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) ) | ~spl3_44),
% 3.74/0.86    inference(avatar_component_clause,[],[f626])).
% 3.74/0.86  fof(f716,plain,(
% 3.74/0.86    spl3_49 | ~spl3_22 | ~spl3_39),
% 3.74/0.86    inference(avatar_split_clause,[],[f546,f538,f203,f714])).
% 3.74/0.86  fof(f203,plain,(
% 3.74/0.86    spl3_22 <=> ! [X11,X10,X12] : (~r1_tarski(X10,X11) | r1_tarski(k6_subset_1(X10,X12),X11))),
% 3.74/0.86    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 3.74/0.86  fof(f538,plain,(
% 3.74/0.86    spl3_39 <=> ! [X36,X35] : r1_tarski(X35,k2_xboole_0(X36,k6_subset_1(X35,X36)))),
% 3.74/0.86    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).
% 3.74/0.86  fof(f546,plain,(
% 3.74/0.86    ( ! [X4,X2,X3] : (r1_tarski(k6_subset_1(X2,X3),k2_xboole_0(X4,k6_subset_1(X2,X4)))) ) | (~spl3_22 | ~spl3_39)),
% 3.74/0.86    inference(resolution,[],[f539,f204])).
% 3.74/0.86  fof(f204,plain,(
% 3.74/0.86    ( ! [X12,X10,X11] : (~r1_tarski(X10,X11) | r1_tarski(k6_subset_1(X10,X12),X11)) ) | ~spl3_22),
% 3.74/0.86    inference(avatar_component_clause,[],[f203])).
% 3.74/0.86  fof(f539,plain,(
% 3.74/0.86    ( ! [X35,X36] : (r1_tarski(X35,k2_xboole_0(X36,k6_subset_1(X35,X36)))) ) | ~spl3_39),
% 3.74/0.86    inference(avatar_component_clause,[],[f538])).
% 3.74/0.86  fof(f628,plain,(
% 3.74/0.86    spl3_44),
% 3.74/0.86    inference(avatar_split_clause,[],[f60,f626])).
% 3.74/0.86  fof(f60,plain,(
% 3.74/0.86    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.74/0.86    inference(cnf_transformation,[],[f29])).
% 3.74/0.86  fof(f29,plain,(
% 3.74/0.86    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.74/0.86    inference(flattening,[],[f28])).
% 3.74/0.86  fof(f28,plain,(
% 3.74/0.86    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.74/0.86    inference(ennf_transformation,[],[f17])).
% 3.74/0.86  fof(f17,axiom,(
% 3.74/0.86    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 3.74/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).
% 3.74/0.86  fof(f540,plain,(
% 3.74/0.86    spl3_39 | ~spl3_8 | ~spl3_35),
% 3.74/0.86    inference(avatar_split_clause,[],[f514,f433,f112,f538])).
% 3.74/0.86  fof(f433,plain,(
% 3.74/0.86    spl3_35 <=> ! [X1,X0,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k6_subset_1(X0,X1),X2))),
% 3.74/0.86    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).
% 3.74/0.86  fof(f514,plain,(
% 3.74/0.86    ( ! [X35,X36] : (r1_tarski(X35,k2_xboole_0(X36,k6_subset_1(X35,X36)))) ) | (~spl3_8 | ~spl3_35)),
% 3.74/0.86    inference(resolution,[],[f434,f113])).
% 3.74/0.86  fof(f434,plain,(
% 3.74/0.86    ( ! [X2,X0,X1] : (~r1_tarski(k6_subset_1(X0,X1),X2) | r1_tarski(X0,k2_xboole_0(X1,X2))) ) | ~spl3_35),
% 3.74/0.86    inference(avatar_component_clause,[],[f433])).
% 3.74/0.86  fof(f473,plain,(
% 3.74/0.86    spl3_37 | ~spl3_8 | ~spl3_15 | ~spl3_23),
% 3.74/0.86    inference(avatar_split_clause,[],[f449,f210,f150,f112,f471])).
% 3.74/0.86  fof(f210,plain,(
% 3.74/0.86    spl3_23 <=> ! [X1,X0] : (k2_xboole_0(X0,k6_subset_1(X1,X0)) = X1 | ~r1_tarski(X0,X1))),
% 3.74/0.86    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 3.74/0.86  fof(f449,plain,(
% 3.74/0.86    ( ! [X9] : (k2_xboole_0(X9,k1_xboole_0) = X9) ) | (~spl3_8 | ~spl3_15 | ~spl3_23)),
% 3.74/0.86    inference(forward_demodulation,[],[f439,f151])).
% 3.74/0.86  fof(f439,plain,(
% 3.74/0.86    ( ! [X9] : (k2_xboole_0(X9,k6_subset_1(X9,X9)) = X9) ) | (~spl3_8 | ~spl3_23)),
% 3.74/0.86    inference(resolution,[],[f211,f113])).
% 3.74/0.86  fof(f211,plain,(
% 3.74/0.86    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,k6_subset_1(X1,X0)) = X1) ) | ~spl3_23),
% 3.74/0.86    inference(avatar_component_clause,[],[f210])).
% 3.74/0.86  fof(f435,plain,(
% 3.74/0.86    spl3_35),
% 3.74/0.86    inference(avatar_split_clause,[],[f78,f433])).
% 3.74/0.86  fof(f78,plain,(
% 3.74/0.86    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k6_subset_1(X0,X1),X2)) )),
% 3.74/0.86    inference(definition_unfolding,[],[f65,f56])).
% 3.74/0.86  fof(f56,plain,(
% 3.74/0.86    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 3.74/0.86    inference(cnf_transformation,[],[f12])).
% 3.74/0.86  fof(f12,axiom,(
% 3.74/0.86    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 3.74/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 3.74/0.86  fof(f65,plain,(
% 3.74/0.86    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 3.74/0.86    inference(cnf_transformation,[],[f33])).
% 3.74/0.86  fof(f33,plain,(
% 3.74/0.86    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 3.74/0.86    inference(ennf_transformation,[],[f9])).
% 3.74/0.86  fof(f9,axiom,(
% 3.74/0.86    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 3.74/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).
% 3.74/0.86  fof(f212,plain,(
% 3.74/0.86    spl3_23),
% 3.74/0.86    inference(avatar_split_clause,[],[f74,f210])).
% 3.74/0.86  fof(f74,plain,(
% 3.74/0.86    ( ! [X0,X1] : (k2_xboole_0(X0,k6_subset_1(X1,X0)) = X1 | ~r1_tarski(X0,X1)) )),
% 3.74/0.86    inference(definition_unfolding,[],[f59,f56])).
% 3.74/0.86  fof(f59,plain,(
% 3.74/0.86    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1)) )),
% 3.74/0.86    inference(cnf_transformation,[],[f27])).
% 3.74/0.86  fof(f27,plain,(
% 3.74/0.86    ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1))),
% 3.74/0.86    inference(ennf_transformation,[],[f10])).
% 3.74/0.86  fof(f10,axiom,(
% 3.74/0.86    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1)),
% 3.74/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).
% 3.74/0.86  fof(f205,plain,(
% 3.74/0.86    spl3_22 | ~spl3_7 | ~spl3_20),
% 3.74/0.86    inference(avatar_split_clause,[],[f196,f189,f107,f203])).
% 3.74/0.86  fof(f107,plain,(
% 3.74/0.86    spl3_7 <=> ! [X1,X0] : r1_tarski(k6_subset_1(X0,X1),X0)),
% 3.74/0.86    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 3.74/0.86  fof(f189,plain,(
% 3.74/0.86    spl3_20 <=> ! [X1,X0,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 3.74/0.86    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 3.74/0.86  fof(f196,plain,(
% 3.74/0.86    ( ! [X12,X10,X11] : (~r1_tarski(X10,X11) | r1_tarski(k6_subset_1(X10,X12),X11)) ) | (~spl3_7 | ~spl3_20)),
% 3.74/0.86    inference(resolution,[],[f190,f108])).
% 3.74/0.86  fof(f108,plain,(
% 3.74/0.86    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X0)) ) | ~spl3_7),
% 3.74/0.86    inference(avatar_component_clause,[],[f107])).
% 3.74/0.86  fof(f190,plain,(
% 3.74/0.86    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) ) | ~spl3_20),
% 3.74/0.86    inference(avatar_component_clause,[],[f189])).
% 3.74/0.86  fof(f191,plain,(
% 3.74/0.86    spl3_20),
% 3.74/0.86    inference(avatar_split_clause,[],[f68,f189])).
% 3.74/0.86  fof(f68,plain,(
% 3.74/0.86    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 3.74/0.86    inference(cnf_transformation,[],[f39])).
% 3.74/0.86  fof(f39,plain,(
% 3.74/0.86    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 3.74/0.86    inference(flattening,[],[f38])).
% 3.74/0.86  fof(f38,plain,(
% 3.74/0.86    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 3.74/0.86    inference(ennf_transformation,[],[f3])).
% 3.74/0.86  fof(f3,axiom,(
% 3.74/0.86    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 3.74/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 3.74/0.86  fof(f178,plain,(
% 3.74/0.86    ~spl3_18 | spl3_9 | ~spl3_14),
% 3.74/0.86    inference(avatar_split_clause,[],[f171,f141,f116,f175])).
% 3.74/0.86  fof(f116,plain,(
% 3.74/0.86    spl3_9 <=> r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)),
% 3.74/0.86    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 3.74/0.86  fof(f141,plain,(
% 3.74/0.86    spl3_14 <=> ! [X1,X0] : (r1_tarski(X0,X1) | k1_xboole_0 != k6_subset_1(X0,X1))),
% 3.74/0.86    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 3.74/0.86  fof(f171,plain,(
% 3.74/0.86    k1_xboole_0 != k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) | (spl3_9 | ~spl3_14)),
% 3.74/0.86    inference(resolution,[],[f142,f118])).
% 3.74/0.86  fof(f118,plain,(
% 3.74/0.86    ~r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) | spl3_9),
% 3.74/0.86    inference(avatar_component_clause,[],[f116])).
% 3.74/0.86  fof(f142,plain,(
% 3.74/0.86    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k6_subset_1(X0,X1)) ) | ~spl3_14),
% 3.74/0.86    inference(avatar_component_clause,[],[f141])).
% 3.74/0.86  fof(f152,plain,(
% 3.74/0.86    spl3_15 | ~spl3_8 | ~spl3_13),
% 3.74/0.86    inference(avatar_split_clause,[],[f145,f137,f112,f150])).
% 3.74/0.86  fof(f145,plain,(
% 3.74/0.86    ( ! [X2] : (k1_xboole_0 = k6_subset_1(X2,X2)) ) | (~spl3_8 | ~spl3_13)),
% 3.74/0.86    inference(resolution,[],[f138,f113])).
% 3.74/0.86  fof(f143,plain,(
% 3.74/0.86    spl3_14),
% 3.74/0.86    inference(avatar_split_clause,[],[f76,f141])).
% 3.74/0.86  fof(f76,plain,(
% 3.74/0.86    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k6_subset_1(X0,X1)) )),
% 3.74/0.86    inference(definition_unfolding,[],[f61,f56])).
% 3.74/0.86  fof(f61,plain,(
% 3.74/0.86    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 3.74/0.86    inference(cnf_transformation,[],[f44])).
% 3.74/0.86  fof(f44,plain,(
% 3.74/0.86    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 3.74/0.86    inference(nnf_transformation,[],[f1])).
% 3.74/0.86  fof(f1,axiom,(
% 3.74/0.86    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 3.74/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 3.74/0.86  fof(f139,plain,(
% 3.74/0.86    spl3_13),
% 3.74/0.86    inference(avatar_split_clause,[],[f75,f137])).
% 3.74/0.86  fof(f75,plain,(
% 3.74/0.86    ( ! [X0,X1] : (k1_xboole_0 = k6_subset_1(X0,X1) | ~r1_tarski(X0,X1)) )),
% 3.74/0.86    inference(definition_unfolding,[],[f62,f56])).
% 3.74/0.86  fof(f62,plain,(
% 3.74/0.86    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 3.74/0.86    inference(cnf_transformation,[],[f44])).
% 3.74/0.86  fof(f135,plain,(
% 3.74/0.86    spl3_12),
% 3.74/0.86    inference(avatar_split_clause,[],[f57,f133])).
% 3.74/0.86  fof(f57,plain,(
% 3.74/0.86    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.74/0.86    inference(cnf_transformation,[],[f24])).
% 3.74/0.86  fof(f24,plain,(
% 3.74/0.86    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 3.74/0.86    inference(ennf_transformation,[],[f13])).
% 3.74/0.86  fof(f13,axiom,(
% 3.74/0.86    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 3.74/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).
% 3.74/0.86  fof(f123,plain,(
% 3.74/0.86    spl3_10),
% 3.74/0.86    inference(avatar_split_clause,[],[f53,f121])).
% 3.74/0.86  fof(f53,plain,(
% 3.74/0.86    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 3.74/0.86    inference(cnf_transformation,[],[f23])).
% 3.74/0.86  fof(f23,plain,(
% 3.74/0.86    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 3.74/0.86    inference(ennf_transformation,[],[f7])).
% 3.74/0.86  fof(f7,axiom,(
% 3.74/0.86    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 3.74/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 3.74/0.86  fof(f119,plain,(
% 3.74/0.86    ~spl3_9),
% 3.74/0.86    inference(avatar_split_clause,[],[f50,f116])).
% 3.74/0.86  fof(f50,plain,(
% 3.74/0.86    ~r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)),
% 3.74/0.86    inference(cnf_transformation,[],[f43])).
% 3.74/0.86  fof(f43,plain,(
% 3.74/0.86    ~r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) & v2_funct_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 3.74/0.86    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f42])).
% 3.74/0.86  fof(f42,plain,(
% 3.74/0.86    ? [X0,X1] : (~r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) => (~r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) & v2_funct_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 3.74/0.86    introduced(choice_axiom,[])).
% 3.74/0.86  fof(f22,plain,(
% 3.74/0.86    ? [X0,X1] : (~r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 3.74/0.86    inference(flattening,[],[f21])).
% 3.74/0.86  fof(f21,plain,(
% 3.74/0.86    ? [X0,X1] : ((~r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) & v2_funct_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 3.74/0.86    inference(ennf_transformation,[],[f20])).
% 3.74/0.86  fof(f20,negated_conjecture,(
% 3.74/0.86    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)))),
% 3.74/0.86    inference(negated_conjecture,[],[f19])).
% 3.74/0.86  fof(f19,conjecture,(
% 3.74/0.86    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)))),
% 3.74/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_funct_1)).
% 3.74/0.86  fof(f114,plain,(
% 3.74/0.86    spl3_8 | ~spl3_6 | ~spl3_7),
% 3.74/0.86    inference(avatar_split_clause,[],[f110,f107,f103,f112])).
% 3.74/0.86  fof(f103,plain,(
% 3.74/0.86    spl3_6 <=> ! [X0] : k6_subset_1(X0,k1_xboole_0) = X0),
% 3.74/0.86    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 3.74/0.86  fof(f110,plain,(
% 3.74/0.86    ( ! [X0] : (r1_tarski(X0,X0)) ) | (~spl3_6 | ~spl3_7)),
% 3.74/0.86    inference(superposition,[],[f108,f104])).
% 3.74/0.86  fof(f104,plain,(
% 3.74/0.86    ( ! [X0] : (k6_subset_1(X0,k1_xboole_0) = X0) ) | ~spl3_6),
% 3.74/0.86    inference(avatar_component_clause,[],[f103])).
% 3.74/0.86  fof(f109,plain,(
% 3.74/0.86    spl3_7),
% 3.74/0.86    inference(avatar_split_clause,[],[f73,f107])).
% 3.74/0.86  fof(f73,plain,(
% 3.74/0.86    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X0)) )),
% 3.74/0.86    inference(definition_unfolding,[],[f55,f56])).
% 3.74/0.86  fof(f55,plain,(
% 3.74/0.86    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 3.74/0.86    inference(cnf_transformation,[],[f5])).
% 3.74/0.86  fof(f5,axiom,(
% 3.74/0.86    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 3.74/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 3.74/0.86  fof(f105,plain,(
% 3.74/0.86    spl3_6),
% 3.74/0.86    inference(avatar_split_clause,[],[f72,f103])).
% 3.74/0.86  fof(f72,plain,(
% 3.74/0.86    ( ! [X0] : (k6_subset_1(X0,k1_xboole_0) = X0) )),
% 3.74/0.86    inference(definition_unfolding,[],[f52,f56])).
% 3.74/0.86  fof(f52,plain,(
% 3.74/0.86    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.74/0.86    inference(cnf_transformation,[],[f6])).
% 3.74/0.86  fof(f6,axiom,(
% 3.74/0.86    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.74/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 3.74/0.86  fof(f93,plain,(
% 3.74/0.86    spl3_3),
% 3.74/0.86    inference(avatar_split_clause,[],[f49,f90])).
% 3.74/0.86  fof(f49,plain,(
% 3.74/0.86    v2_funct_1(sK1)),
% 3.74/0.86    inference(cnf_transformation,[],[f43])).
% 3.74/0.86  fof(f88,plain,(
% 3.74/0.86    spl3_2),
% 3.74/0.86    inference(avatar_split_clause,[],[f48,f85])).
% 3.74/0.86  fof(f48,plain,(
% 3.74/0.86    v1_funct_1(sK1)),
% 3.74/0.86    inference(cnf_transformation,[],[f43])).
% 3.74/0.86  fof(f83,plain,(
% 3.74/0.86    spl3_1),
% 3.74/0.86    inference(avatar_split_clause,[],[f47,f80])).
% 3.74/0.86  fof(f47,plain,(
% 3.74/0.86    v1_relat_1(sK1)),
% 3.74/0.86    inference(cnf_transformation,[],[f43])).
% 3.74/0.86  % SZS output end Proof for theBenchmark
% 3.74/0.86  % (26402)------------------------------
% 3.74/0.86  % (26402)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.74/0.86  % (26402)Termination reason: Refutation
% 3.74/0.86  
% 3.74/0.86  % (26402)Memory used [KB]: 13432
% 3.74/0.86  % (26402)Time elapsed: 0.388 s
% 3.74/0.86  % (26402)------------------------------
% 3.74/0.86  % (26402)------------------------------
% 3.74/0.87  % (26389)Success in time 0.507 s
%------------------------------------------------------------------------------
