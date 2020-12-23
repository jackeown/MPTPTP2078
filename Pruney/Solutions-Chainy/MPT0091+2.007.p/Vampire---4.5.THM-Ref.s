%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:39 EST 2020

% Result     : Theorem 0.72s
% Output     : Refutation 0.72s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 133 expanded)
%              Number of leaves         :   22 (  63 expanded)
%              Depth                    :    6
%              Number of atoms          :  183 ( 314 expanded)
%              Number of equality atoms :   49 (  87 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f512,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f25,f30,f35,f39,f43,f47,f51,f55,f75,f86,f98,f112,f184,f229,f364,f490])).

fof(f490,plain,
    ( spl3_11
    | ~ spl3_13
    | ~ spl3_29 ),
    inference(avatar_contradiction_clause,[],[f489])).

fof(f489,plain,
    ( $false
    | spl3_11
    | ~ spl3_13
    | ~ spl3_29 ),
    inference(subsumption_resolution,[],[f97,f465])).

fof(f465,plain,
    ( sK0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_13
    | ~ spl3_29 ),
    inference(superposition,[],[f363,f111])).

fof(f111,plain,
    ( sK0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl3_13
  <=> sK0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f363,plain,
    ( ! [X0] : k4_xboole_0(sK0,k4_xboole_0(X0,sK2)) = k4_xboole_0(sK0,X0)
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f362])).

fof(f362,plain,
    ( spl3_29
  <=> ! [X0] : k4_xboole_0(sK0,k4_xboole_0(X0,sK2)) = k4_xboole_0(sK0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f97,plain,
    ( sK0 != k4_xboole_0(sK0,sK1)
    | spl3_11 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl3_11
  <=> sK0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f364,plain,
    ( spl3_29
    | ~ spl3_9
    | ~ spl3_21
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f297,f226,f182,f73,f362])).

fof(f73,plain,
    ( spl3_9
  <=> ! [X1,X0,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f182,plain,
    ( spl3_21
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f226,plain,
    ( spl3_24
  <=> k1_xboole_0 = k3_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f297,plain,
    ( ! [X0] : k4_xboole_0(sK0,k4_xboole_0(X0,sK2)) = k4_xboole_0(sK0,X0)
    | ~ spl3_9
    | ~ spl3_21
    | ~ spl3_24 ),
    inference(forward_demodulation,[],[f291,f183])).

fof(f183,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0)
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f182])).

fof(f291,plain,
    ( ! [X0] : k4_xboole_0(sK0,k4_xboole_0(X0,sK2)) = k2_xboole_0(k4_xboole_0(sK0,X0),k1_xboole_0)
    | ~ spl3_9
    | ~ spl3_24 ),
    inference(superposition,[],[f74,f228])).

fof(f228,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK2)
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f226])).

fof(f74,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f73])).

fof(f229,plain,
    ( spl3_24
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f93,f83,f53,f41,f37,f226])).

fof(f37,plain,
    ( spl3_4
  <=> ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f41,plain,
    ( spl3_5
  <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f53,plain,
    ( spl3_8
  <=> ! [X1,X0] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f83,plain,
    ( spl3_10
  <=> sK0 = k4_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f93,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK2)
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f89,f70])).

fof(f70,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f64,f38])).

fof(f38,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f37])).

fof(f64,plain,
    ( ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0)
    | ~ spl3_5
    | ~ spl3_8 ),
    inference(superposition,[],[f54,f42])).

fof(f42,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f41])).

fof(f54,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f53])).

fof(f89,plain,
    ( k3_xboole_0(sK0,sK2) = k4_xboole_0(sK0,sK0)
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(superposition,[],[f54,f85])).

fof(f85,plain,
    ( sK0 = k4_xboole_0(sK0,sK2)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f83])).

% (16370)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
fof(f184,plain,
    ( spl3_21
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f81,f73,f41,f37,f182])).

fof(f81,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0)
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f79,f42])).

fof(f79,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,k1_xboole_0)) = k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0)
    | ~ spl3_4
    | ~ spl3_9 ),
    inference(superposition,[],[f74,f38])).

fof(f112,plain,
    ( spl3_13
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f57,f45,f32,f109])).

fof(f32,plain,
    ( spl3_3
  <=> r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f45,plain,
    ( spl3_6
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f57,plain,
    ( sK0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f34,f46])).

fof(f46,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f45])).

fof(f34,plain,
    ( r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f32])).

fof(f98,plain,
    ( ~ spl3_11
    | spl3_1
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f59,f49,f22,f95])).

fof(f22,plain,
    ( spl3_1
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f49,plain,
    ( spl3_7
  <=> ! [X1,X0] :
        ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f59,plain,
    ( sK0 != k4_xboole_0(sK0,sK1)
    | spl3_1
    | ~ spl3_7 ),
    inference(unit_resulting_resolution,[],[f24,f50])).

fof(f50,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) != X0
        | r1_xboole_0(X0,X1) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f49])).

fof(f24,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f22])).

fof(f86,plain,
    ( spl3_10
    | ~ spl3_2
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f56,f45,f27,f83])).

fof(f27,plain,
    ( spl3_2
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f56,plain,
    ( sK0 = k4_xboole_0(sK0,sK2)
    | ~ spl3_2
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f29,f46])).

fof(f29,plain,
    ( r1_xboole_0(sK0,sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f27])).

fof(f75,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f20,f73])).

fof(f20,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

fof(f55,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f17,f53])).

fof(f17,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f51,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f19,f49])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f47,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f18,f45])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f43,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f16,f41])).

fof(f16,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f39,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f15,f37])).

fof(f15,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f35,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f14,f32])).

fof(f14,plain,(
    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    & r1_xboole_0(sK0,sK2)
    & ~ r1_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f9])).

fof(f9,plain,
    ( ? [X0,X1,X2] :
        ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
        & r1_xboole_0(X0,X2)
        & ~ r1_xboole_0(X0,X1) )
   => ( r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))
      & r1_xboole_0(sK0,sK2)
      & ~ r1_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
      & r1_xboole_0(X0,X2)
      & ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
          & r1_xboole_0(X0,X2)
          & ~ r1_xboole_0(X0,X1) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
        & r1_xboole_0(X0,X2)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_xboole_1)).

fof(f30,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f13,f27])).

fof(f13,plain,(
    r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f25,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f12,f22])).

fof(f12,plain,(
    ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:46:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.37  ipcrm: permission denied for id (783056897)
% 0.21/0.37  ipcrm: permission denied for id (783089666)
% 0.21/0.38  ipcrm: permission denied for id (783122435)
% 0.21/0.38  ipcrm: permission denied for id (782696452)
% 0.21/0.38  ipcrm: permission denied for id (783155205)
% 0.21/0.38  ipcrm: permission denied for id (783187974)
% 0.21/0.38  ipcrm: permission denied for id (783220743)
% 0.21/0.38  ipcrm: permission denied for id (783253512)
% 0.21/0.38  ipcrm: permission denied for id (783286281)
% 0.21/0.39  ipcrm: permission denied for id (783351819)
% 0.21/0.39  ipcrm: permission denied for id (783417357)
% 0.21/0.39  ipcrm: permission denied for id (782761999)
% 0.21/0.40  ipcrm: permission denied for id (787283985)
% 0.21/0.40  ipcrm: permission denied for id (787316754)
% 0.21/0.40  ipcrm: permission denied for id (787447830)
% 0.21/0.40  ipcrm: permission denied for id (787513368)
% 0.21/0.40  ipcrm: permission denied for id (783777817)
% 0.21/0.41  ipcrm: permission denied for id (783810586)
% 0.21/0.41  ipcrm: permission denied for id (783843355)
% 0.21/0.41  ipcrm: permission denied for id (783876124)
% 0.21/0.41  ipcrm: permission denied for id (783908893)
% 0.21/0.41  ipcrm: permission denied for id (784007198)
% 0.21/0.41  ipcrm: permission denied for id (782827552)
% 0.21/0.41  ipcrm: permission denied for id (784039969)
% 0.21/0.41  ipcrm: permission denied for id (784072738)
% 0.21/0.41  ipcrm: permission denied for id (784105507)
% 0.21/0.41  ipcrm: permission denied for id (784138276)
% 0.21/0.42  ipcrm: permission denied for id (784171045)
% 0.21/0.42  ipcrm: permission denied for id (784203814)
% 0.21/0.42  ipcrm: permission denied for id (784236583)
% 0.21/0.42  ipcrm: permission denied for id (784269352)
% 0.21/0.42  ipcrm: permission denied for id (784302121)
% 0.21/0.42  ipcrm: permission denied for id (784334890)
% 0.21/0.42  ipcrm: permission denied for id (784367659)
% 0.21/0.42  ipcrm: permission denied for id (787611693)
% 0.21/0.42  ipcrm: permission denied for id (787644462)
% 0.21/0.42  ipcrm: permission denied for id (787677231)
% 0.21/0.42  ipcrm: permission denied for id (787710000)
% 0.21/0.42  ipcrm: permission denied for id (787742769)
% 0.21/0.42  ipcrm: permission denied for id (787775538)
% 0.21/0.43  ipcrm: permission denied for id (784695347)
% 0.21/0.43  ipcrm: permission denied for id (787808308)
% 0.21/0.43  ipcrm: permission denied for id (787841077)
% 0.21/0.43  ipcrm: permission denied for id (782893110)
% 0.21/0.43  ipcrm: permission denied for id (787873847)
% 0.21/0.43  ipcrm: permission denied for id (784793656)
% 0.21/0.43  ipcrm: permission denied for id (787906617)
% 0.21/0.43  ipcrm: permission denied for id (784859194)
% 0.21/0.43  ipcrm: permission denied for id (784924732)
% 0.21/0.43  ipcrm: permission denied for id (787972157)
% 0.21/0.44  ipcrm: permission denied for id (784990270)
% 0.21/0.44  ipcrm: permission denied for id (788004927)
% 0.21/0.44  ipcrm: permission denied for id (785055808)
% 0.21/0.44  ipcrm: permission denied for id (785088577)
% 0.21/0.44  ipcrm: permission denied for id (782925891)
% 0.21/0.44  ipcrm: permission denied for id (785154116)
% 0.21/0.45  ipcrm: permission denied for id (785219654)
% 0.21/0.45  ipcrm: permission denied for id (785252423)
% 0.21/0.45  ipcrm: permission denied for id (785285192)
% 0.21/0.45  ipcrm: permission denied for id (785350730)
% 0.21/0.45  ipcrm: permission denied for id (785383499)
% 0.21/0.45  ipcrm: permission denied for id (788136012)
% 0.21/0.45  ipcrm: permission denied for id (788168781)
% 0.21/0.45  ipcrm: permission denied for id (788201550)
% 0.21/0.46  ipcrm: permission denied for id (785547344)
% 0.21/0.46  ipcrm: permission denied for id (788267089)
% 0.21/0.46  ipcrm: permission denied for id (785612882)
% 0.21/0.46  ipcrm: permission denied for id (785645651)
% 0.21/0.46  ipcrm: permission denied for id (788299860)
% 0.21/0.46  ipcrm: permission denied for id (788332629)
% 0.21/0.46  ipcrm: permission denied for id (785743958)
% 0.21/0.47  ipcrm: permission denied for id (788430937)
% 0.21/0.47  ipcrm: permission denied for id (785875034)
% 0.21/0.47  ipcrm: permission denied for id (788463707)
% 0.21/0.47  ipcrm: permission denied for id (785940572)
% 0.21/0.47  ipcrm: permission denied for id (786006110)
% 0.21/0.47  ipcrm: permission denied for id (786038879)
% 0.21/0.48  ipcrm: permission denied for id (786071648)
% 0.21/0.48  ipcrm: permission denied for id (786137186)
% 0.21/0.48  ipcrm: permission denied for id (786169955)
% 0.21/0.48  ipcrm: permission denied for id (786202724)
% 0.21/0.48  ipcrm: permission denied for id (786235493)
% 0.21/0.48  ipcrm: permission denied for id (786268262)
% 0.21/0.49  ipcrm: permission denied for id (786301031)
% 0.21/0.49  ipcrm: permission denied for id (786333800)
% 0.21/0.49  ipcrm: permission denied for id (786366569)
% 0.21/0.49  ipcrm: permission denied for id (786399338)
% 0.21/0.49  ipcrm: permission denied for id (786432107)
% 0.21/0.49  ipcrm: permission denied for id (786464876)
% 0.21/0.49  ipcrm: permission denied for id (788594797)
% 0.21/0.49  ipcrm: permission denied for id (786530414)
% 0.21/0.50  ipcrm: permission denied for id (786595952)
% 0.21/0.50  ipcrm: permission denied for id (786628721)
% 0.21/0.50  ipcrm: permission denied for id (788660338)
% 0.21/0.50  ipcrm: permission denied for id (786694259)
% 0.21/0.50  ipcrm: permission denied for id (786727028)
% 0.21/0.50  ipcrm: permission denied for id (786792565)
% 0.21/0.51  ipcrm: permission denied for id (786825334)
% 0.21/0.51  ipcrm: permission denied for id (788693111)
% 0.21/0.51  ipcrm: permission denied for id (782991480)
% 0.21/0.51  ipcrm: permission denied for id (788725881)
% 0.21/0.51  ipcrm: permission denied for id (786923642)
% 0.21/0.51  ipcrm: permission denied for id (788824189)
% 0.21/0.52  ipcrm: permission denied for id (787054718)
% 0.21/0.52  ipcrm: permission denied for id (787087487)
% 0.72/0.60  % (16369)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.72/0.62  % (16377)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.72/0.62  % (16366)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.72/0.62  % (16376)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.72/0.62  % (16371)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.72/0.62  % (16369)Refutation found. Thanks to Tanya!
% 0.72/0.62  % SZS status Theorem for theBenchmark
% 0.72/0.62  % SZS output start Proof for theBenchmark
% 0.72/0.62  fof(f512,plain,(
% 0.72/0.62    $false),
% 0.72/0.62    inference(avatar_sat_refutation,[],[f25,f30,f35,f39,f43,f47,f51,f55,f75,f86,f98,f112,f184,f229,f364,f490])).
% 0.72/0.62  fof(f490,plain,(
% 0.72/0.62    spl3_11 | ~spl3_13 | ~spl3_29),
% 0.72/0.62    inference(avatar_contradiction_clause,[],[f489])).
% 0.72/0.62  fof(f489,plain,(
% 0.72/0.62    $false | (spl3_11 | ~spl3_13 | ~spl3_29)),
% 0.72/0.62    inference(subsumption_resolution,[],[f97,f465])).
% 0.72/0.62  fof(f465,plain,(
% 0.72/0.62    sK0 = k4_xboole_0(sK0,sK1) | (~spl3_13 | ~spl3_29)),
% 0.72/0.62    inference(superposition,[],[f363,f111])).
% 0.72/0.62  fof(f111,plain,(
% 0.72/0.62    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) | ~spl3_13),
% 0.72/0.62    inference(avatar_component_clause,[],[f109])).
% 0.72/0.62  fof(f109,plain,(
% 0.72/0.62    spl3_13 <=> sK0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 0.72/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.72/0.62  fof(f363,plain,(
% 0.72/0.62    ( ! [X0] : (k4_xboole_0(sK0,k4_xboole_0(X0,sK2)) = k4_xboole_0(sK0,X0)) ) | ~spl3_29),
% 0.72/0.62    inference(avatar_component_clause,[],[f362])).
% 0.72/0.62  fof(f362,plain,(
% 0.72/0.62    spl3_29 <=> ! [X0] : k4_xboole_0(sK0,k4_xboole_0(X0,sK2)) = k4_xboole_0(sK0,X0)),
% 0.72/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.72/0.62  fof(f97,plain,(
% 0.72/0.62    sK0 != k4_xboole_0(sK0,sK1) | spl3_11),
% 0.72/0.62    inference(avatar_component_clause,[],[f95])).
% 0.72/0.62  fof(f95,plain,(
% 0.72/0.62    spl3_11 <=> sK0 = k4_xboole_0(sK0,sK1)),
% 0.72/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.72/0.62  fof(f364,plain,(
% 0.72/0.62    spl3_29 | ~spl3_9 | ~spl3_21 | ~spl3_24),
% 0.72/0.62    inference(avatar_split_clause,[],[f297,f226,f182,f73,f362])).
% 0.72/0.62  fof(f73,plain,(
% 0.72/0.62    spl3_9 <=> ! [X1,X0,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 0.72/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.72/0.62  fof(f182,plain,(
% 0.72/0.62    spl3_21 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0)),
% 0.72/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.72/0.62  fof(f226,plain,(
% 0.72/0.62    spl3_24 <=> k1_xboole_0 = k3_xboole_0(sK0,sK2)),
% 0.72/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.72/0.62  fof(f297,plain,(
% 0.72/0.62    ( ! [X0] : (k4_xboole_0(sK0,k4_xboole_0(X0,sK2)) = k4_xboole_0(sK0,X0)) ) | (~spl3_9 | ~spl3_21 | ~spl3_24)),
% 0.72/0.62    inference(forward_demodulation,[],[f291,f183])).
% 0.72/0.62  fof(f183,plain,(
% 0.72/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0)) ) | ~spl3_21),
% 0.72/0.62    inference(avatar_component_clause,[],[f182])).
% 0.72/0.62  fof(f291,plain,(
% 0.72/0.62    ( ! [X0] : (k4_xboole_0(sK0,k4_xboole_0(X0,sK2)) = k2_xboole_0(k4_xboole_0(sK0,X0),k1_xboole_0)) ) | (~spl3_9 | ~spl3_24)),
% 0.72/0.62    inference(superposition,[],[f74,f228])).
% 0.72/0.62  fof(f228,plain,(
% 0.72/0.62    k1_xboole_0 = k3_xboole_0(sK0,sK2) | ~spl3_24),
% 0.72/0.62    inference(avatar_component_clause,[],[f226])).
% 0.72/0.62  fof(f74,plain,(
% 0.72/0.62    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))) ) | ~spl3_9),
% 0.72/0.62    inference(avatar_component_clause,[],[f73])).
% 0.72/0.62  fof(f229,plain,(
% 0.72/0.62    spl3_24 | ~spl3_4 | ~spl3_5 | ~spl3_8 | ~spl3_10),
% 0.72/0.62    inference(avatar_split_clause,[],[f93,f83,f53,f41,f37,f226])).
% 0.72/0.62  fof(f37,plain,(
% 0.72/0.62    spl3_4 <=> ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.72/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.72/0.62  fof(f41,plain,(
% 0.72/0.62    spl3_5 <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.72/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.72/0.62  fof(f53,plain,(
% 0.72/0.62    spl3_8 <=> ! [X1,X0] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.72/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.72/0.62  fof(f83,plain,(
% 0.72/0.62    spl3_10 <=> sK0 = k4_xboole_0(sK0,sK2)),
% 0.72/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.72/0.62  fof(f93,plain,(
% 0.72/0.62    k1_xboole_0 = k3_xboole_0(sK0,sK2) | (~spl3_4 | ~spl3_5 | ~spl3_8 | ~spl3_10)),
% 0.72/0.62    inference(forward_demodulation,[],[f89,f70])).
% 0.72/0.62  fof(f70,plain,(
% 0.72/0.62    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) ) | (~spl3_4 | ~spl3_5 | ~spl3_8)),
% 0.72/0.62    inference(forward_demodulation,[],[f64,f38])).
% 0.72/0.62  fof(f38,plain,(
% 0.72/0.62    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) ) | ~spl3_4),
% 0.72/0.62    inference(avatar_component_clause,[],[f37])).
% 0.72/0.62  fof(f64,plain,(
% 0.72/0.62    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0)) ) | (~spl3_5 | ~spl3_8)),
% 0.72/0.62    inference(superposition,[],[f54,f42])).
% 0.72/0.62  fof(f42,plain,(
% 0.72/0.62    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl3_5),
% 0.72/0.62    inference(avatar_component_clause,[],[f41])).
% 0.72/0.62  fof(f54,plain,(
% 0.72/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) ) | ~spl3_8),
% 0.72/0.62    inference(avatar_component_clause,[],[f53])).
% 0.72/0.62  fof(f89,plain,(
% 0.72/0.62    k3_xboole_0(sK0,sK2) = k4_xboole_0(sK0,sK0) | (~spl3_8 | ~spl3_10)),
% 0.72/0.62    inference(superposition,[],[f54,f85])).
% 0.72/0.62  fof(f85,plain,(
% 0.72/0.62    sK0 = k4_xboole_0(sK0,sK2) | ~spl3_10),
% 0.72/0.62    inference(avatar_component_clause,[],[f83])).
% 0.72/0.62  % (16370)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.72/0.62  fof(f184,plain,(
% 0.72/0.62    spl3_21 | ~spl3_4 | ~spl3_5 | ~spl3_9),
% 0.72/0.62    inference(avatar_split_clause,[],[f81,f73,f41,f37,f182])).
% 0.72/0.62  fof(f81,plain,(
% 0.72/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0)) ) | (~spl3_4 | ~spl3_5 | ~spl3_9)),
% 0.72/0.62    inference(forward_demodulation,[],[f79,f42])).
% 0.72/0.62  fof(f79,plain,(
% 0.72/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,k1_xboole_0)) = k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0)) ) | (~spl3_4 | ~spl3_9)),
% 0.72/0.62    inference(superposition,[],[f74,f38])).
% 0.72/0.62  fof(f112,plain,(
% 0.72/0.62    spl3_13 | ~spl3_3 | ~spl3_6),
% 0.72/0.62    inference(avatar_split_clause,[],[f57,f45,f32,f109])).
% 0.72/0.62  fof(f32,plain,(
% 0.72/0.62    spl3_3 <=> r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 0.72/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.72/0.62  fof(f45,plain,(
% 0.72/0.62    spl3_6 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1))),
% 0.72/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.72/0.62  fof(f57,plain,(
% 0.72/0.62    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) | (~spl3_3 | ~spl3_6)),
% 0.72/0.62    inference(unit_resulting_resolution,[],[f34,f46])).
% 0.72/0.62  fof(f46,plain,(
% 0.72/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) ) | ~spl3_6),
% 0.72/0.62    inference(avatar_component_clause,[],[f45])).
% 0.72/0.62  fof(f34,plain,(
% 0.72/0.62    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) | ~spl3_3),
% 0.72/0.62    inference(avatar_component_clause,[],[f32])).
% 0.72/0.62  fof(f98,plain,(
% 0.72/0.62    ~spl3_11 | spl3_1 | ~spl3_7),
% 0.72/0.62    inference(avatar_split_clause,[],[f59,f49,f22,f95])).
% 0.72/0.62  fof(f22,plain,(
% 0.72/0.62    spl3_1 <=> r1_xboole_0(sK0,sK1)),
% 0.72/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.72/0.62  fof(f49,plain,(
% 0.72/0.62    spl3_7 <=> ! [X1,X0] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0)),
% 0.72/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.72/0.62  fof(f59,plain,(
% 0.72/0.62    sK0 != k4_xboole_0(sK0,sK1) | (spl3_1 | ~spl3_7)),
% 0.72/0.62    inference(unit_resulting_resolution,[],[f24,f50])).
% 0.72/0.62  fof(f50,plain,(
% 0.72/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) ) | ~spl3_7),
% 0.72/0.62    inference(avatar_component_clause,[],[f49])).
% 0.72/0.62  fof(f24,plain,(
% 0.72/0.62    ~r1_xboole_0(sK0,sK1) | spl3_1),
% 0.72/0.62    inference(avatar_component_clause,[],[f22])).
% 0.72/0.62  fof(f86,plain,(
% 0.72/0.62    spl3_10 | ~spl3_2 | ~spl3_6),
% 0.72/0.62    inference(avatar_split_clause,[],[f56,f45,f27,f83])).
% 0.72/0.62  fof(f27,plain,(
% 0.72/0.62    spl3_2 <=> r1_xboole_0(sK0,sK2)),
% 0.72/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.72/0.62  fof(f56,plain,(
% 0.72/0.62    sK0 = k4_xboole_0(sK0,sK2) | (~spl3_2 | ~spl3_6)),
% 0.72/0.62    inference(unit_resulting_resolution,[],[f29,f46])).
% 0.72/0.62  fof(f29,plain,(
% 0.72/0.62    r1_xboole_0(sK0,sK2) | ~spl3_2),
% 0.72/0.62    inference(avatar_component_clause,[],[f27])).
% 0.72/0.62  fof(f75,plain,(
% 0.72/0.62    spl3_9),
% 0.72/0.62    inference(avatar_split_clause,[],[f20,f73])).
% 0.72/0.62  fof(f20,plain,(
% 0.72/0.62    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 0.72/0.62    inference(cnf_transformation,[],[f4])).
% 0.72/0.62  fof(f4,axiom,(
% 0.72/0.62    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 0.72/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).
% 0.72/0.62  fof(f55,plain,(
% 0.72/0.62    spl3_8),
% 0.72/0.62    inference(avatar_split_clause,[],[f17,f53])).
% 0.72/0.62  fof(f17,plain,(
% 0.72/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.72/0.62    inference(cnf_transformation,[],[f3])).
% 0.72/0.62  fof(f3,axiom,(
% 0.72/0.62    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.72/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.72/0.62  fof(f51,plain,(
% 0.72/0.62    spl3_7),
% 0.72/0.62    inference(avatar_split_clause,[],[f19,f49])).
% 0.72/0.62  fof(f19,plain,(
% 0.72/0.62    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 0.72/0.62    inference(cnf_transformation,[],[f11])).
% 0.72/0.62  fof(f11,plain,(
% 0.72/0.62    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.72/0.62    inference(nnf_transformation,[],[f5])).
% 0.72/0.62  fof(f5,axiom,(
% 0.72/0.62    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.72/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.72/0.62  fof(f47,plain,(
% 0.72/0.62    spl3_6),
% 0.72/0.62    inference(avatar_split_clause,[],[f18,f45])).
% 0.72/0.62  fof(f18,plain,(
% 0.72/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 0.72/0.62    inference(cnf_transformation,[],[f11])).
% 0.72/0.62  fof(f43,plain,(
% 0.72/0.62    spl3_5),
% 0.72/0.62    inference(avatar_split_clause,[],[f16,f41])).
% 0.72/0.62  fof(f16,plain,(
% 0.72/0.62    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.72/0.62    inference(cnf_transformation,[],[f2])).
% 0.72/0.63  fof(f2,axiom,(
% 0.72/0.63    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.72/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.72/0.63  fof(f39,plain,(
% 0.72/0.63    spl3_4),
% 0.72/0.63    inference(avatar_split_clause,[],[f15,f37])).
% 0.72/0.63  fof(f15,plain,(
% 0.72/0.63    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.72/0.63    inference(cnf_transformation,[],[f1])).
% 0.72/0.63  fof(f1,axiom,(
% 0.72/0.63    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.72/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.72/0.63  fof(f35,plain,(
% 0.72/0.63    spl3_3),
% 0.72/0.63    inference(avatar_split_clause,[],[f14,f32])).
% 0.72/0.63  fof(f14,plain,(
% 0.72/0.63    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 0.72/0.63    inference(cnf_transformation,[],[f10])).
% 0.72/0.63  fof(f10,plain,(
% 0.72/0.63    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) & r1_xboole_0(sK0,sK2) & ~r1_xboole_0(sK0,sK1)),
% 0.72/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f9])).
% 0.72/0.63  fof(f9,plain,(
% 0.72/0.63    ? [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) & r1_xboole_0(X0,X2) & ~r1_xboole_0(X0,X1)) => (r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) & r1_xboole_0(sK0,sK2) & ~r1_xboole_0(sK0,sK1))),
% 0.72/0.63    introduced(choice_axiom,[])).
% 0.72/0.63  fof(f8,plain,(
% 0.72/0.63    ? [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) & r1_xboole_0(X0,X2) & ~r1_xboole_0(X0,X1))),
% 0.72/0.63    inference(ennf_transformation,[],[f7])).
% 0.72/0.63  fof(f7,negated_conjecture,(
% 0.72/0.63    ~! [X0,X1,X2] : ~(r1_xboole_0(X0,k4_xboole_0(X1,X2)) & r1_xboole_0(X0,X2) & ~r1_xboole_0(X0,X1))),
% 0.72/0.63    inference(negated_conjecture,[],[f6])).
% 0.72/0.63  fof(f6,conjecture,(
% 0.72/0.63    ! [X0,X1,X2] : ~(r1_xboole_0(X0,k4_xboole_0(X1,X2)) & r1_xboole_0(X0,X2) & ~r1_xboole_0(X0,X1))),
% 0.72/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_xboole_1)).
% 0.72/0.63  fof(f30,plain,(
% 0.72/0.63    spl3_2),
% 0.72/0.63    inference(avatar_split_clause,[],[f13,f27])).
% 0.72/0.63  fof(f13,plain,(
% 0.72/0.63    r1_xboole_0(sK0,sK2)),
% 0.72/0.63    inference(cnf_transformation,[],[f10])).
% 0.72/0.63  fof(f25,plain,(
% 0.72/0.63    ~spl3_1),
% 0.72/0.63    inference(avatar_split_clause,[],[f12,f22])).
% 0.72/0.63  fof(f12,plain,(
% 0.72/0.63    ~r1_xboole_0(sK0,sK1)),
% 0.72/0.63    inference(cnf_transformation,[],[f10])).
% 0.72/0.63  % SZS output end Proof for theBenchmark
% 0.72/0.63  % (16369)------------------------------
% 0.72/0.63  % (16369)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.72/0.63  % (16369)Termination reason: Refutation
% 0.72/0.63  
% 0.72/0.63  % (16369)Memory used [KB]: 6396
% 0.72/0.63  % (16369)Time elapsed: 0.059 s
% 0.72/0.63  % (16369)------------------------------
% 0.72/0.63  % (16369)------------------------------
% 0.72/0.63  % (16193)Success in time 0.263 s
%------------------------------------------------------------------------------
