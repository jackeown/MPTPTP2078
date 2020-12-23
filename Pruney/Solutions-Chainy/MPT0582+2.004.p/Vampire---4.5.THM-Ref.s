%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:50 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 124 expanded)
%              Number of leaves         :   18 (  54 expanded)
%              Depth                    :    7
%              Number of atoms          :  212 ( 450 expanded)
%              Number of equality atoms :   21 (  31 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f103,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f28,f33,f38,f43,f48,f52,f56,f60,f66,f77,f85,f92,f102])).

fof(f102,plain,
    ( spl3_1
    | ~ spl3_2
    | ~ spl3_5
    | ~ spl3_13 ),
    inference(avatar_contradiction_clause,[],[f101])).

fof(f101,plain,
    ( $false
    | spl3_1
    | ~ spl3_2
    | ~ spl3_5
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f100,f47])).

fof(f47,plain,
    ( v1_relat_1(sK1)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl3_5
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f100,plain,
    ( ~ v1_relat_1(sK1)
    | spl3_1
    | ~ spl3_2
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f98,f32])).

fof(f32,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f30])).

fof(f30,plain,
    ( spl3_2
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f98,plain,
    ( ~ r1_tarski(sK2,sK1)
    | ~ v1_relat_1(sK1)
    | spl3_1
    | ~ spl3_13 ),
    inference(resolution,[],[f91,f27])).

fof(f27,plain,
    ( ~ r1_tarski(sK2,k7_relat_1(sK1,sK0))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f25])).

fof(f25,plain,
    ( spl3_1
  <=> r1_tarski(sK2,k7_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f91,plain,
    ( ! [X0] :
        ( r1_tarski(sK2,k7_relat_1(X0,sK0))
        | ~ r1_tarski(sK2,X0)
        | ~ v1_relat_1(X0) )
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl3_13
  <=> ! [X0] :
        ( r1_tarski(sK2,k7_relat_1(X0,sK0))
        | ~ r1_tarski(sK2,X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f92,plain,
    ( spl3_13
    | ~ spl3_4
    | ~ spl3_8
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f88,f81,f58,f40,f90])).

fof(f40,plain,
    ( spl3_4
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f58,plain,
    ( spl3_8
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
        | ~ r1_tarski(X1,X2)
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f81,plain,
    ( spl3_12
  <=> sK2 = k7_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f88,plain,
    ( ! [X0] :
        ( r1_tarski(sK2,k7_relat_1(X0,sK0))
        | ~ r1_tarski(sK2,X0)
        | ~ v1_relat_1(X0) )
    | ~ spl3_4
    | ~ spl3_8
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f86,f42])).

fof(f42,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f40])).

fof(f86,plain,
    ( ! [X0] :
        ( r1_tarski(sK2,k7_relat_1(X0,sK0))
        | ~ r1_tarski(sK2,X0)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(sK2) )
    | ~ spl3_8
    | ~ spl3_12 ),
    inference(superposition,[],[f59,f83])).

fof(f83,plain,
    ( sK2 = k7_relat_1(sK2,sK0)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f81])).

fof(f59,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
        | ~ r1_tarski(X1,X2)
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X1) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f58])).

fof(f85,plain,
    ( spl3_12
    | ~ spl3_9
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f79,f74,f64,f81])).

% (26711)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
fof(f64,plain,
    ( spl3_9
  <=> ! [X0] : k7_relat_1(sK2,X0) = k5_relat_1(k6_relat_1(X0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f74,plain,
    ( spl3_11
  <=> sK2 = k5_relat_1(k6_relat_1(sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f79,plain,
    ( sK2 = k7_relat_1(sK2,sK0)
    | ~ spl3_9
    | ~ spl3_11 ),
    inference(superposition,[],[f65,f76])).

fof(f76,plain,
    ( sK2 = k5_relat_1(k6_relat_1(sK0),sK2)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f74])).

fof(f65,plain,
    ( ! [X0] : k7_relat_1(sK2,X0) = k5_relat_1(k6_relat_1(X0),sK2)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f64])).

fof(f77,plain,
    ( spl3_11
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f72,f54,f40,f35,f74])).

fof(f35,plain,
    ( spl3_3
  <=> r1_tarski(k1_relat_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f54,plain,
    ( spl3_7
  <=> ! [X1,X0] :
        ( k5_relat_1(k6_relat_1(X0),X1) = X1
        | ~ r1_tarski(k1_relat_1(X1),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f72,plain,
    ( sK2 = k5_relat_1(k6_relat_1(sK0),sK2)
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f71,f42])).

fof(f71,plain,
    ( sK2 = k5_relat_1(k6_relat_1(sK0),sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_3
    | ~ spl3_7 ),
    inference(resolution,[],[f55,f37])).

fof(f37,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f35])).

fof(f55,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k1_relat_1(X1),X0)
        | k5_relat_1(k6_relat_1(X0),X1) = X1
        | ~ v1_relat_1(X1) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f54])).

fof(f66,plain,
    ( spl3_9
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f61,f50,f40,f64])).

fof(f50,plain,
    ( spl3_6
  <=> ! [X1,X0] :
        ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f61,plain,
    ( ! [X0] : k7_relat_1(sK2,X0) = k5_relat_1(k6_relat_1(X0),sK2)
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(resolution,[],[f51,f42])).

fof(f51,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f50])).

fof(f60,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f23,f58])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_relat_1)).

fof(f56,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f22,f54])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

fof(f52,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f21,f50])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f48,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f16,f45])).

fof(f16,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ~ r1_tarski(sK2,k7_relat_1(sK1,sK0))
    & r1_tarski(sK2,sK1)
    & r1_tarski(k1_relat_1(sK2),sK0)
    & v1_relat_1(sK2)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f14,f13])).

fof(f13,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(X2,k7_relat_1(X1,X0))
            & r1_tarski(X2,X1)
            & r1_tarski(k1_relat_1(X2),X0)
            & v1_relat_1(X2) )
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ~ r1_tarski(X2,k7_relat_1(sK1,sK0))
          & r1_tarski(X2,sK1)
          & r1_tarski(k1_relat_1(X2),sK0)
          & v1_relat_1(X2) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ? [X2] :
        ( ~ r1_tarski(X2,k7_relat_1(sK1,sK0))
        & r1_tarski(X2,sK1)
        & r1_tarski(k1_relat_1(X2),sK0)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(sK2,k7_relat_1(sK1,sK0))
      & r1_tarski(sK2,sK1)
      & r1_tarski(k1_relat_1(sK2),sK0)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,k7_relat_1(X1,X0))
          & r1_tarski(X2,X1)
          & r1_tarski(k1_relat_1(X2),X0)
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,k7_relat_1(X1,X0))
          & r1_tarski(X2,X1)
          & r1_tarski(k1_relat_1(X2),X0)
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ( ( r1_tarski(X2,X1)
                & r1_tarski(k1_relat_1(X2),X0) )
             => r1_tarski(X2,k7_relat_1(X1,X0)) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( ( r1_tarski(X2,X1)
              & r1_tarski(k1_relat_1(X2),X0) )
           => r1_tarski(X2,k7_relat_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t186_relat_1)).

fof(f43,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f17,f40])).

fof(f17,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f38,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f18,f35])).

fof(f18,plain,(
    r1_tarski(k1_relat_1(sK2),sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f33,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f19,f30])).

fof(f19,plain,(
    r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f28,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f20,f25])).

fof(f20,plain,(
    ~ r1_tarski(sK2,k7_relat_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:45:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.41  % (26714)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.21/0.41  % (26714)Refutation found. Thanks to Tanya!
% 0.21/0.41  % SZS status Theorem for theBenchmark
% 0.21/0.41  % SZS output start Proof for theBenchmark
% 0.21/0.41  fof(f103,plain,(
% 0.21/0.41    $false),
% 0.21/0.41    inference(avatar_sat_refutation,[],[f28,f33,f38,f43,f48,f52,f56,f60,f66,f77,f85,f92,f102])).
% 0.21/0.41  fof(f102,plain,(
% 0.21/0.41    spl3_1 | ~spl3_2 | ~spl3_5 | ~spl3_13),
% 0.21/0.41    inference(avatar_contradiction_clause,[],[f101])).
% 0.21/0.41  fof(f101,plain,(
% 0.21/0.41    $false | (spl3_1 | ~spl3_2 | ~spl3_5 | ~spl3_13)),
% 0.21/0.41    inference(subsumption_resolution,[],[f100,f47])).
% 0.21/0.41  fof(f47,plain,(
% 0.21/0.41    v1_relat_1(sK1) | ~spl3_5),
% 0.21/0.41    inference(avatar_component_clause,[],[f45])).
% 0.21/0.41  fof(f45,plain,(
% 0.21/0.41    spl3_5 <=> v1_relat_1(sK1)),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.41  fof(f100,plain,(
% 0.21/0.41    ~v1_relat_1(sK1) | (spl3_1 | ~spl3_2 | ~spl3_13)),
% 0.21/0.41    inference(subsumption_resolution,[],[f98,f32])).
% 0.21/0.41  fof(f32,plain,(
% 0.21/0.41    r1_tarski(sK2,sK1) | ~spl3_2),
% 0.21/0.41    inference(avatar_component_clause,[],[f30])).
% 0.21/0.41  fof(f30,plain,(
% 0.21/0.41    spl3_2 <=> r1_tarski(sK2,sK1)),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.41  fof(f98,plain,(
% 0.21/0.41    ~r1_tarski(sK2,sK1) | ~v1_relat_1(sK1) | (spl3_1 | ~spl3_13)),
% 0.21/0.41    inference(resolution,[],[f91,f27])).
% 0.21/0.41  fof(f27,plain,(
% 0.21/0.41    ~r1_tarski(sK2,k7_relat_1(sK1,sK0)) | spl3_1),
% 0.21/0.41    inference(avatar_component_clause,[],[f25])).
% 0.21/0.41  fof(f25,plain,(
% 0.21/0.41    spl3_1 <=> r1_tarski(sK2,k7_relat_1(sK1,sK0))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.41  fof(f91,plain,(
% 0.21/0.41    ( ! [X0] : (r1_tarski(sK2,k7_relat_1(X0,sK0)) | ~r1_tarski(sK2,X0) | ~v1_relat_1(X0)) ) | ~spl3_13),
% 0.21/0.41    inference(avatar_component_clause,[],[f90])).
% 0.21/0.41  fof(f90,plain,(
% 0.21/0.41    spl3_13 <=> ! [X0] : (r1_tarski(sK2,k7_relat_1(X0,sK0)) | ~r1_tarski(sK2,X0) | ~v1_relat_1(X0))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.41  fof(f92,plain,(
% 0.21/0.41    spl3_13 | ~spl3_4 | ~spl3_8 | ~spl3_12),
% 0.21/0.41    inference(avatar_split_clause,[],[f88,f81,f58,f40,f90])).
% 0.21/0.41  fof(f40,plain,(
% 0.21/0.41    spl3_4 <=> v1_relat_1(sK2)),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.41  fof(f58,plain,(
% 0.21/0.41    spl3_8 <=> ! [X1,X0,X2] : (r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.41  fof(f81,plain,(
% 0.21/0.41    spl3_12 <=> sK2 = k7_relat_1(sK2,sK0)),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.41  fof(f88,plain,(
% 0.21/0.41    ( ! [X0] : (r1_tarski(sK2,k7_relat_1(X0,sK0)) | ~r1_tarski(sK2,X0) | ~v1_relat_1(X0)) ) | (~spl3_4 | ~spl3_8 | ~spl3_12)),
% 0.21/0.41    inference(subsumption_resolution,[],[f86,f42])).
% 0.21/0.41  fof(f42,plain,(
% 0.21/0.41    v1_relat_1(sK2) | ~spl3_4),
% 0.21/0.41    inference(avatar_component_clause,[],[f40])).
% 0.21/0.41  fof(f86,plain,(
% 0.21/0.41    ( ! [X0] : (r1_tarski(sK2,k7_relat_1(X0,sK0)) | ~r1_tarski(sK2,X0) | ~v1_relat_1(X0) | ~v1_relat_1(sK2)) ) | (~spl3_8 | ~spl3_12)),
% 0.21/0.41    inference(superposition,[],[f59,f83])).
% 0.21/0.41  fof(f83,plain,(
% 0.21/0.41    sK2 = k7_relat_1(sK2,sK0) | ~spl3_12),
% 0.21/0.41    inference(avatar_component_clause,[],[f81])).
% 0.21/0.41  fof(f59,plain,(
% 0.21/0.41    ( ! [X2,X0,X1] : (r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) ) | ~spl3_8),
% 0.21/0.41    inference(avatar_component_clause,[],[f58])).
% 0.21/0.41  fof(f85,plain,(
% 0.21/0.41    spl3_12 | ~spl3_9 | ~spl3_11),
% 0.21/0.41    inference(avatar_split_clause,[],[f79,f74,f64,f81])).
% 0.21/0.41  % (26711)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.21/0.41  fof(f64,plain,(
% 0.21/0.41    spl3_9 <=> ! [X0] : k7_relat_1(sK2,X0) = k5_relat_1(k6_relat_1(X0),sK2)),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.41  fof(f74,plain,(
% 0.21/0.41    spl3_11 <=> sK2 = k5_relat_1(k6_relat_1(sK0),sK2)),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.41  fof(f79,plain,(
% 0.21/0.41    sK2 = k7_relat_1(sK2,sK0) | (~spl3_9 | ~spl3_11)),
% 0.21/0.41    inference(superposition,[],[f65,f76])).
% 0.21/0.41  fof(f76,plain,(
% 0.21/0.41    sK2 = k5_relat_1(k6_relat_1(sK0),sK2) | ~spl3_11),
% 0.21/0.41    inference(avatar_component_clause,[],[f74])).
% 0.21/0.41  fof(f65,plain,(
% 0.21/0.41    ( ! [X0] : (k7_relat_1(sK2,X0) = k5_relat_1(k6_relat_1(X0),sK2)) ) | ~spl3_9),
% 0.21/0.41    inference(avatar_component_clause,[],[f64])).
% 0.21/0.41  fof(f77,plain,(
% 0.21/0.41    spl3_11 | ~spl3_3 | ~spl3_4 | ~spl3_7),
% 0.21/0.41    inference(avatar_split_clause,[],[f72,f54,f40,f35,f74])).
% 0.21/0.41  fof(f35,plain,(
% 0.21/0.41    spl3_3 <=> r1_tarski(k1_relat_1(sK2),sK0)),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.41  fof(f54,plain,(
% 0.21/0.41    spl3_7 <=> ! [X1,X0] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.41  fof(f72,plain,(
% 0.21/0.41    sK2 = k5_relat_1(k6_relat_1(sK0),sK2) | (~spl3_3 | ~spl3_4 | ~spl3_7)),
% 0.21/0.41    inference(subsumption_resolution,[],[f71,f42])).
% 0.21/0.41  fof(f71,plain,(
% 0.21/0.41    sK2 = k5_relat_1(k6_relat_1(sK0),sK2) | ~v1_relat_1(sK2) | (~spl3_3 | ~spl3_7)),
% 0.21/0.41    inference(resolution,[],[f55,f37])).
% 0.21/0.41  fof(f37,plain,(
% 0.21/0.41    r1_tarski(k1_relat_1(sK2),sK0) | ~spl3_3),
% 0.21/0.41    inference(avatar_component_clause,[],[f35])).
% 0.21/0.41  fof(f55,plain,(
% 0.21/0.41    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | k5_relat_1(k6_relat_1(X0),X1) = X1 | ~v1_relat_1(X1)) ) | ~spl3_7),
% 0.21/0.41    inference(avatar_component_clause,[],[f54])).
% 0.21/0.41  fof(f66,plain,(
% 0.21/0.41    spl3_9 | ~spl3_4 | ~spl3_6),
% 0.21/0.41    inference(avatar_split_clause,[],[f61,f50,f40,f64])).
% 0.21/0.41  fof(f50,plain,(
% 0.21/0.41    spl3_6 <=> ! [X1,X0] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.41  fof(f61,plain,(
% 0.21/0.41    ( ! [X0] : (k7_relat_1(sK2,X0) = k5_relat_1(k6_relat_1(X0),sK2)) ) | (~spl3_4 | ~spl3_6)),
% 0.21/0.41    inference(resolution,[],[f51,f42])).
% 0.21/0.41  fof(f51,plain,(
% 0.21/0.41    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) ) | ~spl3_6),
% 0.21/0.41    inference(avatar_component_clause,[],[f50])).
% 0.21/0.41  fof(f60,plain,(
% 0.21/0.41    spl3_8),
% 0.21/0.41    inference(avatar_split_clause,[],[f23,f58])).
% 0.21/0.41  fof(f23,plain,(
% 0.21/0.41    ( ! [X2,X0,X1] : (r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f12])).
% 0.21/0.41  fof(f12,plain,(
% 0.21/0.41    ! [X0,X1] : (! [X2] : (r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.21/0.41    inference(flattening,[],[f11])).
% 0.21/0.41  fof(f11,plain,(
% 0.21/0.41    ! [X0,X1] : (! [X2] : ((r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.21/0.41    inference(ennf_transformation,[],[f1])).
% 0.21/0.41  fof(f1,axiom,(
% 0.21/0.41    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X1,X2) => r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)))))),
% 0.21/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_relat_1)).
% 0.21/0.41  fof(f56,plain,(
% 0.21/0.41    spl3_7),
% 0.21/0.41    inference(avatar_split_clause,[],[f22,f54])).
% 0.21/0.41  fof(f22,plain,(
% 0.21/0.41    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f10])).
% 0.21/0.41  fof(f10,plain,(
% 0.21/0.41    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.41    inference(flattening,[],[f9])).
% 0.21/0.41  fof(f9,plain,(
% 0.21/0.41    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.41    inference(ennf_transformation,[],[f2])).
% 0.21/0.41  fof(f2,axiom,(
% 0.21/0.41    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 0.21/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).
% 0.21/0.41  fof(f52,plain,(
% 0.21/0.41    spl3_6),
% 0.21/0.41    inference(avatar_split_clause,[],[f21,f50])).
% 0.21/0.41  fof(f21,plain,(
% 0.21/0.41    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f8])).
% 0.21/0.41  fof(f8,plain,(
% 0.21/0.41    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.21/0.41    inference(ennf_transformation,[],[f3])).
% 0.21/0.41  fof(f3,axiom,(
% 0.21/0.41    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.21/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 0.21/0.41  fof(f48,plain,(
% 0.21/0.41    spl3_5),
% 0.21/0.41    inference(avatar_split_clause,[],[f16,f45])).
% 0.21/0.41  fof(f16,plain,(
% 0.21/0.41    v1_relat_1(sK1)),
% 0.21/0.41    inference(cnf_transformation,[],[f15])).
% 0.21/0.41  fof(f15,plain,(
% 0.21/0.41    (~r1_tarski(sK2,k7_relat_1(sK1,sK0)) & r1_tarski(sK2,sK1) & r1_tarski(k1_relat_1(sK2),sK0) & v1_relat_1(sK2)) & v1_relat_1(sK1)),
% 0.21/0.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f14,f13])).
% 0.21/0.41  fof(f13,plain,(
% 0.21/0.41    ? [X0,X1] : (? [X2] : (~r1_tarski(X2,k7_relat_1(X1,X0)) & r1_tarski(X2,X1) & r1_tarski(k1_relat_1(X2),X0) & v1_relat_1(X2)) & v1_relat_1(X1)) => (? [X2] : (~r1_tarski(X2,k7_relat_1(sK1,sK0)) & r1_tarski(X2,sK1) & r1_tarski(k1_relat_1(X2),sK0) & v1_relat_1(X2)) & v1_relat_1(sK1))),
% 0.21/0.41    introduced(choice_axiom,[])).
% 0.21/0.41  fof(f14,plain,(
% 0.21/0.41    ? [X2] : (~r1_tarski(X2,k7_relat_1(sK1,sK0)) & r1_tarski(X2,sK1) & r1_tarski(k1_relat_1(X2),sK0) & v1_relat_1(X2)) => (~r1_tarski(sK2,k7_relat_1(sK1,sK0)) & r1_tarski(sK2,sK1) & r1_tarski(k1_relat_1(sK2),sK0) & v1_relat_1(sK2))),
% 0.21/0.41    introduced(choice_axiom,[])).
% 0.21/0.41  fof(f7,plain,(
% 0.21/0.41    ? [X0,X1] : (? [X2] : (~r1_tarski(X2,k7_relat_1(X1,X0)) & r1_tarski(X2,X1) & r1_tarski(k1_relat_1(X2),X0) & v1_relat_1(X2)) & v1_relat_1(X1))),
% 0.21/0.41    inference(flattening,[],[f6])).
% 0.21/0.41  fof(f6,plain,(
% 0.21/0.41    ? [X0,X1] : (? [X2] : ((~r1_tarski(X2,k7_relat_1(X1,X0)) & (r1_tarski(X2,X1) & r1_tarski(k1_relat_1(X2),X0))) & v1_relat_1(X2)) & v1_relat_1(X1))),
% 0.21/0.41    inference(ennf_transformation,[],[f5])).
% 0.21/0.41  fof(f5,negated_conjecture,(
% 0.21/0.41    ~! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => ((r1_tarski(X2,X1) & r1_tarski(k1_relat_1(X2),X0)) => r1_tarski(X2,k7_relat_1(X1,X0)))))),
% 0.21/0.41    inference(negated_conjecture,[],[f4])).
% 0.21/0.41  fof(f4,conjecture,(
% 0.21/0.41    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => ((r1_tarski(X2,X1) & r1_tarski(k1_relat_1(X2),X0)) => r1_tarski(X2,k7_relat_1(X1,X0)))))),
% 0.21/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t186_relat_1)).
% 0.21/0.41  fof(f43,plain,(
% 0.21/0.41    spl3_4),
% 0.21/0.41    inference(avatar_split_clause,[],[f17,f40])).
% 0.21/0.41  fof(f17,plain,(
% 0.21/0.41    v1_relat_1(sK2)),
% 0.21/0.41    inference(cnf_transformation,[],[f15])).
% 0.21/0.41  fof(f38,plain,(
% 0.21/0.41    spl3_3),
% 0.21/0.41    inference(avatar_split_clause,[],[f18,f35])).
% 0.21/0.41  fof(f18,plain,(
% 0.21/0.41    r1_tarski(k1_relat_1(sK2),sK0)),
% 0.21/0.41    inference(cnf_transformation,[],[f15])).
% 0.21/0.41  fof(f33,plain,(
% 0.21/0.41    spl3_2),
% 0.21/0.41    inference(avatar_split_clause,[],[f19,f30])).
% 0.21/0.41  fof(f19,plain,(
% 0.21/0.41    r1_tarski(sK2,sK1)),
% 0.21/0.41    inference(cnf_transformation,[],[f15])).
% 0.21/0.41  fof(f28,plain,(
% 0.21/0.41    ~spl3_1),
% 0.21/0.41    inference(avatar_split_clause,[],[f20,f25])).
% 0.21/0.41  fof(f20,plain,(
% 0.21/0.41    ~r1_tarski(sK2,k7_relat_1(sK1,sK0))),
% 0.21/0.41    inference(cnf_transformation,[],[f15])).
% 0.21/0.41  % SZS output end Proof for theBenchmark
% 0.21/0.41  % (26714)------------------------------
% 0.21/0.41  % (26714)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.41  % (26714)Termination reason: Refutation
% 0.21/0.41  
% 0.21/0.41  % (26714)Memory used [KB]: 6140
% 0.21/0.41  % (26714)Time elapsed: 0.005 s
% 0.21/0.41  % (26714)------------------------------
% 0.21/0.41  % (26714)------------------------------
% 0.21/0.41  % (26703)Success in time 0.059 s
%------------------------------------------------------------------------------
