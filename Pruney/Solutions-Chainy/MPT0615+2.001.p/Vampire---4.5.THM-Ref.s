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
% DateTime   : Thu Dec  3 12:51:43 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 134 expanded)
%              Number of leaves         :   13 (  41 expanded)
%              Depth                    :   13
%              Number of atoms          :  175 ( 561 expanded)
%              Number of equality atoms :   17 (  20 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (20632)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
fof(f762,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f61,f62,f715,f759])).

fof(f759,plain,
    ( ~ spl2_1
    | spl2_2 ),
    inference(avatar_contradiction_clause,[],[f758])).

fof(f758,plain,
    ( $false
    | ~ spl2_1
    | spl2_2 ),
    inference(subsumption_resolution,[],[f749,f60])).

fof(f60,plain,
    ( ~ r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0)))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl2_2
  <=> r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f749,plain,
    ( r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0)))
    | ~ spl2_1 ),
    inference(superposition,[],[f725,f67])).

fof(f67,plain,(
    sK0 = k7_relat_1(sK0,k1_relat_1(sK0)) ),
    inference(resolution,[],[f37,f33])).

fof(f33,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ( ~ r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0)))
      | ~ r1_tarski(sK0,sK1) )
    & ( r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0)))
      | r1_tarski(sK0,sK1) )
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f28,f27])).

fof(f27,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0)))
              | ~ r1_tarski(X0,X1) )
            & ( r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0)))
              | r1_tarski(X0,X1) )
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ( ~ r1_tarski(sK0,k7_relat_1(X1,k1_relat_1(sK0)))
            | ~ r1_tarski(sK0,X1) )
          & ( r1_tarski(sK0,k7_relat_1(X1,k1_relat_1(sK0)))
            | r1_tarski(sK0,X1) )
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X1] :
        ( ( ~ r1_tarski(sK0,k7_relat_1(X1,k1_relat_1(sK0)))
          | ~ r1_tarski(sK0,X1) )
        & ( r1_tarski(sK0,k7_relat_1(X1,k1_relat_1(sK0)))
          | r1_tarski(sK0,X1) )
        & v1_relat_1(X1) )
   => ( ( ~ r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0)))
        | ~ r1_tarski(sK0,sK1) )
      & ( r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0)))
        | r1_tarski(sK0,sK1) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0)))
            | ~ r1_tarski(X0,X1) )
          & ( r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0)))
            | r1_tarski(X0,X1) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0)))
            | ~ r1_tarski(X0,X1) )
          & ( r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0)))
            | r1_tarski(X0,X1) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r1_tarski(X0,X1)
          <~> r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0))) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_tarski(X0,X1)
            <=> r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0))) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
          <=> r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t219_relat_1)).

fof(f37,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

% (20623)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
fof(f725,plain,
    ( ! [X0] : r1_tarski(k7_relat_1(sK0,X0),k7_relat_1(sK1,X0))
    | ~ spl2_1 ),
    inference(subsumption_resolution,[],[f724,f33])).

fof(f724,plain,
    ( ! [X0] :
        ( r1_tarski(k7_relat_1(sK0,X0),k7_relat_1(sK1,X0))
        | ~ v1_relat_1(sK0) )
    | ~ spl2_1 ),
    inference(subsumption_resolution,[],[f716,f34])).

fof(f34,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f716,plain,
    ( ! [X0] :
        ( r1_tarski(k7_relat_1(sK0,X0),k7_relat_1(sK1,X0))
        | ~ v1_relat_1(sK1)
        | ~ v1_relat_1(sK0) )
    | ~ spl2_1 ),
    inference(resolution,[],[f55,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_relat_1)).

fof(f55,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl2_1
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f715,plain,
    ( spl2_1
    | ~ spl2_2 ),
    inference(avatar_contradiction_clause,[],[f714])).

fof(f714,plain,
    ( $false
    | spl2_1
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f687,f56])).

fof(f56,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f54])).

fof(f687,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl2_2 ),
    inference(superposition,[],[f113,f300])).

fof(f300,plain,(
    ! [X1] : sK1 = k2_xboole_0(sK1,k7_relat_1(sK1,X1)) ),
    inference(superposition,[],[f128,f177])).

fof(f177,plain,(
    ! [X1] : sK1 = k7_relat_1(sK1,k2_xboole_0(k1_relat_1(sK1),X1)) ),
    inference(resolution,[],[f90,f34])).

fof(f90,plain,(
    ! [X2,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,k2_xboole_0(k1_relat_1(X1),X2)) = X1 ) ),
    inference(resolution,[],[f41,f39])).

fof(f39,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | k7_relat_1(X1,X0) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

fof(f128,plain,(
    ! [X0] : k7_relat_1(sK1,k2_xboole_0(k1_relat_1(sK1),X0)) = k2_xboole_0(sK1,k7_relat_1(sK1,X0)) ),
    inference(superposition,[],[f106,f68])).

fof(f68,plain,(
    sK1 = k7_relat_1(sK1,k1_relat_1(sK1)) ),
    inference(resolution,[],[f37,f34])).

fof(f106,plain,(
    ! [X2,X3] : k7_relat_1(sK1,k2_xboole_0(X2,X3)) = k2_xboole_0(k7_relat_1(sK1,X2),k7_relat_1(sK1,X3)) ),
    inference(resolution,[],[f48,f34])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_relat_1)).

fof(f113,plain,
    ( ! [X0] : r1_tarski(sK0,k2_xboole_0(X0,k7_relat_1(sK1,k1_relat_1(sK0))))
    | ~ spl2_2 ),
    inference(resolution,[],[f110,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X0,X1),X2)
      | r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f110,plain,
    ( ! [X0] : r1_tarski(k4_xboole_0(sK0,X0),k7_relat_1(sK1,k1_relat_1(sK0)))
    | ~ spl2_2 ),
    inference(resolution,[],[f82,f40])).

fof(f40,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f82,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | r1_tarski(X0,k7_relat_1(sK1,k1_relat_1(sK0))) )
    | ~ spl2_2 ),
    inference(resolution,[],[f50,f59])).

fof(f59,plain,
    ( r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0)))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f58])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f62,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f35,f58,f54])).

fof(f35,plain,
    ( r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0)))
    | r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f61,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f36,f58,f54])).

fof(f36,plain,
    ( ~ r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0)))
    | ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:32:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (20628)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.46  % (20636)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.50  % (20625)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.50  % (20622)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.51  % (20628)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  % (20632)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.51  fof(f762,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(avatar_sat_refutation,[],[f61,f62,f715,f759])).
% 0.20/0.51  fof(f759,plain,(
% 0.20/0.51    ~spl2_1 | spl2_2),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f758])).
% 0.20/0.51  fof(f758,plain,(
% 0.20/0.51    $false | (~spl2_1 | spl2_2)),
% 0.20/0.51    inference(subsumption_resolution,[],[f749,f60])).
% 0.20/0.51  fof(f60,plain,(
% 0.20/0.51    ~r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0))) | spl2_2),
% 0.20/0.51    inference(avatar_component_clause,[],[f58])).
% 0.20/0.51  fof(f58,plain,(
% 0.20/0.51    spl2_2 <=> r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.51  fof(f749,plain,(
% 0.20/0.51    r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0))) | ~spl2_1),
% 0.20/0.51    inference(superposition,[],[f725,f67])).
% 0.20/0.51  fof(f67,plain,(
% 0.20/0.51    sK0 = k7_relat_1(sK0,k1_relat_1(sK0))),
% 0.20/0.51    inference(resolution,[],[f37,f33])).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    v1_relat_1(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f29])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    ((~r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0))) | ~r1_tarski(sK0,sK1)) & (r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0))) | r1_tarski(sK0,sK1)) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f28,f27])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : ((~r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0))) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0))) | r1_tarski(X0,X1)) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : ((~r1_tarski(sK0,k7_relat_1(X1,k1_relat_1(sK0))) | ~r1_tarski(sK0,X1)) & (r1_tarski(sK0,k7_relat_1(X1,k1_relat_1(sK0))) | r1_tarski(sK0,X1)) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    ? [X1] : ((~r1_tarski(sK0,k7_relat_1(X1,k1_relat_1(sK0))) | ~r1_tarski(sK0,X1)) & (r1_tarski(sK0,k7_relat_1(X1,k1_relat_1(sK0))) | r1_tarski(sK0,X1)) & v1_relat_1(X1)) => ((~r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0))) | ~r1_tarski(sK0,sK1)) & (r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0))) | r1_tarski(sK0,sK1)) & v1_relat_1(sK1))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : ((~r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0))) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0))) | r1_tarski(X0,X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.20/0.51    inference(flattening,[],[f25])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : (((~r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0))) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0))) | r1_tarski(X0,X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.20/0.51    inference(nnf_transformation,[],[f14])).
% 0.20/0.51  fof(f14,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : ((r1_tarski(X0,X1) <~> r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0)))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f13])).
% 0.20/0.51  fof(f13,negated_conjecture,(
% 0.20/0.51    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) <=> r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0))))))),
% 0.20/0.51    inference(negated_conjecture,[],[f12])).
% 0.20/0.51  fof(f12,conjecture,(
% 0.20/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) <=> r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0))))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t219_relat_1)).
% 0.20/0.51  fof(f37,plain,(
% 0.20/0.51    ( ! [X0] : (~v1_relat_1(X0) | k7_relat_1(X0,k1_relat_1(X0)) = X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f15])).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f11])).
% 0.20/0.51  fof(f11,axiom,(
% 0.20/0.51    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).
% 0.20/0.51  % (20623)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.51  fof(f725,plain,(
% 0.20/0.51    ( ! [X0] : (r1_tarski(k7_relat_1(sK0,X0),k7_relat_1(sK1,X0))) ) | ~spl2_1),
% 0.20/0.51    inference(subsumption_resolution,[],[f724,f33])).
% 0.20/0.51  fof(f724,plain,(
% 0.20/0.51    ( ! [X0] : (r1_tarski(k7_relat_1(sK0,X0),k7_relat_1(sK1,X0)) | ~v1_relat_1(sK0)) ) | ~spl2_1),
% 0.20/0.51    inference(subsumption_resolution,[],[f716,f34])).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    v1_relat_1(sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f29])).
% 0.20/0.51  fof(f716,plain,(
% 0.20/0.51    ( ! [X0] : (r1_tarski(k7_relat_1(sK0,X0),k7_relat_1(sK1,X0)) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0)) ) | ~spl2_1),
% 0.20/0.51    inference(resolution,[],[f55,f42])).
% 0.20/0.51  fof(f42,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f20])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ! [X0,X1] : (! [X2] : (r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.20/0.51    inference(flattening,[],[f19])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    ! [X0,X1] : (! [X2] : ((r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,axiom,(
% 0.20/0.51    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X1,X2) => r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_relat_1)).
% 0.20/0.51  fof(f55,plain,(
% 0.20/0.51    r1_tarski(sK0,sK1) | ~spl2_1),
% 0.20/0.51    inference(avatar_component_clause,[],[f54])).
% 0.20/0.51  fof(f54,plain,(
% 0.20/0.51    spl2_1 <=> r1_tarski(sK0,sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.51  fof(f715,plain,(
% 0.20/0.51    spl2_1 | ~spl2_2),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f714])).
% 0.20/0.51  fof(f714,plain,(
% 0.20/0.51    $false | (spl2_1 | ~spl2_2)),
% 0.20/0.51    inference(subsumption_resolution,[],[f687,f56])).
% 0.20/0.51  fof(f56,plain,(
% 0.20/0.51    ~r1_tarski(sK0,sK1) | spl2_1),
% 0.20/0.51    inference(avatar_component_clause,[],[f54])).
% 0.20/0.51  fof(f687,plain,(
% 0.20/0.51    r1_tarski(sK0,sK1) | ~spl2_2),
% 0.20/0.51    inference(superposition,[],[f113,f300])).
% 0.20/0.51  fof(f300,plain,(
% 0.20/0.51    ( ! [X1] : (sK1 = k2_xboole_0(sK1,k7_relat_1(sK1,X1))) )),
% 0.20/0.51    inference(superposition,[],[f128,f177])).
% 0.20/0.51  fof(f177,plain,(
% 0.20/0.51    ( ! [X1] : (sK1 = k7_relat_1(sK1,k2_xboole_0(k1_relat_1(sK1),X1))) )),
% 0.20/0.51    inference(resolution,[],[f90,f34])).
% 0.20/0.51  fof(f90,plain,(
% 0.20/0.51    ( ! [X2,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,k2_xboole_0(k1_relat_1(X1),X2)) = X1) )),
% 0.20/0.51    inference(resolution,[],[f41,f39])).
% 0.20/0.51  fof(f39,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.20/0.51  fof(f41,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f18])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.20/0.51    inference(flattening,[],[f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f10])).
% 0.20/0.51  fof(f10,axiom,(
% 0.20/0.51    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).
% 0.20/0.51  fof(f128,plain,(
% 0.20/0.51    ( ! [X0] : (k7_relat_1(sK1,k2_xboole_0(k1_relat_1(sK1),X0)) = k2_xboole_0(sK1,k7_relat_1(sK1,X0))) )),
% 0.20/0.51    inference(superposition,[],[f106,f68])).
% 0.20/0.51  fof(f68,plain,(
% 0.20/0.51    sK1 = k7_relat_1(sK1,k1_relat_1(sK1))),
% 0.20/0.51    inference(resolution,[],[f37,f34])).
% 0.20/0.51  fof(f106,plain,(
% 0.20/0.51    ( ! [X2,X3] : (k7_relat_1(sK1,k2_xboole_0(X2,X3)) = k2_xboole_0(k7_relat_1(sK1,X2),k7_relat_1(sK1,X3))) )),
% 0.20/0.51    inference(resolution,[],[f48,f34])).
% 0.20/0.51  fof(f48,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f21])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (k7_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 0.20/0.51    inference(ennf_transformation,[],[f9])).
% 0.20/0.51  fof(f9,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_relat_1)).
% 0.20/0.51  fof(f113,plain,(
% 0.20/0.51    ( ! [X0] : (r1_tarski(sK0,k2_xboole_0(X0,k7_relat_1(sK1,k1_relat_1(sK0))))) ) | ~spl2_2),
% 0.20/0.51    inference(resolution,[],[f110,f49])).
% 0.20/0.51  fof(f49,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~r1_tarski(k4_xboole_0(X0,X1),X2) | r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 0.20/0.51    inference(ennf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).
% 0.20/0.51  fof(f110,plain,(
% 0.20/0.51    ( ! [X0] : (r1_tarski(k4_xboole_0(sK0,X0),k7_relat_1(sK1,k1_relat_1(sK0)))) ) | ~spl2_2),
% 0.20/0.51    inference(resolution,[],[f82,f40])).
% 0.20/0.51  fof(f40,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.20/0.51  fof(f82,plain,(
% 0.20/0.51    ( ! [X0] : (~r1_tarski(X0,sK0) | r1_tarski(X0,k7_relat_1(sK1,k1_relat_1(sK0)))) ) | ~spl2_2),
% 0.20/0.51    inference(resolution,[],[f50,f59])).
% 0.20/0.51  fof(f59,plain,(
% 0.20/0.51    r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0))) | ~spl2_2),
% 0.20/0.51    inference(avatar_component_clause,[],[f58])).
% 0.20/0.51  fof(f50,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f24])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.51    inference(flattening,[],[f23])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.51    inference(ennf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.20/0.51  fof(f62,plain,(
% 0.20/0.51    spl2_1 | spl2_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f35,f58,f54])).
% 0.20/0.51  fof(f35,plain,(
% 0.20/0.51    r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0))) | r1_tarski(sK0,sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f29])).
% 0.20/0.51  fof(f61,plain,(
% 0.20/0.51    ~spl2_1 | ~spl2_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f36,f58,f54])).
% 0.20/0.51  fof(f36,plain,(
% 0.20/0.51    ~r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0))) | ~r1_tarski(sK0,sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f29])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (20628)------------------------------
% 0.20/0.51  % (20628)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (20628)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (20628)Memory used [KB]: 11257
% 0.20/0.51  % (20628)Time elapsed: 0.085 s
% 0.20/0.51  % (20628)------------------------------
% 0.20/0.51  % (20628)------------------------------
% 0.20/0.51  % (20626)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.51  % (20617)Success in time 0.154 s
%------------------------------------------------------------------------------
