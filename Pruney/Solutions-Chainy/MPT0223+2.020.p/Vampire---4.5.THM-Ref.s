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
% DateTime   : Thu Dec  3 12:35:53 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 199 expanded)
%              Number of leaves         :   14 (  55 expanded)
%              Depth                    :   21
%              Number of atoms          :  175 ( 589 expanded)
%              Number of equality atoms :   69 ( 309 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f632,plain,(
    $false ),
    inference(subsumption_resolution,[],[f631,f40])).

fof(f40,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( sK0 != sK1
    & k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f24])).

fof(f24,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) )
   => ( sK0 != sK1
      & k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_zfmisc_1)).

fof(f631,plain,(
    sK0 = sK1 ),
    inference(resolution,[],[f591,f73])).

fof(f73,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK3(X0,X1) != X0
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( sK3(X0,X1) = X0
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK3(X0,X1) != X0
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( sK3(X0,X1) = X0
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f591,plain,(
    r2_hidden(sK1,k1_tarski(sK0)) ),
    inference(subsumption_resolution,[],[f580,f72])).

fof(f72,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f580,plain,
    ( r2_hidden(sK1,k1_tarski(sK0))
    | ~ r2_hidden(sK1,k1_tarski(sK1)) ),
    inference(superposition,[],[f524,f39])).

fof(f39,plain,(
    k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f25])).

fof(f524,plain,(
    ! [X3] :
      ( r2_hidden(sK1,k3_xboole_0(k1_tarski(sK0),X3))
      | ~ r2_hidden(sK1,X3) ) ),
    inference(superposition,[],[f506,f43])).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f506,plain,(
    ! [X3] :
      ( r2_hidden(sK1,k3_xboole_0(X3,k1_tarski(sK0)))
      | ~ r2_hidden(sK1,X3) ) ),
    inference(resolution,[],[f142,f322])).

fof(f322,plain,(
    ! [X0] : ~ r2_hidden(sK1,k4_xboole_0(X0,k1_tarski(sK0))) ),
    inference(resolution,[],[f311,f42])).

fof(f42,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f311,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,k1_tarski(sK0))
      | ~ r2_hidden(sK1,X0) ) ),
    inference(resolution,[],[f92,f298])).

fof(f298,plain,(
    ! [X1] :
      ( r2_hidden(sK0,k3_xboole_0(k1_tarski(sK0),X1))
      | ~ r2_hidden(sK1,X1) ) ),
    inference(subsumption_resolution,[],[f297,f200])).

fof(f200,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(k1_tarski(sK0),X0)
      | ~ r2_hidden(sK1,X0) ) ),
    inference(superposition,[],[f189,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l22_zfmisc_1)).

fof(f189,plain,(
    ! [X1] : ~ r1_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),X1)) ),
    inference(subsumption_resolution,[],[f179,f114])).

fof(f114,plain,(
    k1_xboole_0 != k1_tarski(sK0) ),
    inference(resolution,[],[f109,f72])).

fof(f109,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_tarski(sK0))
      | k1_xboole_0 != k1_tarski(sK0) ) ),
    inference(resolution,[],[f104,f91])).

fof(f91,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
      | ~ r2_hidden(X0,k1_tarski(sK0)) ) ),
    inference(superposition,[],[f48,f39])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f104,plain,
    ( r1_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | k1_xboole_0 != k1_tarski(sK0) ),
    inference(superposition,[],[f51,f39])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f179,plain,(
    ! [X1] :
      ( k1_xboole_0 = k1_tarski(sK0)
      | ~ r1_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),X1)) ) ),
    inference(superposition,[],[f171,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f171,plain,(
    ! [X0] : k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),X0)) ),
    inference(forward_demodulation,[],[f159,f44])).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f159,plain,(
    ! [X0] : k3_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),X0)) = k2_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),X0)) ),
    inference(superposition,[],[f57,f39])).

fof(f57,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_xboole_1)).

fof(f297,plain,(
    ! [X1] :
      ( r2_hidden(sK0,k3_xboole_0(k1_tarski(sK0),X1))
      | r1_xboole_0(k1_tarski(sK0),X1)
      | ~ r2_hidden(sK1,X1) ) ),
    inference(superposition,[],[f47,f289])).

fof(f289,plain,(
    ! [X0] :
      ( sK0 = sK2(k1_tarski(sK0),X0)
      | ~ r2_hidden(sK1,X0) ) ),
    inference(superposition,[],[f244,f49])).

fof(f244,plain,(
    ! [X0] : sK0 = sK2(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),X0)) ),
    inference(resolution,[],[f190,f73])).

fof(f190,plain,(
    ! [X4] : r2_hidden(sK2(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),X4)),k1_tarski(sK0)) ),
    inference(subsumption_resolution,[],[f182,f189])).

fof(f182,plain,(
    ! [X4] :
      ( r2_hidden(sK2(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),X4)),k1_tarski(sK0))
      | r1_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),X4)) ) ),
    inference(superposition,[],[f47,f171])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f92,plain,(
    ! [X2,X3,X1] :
      ( ~ r2_hidden(X3,k3_xboole_0(X2,X1))
      | ~ r1_xboole_0(X1,X2) ) ),
    inference(superposition,[],[f48,f43])).

fof(f142,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k4_xboole_0(X0,X1))
      | r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X2,X0) ) ),
    inference(superposition,[],[f60,f46])).

fof(f46,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) ) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:23:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (26329)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.50  % (26321)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.50  % (26327)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.50  % (26320)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.50  % (26313)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (26314)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.51  % (26316)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.52  % (26335)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.52  % (26318)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.52  % (26311)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.53  % (26307)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.53  % (26334)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.53  % (26312)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.53  % (26308)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.53  % (26333)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.53  % (26308)Refutation not found, incomplete strategy% (26308)------------------------------
% 0.20/0.53  % (26308)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (26308)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (26308)Memory used [KB]: 1663
% 0.20/0.53  % (26308)Time elapsed: 0.126 s
% 0.20/0.53  % (26308)------------------------------
% 0.20/0.53  % (26308)------------------------------
% 0.20/0.53  % (26309)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.53  % (26310)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.53  % (26315)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.54  % (26325)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.54  % (26317)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.54  % (26326)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.54  % (26336)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.54  % (26336)Refutation not found, incomplete strategy% (26336)------------------------------
% 0.20/0.54  % (26336)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (26336)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (26336)Memory used [KB]: 1663
% 0.20/0.54  % (26336)Time elapsed: 0.137 s
% 0.20/0.54  % (26336)------------------------------
% 0.20/0.54  % (26336)------------------------------
% 0.20/0.54  % (26331)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.55  % (26328)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.55  % (26319)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.55  % (26332)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.55  % (26330)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.55  % (26323)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.55  % (26324)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.55  % (26323)Refutation not found, incomplete strategy% (26323)------------------------------
% 0.20/0.55  % (26323)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (26323)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (26323)Memory used [KB]: 10618
% 0.20/0.55  % (26323)Time elapsed: 0.149 s
% 0.20/0.55  % (26323)------------------------------
% 0.20/0.55  % (26323)------------------------------
% 0.20/0.56  % (26322)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.56  % (26316)Refutation found. Thanks to Tanya!
% 0.20/0.56  % SZS status Theorem for theBenchmark
% 0.20/0.56  % SZS output start Proof for theBenchmark
% 0.20/0.56  fof(f632,plain,(
% 0.20/0.56    $false),
% 0.20/0.56    inference(subsumption_resolution,[],[f631,f40])).
% 0.20/0.56  fof(f40,plain,(
% 0.20/0.56    sK0 != sK1),
% 0.20/0.56    inference(cnf_transformation,[],[f25])).
% 0.20/0.56  fof(f25,plain,(
% 0.20/0.56    sK0 != sK1 & k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 0.20/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f24])).
% 0.20/0.56  fof(f24,plain,(
% 0.20/0.56    ? [X0,X1] : (X0 != X1 & k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1))) => (sK0 != sK1 & k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),
% 0.20/0.56    introduced(choice_axiom,[])).
% 0.20/0.56  fof(f19,plain,(
% 0.20/0.56    ? [X0,X1] : (X0 != X1 & k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.20/0.56    inference(ennf_transformation,[],[f17])).
% 0.20/0.56  fof(f17,negated_conjecture,(
% 0.20/0.56    ~! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 0.20/0.56    inference(negated_conjecture,[],[f16])).
% 0.20/0.56  fof(f16,conjecture,(
% 0.20/0.56    ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_zfmisc_1)).
% 0.20/0.56  fof(f631,plain,(
% 0.20/0.56    sK0 = sK1),
% 0.20/0.56    inference(resolution,[],[f591,f73])).
% 0.20/0.56  fof(f73,plain,(
% 0.20/0.56    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 0.20/0.56    inference(equality_resolution,[],[f52])).
% 0.20/0.56  fof(f52,plain,(
% 0.20/0.56    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 0.20/0.56    inference(cnf_transformation,[],[f32])).
% 0.20/0.56  fof(f32,plain,(
% 0.20/0.56    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.20/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f31])).
% 0.20/0.56  fof(f31,plain,(
% 0.20/0.56    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1))))),
% 0.20/0.56    introduced(choice_axiom,[])).
% 0.20/0.56  fof(f30,plain,(
% 0.20/0.56    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.20/0.56    inference(rectify,[],[f29])).
% 0.20/0.56  fof(f29,plain,(
% 0.20/0.56    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.20/0.56    inference(nnf_transformation,[],[f10])).
% 0.20/0.56  fof(f10,axiom,(
% 0.20/0.56    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 0.20/0.56  fof(f591,plain,(
% 0.20/0.56    r2_hidden(sK1,k1_tarski(sK0))),
% 0.20/0.56    inference(subsumption_resolution,[],[f580,f72])).
% 0.20/0.56  fof(f72,plain,(
% 0.20/0.56    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 0.20/0.56    inference(equality_resolution,[],[f71])).
% 0.20/0.56  fof(f71,plain,(
% 0.20/0.56    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 0.20/0.56    inference(equality_resolution,[],[f53])).
% 0.20/0.56  fof(f53,plain,(
% 0.20/0.56    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 0.20/0.56    inference(cnf_transformation,[],[f32])).
% 0.20/0.56  fof(f580,plain,(
% 0.20/0.56    r2_hidden(sK1,k1_tarski(sK0)) | ~r2_hidden(sK1,k1_tarski(sK1))),
% 0.20/0.56    inference(superposition,[],[f524,f39])).
% 0.20/0.56  fof(f39,plain,(
% 0.20/0.56    k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 0.20/0.56    inference(cnf_transformation,[],[f25])).
% 0.20/0.56  fof(f524,plain,(
% 0.20/0.56    ( ! [X3] : (r2_hidden(sK1,k3_xboole_0(k1_tarski(sK0),X3)) | ~r2_hidden(sK1,X3)) )),
% 0.20/0.56    inference(superposition,[],[f506,f43])).
% 0.20/0.56  fof(f43,plain,(
% 0.20/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f1])).
% 0.20/0.56  fof(f1,axiom,(
% 0.20/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.56  fof(f506,plain,(
% 0.20/0.56    ( ! [X3] : (r2_hidden(sK1,k3_xboole_0(X3,k1_tarski(sK0))) | ~r2_hidden(sK1,X3)) )),
% 0.20/0.56    inference(resolution,[],[f142,f322])).
% 0.20/0.56  fof(f322,plain,(
% 0.20/0.56    ( ! [X0] : (~r2_hidden(sK1,k4_xboole_0(X0,k1_tarski(sK0)))) )),
% 0.20/0.56    inference(resolution,[],[f311,f42])).
% 0.20/0.56  fof(f42,plain,(
% 0.20/0.56    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f8])).
% 0.20/0.56  fof(f8,axiom,(
% 0.20/0.56    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.20/0.56  fof(f311,plain,(
% 0.20/0.56    ( ! [X0] : (~r1_xboole_0(X0,k1_tarski(sK0)) | ~r2_hidden(sK1,X0)) )),
% 0.20/0.56    inference(resolution,[],[f92,f298])).
% 0.20/0.56  fof(f298,plain,(
% 0.20/0.56    ( ! [X1] : (r2_hidden(sK0,k3_xboole_0(k1_tarski(sK0),X1)) | ~r2_hidden(sK1,X1)) )),
% 0.20/0.56    inference(subsumption_resolution,[],[f297,f200])).
% 0.20/0.56  fof(f200,plain,(
% 0.20/0.56    ( ! [X0] : (~r1_xboole_0(k1_tarski(sK0),X0) | ~r2_hidden(sK1,X0)) )),
% 0.20/0.56    inference(superposition,[],[f189,f49])).
% 0.20/0.56  fof(f49,plain,(
% 0.20/0.56    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f21])).
% 0.20/0.56  fof(f21,plain,(
% 0.20/0.56    ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1))),
% 0.20/0.56    inference(ennf_transformation,[],[f15])).
% 0.20/0.56  fof(f15,axiom,(
% 0.20/0.56    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l22_zfmisc_1)).
% 0.20/0.56  fof(f189,plain,(
% 0.20/0.56    ( ! [X1] : (~r1_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),X1))) )),
% 0.20/0.56    inference(subsumption_resolution,[],[f179,f114])).
% 0.20/0.56  fof(f114,plain,(
% 0.20/0.56    k1_xboole_0 != k1_tarski(sK0)),
% 0.20/0.56    inference(resolution,[],[f109,f72])).
% 0.20/0.56  fof(f109,plain,(
% 0.20/0.56    ( ! [X0] : (~r2_hidden(X0,k1_tarski(sK0)) | k1_xboole_0 != k1_tarski(sK0)) )),
% 0.20/0.56    inference(resolution,[],[f104,f91])).
% 0.20/0.56  fof(f91,plain,(
% 0.20/0.56    ( ! [X0] : (~r1_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) | ~r2_hidden(X0,k1_tarski(sK0))) )),
% 0.20/0.56    inference(superposition,[],[f48,f39])).
% 0.20/0.56  fof(f48,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f27])).
% 0.20/0.56  fof(f27,plain,(
% 0.20/0.56    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.20/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f26])).
% 0.20/0.56  fof(f26,plain,(
% 0.20/0.56    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)))),
% 0.20/0.56    introduced(choice_axiom,[])).
% 0.20/0.56  fof(f20,plain,(
% 0.20/0.56    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.20/0.56    inference(ennf_transformation,[],[f18])).
% 0.20/0.56  fof(f18,plain,(
% 0.20/0.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.56    inference(rectify,[],[f4])).
% 0.20/0.56  fof(f4,axiom,(
% 0.20/0.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.20/0.56  fof(f104,plain,(
% 0.20/0.56    r1_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) | k1_xboole_0 != k1_tarski(sK0)),
% 0.20/0.56    inference(superposition,[],[f51,f39])).
% 0.20/0.56  fof(f51,plain,(
% 0.20/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f28])).
% 0.20/0.56  fof(f28,plain,(
% 0.20/0.56    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.20/0.56    inference(nnf_transformation,[],[f2])).
% 0.20/0.56  fof(f2,axiom,(
% 0.20/0.56    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.20/0.56  fof(f179,plain,(
% 0.20/0.56    ( ! [X1] : (k1_xboole_0 = k1_tarski(sK0) | ~r1_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),X1))) )),
% 0.20/0.56    inference(superposition,[],[f171,f50])).
% 0.20/0.56  fof(f50,plain,(
% 0.20/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f28])).
% 0.20/0.56  fof(f171,plain,(
% 0.20/0.56    ( ! [X0] : (k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),X0))) )),
% 0.20/0.56    inference(forward_demodulation,[],[f159,f44])).
% 0.20/0.56  fof(f44,plain,(
% 0.20/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 0.20/0.56    inference(cnf_transformation,[],[f6])).
% 0.20/0.56  fof(f6,axiom,(
% 0.20/0.56    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).
% 0.20/0.56  fof(f159,plain,(
% 0.20/0.56    ( ! [X0] : (k3_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),X0)) = k2_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),X0))) )),
% 0.20/0.56    inference(superposition,[],[f57,f39])).
% 0.20/0.56  fof(f57,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 0.20/0.56    inference(cnf_transformation,[],[f7])).
% 0.20/0.56  fof(f7,axiom,(
% 0.20/0.56    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_xboole_1)).
% 0.20/0.56  fof(f297,plain,(
% 0.20/0.56    ( ! [X1] : (r2_hidden(sK0,k3_xboole_0(k1_tarski(sK0),X1)) | r1_xboole_0(k1_tarski(sK0),X1) | ~r2_hidden(sK1,X1)) )),
% 0.20/0.56    inference(superposition,[],[f47,f289])).
% 0.20/0.56  fof(f289,plain,(
% 0.20/0.56    ( ! [X0] : (sK0 = sK2(k1_tarski(sK0),X0) | ~r2_hidden(sK1,X0)) )),
% 0.20/0.56    inference(superposition,[],[f244,f49])).
% 0.20/0.56  fof(f244,plain,(
% 0.20/0.56    ( ! [X0] : (sK0 = sK2(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),X0))) )),
% 0.20/0.56    inference(resolution,[],[f190,f73])).
% 0.20/0.56  fof(f190,plain,(
% 0.20/0.56    ( ! [X4] : (r2_hidden(sK2(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),X4)),k1_tarski(sK0))) )),
% 0.20/0.56    inference(subsumption_resolution,[],[f182,f189])).
% 0.20/0.56  fof(f182,plain,(
% 0.20/0.56    ( ! [X4] : (r2_hidden(sK2(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),X4)),k1_tarski(sK0)) | r1_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),X4))) )),
% 0.20/0.56    inference(superposition,[],[f47,f171])).
% 0.20/0.56  fof(f47,plain,(
% 0.20/0.56    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f27])).
% 0.20/0.56  fof(f92,plain,(
% 0.20/0.56    ( ! [X2,X3,X1] : (~r2_hidden(X3,k3_xboole_0(X2,X1)) | ~r1_xboole_0(X1,X2)) )),
% 0.20/0.56    inference(superposition,[],[f48,f43])).
% 0.20/0.56  fof(f142,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (r2_hidden(X2,k4_xboole_0(X0,X1)) | r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r2_hidden(X2,X0)) )),
% 0.20/0.56    inference(superposition,[],[f60,f46])).
% 0.20/0.56  fof(f46,plain,(
% 0.20/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.56    inference(cnf_transformation,[],[f5])).
% 0.20/0.56  fof(f5,axiom,(
% 0.20/0.56    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.20/0.56  fof(f60,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f33])).
% 0.20/0.56  fof(f33,plain,(
% 0.20/0.56    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 0.20/0.56    inference(nnf_transformation,[],[f22])).
% 0.20/0.56  fof(f22,plain,(
% 0.20/0.56    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 0.20/0.56    inference(ennf_transformation,[],[f3])).
% 0.20/0.56  fof(f3,axiom,(
% 0.20/0.56    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).
% 0.20/0.56  % SZS output end Proof for theBenchmark
% 0.20/0.56  % (26316)------------------------------
% 0.20/0.56  % (26316)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (26316)Termination reason: Refutation
% 0.20/0.56  
% 0.20/0.56  % (26316)Memory used [KB]: 2174
% 0.20/0.56  % (26316)Time elapsed: 0.158 s
% 0.20/0.56  % (26316)------------------------------
% 0.20/0.56  % (26316)------------------------------
% 0.20/0.56  % (26306)Success in time 0.209 s
%------------------------------------------------------------------------------
