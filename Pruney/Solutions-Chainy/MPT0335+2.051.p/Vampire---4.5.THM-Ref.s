%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:22 EST 2020

% Result     : Theorem 7.01s
% Output     : Refutation 7.01s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 264 expanded)
%              Number of leaves         :    8 (  64 expanded)
%              Depth                    :   18
%              Number of atoms          :  204 (1518 expanded)
%              Number of equality atoms :   42 ( 386 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2873,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2869,f2839])).

fof(f2839,plain,(
    r2_hidden(sK5(sK0,sK2,k1_tarski(sK3)),sK0) ),
    inference(subsumption_resolution,[],[f2838,f405])).

fof(f405,plain,(
    ! [X7] :
      ( ~ r2_hidden(X7,k1_tarski(sK3))
      | r2_hidden(X7,sK0) ) ),
    inference(superposition,[],[f47,f387])).

fof(f387,plain,(
    k1_tarski(sK3) = k3_xboole_0(k1_tarski(sK3),sK0) ),
    inference(forward_demodulation,[],[f377,f31])).

fof(f31,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f377,plain,(
    k2_tarski(sK3,sK3) = k3_xboole_0(k2_tarski(sK3,sK3),sK0) ),
    inference(resolution,[],[f52,f29])).

fof(f29,plain,(
    r2_hidden(sK3,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( k1_tarski(sK3) != k3_xboole_0(sK0,sK2)
    & r2_hidden(sK3,sK0)
    & k1_tarski(sK3) = k3_xboole_0(sK1,sK2)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f16])).

fof(f16,plain,
    ( ? [X0,X1,X2,X3] :
        ( k1_tarski(X3) != k3_xboole_0(X0,X2)
        & r2_hidden(X3,X0)
        & k3_xboole_0(X1,X2) = k1_tarski(X3)
        & r1_tarski(X0,X1) )
   => ( k1_tarski(sK3) != k3_xboole_0(sK0,sK2)
      & r2_hidden(sK3,sK0)
      & k1_tarski(sK3) = k3_xboole_0(sK1,sK2)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_tarski(X3) != k3_xboole_0(X0,X2)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_tarski(X3) != k3_xboole_0(X0,X2)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r2_hidden(X3,X0)
          & k3_xboole_0(X1,X2) = k1_tarski(X3)
          & r1_tarski(X0,X1) )
       => k1_tarski(X3) = k3_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(X3,X0)
        & k3_xboole_0(X1,X2) = k1_tarski(X3)
        & r1_tarski(X0,X1) )
     => k1_tarski(X3) = k3_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_zfmisc_1)).

fof(f52,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK0)
      | k2_tarski(sK3,X2) = k3_xboole_0(k2_tarski(sK3,X2),sK0) ) ),
    inference(resolution,[],[f29,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X2,X1)
        & r2_hidden(X0,X1) )
     => k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_zfmisc_1)).

fof(f47,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
            | ~ r2_hidden(sK5(X0,X1,X2),X0)
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK5(X0,X1,X2),X1)
              & r2_hidden(sK5(X0,X1,X2),X0) )
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f24,f25])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
          | ~ r2_hidden(sK5(X0,X1,X2),X0)
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK5(X0,X1,X2),X1)
            & r2_hidden(sK5(X0,X1,X2),X0) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f2838,plain,
    ( r2_hidden(sK5(sK0,sK2,k1_tarski(sK3)),sK0)
    | r2_hidden(sK5(sK0,sK2,k1_tarski(sK3)),k1_tarski(sK3)) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X0] :
      ( k1_tarski(sK3) != X0
      | r2_hidden(sK5(sK0,sK2,X0),sK0)
      | r2_hidden(sK5(sK0,sK2,X0),X0) ) ),
    inference(superposition,[],[f30,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK5(X0,X1,X2),X0)
      | r2_hidden(sK5(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f30,plain,(
    k1_tarski(sK3) != k3_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f2869,plain,(
    ~ r2_hidden(sK5(sK0,sK2,k1_tarski(sK3)),sK0) ),
    inference(resolution,[],[f2861,f49])).

fof(f49,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f27,f34])).

fof(f34,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f20])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f27,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f2861,plain,(
    ~ r2_hidden(sK5(sK0,sK2,k1_tarski(sK3)),sK1) ),
    inference(subsumption_resolution,[],[f2856,f2860])).

fof(f2860,plain,(
    r2_hidden(sK5(sK0,sK2,k1_tarski(sK3)),sK2) ),
    inference(subsumption_resolution,[],[f2855,f30])).

fof(f2855,plain,
    ( k1_tarski(sK3) = k3_xboole_0(sK0,sK2)
    | r2_hidden(sK5(sK0,sK2,k1_tarski(sK3)),sK2) ),
    inference(resolution,[],[f2853,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK5(X0,X1,X2),X1)
      | r2_hidden(sK5(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f2853,plain,(
    ~ r2_hidden(sK5(sK0,sK2,k1_tarski(sK3)),k1_tarski(sK3)) ),
    inference(subsumption_resolution,[],[f2852,f63])).

fof(f63,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,k1_tarski(sK3))
      | r2_hidden(X5,sK2) ) ),
    inference(superposition,[],[f47,f28])).

fof(f28,plain,(
    k1_tarski(sK3) = k3_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f2852,plain,
    ( ~ r2_hidden(sK5(sK0,sK2,k1_tarski(sK3)),sK2)
    | ~ r2_hidden(sK5(sK0,sK2,k1_tarski(sK3)),k1_tarski(sK3)) ),
    inference(subsumption_resolution,[],[f2846,f30])).

fof(f2846,plain,
    ( k1_tarski(sK3) = k3_xboole_0(sK0,sK2)
    | ~ r2_hidden(sK5(sK0,sK2,k1_tarski(sK3)),sK2)
    | ~ r2_hidden(sK5(sK0,sK2,k1_tarski(sK3)),k1_tarski(sK3)) ),
    inference(resolution,[],[f2839,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK5(X0,X1,X2),X1)
      | ~ r2_hidden(sK5(X0,X1,X2),X0)
      | ~ r2_hidden(sK5(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f2856,plain,
    ( ~ r2_hidden(sK5(sK0,sK2,k1_tarski(sK3)),sK2)
    | ~ r2_hidden(sK5(sK0,sK2,k1_tarski(sK3)),sK1) ),
    inference(resolution,[],[f2853,f62])).

fof(f62,plain,(
    ! [X4] :
      ( r2_hidden(X4,k1_tarski(sK3))
      | ~ r2_hidden(X4,sK2)
      | ~ r2_hidden(X4,sK1) ) ),
    inference(superposition,[],[f46,f28])).

fof(f46,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:28:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.55  % (15117)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.55  % (15119)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.55  % (15125)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.56  % (15111)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.56  % (15109)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.56  % (15127)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.59  % (15106)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.60  % (15108)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.60  % (15105)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.60  % (15122)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.82/0.60  % (15116)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.82/0.60  % (15131)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.82/0.61  % (15121)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.82/0.61  % (15114)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.82/0.61  % (15124)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.82/0.61  % (15113)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.82/0.61  % (15115)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.82/0.61  % (15130)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.82/0.61  % (15107)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.82/0.61  % (15132)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.82/0.61  % (15112)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.82/0.62  % (15120)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.82/0.62  % (15128)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.82/0.62  % (15129)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.82/0.62  % (15126)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.82/0.62  % (15103)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.82/0.62  % (15123)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.82/0.63  % (15104)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 2.05/0.63  % (15118)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 2.05/0.64  % (15110)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 3.68/0.85  % (15108)Time limit reached!
% 3.68/0.85  % (15108)------------------------------
% 3.68/0.85  % (15108)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.68/0.85  % (15108)Termination reason: Time limit
% 3.68/0.85  
% 3.68/0.85  % (15108)Memory used [KB]: 7036
% 3.68/0.85  % (15108)Time elapsed: 0.416 s
% 3.68/0.85  % (15108)------------------------------
% 3.68/0.85  % (15108)------------------------------
% 4.34/0.95  % (15113)Time limit reached!
% 4.34/0.95  % (15113)------------------------------
% 4.34/0.95  % (15113)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.34/0.95  % (15115)Time limit reached!
% 4.34/0.95  % (15115)------------------------------
% 4.34/0.95  % (15115)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.34/0.95  % (15115)Termination reason: Time limit
% 4.34/0.95  % (15113)Termination reason: Time limit
% 4.34/0.95  
% 4.34/0.95  % (15113)Termination phase: Saturation
% 4.34/0.95  
% 4.34/0.95  % (15115)Memory used [KB]: 8059
% 4.34/0.95  % (15113)Memory used [KB]: 13688
% 4.34/0.95  % (15115)Time elapsed: 0.520 s
% 4.34/0.95  % (15113)Time elapsed: 0.500 s
% 4.34/0.95  % (15115)------------------------------
% 4.34/0.95  % (15115)------------------------------
% 4.34/0.95  % (15113)------------------------------
% 4.34/0.95  % (15113)------------------------------
% 4.34/0.95  % (15103)Time limit reached!
% 4.34/0.95  % (15103)------------------------------
% 4.34/0.95  % (15103)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.34/0.95  % (15103)Termination reason: Time limit
% 4.34/0.95  
% 4.34/0.95  % (15103)Memory used [KB]: 2558
% 4.34/0.95  % (15103)Time elapsed: 0.519 s
% 4.34/0.95  % (15103)------------------------------
% 4.34/0.95  % (15103)------------------------------
% 4.62/0.98  % (15104)Time limit reached!
% 4.62/0.98  % (15104)------------------------------
% 4.62/0.98  % (15104)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.62/0.98  % (15104)Termination reason: Time limit
% 4.62/0.98  % (15104)Termination phase: Saturation
% 4.62/0.98  
% 4.62/0.98  % (15104)Memory used [KB]: 6908
% 4.62/0.98  % (15104)Time elapsed: 0.500 s
% 4.62/0.98  % (15104)------------------------------
% 4.62/0.98  % (15104)------------------------------
% 4.62/1.00  % (15120)Time limit reached!
% 4.62/1.00  % (15120)------------------------------
% 4.62/1.00  % (15120)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.62/1.00  % (15120)Termination reason: Time limit
% 4.62/1.00  % (15120)Termination phase: Saturation
% 4.62/1.00  
% 4.62/1.00  % (15120)Memory used [KB]: 12665
% 4.62/1.00  % (15120)Time elapsed: 0.500 s
% 4.62/1.00  % (15120)------------------------------
% 4.62/1.00  % (15120)------------------------------
% 5.13/1.05  % (15131)Time limit reached!
% 5.13/1.05  % (15131)------------------------------
% 5.13/1.05  % (15131)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.13/1.05  % (15131)Termination reason: Time limit
% 5.13/1.05  % (15131)Termination phase: Saturation
% 5.13/1.05  
% 5.13/1.05  % (15131)Memory used [KB]: 7291
% 5.13/1.05  % (15131)Time elapsed: 0.600 s
% 5.13/1.05  % (15131)------------------------------
% 5.13/1.05  % (15131)------------------------------
% 5.13/1.05  % (15110)Time limit reached!
% 5.13/1.05  % (15110)------------------------------
% 5.13/1.05  % (15110)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.13/1.05  % (15110)Termination reason: Time limit
% 5.13/1.05  
% 5.13/1.05  % (15110)Memory used [KB]: 8571
% 5.13/1.05  % (15110)Time elapsed: 0.619 s
% 5.13/1.05  % (15110)------------------------------
% 5.13/1.05  % (15110)------------------------------
% 5.13/1.06  % (15119)Time limit reached!
% 5.13/1.06  % (15119)------------------------------
% 5.13/1.06  % (15119)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.13/1.06  % (15119)Termination reason: Time limit
% 5.13/1.06  % (15119)Termination phase: Saturation
% 5.13/1.06  
% 5.13/1.06  % (15119)Memory used [KB]: 15223
% 5.13/1.06  % (15119)Time elapsed: 0.600 s
% 5.13/1.06  % (15119)------------------------------
% 5.13/1.06  % (15119)------------------------------
% 6.23/1.17  % (15147)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 6.55/1.21  % (15157)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 6.55/1.23  % (15153)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 6.55/1.23  % (15160)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 6.55/1.23  % (15151)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 6.55/1.24  % (15124)Time limit reached!
% 6.55/1.24  % (15124)------------------------------
% 6.55/1.24  % (15124)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.55/1.24  % (15124)Termination reason: Time limit
% 6.55/1.24  
% 6.55/1.24  % (15124)Memory used [KB]: 3965
% 6.55/1.24  % (15124)Time elapsed: 0.809 s
% 6.55/1.24  % (15124)------------------------------
% 6.55/1.24  % (15124)------------------------------
% 7.01/1.27  % (15152)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 7.01/1.28  % (15126)Refutation found. Thanks to Tanya!
% 7.01/1.28  % SZS status Theorem for theBenchmark
% 7.01/1.28  % SZS output start Proof for theBenchmark
% 7.01/1.28  fof(f2873,plain,(
% 7.01/1.28    $false),
% 7.01/1.28    inference(subsumption_resolution,[],[f2869,f2839])).
% 7.01/1.28  fof(f2839,plain,(
% 7.01/1.28    r2_hidden(sK5(sK0,sK2,k1_tarski(sK3)),sK0)),
% 7.01/1.28    inference(subsumption_resolution,[],[f2838,f405])).
% 7.01/1.28  fof(f405,plain,(
% 7.01/1.28    ( ! [X7] : (~r2_hidden(X7,k1_tarski(sK3)) | r2_hidden(X7,sK0)) )),
% 7.01/1.28    inference(superposition,[],[f47,f387])).
% 7.01/1.28  fof(f387,plain,(
% 7.01/1.28    k1_tarski(sK3) = k3_xboole_0(k1_tarski(sK3),sK0)),
% 7.01/1.28    inference(forward_demodulation,[],[f377,f31])).
% 7.01/1.28  fof(f31,plain,(
% 7.01/1.28    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 7.01/1.28    inference(cnf_transformation,[],[f5])).
% 7.01/1.28  fof(f5,axiom,(
% 7.01/1.28    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 7.01/1.28    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 7.01/1.28  fof(f377,plain,(
% 7.01/1.28    k2_tarski(sK3,sK3) = k3_xboole_0(k2_tarski(sK3,sK3),sK0)),
% 7.01/1.28    inference(resolution,[],[f52,f29])).
% 7.01/1.28  fof(f29,plain,(
% 7.01/1.28    r2_hidden(sK3,sK0)),
% 7.01/1.28    inference(cnf_transformation,[],[f17])).
% 7.01/1.28  fof(f17,plain,(
% 7.01/1.28    k1_tarski(sK3) != k3_xboole_0(sK0,sK2) & r2_hidden(sK3,sK0) & k1_tarski(sK3) = k3_xboole_0(sK1,sK2) & r1_tarski(sK0,sK1)),
% 7.01/1.28    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f16])).
% 7.01/1.28  fof(f16,plain,(
% 7.01/1.28    ? [X0,X1,X2,X3] : (k1_tarski(X3) != k3_xboole_0(X0,X2) & r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => (k1_tarski(sK3) != k3_xboole_0(sK0,sK2) & r2_hidden(sK3,sK0) & k1_tarski(sK3) = k3_xboole_0(sK1,sK2) & r1_tarski(sK0,sK1))),
% 7.01/1.28    introduced(choice_axiom,[])).
% 7.01/1.28  fof(f12,plain,(
% 7.01/1.28    ? [X0,X1,X2,X3] : (k1_tarski(X3) != k3_xboole_0(X0,X2) & r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1))),
% 7.01/1.28    inference(flattening,[],[f11])).
% 7.01/1.28  fof(f11,plain,(
% 7.01/1.28    ? [X0,X1,X2,X3] : (k1_tarski(X3) != k3_xboole_0(X0,X2) & (r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)))),
% 7.01/1.28    inference(ennf_transformation,[],[f10])).
% 7.01/1.28  fof(f10,negated_conjecture,(
% 7.01/1.28    ~! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k1_tarski(X3) = k3_xboole_0(X0,X2))),
% 7.01/1.28    inference(negated_conjecture,[],[f9])).
% 7.01/1.28  fof(f9,conjecture,(
% 7.01/1.28    ! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k1_tarski(X3) = k3_xboole_0(X0,X2))),
% 7.01/1.28    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_zfmisc_1)).
% 7.01/1.28  fof(f52,plain,(
% 7.01/1.28    ( ! [X2] : (~r2_hidden(X2,sK0) | k2_tarski(sK3,X2) = k3_xboole_0(k2_tarski(sK3,X2),sK0)) )),
% 7.01/1.28    inference(resolution,[],[f29,f39])).
% 7.01/1.28  fof(f39,plain,(
% 7.01/1.28    ( ! [X2,X0,X1] : (k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X0,X1)) )),
% 7.01/1.28    inference(cnf_transformation,[],[f15])).
% 7.01/1.28  fof(f15,plain,(
% 7.01/1.28    ! [X0,X1,X2] : (k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X0,X1))),
% 7.01/1.28    inference(flattening,[],[f14])).
% 7.01/1.28  fof(f14,plain,(
% 7.01/1.28    ! [X0,X1,X2] : (k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) | (~r2_hidden(X2,X1) | ~r2_hidden(X0,X1)))),
% 7.01/1.28    inference(ennf_transformation,[],[f8])).
% 7.01/1.28  fof(f8,axiom,(
% 7.01/1.28    ! [X0,X1,X2] : ((r2_hidden(X2,X1) & r2_hidden(X0,X1)) => k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1))),
% 7.01/1.28    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_zfmisc_1)).
% 7.01/1.28  fof(f47,plain,(
% 7.01/1.28    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 7.01/1.28    inference(equality_resolution,[],[f41])).
% 7.01/1.28  fof(f41,plain,(
% 7.01/1.28    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 7.01/1.28    inference(cnf_transformation,[],[f26])).
% 7.01/1.28  fof(f26,plain,(
% 7.01/1.28    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 7.01/1.28    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f24,f25])).
% 7.01/1.28  fof(f25,plain,(
% 7.01/1.28    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 7.01/1.28    introduced(choice_axiom,[])).
% 7.01/1.28  fof(f24,plain,(
% 7.01/1.28    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 7.01/1.28    inference(rectify,[],[f23])).
% 7.01/1.29  fof(f23,plain,(
% 7.01/1.29    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 7.01/1.29    inference(flattening,[],[f22])).
% 7.01/1.29  fof(f22,plain,(
% 7.01/1.29    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 7.01/1.29    inference(nnf_transformation,[],[f2])).
% 7.01/1.29  fof(f2,axiom,(
% 7.01/1.29    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 7.01/1.29    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 7.01/1.29  fof(f2838,plain,(
% 7.01/1.29    r2_hidden(sK5(sK0,sK2,k1_tarski(sK3)),sK0) | r2_hidden(sK5(sK0,sK2,k1_tarski(sK3)),k1_tarski(sK3))),
% 7.01/1.29    inference(equality_resolution,[],[f65])).
% 7.01/1.29  fof(f65,plain,(
% 7.01/1.29    ( ! [X0] : (k1_tarski(sK3) != X0 | r2_hidden(sK5(sK0,sK2,X0),sK0) | r2_hidden(sK5(sK0,sK2,X0),X0)) )),
% 7.01/1.29    inference(superposition,[],[f30,f43])).
% 7.01/1.29  fof(f43,plain,(
% 7.01/1.29    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK5(X0,X1,X2),X0) | r2_hidden(sK5(X0,X1,X2),X2)) )),
% 7.01/1.29    inference(cnf_transformation,[],[f26])).
% 7.01/1.29  fof(f30,plain,(
% 7.01/1.29    k1_tarski(sK3) != k3_xboole_0(sK0,sK2)),
% 7.01/1.29    inference(cnf_transformation,[],[f17])).
% 7.01/1.29  fof(f2869,plain,(
% 7.01/1.29    ~r2_hidden(sK5(sK0,sK2,k1_tarski(sK3)),sK0)),
% 7.01/1.29    inference(resolution,[],[f2861,f49])).
% 7.01/1.29  fof(f49,plain,(
% 7.01/1.29    ( ! [X0] : (r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0)) )),
% 7.01/1.29    inference(resolution,[],[f27,f34])).
% 7.01/1.29  fof(f34,plain,(
% 7.01/1.29    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 7.01/1.29    inference(cnf_transformation,[],[f21])).
% 7.01/1.29  fof(f21,plain,(
% 7.01/1.29    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.01/1.29    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f20])).
% 7.01/1.29  fof(f20,plain,(
% 7.01/1.29    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 7.01/1.29    introduced(choice_axiom,[])).
% 7.01/1.29  fof(f19,plain,(
% 7.01/1.29    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.01/1.29    inference(rectify,[],[f18])).
% 7.01/1.29  fof(f18,plain,(
% 7.01/1.29    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 7.01/1.29    inference(nnf_transformation,[],[f13])).
% 7.01/1.29  fof(f13,plain,(
% 7.01/1.29    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 7.01/1.29    inference(ennf_transformation,[],[f1])).
% 7.01/1.29  fof(f1,axiom,(
% 7.01/1.29    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.01/1.29    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 7.01/1.29  fof(f27,plain,(
% 7.01/1.29    r1_tarski(sK0,sK1)),
% 7.01/1.29    inference(cnf_transformation,[],[f17])).
% 7.01/1.29  fof(f2861,plain,(
% 7.01/1.29    ~r2_hidden(sK5(sK0,sK2,k1_tarski(sK3)),sK1)),
% 7.01/1.29    inference(subsumption_resolution,[],[f2856,f2860])).
% 7.01/1.29  fof(f2860,plain,(
% 7.01/1.29    r2_hidden(sK5(sK0,sK2,k1_tarski(sK3)),sK2)),
% 7.01/1.29    inference(subsumption_resolution,[],[f2855,f30])).
% 7.01/1.29  fof(f2855,plain,(
% 7.01/1.29    k1_tarski(sK3) = k3_xboole_0(sK0,sK2) | r2_hidden(sK5(sK0,sK2,k1_tarski(sK3)),sK2)),
% 7.01/1.29    inference(resolution,[],[f2853,f44])).
% 7.01/1.29  fof(f44,plain,(
% 7.01/1.29    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK5(X0,X1,X2),X1) | r2_hidden(sK5(X0,X1,X2),X2)) )),
% 7.01/1.29    inference(cnf_transformation,[],[f26])).
% 7.01/1.29  fof(f2853,plain,(
% 7.01/1.29    ~r2_hidden(sK5(sK0,sK2,k1_tarski(sK3)),k1_tarski(sK3))),
% 7.01/1.29    inference(subsumption_resolution,[],[f2852,f63])).
% 7.01/1.29  fof(f63,plain,(
% 7.01/1.29    ( ! [X5] : (~r2_hidden(X5,k1_tarski(sK3)) | r2_hidden(X5,sK2)) )),
% 7.01/1.29    inference(superposition,[],[f47,f28])).
% 7.01/1.29  fof(f28,plain,(
% 7.01/1.29    k1_tarski(sK3) = k3_xboole_0(sK1,sK2)),
% 7.01/1.29    inference(cnf_transformation,[],[f17])).
% 7.01/1.29  fof(f2852,plain,(
% 7.01/1.29    ~r2_hidden(sK5(sK0,sK2,k1_tarski(sK3)),sK2) | ~r2_hidden(sK5(sK0,sK2,k1_tarski(sK3)),k1_tarski(sK3))),
% 7.01/1.29    inference(subsumption_resolution,[],[f2846,f30])).
% 7.01/1.29  fof(f2846,plain,(
% 7.01/1.29    k1_tarski(sK3) = k3_xboole_0(sK0,sK2) | ~r2_hidden(sK5(sK0,sK2,k1_tarski(sK3)),sK2) | ~r2_hidden(sK5(sK0,sK2,k1_tarski(sK3)),k1_tarski(sK3))),
% 7.01/1.29    inference(resolution,[],[f2839,f45])).
% 7.01/1.29  fof(f45,plain,(
% 7.01/1.29    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | ~r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) )),
% 7.01/1.29    inference(cnf_transformation,[],[f26])).
% 7.01/1.29  fof(f2856,plain,(
% 7.01/1.29    ~r2_hidden(sK5(sK0,sK2,k1_tarski(sK3)),sK2) | ~r2_hidden(sK5(sK0,sK2,k1_tarski(sK3)),sK1)),
% 7.01/1.29    inference(resolution,[],[f2853,f62])).
% 7.01/1.29  fof(f62,plain,(
% 7.01/1.29    ( ! [X4] : (r2_hidden(X4,k1_tarski(sK3)) | ~r2_hidden(X4,sK2) | ~r2_hidden(X4,sK1)) )),
% 7.01/1.29    inference(superposition,[],[f46,f28])).
% 7.01/1.29  fof(f46,plain,(
% 7.01/1.29    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_xboole_0(X0,X1)) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 7.01/1.29    inference(equality_resolution,[],[f42])).
% 7.01/1.29  fof(f42,plain,(
% 7.01/1.29    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k3_xboole_0(X0,X1) != X2) )),
% 7.01/1.29    inference(cnf_transformation,[],[f26])).
% 7.01/1.29  % SZS output end Proof for theBenchmark
% 7.01/1.29  % (15126)------------------------------
% 7.01/1.29  % (15126)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.01/1.29  % (15126)Termination reason: Refutation
% 7.01/1.29  
% 7.01/1.29  % (15126)Memory used [KB]: 3709
% 7.01/1.29  % (15126)Time elapsed: 0.840 s
% 7.01/1.29  % (15126)------------------------------
% 7.01/1.29  % (15126)------------------------------
% 7.01/1.29  % (15164)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 7.01/1.29  % (15161)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 7.34/1.31  % (15101)Success in time 0.938 s
%------------------------------------------------------------------------------
