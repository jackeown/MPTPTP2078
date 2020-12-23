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
% DateTime   : Thu Dec  3 12:40:35 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 194 expanded)
%              Number of leaves         :   12 (  51 expanded)
%              Depth                    :   16
%              Number of atoms          :  215 ( 745 expanded)
%              Number of equality atoms :   59 ( 167 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f353,plain,(
    $false ),
    inference(subsumption_resolution,[],[f346,f61])).

fof(f61,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK4(X0,X1) != X0
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( sK4(X0,X1) = X0
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f30,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK4(X0,X1) != X0
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( sK4(X0,X1) = X0
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
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
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f346,plain,(
    ~ r2_hidden(sK0,k1_tarski(sK0)) ),
    inference(backward_demodulation,[],[f112,f343])).

fof(f343,plain,(
    sK0 = sK2 ),
    inference(subsumption_resolution,[],[f341,f112])).

fof(f341,plain,
    ( sK0 = sK2
    | r2_hidden(sK0,k1_tarski(sK2)) ),
    inference(resolution,[],[f293,f182])).

fof(f182,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X3,k3_xboole_0(X4,X5))
      | r2_hidden(X3,X5) ) ),
    inference(subsumption_resolution,[],[f177,f119])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | r2_hidden(X2,X0) ) ),
    inference(subsumption_resolution,[],[f116,f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k4_xboole_0(X1,X2))
      | ~ r2_hidden(X0,k3_xboole_0(X1,X2)) ) ),
    inference(resolution,[],[f85,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f85,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) ),
    inference(backward_demodulation,[],[f70,f79])).

fof(f79,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[],[f51,f38])).

fof(f38,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f51,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f70,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,k3_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) ),
    inference(superposition,[],[f40,f42])).

fof(f42,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f40,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l97_xboole_1)).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k4_xboole_0(X0,X1))
      | r2_hidden(X2,X0)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(superposition,[],[f55,f42])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f177,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X3,k3_xboole_0(X4,X5))
      | r2_hidden(X3,X5)
      | ~ r2_hidden(X3,X4) ) ),
    inference(resolution,[],[f73,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f73,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X3,k5_xboole_0(X4,X5))
      | ~ r2_hidden(X3,k3_xboole_0(X4,X5)) ) ),
    inference(resolution,[],[f45,f40])).

fof(f293,plain,
    ( r2_hidden(sK0,k3_xboole_0(sK1,k1_tarski(sK2)))
    | sK0 = sK2 ),
    inference(subsumption_resolution,[],[f292,f270])).

fof(f270,plain,(
    r2_hidden(sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f264])).

fof(f264,plain,
    ( r2_hidden(sK0,sK1)
    | r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f262,f34])).

fof(f34,plain,
    ( r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2)))
    | r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ( sK0 = sK2
      | ~ r2_hidden(sK0,sK1)
      | ~ r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2))) )
    & ( ( sK0 != sK2
        & r2_hidden(sK0,sK1) )
      | r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f25])).

fof(f25,plain,
    ( ? [X0,X1,X2] :
        ( ( X0 = X2
          | ~ r2_hidden(X0,X1)
          | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) )
        & ( ( X0 != X2
            & r2_hidden(X0,X1) )
          | r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) )
   => ( ( sK0 = sK2
        | ~ r2_hidden(sK0,sK1)
        | ~ r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2))) )
      & ( ( sK0 != sK2
          & r2_hidden(sK0,sK1) )
        | r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2))) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ( X0 = X2
        | ~ r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( ( X0 = X2
        | ~ r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <~> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
      <=> ( X0 != X2
          & r2_hidden(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f262,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k4_xboole_0(X1,X2))
      | r2_hidden(X0,X1) ) ),
    inference(subsumption_resolution,[],[f253,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k4_xboole_0(X2,X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f45,f39])).

fof(f39,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f253,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k4_xboole_0(X1,X2))
      | r2_hidden(X0,X2) ) ),
    inference(resolution,[],[f91,f182])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k3_xboole_0(X0,X1))
      | r2_hidden(X2,X0)
      | ~ r2_hidden(X2,k4_xboole_0(X0,X1)) ) ),
    inference(superposition,[],[f52,f42])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X1)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f292,plain,
    ( r2_hidden(sK0,k3_xboole_0(sK1,k1_tarski(sK2)))
    | ~ r2_hidden(sK0,sK1)
    | sK0 = sK2 ),
    inference(duplicate_literal_removal,[],[f284])).

fof(f284,plain,
    ( r2_hidden(sK0,k3_xboole_0(sK1,k1_tarski(sK2)))
    | ~ r2_hidden(sK0,sK1)
    | ~ r2_hidden(sK0,sK1)
    | sK0 = sK2 ),
    inference(resolution,[],[f104,f36])).

fof(f36,plain,
    ( ~ r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2)))
    | ~ r2_hidden(sK0,sK1)
    | sK0 = sK2 ),
    inference(cnf_transformation,[],[f26])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k4_xboole_0(X0,X1))
      | r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X2,X0) ) ),
    inference(superposition,[],[f54,f42])).

fof(f112,plain,(
    ~ r2_hidden(sK0,k1_tarski(sK2)) ),
    inference(subsumption_resolution,[],[f107,f62])).

fof(f62,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f107,plain,
    ( ~ r2_hidden(sK0,k1_tarski(sK2))
    | sK0 != sK2 ),
    inference(resolution,[],[f72,f35])).

fof(f35,plain,
    ( r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2)))
    | sK0 != sK2 ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n013.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:23:09 EST 2020
% 0.19/0.35  % CPUTime    : 
% 0.21/0.46  % (304)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.47  % (319)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.52  % (300)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.52  % (301)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.53  % (32765)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.54  % (322)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.54  % (318)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.54  % (310)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.54  % (305)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.54  % (311)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.54  % (32767)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.54  % (324)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.54  % (302)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.54  % (313)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.54  % (311)Refutation not found, incomplete strategy% (311)------------------------------
% 0.21/0.54  % (311)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (311)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (311)Memory used [KB]: 1663
% 0.21/0.54  % (311)Time elapsed: 0.091 s
% 0.21/0.54  % (311)------------------------------
% 0.21/0.54  % (311)------------------------------
% 0.21/0.54  % (313)Refutation not found, incomplete strategy% (313)------------------------------
% 0.21/0.54  % (313)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (313)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (313)Memory used [KB]: 10618
% 0.21/0.54  % (313)Time elapsed: 0.136 s
% 0.21/0.54  % (313)------------------------------
% 0.21/0.54  % (313)------------------------------
% 0.21/0.55  % (323)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (32766)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.55  % (32766)Refutation not found, incomplete strategy% (32766)------------------------------
% 0.21/0.55  % (32766)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (32766)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (32766)Memory used [KB]: 1663
% 0.21/0.55  % (32766)Time elapsed: 0.130 s
% 0.21/0.55  % (32766)------------------------------
% 0.21/0.55  % (32766)------------------------------
% 0.21/0.55  % (321)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.55  % (306)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.55  % (326)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.55  % (315)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.55  % (314)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.55  % (312)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.55  % (314)Refutation not found, incomplete strategy% (314)------------------------------
% 0.21/0.55  % (314)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (309)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.55  % (303)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (307)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.55  % (316)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.56  % (306)Refutation found. Thanks to Tanya!
% 0.21/0.56  % SZS status Theorem for theBenchmark
% 0.21/0.56  % (317)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.53/0.56  % (325)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.53/0.56  % (308)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.53/0.56  % (308)Refutation not found, incomplete strategy% (308)------------------------------
% 1.53/0.56  % (308)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.56  % (308)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.56  
% 1.53/0.56  % (308)Memory used [KB]: 6140
% 1.53/0.56  % (308)Time elapsed: 0.149 s
% 1.53/0.56  % (308)------------------------------
% 1.53/0.56  % (308)------------------------------
% 1.53/0.56  % (320)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.53/0.56  % (314)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.56  
% 1.53/0.56  % (314)Memory used [KB]: 1663
% 1.53/0.56  % (314)Time elapsed: 0.141 s
% 1.53/0.56  % (314)------------------------------
% 1.53/0.56  % (314)------------------------------
% 1.65/0.58  % SZS output start Proof for theBenchmark
% 1.65/0.58  fof(f353,plain,(
% 1.65/0.58    $false),
% 1.65/0.58    inference(subsumption_resolution,[],[f346,f61])).
% 1.65/0.58  fof(f61,plain,(
% 1.65/0.58    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 1.65/0.58    inference(equality_resolution,[],[f60])).
% 1.65/0.58  fof(f60,plain,(
% 1.65/0.58    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 1.65/0.58    inference(equality_resolution,[],[f47])).
% 1.65/0.58  fof(f47,plain,(
% 1.65/0.58    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 1.65/0.58    inference(cnf_transformation,[],[f32])).
% 1.65/0.58  fof(f32,plain,(
% 1.65/0.58    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.65/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f30,f31])).
% 1.65/0.58  fof(f31,plain,(
% 1.65/0.58    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1))))),
% 1.65/0.58    introduced(choice_axiom,[])).
% 1.65/0.58  fof(f30,plain,(
% 1.65/0.58    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.65/0.58    inference(rectify,[],[f29])).
% 1.65/0.58  fof(f29,plain,(
% 1.65/0.58    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.65/0.58    inference(nnf_transformation,[],[f8])).
% 1.65/0.58  fof(f8,axiom,(
% 1.65/0.58    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 1.65/0.58  fof(f346,plain,(
% 1.65/0.58    ~r2_hidden(sK0,k1_tarski(sK0))),
% 1.65/0.58    inference(backward_demodulation,[],[f112,f343])).
% 1.65/0.58  fof(f343,plain,(
% 1.65/0.58    sK0 = sK2),
% 1.65/0.58    inference(subsumption_resolution,[],[f341,f112])).
% 1.65/0.58  fof(f341,plain,(
% 1.65/0.58    sK0 = sK2 | r2_hidden(sK0,k1_tarski(sK2))),
% 1.65/0.58    inference(resolution,[],[f293,f182])).
% 1.65/0.58  fof(f182,plain,(
% 1.65/0.58    ( ! [X4,X5,X3] : (~r2_hidden(X3,k3_xboole_0(X4,X5)) | r2_hidden(X3,X5)) )),
% 1.65/0.58    inference(subsumption_resolution,[],[f177,f119])).
% 1.65/0.58  fof(f119,plain,(
% 1.65/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | r2_hidden(X2,X0)) )),
% 1.65/0.58    inference(subsumption_resolution,[],[f116,f96])).
% 1.65/0.58  fof(f96,plain,(
% 1.65/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X0,k4_xboole_0(X1,X2)) | ~r2_hidden(X0,k3_xboole_0(X1,X2))) )),
% 1.65/0.58    inference(resolution,[],[f85,f45])).
% 1.65/0.58  fof(f45,plain,(
% 1.65/0.58    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.65/0.58    inference(cnf_transformation,[],[f28])).
% 1.65/0.58  fof(f28,plain,(
% 1.65/0.58    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.65/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f27])).
% 1.65/0.58  fof(f27,plain,(
% 1.65/0.58    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 1.65/0.58    introduced(choice_axiom,[])).
% 1.65/0.58  fof(f21,plain,(
% 1.65/0.58    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.65/0.58    inference(ennf_transformation,[],[f19])).
% 1.65/0.58  fof(f19,plain,(
% 1.65/0.58    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.65/0.58    inference(rectify,[],[f3])).
% 1.65/0.58  fof(f3,axiom,(
% 1.65/0.58    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.65/0.58  fof(f85,plain,(
% 1.65/0.58    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1))) )),
% 1.65/0.58    inference(backward_demodulation,[],[f70,f79])).
% 1.65/0.58  fof(f79,plain,(
% 1.65/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.65/0.58    inference(superposition,[],[f51,f38])).
% 1.65/0.58  fof(f38,plain,(
% 1.65/0.58    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.65/0.58    inference(cnf_transformation,[],[f18])).
% 1.65/0.58  fof(f18,plain,(
% 1.65/0.58    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.65/0.58    inference(rectify,[],[f1])).
% 1.65/0.58  fof(f1,axiom,(
% 1.65/0.58    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.65/0.58  fof(f51,plain,(
% 1.65/0.58    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 1.65/0.58    inference(cnf_transformation,[],[f6])).
% 1.65/0.58  fof(f6,axiom,(
% 1.65/0.58    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).
% 1.65/0.58  fof(f70,plain,(
% 1.65/0.58    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,k3_xboole_0(X0,X1)),k4_xboole_0(X0,X1))) )),
% 1.65/0.58    inference(superposition,[],[f40,f42])).
% 1.65/0.58  fof(f42,plain,(
% 1.65/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.65/0.58    inference(cnf_transformation,[],[f5])).
% 1.65/0.58  fof(f5,axiom,(
% 1.65/0.58    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.65/0.58  fof(f40,plain,(
% 1.65/0.58    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 1.65/0.58    inference(cnf_transformation,[],[f4])).
% 1.65/0.58  fof(f4,axiom,(
% 1.65/0.58    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l97_xboole_1)).
% 1.65/0.58  fof(f116,plain,(
% 1.65/0.58    ( ! [X2,X0,X1] : (r2_hidden(X2,k4_xboole_0(X0,X1)) | r2_hidden(X2,X0) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 1.65/0.58    inference(superposition,[],[f55,f42])).
% 1.65/0.58  fof(f55,plain,(
% 1.65/0.58    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 1.65/0.58    inference(cnf_transformation,[],[f33])).
% 1.65/0.58  fof(f33,plain,(
% 1.65/0.58    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 1.65/0.58    inference(nnf_transformation,[],[f22])).
% 1.65/0.58  fof(f22,plain,(
% 1.65/0.58    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 1.65/0.58    inference(ennf_transformation,[],[f2])).
% 1.65/0.58  fof(f2,axiom,(
% 1.65/0.58    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).
% 1.65/0.58  fof(f177,plain,(
% 1.65/0.58    ( ! [X4,X5,X3] : (~r2_hidden(X3,k3_xboole_0(X4,X5)) | r2_hidden(X3,X5) | ~r2_hidden(X3,X4)) )),
% 1.65/0.58    inference(resolution,[],[f73,f54])).
% 1.65/0.58  fof(f54,plain,(
% 1.65/0.58    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) )),
% 1.65/0.58    inference(cnf_transformation,[],[f33])).
% 1.65/0.58  fof(f73,plain,(
% 1.65/0.58    ( ! [X4,X5,X3] : (~r2_hidden(X3,k5_xboole_0(X4,X5)) | ~r2_hidden(X3,k3_xboole_0(X4,X5))) )),
% 1.65/0.58    inference(resolution,[],[f45,f40])).
% 1.65/0.58  fof(f293,plain,(
% 1.65/0.58    r2_hidden(sK0,k3_xboole_0(sK1,k1_tarski(sK2))) | sK0 = sK2),
% 1.65/0.58    inference(subsumption_resolution,[],[f292,f270])).
% 1.65/0.58  fof(f270,plain,(
% 1.65/0.58    r2_hidden(sK0,sK1)),
% 1.65/0.58    inference(duplicate_literal_removal,[],[f264])).
% 1.65/0.58  fof(f264,plain,(
% 1.65/0.58    r2_hidden(sK0,sK1) | r2_hidden(sK0,sK1)),
% 1.65/0.58    inference(resolution,[],[f262,f34])).
% 1.65/0.58  fof(f34,plain,(
% 1.65/0.58    r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2))) | r2_hidden(sK0,sK1)),
% 1.65/0.58    inference(cnf_transformation,[],[f26])).
% 1.65/0.58  fof(f26,plain,(
% 1.65/0.58    (sK0 = sK2 | ~r2_hidden(sK0,sK1) | ~r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2)))) & ((sK0 != sK2 & r2_hidden(sK0,sK1)) | r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2))))),
% 1.65/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f25])).
% 1.65/0.58  fof(f25,plain,(
% 1.65/0.58    ? [X0,X1,X2] : ((X0 = X2 | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) & ((X0 != X2 & r2_hidden(X0,X1)) | r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))))) => ((sK0 = sK2 | ~r2_hidden(sK0,sK1) | ~r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2)))) & ((sK0 != sK2 & r2_hidden(sK0,sK1)) | r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2)))))),
% 1.65/0.58    introduced(choice_axiom,[])).
% 1.65/0.58  fof(f24,plain,(
% 1.65/0.58    ? [X0,X1,X2] : ((X0 = X2 | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) & ((X0 != X2 & r2_hidden(X0,X1)) | r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 1.65/0.58    inference(flattening,[],[f23])).
% 1.65/0.58  fof(f23,plain,(
% 1.65/0.58    ? [X0,X1,X2] : (((X0 = X2 | ~r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) & ((X0 != X2 & r2_hidden(X0,X1)) | r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 1.65/0.58    inference(nnf_transformation,[],[f20])).
% 1.65/0.58  fof(f20,plain,(
% 1.65/0.58    ? [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <~> (X0 != X2 & r2_hidden(X0,X1)))),
% 1.65/0.58    inference(ennf_transformation,[],[f17])).
% 1.65/0.58  fof(f17,negated_conjecture,(
% 1.65/0.58    ~! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 1.65/0.58    inference(negated_conjecture,[],[f16])).
% 1.65/0.58  fof(f16,conjecture,(
% 1.65/0.58    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 1.65/0.58  fof(f262,plain,(
% 1.65/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X0,k4_xboole_0(X1,X2)) | r2_hidden(X0,X1)) )),
% 1.65/0.58    inference(subsumption_resolution,[],[f253,f72])).
% 1.65/0.58  fof(f72,plain,(
% 1.65/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X0,k4_xboole_0(X2,X1)) | ~r2_hidden(X0,X1)) )),
% 1.65/0.58    inference(resolution,[],[f45,f39])).
% 1.65/0.58  fof(f39,plain,(
% 1.65/0.58    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 1.65/0.58    inference(cnf_transformation,[],[f7])).
% 1.65/0.58  fof(f7,axiom,(
% 1.65/0.58    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 1.65/0.58  fof(f253,plain,(
% 1.65/0.58    ( ! [X2,X0,X1] : (r2_hidden(X0,X1) | ~r2_hidden(X0,k4_xboole_0(X1,X2)) | r2_hidden(X0,X2)) )),
% 1.65/0.58    inference(resolution,[],[f91,f182])).
% 1.65/0.58  fof(f91,plain,(
% 1.65/0.58    ( ! [X2,X0,X1] : (r2_hidden(X2,k3_xboole_0(X0,X1)) | r2_hidden(X2,X0) | ~r2_hidden(X2,k4_xboole_0(X0,X1))) )),
% 1.65/0.58    inference(superposition,[],[f52,f42])).
% 1.65/0.58  fof(f52,plain,(
% 1.65/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X1) | r2_hidden(X0,X2)) )),
% 1.65/0.58    inference(cnf_transformation,[],[f33])).
% 1.65/0.58  fof(f292,plain,(
% 1.65/0.58    r2_hidden(sK0,k3_xboole_0(sK1,k1_tarski(sK2))) | ~r2_hidden(sK0,sK1) | sK0 = sK2),
% 1.65/0.58    inference(duplicate_literal_removal,[],[f284])).
% 1.65/0.58  fof(f284,plain,(
% 1.65/0.58    r2_hidden(sK0,k3_xboole_0(sK1,k1_tarski(sK2))) | ~r2_hidden(sK0,sK1) | ~r2_hidden(sK0,sK1) | sK0 = sK2),
% 1.65/0.58    inference(resolution,[],[f104,f36])).
% 1.65/0.58  fof(f36,plain,(
% 1.65/0.58    ~r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2))) | ~r2_hidden(sK0,sK1) | sK0 = sK2),
% 1.65/0.58    inference(cnf_transformation,[],[f26])).
% 1.65/0.58  fof(f104,plain,(
% 1.65/0.58    ( ! [X2,X0,X1] : (r2_hidden(X2,k4_xboole_0(X0,X1)) | r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r2_hidden(X2,X0)) )),
% 1.65/0.58    inference(superposition,[],[f54,f42])).
% 1.65/0.58  fof(f112,plain,(
% 1.65/0.58    ~r2_hidden(sK0,k1_tarski(sK2))),
% 1.65/0.58    inference(subsumption_resolution,[],[f107,f62])).
% 1.65/0.58  fof(f62,plain,(
% 1.65/0.58    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 1.65/0.58    inference(equality_resolution,[],[f46])).
% 1.65/0.58  fof(f46,plain,(
% 1.65/0.58    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.65/0.58    inference(cnf_transformation,[],[f32])).
% 1.65/0.58  fof(f107,plain,(
% 1.65/0.58    ~r2_hidden(sK0,k1_tarski(sK2)) | sK0 != sK2),
% 1.65/0.58    inference(resolution,[],[f72,f35])).
% 1.65/0.58  fof(f35,plain,(
% 1.65/0.58    r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2))) | sK0 != sK2),
% 1.65/0.58    inference(cnf_transformation,[],[f26])).
% 1.65/0.58  % SZS output end Proof for theBenchmark
% 1.65/0.58  % (306)------------------------------
% 1.65/0.58  % (306)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.65/0.58  % (306)Termination reason: Refutation
% 1.65/0.58  
% 1.65/0.58  % (306)Memory used [KB]: 1918
% 1.65/0.58  % (306)Time elapsed: 0.144 s
% 1.65/0.58  % (306)------------------------------
% 1.65/0.58  % (306)------------------------------
% 1.65/0.58  % (32764)Success in time 0.217 s
%------------------------------------------------------------------------------
