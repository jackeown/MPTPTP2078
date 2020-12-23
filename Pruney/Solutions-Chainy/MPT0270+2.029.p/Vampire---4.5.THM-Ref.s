%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:00 EST 2020

% Result     : Theorem 1.37s
% Output     : Refutation 1.37s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 376 expanded)
%              Number of leaves         :   11 (  94 expanded)
%              Depth                    :   23
%              Number of atoms          :  209 (1319 expanded)
%              Number of equality atoms :   48 ( 311 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f315,plain,(
    $false ),
    inference(resolution,[],[f304,f206])).

fof(f206,plain,(
    r2_hidden(sK2(sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    inference(resolution,[],[f190,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
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
    inference(rectify,[],[f4])).

fof(f4,axiom,(
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

fof(f190,plain,(
    ~ r1_xboole_0(sK1,k1_tarski(sK0)) ),
    inference(trivial_inequality_removal,[],[f189])).

fof(f189,plain,
    ( sK1 != sK1
    | ~ r1_xboole_0(sK1,k1_tarski(sK0)) ),
    inference(superposition,[],[f187,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f187,plain,(
    sK1 != k4_xboole_0(sK1,k1_tarski(sK0)) ),
    inference(subsumption_resolution,[],[f184,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f184,plain,
    ( r2_hidden(sK0,sK1)
    | sK1 != k4_xboole_0(sK1,k1_tarski(sK0)) ),
    inference(resolution,[],[f167,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f167,plain,
    ( ~ r1_xboole_0(sK1,k1_tarski(sK0))
    | r2_hidden(sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f151])).

fof(f151,plain,
    ( ~ r1_xboole_0(sK1,k1_tarski(sK0))
    | r2_hidden(sK0,sK1)
    | r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f102,f100])).

fof(f100,plain,
    ( r2_hidden(sK2(k1_tarski(sK0),sK1),k1_tarski(sK0))
    | r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f98,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f98,plain,
    ( ~ r1_xboole_0(k1_tarski(sK0),sK1)
    | r2_hidden(sK0,sK1) ),
    inference(trivial_inequality_removal,[],[f97])).

fof(f97,plain,
    ( k1_tarski(sK0) != k1_tarski(sK0)
    | r2_hidden(sK0,sK1)
    | ~ r1_xboole_0(k1_tarski(sK0),sK1) ),
    inference(superposition,[],[f44,f56])).

fof(f44,plain,
    ( k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)
    | r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ( r2_hidden(sK0,sK1)
      | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) )
    & ( ~ r2_hidden(sK0,sK1)
      | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f26])).

fof(f26,plain,
    ( ? [X0,X1] :
        ( ( r2_hidden(X0,X1)
          | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) )
        & ( ~ r2_hidden(X0,X1)
          | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) ) )
   => ( ( r2_hidden(sK0,sK1)
        | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) )
      & ( ~ r2_hidden(sK0,sK1)
        | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,X1)
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) )
      & ( ~ r2_hidden(X0,X1)
        | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <~> ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
      <=> ~ r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_zfmisc_1)).

fof(f102,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2(k1_tarski(sK0),sK1),X0)
      | ~ r1_xboole_0(sK1,X0)
      | r2_hidden(sK0,sK1) ) ),
    inference(resolution,[],[f101,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f101,plain,
    ( r2_hidden(sK2(k1_tarski(sK0),sK1),sK1)
    | r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f98,f53])).

fof(f304,plain,(
    ! [X5] : ~ r2_hidden(X5,k1_tarski(sK0)) ),
    inference(subsumption_resolution,[],[f302,f241])).

fof(f241,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,k1_tarski(sK0)) ) ),
    inference(resolution,[],[f236,f54])).

fof(f236,plain,(
    r1_xboole_0(k1_tarski(sK0),sK1) ),
    inference(trivial_inequality_removal,[],[f232])).

fof(f232,plain,
    ( k1_tarski(sK0) != k1_tarski(sK0)
    | r1_xboole_0(k1_tarski(sK0),sK1) ),
    inference(superposition,[],[f57,f192])).

fof(f192,plain,(
    k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(resolution,[],[f191,f43])).

fof(f43,plain,
    ( ~ r2_hidden(sK0,sK1)
    | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f191,plain,(
    r2_hidden(sK0,sK1) ),
    inference(trivial_inequality_removal,[],[f188])).

fof(f188,plain,
    ( sK1 != sK1
    | r2_hidden(sK0,sK1) ),
    inference(superposition,[],[f187,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f302,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,k1_tarski(sK0))
      | r2_hidden(X5,sK1) ) ),
    inference(superposition,[],[f82,f249])).

fof(f249,plain,(
    k1_tarski(sK0) = k3_xboole_0(sK1,k1_tarski(sK0)) ),
    inference(backward_demodulation,[],[f237,f242])).

fof(f242,plain,(
    k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) ),
    inference(resolution,[],[f231,f59])).

fof(f231,plain,(
    ~ r2_hidden(sK0,k1_tarski(sK0)) ),
    inference(superposition,[],[f210,f192])).

fof(f210,plain,(
    ! [X0] : ~ r2_hidden(sK0,k4_xboole_0(X0,sK1)) ),
    inference(resolution,[],[f194,f47])).

fof(f47,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f194,plain,(
    ! [X1] :
      ( ~ r1_xboole_0(X1,sK1)
      | ~ r2_hidden(sK0,X1) ) ),
    inference(resolution,[],[f191,f54])).

fof(f237,plain,(
    k4_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) = k3_xboole_0(sK1,k1_tarski(sK0)) ),
    inference(forward_demodulation,[],[f233,f48])).

fof(f48,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f233,plain,(
    k3_xboole_0(k1_tarski(sK0),sK1) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) ),
    inference(superposition,[],[f50,f192])).

fof(f50,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f82,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f34,f35])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(sK3(X0,X1,X2),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
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
    inference(rectify,[],[f33])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f32,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:55:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (5859)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (5884)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.51  % (5868)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.52  % (5858)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.21/0.53  % (5856)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.21/0.53  % (5876)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.21/0.53  % (5854)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.21/0.53  % (5854)Refutation not found, incomplete strategy% (5854)------------------------------
% 1.21/0.53  % (5854)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.21/0.53  % (5854)Termination reason: Refutation not found, incomplete strategy
% 1.21/0.53  
% 1.21/0.53  % (5854)Memory used [KB]: 1663
% 1.21/0.53  % (5854)Time elapsed: 0.115 s
% 1.21/0.53  % (5854)------------------------------
% 1.21/0.53  % (5854)------------------------------
% 1.21/0.54  % (5883)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.21/0.54  % (5863)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.37/0.54  % (5855)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.37/0.54  % (5863)Refutation not found, incomplete strategy% (5863)------------------------------
% 1.37/0.54  % (5863)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.54  % (5863)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.54  
% 1.37/0.54  % (5863)Memory used [KB]: 10618
% 1.37/0.54  % (5863)Time elapsed: 0.127 s
% 1.37/0.54  % (5863)------------------------------
% 1.37/0.54  % (5863)------------------------------
% 1.37/0.54  % (5857)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.37/0.54  % (5865)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.37/0.54  % (5865)Refutation not found, incomplete strategy% (5865)------------------------------
% 1.37/0.54  % (5865)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.54  % (5865)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.54  
% 1.37/0.54  % (5865)Memory used [KB]: 10618
% 1.37/0.54  % (5865)Time elapsed: 0.130 s
% 1.37/0.54  % (5865)------------------------------
% 1.37/0.54  % (5865)------------------------------
% 1.37/0.54  % (5862)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.37/0.54  % (5878)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.37/0.55  % (5881)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.37/0.55  % (5875)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.37/0.55  % (5879)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.37/0.55  % (5867)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.37/0.55  % (5877)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.37/0.55  % (5870)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.37/0.55  % (5874)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.37/0.55  % (5873)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.37/0.55  % (5869)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.37/0.55  % (5864)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.37/0.56  % (5880)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.37/0.56  % (5882)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.37/0.56  % (5871)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.37/0.56  % (5878)Refutation found. Thanks to Tanya!
% 1.37/0.56  % SZS status Theorem for theBenchmark
% 1.37/0.56  % SZS output start Proof for theBenchmark
% 1.37/0.56  fof(f315,plain,(
% 1.37/0.56    $false),
% 1.37/0.56    inference(resolution,[],[f304,f206])).
% 1.37/0.56  fof(f206,plain,(
% 1.37/0.56    r2_hidden(sK2(sK1,k1_tarski(sK0)),k1_tarski(sK0))),
% 1.37/0.56    inference(resolution,[],[f190,f53])).
% 1.37/0.56  fof(f53,plain,(
% 1.37/0.56    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 1.37/0.56    inference(cnf_transformation,[],[f29])).
% 1.37/0.56  fof(f29,plain,(
% 1.37/0.56    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.37/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f28])).
% 1.37/0.56  fof(f28,plain,(
% 1.37/0.56    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 1.37/0.56    introduced(choice_axiom,[])).
% 1.37/0.56  fof(f21,plain,(
% 1.37/0.56    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.37/0.56    inference(ennf_transformation,[],[f19])).
% 1.37/0.56  fof(f19,plain,(
% 1.37/0.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.37/0.56    inference(rectify,[],[f4])).
% 1.37/0.56  fof(f4,axiom,(
% 1.37/0.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.37/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.37/0.56  fof(f190,plain,(
% 1.37/0.56    ~r1_xboole_0(sK1,k1_tarski(sK0))),
% 1.37/0.56    inference(trivial_inequality_removal,[],[f189])).
% 1.37/0.56  fof(f189,plain,(
% 1.37/0.56    sK1 != sK1 | ~r1_xboole_0(sK1,k1_tarski(sK0))),
% 1.37/0.56    inference(superposition,[],[f187,f56])).
% 1.37/0.56  fof(f56,plain,(
% 1.37/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 1.37/0.56    inference(cnf_transformation,[],[f30])).
% 1.37/0.56  fof(f30,plain,(
% 1.37/0.56    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 1.37/0.56    inference(nnf_transformation,[],[f10])).
% 1.37/0.56  fof(f10,axiom,(
% 1.37/0.56    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.37/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.37/0.56  fof(f187,plain,(
% 1.37/0.56    sK1 != k4_xboole_0(sK1,k1_tarski(sK0))),
% 1.37/0.56    inference(subsumption_resolution,[],[f184,f58])).
% 1.37/0.56  fof(f58,plain,(
% 1.37/0.56    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) )),
% 1.37/0.56    inference(cnf_transformation,[],[f31])).
% 1.37/0.56  fof(f31,plain,(
% 1.37/0.56    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 1.37/0.56    inference(nnf_transformation,[],[f16])).
% 1.37/0.56  fof(f16,axiom,(
% 1.37/0.56    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 1.37/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 1.37/0.56  fof(f184,plain,(
% 1.37/0.56    r2_hidden(sK0,sK1) | sK1 != k4_xboole_0(sK1,k1_tarski(sK0))),
% 1.37/0.56    inference(resolution,[],[f167,f57])).
% 1.37/0.56  fof(f57,plain,(
% 1.37/0.56    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 1.37/0.56    inference(cnf_transformation,[],[f30])).
% 1.37/0.56  fof(f167,plain,(
% 1.37/0.56    ~r1_xboole_0(sK1,k1_tarski(sK0)) | r2_hidden(sK0,sK1)),
% 1.37/0.56    inference(duplicate_literal_removal,[],[f151])).
% 1.37/0.56  fof(f151,plain,(
% 1.37/0.56    ~r1_xboole_0(sK1,k1_tarski(sK0)) | r2_hidden(sK0,sK1) | r2_hidden(sK0,sK1)),
% 1.37/0.56    inference(resolution,[],[f102,f100])).
% 1.37/0.56  fof(f100,plain,(
% 1.37/0.56    r2_hidden(sK2(k1_tarski(sK0),sK1),k1_tarski(sK0)) | r2_hidden(sK0,sK1)),
% 1.37/0.56    inference(resolution,[],[f98,f52])).
% 1.37/0.56  fof(f52,plain,(
% 1.37/0.56    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 1.37/0.56    inference(cnf_transformation,[],[f29])).
% 1.37/0.56  fof(f98,plain,(
% 1.37/0.56    ~r1_xboole_0(k1_tarski(sK0),sK1) | r2_hidden(sK0,sK1)),
% 1.37/0.56    inference(trivial_inequality_removal,[],[f97])).
% 1.37/0.56  fof(f97,plain,(
% 1.37/0.56    k1_tarski(sK0) != k1_tarski(sK0) | r2_hidden(sK0,sK1) | ~r1_xboole_0(k1_tarski(sK0),sK1)),
% 1.37/0.56    inference(superposition,[],[f44,f56])).
% 1.37/0.56  fof(f44,plain,(
% 1.37/0.56    k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) | r2_hidden(sK0,sK1)),
% 1.37/0.56    inference(cnf_transformation,[],[f27])).
% 1.37/0.56  fof(f27,plain,(
% 1.37/0.56    (r2_hidden(sK0,sK1) | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)) & (~r2_hidden(sK0,sK1) | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1))),
% 1.37/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f26])).
% 1.37/0.56  fof(f26,plain,(
% 1.37/0.56    ? [X0,X1] : ((r2_hidden(X0,X1) | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)) & (~r2_hidden(X0,X1) | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1))) => ((r2_hidden(sK0,sK1) | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)) & (~r2_hidden(sK0,sK1) | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1)))),
% 1.37/0.56    introduced(choice_axiom,[])).
% 1.37/0.56  fof(f25,plain,(
% 1.37/0.56    ? [X0,X1] : ((r2_hidden(X0,X1) | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)) & (~r2_hidden(X0,X1) | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)))),
% 1.37/0.56    inference(nnf_transformation,[],[f20])).
% 1.37/0.56  fof(f20,plain,(
% 1.37/0.56    ? [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <~> ~r2_hidden(X0,X1))),
% 1.37/0.56    inference(ennf_transformation,[],[f18])).
% 1.37/0.56  fof(f18,negated_conjecture,(
% 1.37/0.56    ~! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <=> ~r2_hidden(X0,X1))),
% 1.37/0.56    inference(negated_conjecture,[],[f17])).
% 1.37/0.56  fof(f17,conjecture,(
% 1.37/0.56    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <=> ~r2_hidden(X0,X1))),
% 1.37/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_zfmisc_1)).
% 1.37/0.56  fof(f102,plain,(
% 1.37/0.56    ( ! [X0] : (~r2_hidden(sK2(k1_tarski(sK0),sK1),X0) | ~r1_xboole_0(sK1,X0) | r2_hidden(sK0,sK1)) )),
% 1.37/0.56    inference(resolution,[],[f101,f54])).
% 1.37/0.56  fof(f54,plain,(
% 1.37/0.56    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.37/0.56    inference(cnf_transformation,[],[f29])).
% 1.37/0.56  fof(f101,plain,(
% 1.37/0.56    r2_hidden(sK2(k1_tarski(sK0),sK1),sK1) | r2_hidden(sK0,sK1)),
% 1.37/0.56    inference(resolution,[],[f98,f53])).
% 1.37/0.56  fof(f304,plain,(
% 1.37/0.56    ( ! [X5] : (~r2_hidden(X5,k1_tarski(sK0))) )),
% 1.37/0.56    inference(subsumption_resolution,[],[f302,f241])).
% 1.37/0.56  fof(f241,plain,(
% 1.37/0.56    ( ! [X0] : (~r2_hidden(X0,sK1) | ~r2_hidden(X0,k1_tarski(sK0))) )),
% 1.37/0.56    inference(resolution,[],[f236,f54])).
% 1.37/0.56  fof(f236,plain,(
% 1.37/0.56    r1_xboole_0(k1_tarski(sK0),sK1)),
% 1.37/0.56    inference(trivial_inequality_removal,[],[f232])).
% 1.37/0.56  fof(f232,plain,(
% 1.37/0.56    k1_tarski(sK0) != k1_tarski(sK0) | r1_xboole_0(k1_tarski(sK0),sK1)),
% 1.37/0.56    inference(superposition,[],[f57,f192])).
% 1.37/0.56  fof(f192,plain,(
% 1.37/0.56    k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1)),
% 1.37/0.56    inference(resolution,[],[f191,f43])).
% 1.37/0.56  fof(f43,plain,(
% 1.37/0.56    ~r2_hidden(sK0,sK1) | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1)),
% 1.37/0.56    inference(cnf_transformation,[],[f27])).
% 1.37/0.56  fof(f191,plain,(
% 1.37/0.56    r2_hidden(sK0,sK1)),
% 1.37/0.56    inference(trivial_inequality_removal,[],[f188])).
% 1.37/0.56  fof(f188,plain,(
% 1.37/0.56    sK1 != sK1 | r2_hidden(sK0,sK1)),
% 1.37/0.56    inference(superposition,[],[f187,f59])).
% 1.37/0.56  fof(f59,plain,(
% 1.37/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) )),
% 1.37/0.56    inference(cnf_transformation,[],[f31])).
% 1.37/0.56  fof(f302,plain,(
% 1.37/0.56    ( ! [X5] : (~r2_hidden(X5,k1_tarski(sK0)) | r2_hidden(X5,sK1)) )),
% 1.37/0.56    inference(superposition,[],[f82,f249])).
% 1.37/0.56  fof(f249,plain,(
% 1.37/0.56    k1_tarski(sK0) = k3_xboole_0(sK1,k1_tarski(sK0))),
% 1.37/0.56    inference(backward_demodulation,[],[f237,f242])).
% 1.37/0.56  fof(f242,plain,(
% 1.37/0.56    k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK0))),
% 1.37/0.56    inference(resolution,[],[f231,f59])).
% 1.37/0.56  fof(f231,plain,(
% 1.37/0.56    ~r2_hidden(sK0,k1_tarski(sK0))),
% 1.37/0.56    inference(superposition,[],[f210,f192])).
% 1.37/0.56  fof(f210,plain,(
% 1.37/0.56    ( ! [X0] : (~r2_hidden(sK0,k4_xboole_0(X0,sK1))) )),
% 1.37/0.56    inference(resolution,[],[f194,f47])).
% 1.37/0.56  fof(f47,plain,(
% 1.37/0.56    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 1.37/0.56    inference(cnf_transformation,[],[f9])).
% 1.37/0.56  fof(f9,axiom,(
% 1.37/0.56    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 1.37/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 1.37/0.56  fof(f194,plain,(
% 1.37/0.56    ( ! [X1] : (~r1_xboole_0(X1,sK1) | ~r2_hidden(sK0,X1)) )),
% 1.37/0.56    inference(resolution,[],[f191,f54])).
% 1.37/0.56  fof(f237,plain,(
% 1.37/0.56    k4_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) = k3_xboole_0(sK1,k1_tarski(sK0))),
% 1.37/0.56    inference(forward_demodulation,[],[f233,f48])).
% 1.37/0.56  fof(f48,plain,(
% 1.37/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.37/0.56    inference(cnf_transformation,[],[f1])).
% 1.37/0.56  fof(f1,axiom,(
% 1.37/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.37/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.37/0.56  fof(f233,plain,(
% 1.37/0.56    k3_xboole_0(k1_tarski(sK0),sK1) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK0))),
% 1.37/0.56    inference(superposition,[],[f50,f192])).
% 1.37/0.56  fof(f50,plain,(
% 1.37/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.37/0.56    inference(cnf_transformation,[],[f8])).
% 1.37/0.56  fof(f8,axiom,(
% 1.37/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.37/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.37/0.56  fof(f82,plain,(
% 1.37/0.56    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 1.37/0.56    inference(equality_resolution,[],[f61])).
% 1.37/0.56  fof(f61,plain,(
% 1.37/0.56    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 1.37/0.56    inference(cnf_transformation,[],[f36])).
% 1.37/0.56  fof(f36,plain,(
% 1.37/0.56    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.37/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f34,f35])).
% 1.37/0.56  fof(f35,plain,(
% 1.37/0.56    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 1.37/0.56    introduced(choice_axiom,[])).
% 1.37/0.56  fof(f34,plain,(
% 1.37/0.56    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.37/0.56    inference(rectify,[],[f33])).
% 1.37/0.56  fof(f33,plain,(
% 1.37/0.56    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.37/0.56    inference(flattening,[],[f32])).
% 1.37/0.56  fof(f32,plain,(
% 1.37/0.56    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.37/0.56    inference(nnf_transformation,[],[f2])).
% 1.37/0.56  fof(f2,axiom,(
% 1.37/0.56    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.37/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.37/0.56  % SZS output end Proof for theBenchmark
% 1.37/0.56  % (5878)------------------------------
% 1.37/0.56  % (5878)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.56  % (5878)Termination reason: Refutation
% 1.37/0.56  
% 1.37/0.56  % (5878)Memory used [KB]: 1918
% 1.37/0.56  % (5878)Time elapsed: 0.135 s
% 1.37/0.56  % (5878)------------------------------
% 1.37/0.56  % (5878)------------------------------
% 1.37/0.57  % (5852)Success in time 0.199 s
%------------------------------------------------------------------------------
