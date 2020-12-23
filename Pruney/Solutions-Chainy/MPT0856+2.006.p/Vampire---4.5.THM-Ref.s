%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:14 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 104 expanded)
%              Number of leaves         :   18 (  28 expanded)
%              Depth                    :   17
%              Number of atoms          :  192 ( 279 expanded)
%              Number of equality atoms :   30 (  48 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f283,plain,(
    $false ),
    inference(subsumption_resolution,[],[f279,f102])).

fof(f102,plain,(
    ! [X0] : r2_hidden(X0,k1_zfmisc_1(X0)) ),
    inference(subsumption_resolution,[],[f99,f54])).

fof(f54,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f99,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_zfmisc_1(X0))
      | r2_hidden(X0,k1_zfmisc_1(X0)) ) ),
    inference(resolution,[],[f66,f92])).

fof(f92,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f58,f55])).

fof(f55,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f58,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f279,plain,(
    ~ r2_hidden(k1_mcart_1(sK0),k1_zfmisc_1(k1_mcart_1(sK0))) ),
    inference(resolution,[],[f276,f127])).

fof(f127,plain,(
    r2_hidden(k1_mcart_1(sK0),k1_tarski(sK1)) ),
    inference(resolution,[],[f81,f52])).

fof(f52,plain,(
    r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),sK2)) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( ( ~ r2_hidden(k2_mcart_1(sK0),sK2)
      | sK1 != k1_mcart_1(sK0) )
    & r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f35])).

fof(f35,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r2_hidden(k2_mcart_1(X0),X2)
          | k1_mcart_1(X0) != X1 )
        & r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) )
   => ( ( ~ r2_hidden(k2_mcart_1(sK0),sK2)
        | sK1 != k1_mcart_1(sK0) )
      & r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(k2_mcart_1(X0),X2)
        | k1_mcart_1(X0) != X1 )
      & r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    inference(ennf_transformation,[],[f24])).

% (2120)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
fof(f24,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))
       => ( r2_hidden(k2_mcart_1(X0),X2)
          & k1_mcart_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & k1_mcart_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_mcart_1)).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f276,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,k1_tarski(sK1))
      | ~ r2_hidden(X4,k1_zfmisc_1(k1_mcart_1(sK0))) ) ),
    inference(resolution,[],[f268,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f37])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
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

fof(f268,plain,(
    r1_xboole_0(k1_tarski(sK1),k1_zfmisc_1(k1_mcart_1(sK0))) ),
    inference(trivial_inequality_removal,[],[f267])).

fof(f267,plain,
    ( k1_tarski(sK1) != k1_tarski(sK1)
    | r1_xboole_0(k1_tarski(sK1),k1_zfmisc_1(k1_mcart_1(sK0))) ),
    inference(superposition,[],[f75,f264])).

fof(f264,plain,(
    k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),k1_zfmisc_1(k1_mcart_1(sK0))) ),
    inference(resolution,[],[f146,f142])).

fof(f142,plain,(
    ~ r1_tarski(sK1,k1_mcart_1(sK0)) ),
    inference(subsumption_resolution,[],[f133,f141])).

fof(f141,plain,(
    sK1 != k1_mcart_1(sK0) ),
    inference(subsumption_resolution,[],[f53,f137])).

fof(f137,plain,(
    r2_hidden(k2_mcart_1(sK0),sK2) ),
    inference(resolution,[],[f82,f52])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k2_mcart_1(X0),X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f53,plain,
    ( ~ r2_hidden(k2_mcart_1(sK0),sK2)
    | sK1 != k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f133,plain,
    ( ~ r1_tarski(sK1,k1_mcart_1(sK0))
    | sK1 = k1_mcart_1(sK0) ),
    inference(resolution,[],[f131,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f131,plain,(
    r1_tarski(k1_mcart_1(sK0),sK1) ),
    inference(resolution,[],[f127,f121])).

fof(f121,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_tarski(X0))
      | r1_tarski(X1,X0) ) ),
    inference(superposition,[],[f116,f56])).

fof(f56,plain,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).

fof(f116,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f114,f95])).

fof(f95,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X1,k1_zfmisc_1(X2))
      | r1_tarski(X1,X2) ) ),
    inference(resolution,[],[f76,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

% (2129)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
fof(f18,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

% (2130)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
fof(f76,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f114,plain,(
    ! [X2,X3] :
      ( r2_hidden(X2,k1_zfmisc_1(k3_tarski(X3)))
      | ~ r2_hidden(X2,X3) ) ),
    inference(resolution,[],[f71,f57])).

fof(f57,plain,(
    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_zfmisc_1)).

fof(f71,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f42,f43])).

% (2126)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f146,plain,(
    ! [X8,X9] :
      ( r1_tarski(X8,X9)
      | k1_tarski(X8) = k4_xboole_0(k1_tarski(X8),k1_zfmisc_1(X9)) ) ),
    inference(resolution,[],[f79,f95])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
        | r2_hidden(X0,X1) )
      & ( ~ r2_hidden(X0,X1)
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l33_zfmisc_1)).

fof(f75,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n003.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:20:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (2125)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.51  % (2117)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.52  % (2109)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.54  % (2106)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (2105)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (2101)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (2102)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (2107)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.54  % (2118)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.54  % (2104)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (2104)Refutation not found, incomplete strategy% (2104)------------------------------
% 0.22/0.54  % (2104)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (2104)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (2104)Memory used [KB]: 10746
% 0.22/0.54  % (2104)Time elapsed: 0.134 s
% 0.22/0.54  % (2104)------------------------------
% 0.22/0.54  % (2104)------------------------------
% 0.22/0.55  % (2131)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.55  % (2127)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.55  % (2109)Refutation found. Thanks to Tanya!
% 0.22/0.55  % SZS status Theorem for theBenchmark
% 0.22/0.55  % SZS output start Proof for theBenchmark
% 0.22/0.55  fof(f283,plain,(
% 0.22/0.55    $false),
% 0.22/0.55    inference(subsumption_resolution,[],[f279,f102])).
% 0.22/0.55  fof(f102,plain,(
% 0.22/0.55    ( ! [X0] : (r2_hidden(X0,k1_zfmisc_1(X0))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f99,f54])).
% 0.22/0.55  fof(f54,plain,(
% 0.22/0.55    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f17])).
% 0.22/0.55  fof(f17,axiom,(
% 0.22/0.55    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.22/0.55  fof(f99,plain,(
% 0.22/0.55    ( ! [X0] : (v1_xboole_0(k1_zfmisc_1(X0)) | r2_hidden(X0,k1_zfmisc_1(X0))) )),
% 0.22/0.55    inference(resolution,[],[f66,f92])).
% 0.22/0.55  fof(f92,plain,(
% 0.22/0.55    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.22/0.55    inference(forward_demodulation,[],[f58,f55])).
% 0.22/0.55  fof(f55,plain,(
% 0.22/0.55    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.22/0.55    inference(cnf_transformation,[],[f15])).
% 0.22/0.55  fof(f15,axiom,(
% 0.22/0.55    ! [X0] : k2_subset_1(X0) = X0),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.22/0.55  fof(f58,plain,(
% 0.22/0.55    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f16])).
% 0.22/0.55  fof(f16,axiom,(
% 0.22/0.55    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.22/0.55  fof(f66,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f29])).
% 0.22/0.55  fof(f29,plain,(
% 0.22/0.55    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.22/0.55    inference(flattening,[],[f28])).
% 0.22/0.55  fof(f28,plain,(
% 0.22/0.55    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.22/0.55    inference(ennf_transformation,[],[f19])).
% 0.22/0.55  fof(f19,axiom,(
% 0.22/0.55    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.22/0.55  fof(f279,plain,(
% 0.22/0.55    ~r2_hidden(k1_mcart_1(sK0),k1_zfmisc_1(k1_mcart_1(sK0)))),
% 0.22/0.55    inference(resolution,[],[f276,f127])).
% 0.22/0.55  fof(f127,plain,(
% 0.22/0.55    r2_hidden(k1_mcart_1(sK0),k1_tarski(sK1))),
% 0.22/0.55    inference(resolution,[],[f81,f52])).
% 0.22/0.55  fof(f52,plain,(
% 0.22/0.55    r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),sK2))),
% 0.22/0.55    inference(cnf_transformation,[],[f36])).
% 0.22/0.55  fof(f36,plain,(
% 0.22/0.55    (~r2_hidden(k2_mcart_1(sK0),sK2) | sK1 != k1_mcart_1(sK0)) & r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),sK2))),
% 0.22/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f35])).
% 0.22/0.55  fof(f35,plain,(
% 0.22/0.55    ? [X0,X1,X2] : ((~r2_hidden(k2_mcart_1(X0),X2) | k1_mcart_1(X0) != X1) & r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))) => ((~r2_hidden(k2_mcart_1(sK0),sK2) | sK1 != k1_mcart_1(sK0)) & r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),sK2)))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f26,plain,(
% 0.22/0.55    ? [X0,X1,X2] : ((~r2_hidden(k2_mcart_1(X0),X2) | k1_mcart_1(X0) != X1) & r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)))),
% 0.22/0.55    inference(ennf_transformation,[],[f24])).
% 0.22/0.55  % (2120)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.55  fof(f24,negated_conjecture,(
% 0.22/0.55    ~! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) => (r2_hidden(k2_mcart_1(X0),X2) & k1_mcart_1(X0) = X1))),
% 0.22/0.55    inference(negated_conjecture,[],[f23])).
% 0.22/0.55  fof(f23,conjecture,(
% 0.22/0.55    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) => (r2_hidden(k2_mcart_1(X0),X2) & k1_mcart_1(X0) = X1))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_mcart_1)).
% 0.22/0.55  fof(f81,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f32])).
% 0.22/0.55  fof(f32,plain,(
% 0.22/0.55    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.22/0.55    inference(ennf_transformation,[],[f21])).
% 0.22/0.55  fof(f21,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).
% 0.22/0.55  fof(f276,plain,(
% 0.22/0.55    ( ! [X4] : (~r2_hidden(X4,k1_tarski(sK1)) | ~r2_hidden(X4,k1_zfmisc_1(k1_mcart_1(sK0)))) )),
% 0.22/0.55    inference(resolution,[],[f268,f65])).
% 0.22/0.55  fof(f65,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f38])).
% 0.22/0.55  fof(f38,plain,(
% 0.22/0.55    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.22/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f37])).
% 0.22/0.55  fof(f37,plain,(
% 0.22/0.55    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f27,plain,(
% 0.22/0.55    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.22/0.55    inference(ennf_transformation,[],[f25])).
% 0.22/0.55  fof(f25,plain,(
% 0.22/0.55    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.55    inference(rectify,[],[f2])).
% 0.22/0.55  fof(f2,axiom,(
% 0.22/0.55    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.22/0.55  fof(f268,plain,(
% 0.22/0.55    r1_xboole_0(k1_tarski(sK1),k1_zfmisc_1(k1_mcart_1(sK0)))),
% 0.22/0.55    inference(trivial_inequality_removal,[],[f267])).
% 0.22/0.55  fof(f267,plain,(
% 0.22/0.55    k1_tarski(sK1) != k1_tarski(sK1) | r1_xboole_0(k1_tarski(sK1),k1_zfmisc_1(k1_mcart_1(sK0)))),
% 0.22/0.55    inference(superposition,[],[f75,f264])).
% 0.22/0.55  fof(f264,plain,(
% 0.22/0.55    k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),k1_zfmisc_1(k1_mcart_1(sK0)))),
% 0.22/0.55    inference(resolution,[],[f146,f142])).
% 0.22/0.55  fof(f142,plain,(
% 0.22/0.55    ~r1_tarski(sK1,k1_mcart_1(sK0))),
% 0.22/0.55    inference(subsumption_resolution,[],[f133,f141])).
% 0.22/0.55  fof(f141,plain,(
% 0.22/0.55    sK1 != k1_mcart_1(sK0)),
% 0.22/0.55    inference(subsumption_resolution,[],[f53,f137])).
% 0.22/0.55  fof(f137,plain,(
% 0.22/0.55    r2_hidden(k2_mcart_1(sK0),sK2)),
% 0.22/0.55    inference(resolution,[],[f82,f52])).
% 0.22/0.55  fof(f82,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k2_mcart_1(X0),X2)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f32])).
% 0.22/0.55  fof(f53,plain,(
% 0.22/0.55    ~r2_hidden(k2_mcart_1(sK0),sK2) | sK1 != k1_mcart_1(sK0)),
% 0.22/0.55    inference(cnf_transformation,[],[f36])).
% 0.22/0.55  fof(f133,plain,(
% 0.22/0.55    ~r1_tarski(sK1,k1_mcart_1(sK0)) | sK1 = k1_mcart_1(sK0)),
% 0.22/0.55    inference(resolution,[],[f131,f70])).
% 0.22/0.55  fof(f70,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.22/0.55    inference(cnf_transformation,[],[f40])).
% 0.22/0.55  fof(f40,plain,(
% 0.22/0.55    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.55    inference(flattening,[],[f39])).
% 0.22/0.55  fof(f39,plain,(
% 0.22/0.55    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.55    inference(nnf_transformation,[],[f3])).
% 0.22/0.55  fof(f3,axiom,(
% 0.22/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.55  fof(f131,plain,(
% 0.22/0.55    r1_tarski(k1_mcart_1(sK0),sK1)),
% 0.22/0.55    inference(resolution,[],[f127,f121])).
% 0.22/0.55  fof(f121,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~r2_hidden(X1,k1_tarski(X0)) | r1_tarski(X1,X0)) )),
% 0.22/0.55    inference(superposition,[],[f116,f56])).
% 0.22/0.55  fof(f56,plain,(
% 0.22/0.55    ( ! [X0] : (k3_tarski(k1_tarski(X0)) = X0) )),
% 0.22/0.55    inference(cnf_transformation,[],[f14])).
% 0.22/0.55  fof(f14,axiom,(
% 0.22/0.55    ! [X0] : k3_tarski(k1_tarski(X0)) = X0),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).
% 0.22/0.55  fof(f116,plain,(
% 0.22/0.55    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) )),
% 0.22/0.55    inference(resolution,[],[f114,f95])).
% 0.22/0.55  fof(f95,plain,(
% 0.22/0.55    ( ! [X2,X1] : (~r2_hidden(X1,k1_zfmisc_1(X2)) | r1_tarski(X1,X2)) )),
% 0.22/0.55    inference(resolution,[],[f76,f67])).
% 0.22/0.55  fof(f67,plain,(
% 0.22/0.55    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f30])).
% 0.22/0.55  fof(f30,plain,(
% 0.22/0.55    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.22/0.55    inference(ennf_transformation,[],[f18])).
% 0.22/0.55  % (2129)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.55  fof(f18,axiom,(
% 0.22/0.55    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 0.22/0.55  % (2130)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.55  fof(f76,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f46])).
% 0.22/0.55  fof(f46,plain,(
% 0.22/0.55    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.55    inference(nnf_transformation,[],[f20])).
% 0.22/0.55  fof(f20,axiom,(
% 0.22/0.55    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.55  fof(f114,plain,(
% 0.22/0.55    ( ! [X2,X3] : (r2_hidden(X2,k1_zfmisc_1(k3_tarski(X3))) | ~r2_hidden(X2,X3)) )),
% 0.22/0.55    inference(resolution,[],[f71,f57])).
% 0.22/0.55  fof(f57,plain,(
% 0.22/0.55    ( ! [X0] : (r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0)))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f12])).
% 0.22/0.55  fof(f12,axiom,(
% 0.22/0.55    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0)))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_zfmisc_1)).
% 0.22/0.55  fof(f71,plain,(
% 0.22/0.55    ( ! [X0,X3,X1] : (~r1_tarski(X0,X1) | ~r2_hidden(X3,X0) | r2_hidden(X3,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f44])).
% 0.22/0.55  fof(f44,plain,(
% 0.22/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f42,f43])).
% 0.22/0.55  % (2126)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.55  fof(f43,plain,(
% 0.22/0.55    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f42,plain,(
% 0.22/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.55    inference(rectify,[],[f41])).
% 0.22/0.55  fof(f41,plain,(
% 0.22/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.55    inference(nnf_transformation,[],[f31])).
% 0.22/0.55  fof(f31,plain,(
% 0.22/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.55    inference(ennf_transformation,[],[f1])).
% 0.22/0.55  fof(f1,axiom,(
% 0.22/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.55  fof(f146,plain,(
% 0.22/0.55    ( ! [X8,X9] : (r1_tarski(X8,X9) | k1_tarski(X8) = k4_xboole_0(k1_tarski(X8),k1_zfmisc_1(X9))) )),
% 0.22/0.55    inference(resolution,[],[f79,f95])).
% 0.22/0.55  fof(f79,plain,(
% 0.22/0.55    ( ! [X0,X1] : (r2_hidden(X0,X1) | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f47])).
% 0.22/0.55  fof(f47,plain,(
% 0.22/0.55    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) & (~r2_hidden(X0,X1) | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)))),
% 0.22/0.55    inference(nnf_transformation,[],[f10])).
% 0.22/0.55  fof(f10,axiom,(
% 0.22/0.55    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <=> ~r2_hidden(X0,X1))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l33_zfmisc_1)).
% 0.22/0.55  fof(f75,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f45])).
% 0.22/0.55  fof(f45,plain,(
% 0.22/0.55    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.22/0.55    inference(nnf_transformation,[],[f4])).
% 0.22/0.55  fof(f4,axiom,(
% 0.22/0.55    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.22/0.55  % SZS output end Proof for theBenchmark
% 0.22/0.55  % (2109)------------------------------
% 0.22/0.55  % (2109)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (2109)Termination reason: Refutation
% 0.22/0.55  
% 0.22/0.55  % (2109)Memory used [KB]: 6652
% 0.22/0.55  % (2109)Time elapsed: 0.087 s
% 0.22/0.55  % (2109)------------------------------
% 0.22/0.55  % (2109)------------------------------
% 0.22/0.55  % (2116)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.55  % (2100)Success in time 0.188 s
%------------------------------------------------------------------------------
