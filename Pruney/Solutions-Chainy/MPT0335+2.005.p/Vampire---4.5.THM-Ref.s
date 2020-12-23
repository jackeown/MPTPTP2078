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
% DateTime   : Thu Dec  3 12:43:15 EST 2020

% Result     : Theorem 1.54s
% Output     : Refutation 1.54s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 223 expanded)
%              Number of leaves         :   10 (  60 expanded)
%              Depth                    :   21
%              Number of atoms          :  145 ( 652 expanded)
%              Number of equality atoms :   69 ( 340 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f702,plain,(
    $false ),
    inference(subsumption_resolution,[],[f700,f35])).

fof(f35,plain,(
    r2_hidden(sK3,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( k1_tarski(sK3) != k3_xboole_0(sK0,sK2)
    & r2_hidden(sK3,sK0)
    & k1_tarski(sK3) = k3_xboole_0(sK1,sK2)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f21])).

fof(f21,plain,
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

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_tarski(X3) != k3_xboole_0(X0,X2)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_tarski(X3) != k3_xboole_0(X0,X2)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r2_hidden(X3,X0)
          & k3_xboole_0(X1,X2) = k1_tarski(X3)
          & r1_tarski(X0,X1) )
       => k1_tarski(X3) = k3_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(X3,X0)
        & k3_xboole_0(X1,X2) = k1_tarski(X3)
        & r1_tarski(X0,X1) )
     => k1_tarski(X3) = k3_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_zfmisc_1)).

fof(f700,plain,(
    ~ r2_hidden(sK3,sK0) ),
    inference(backward_demodulation,[],[f683,f695])).

fof(f695,plain,(
    sK3 = sK4(k1_tarski(sK3),sK0) ),
    inference(resolution,[],[f682,f53])).

fof(f53,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK5(X0,X1) != X0
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( sK5(X0,X1) = X0
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f28,f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK5(X0,X1) != X0
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( sK5(X0,X1) = X0
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f27,plain,(
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

fof(f682,plain,(
    r2_hidden(sK4(k1_tarski(sK3),sK0),k1_tarski(sK3)) ),
    inference(resolution,[],[f680,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK4(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f680,plain,(
    ~ r1_tarski(k1_tarski(sK3),sK0) ),
    inference(subsumption_resolution,[],[f670,f36])).

fof(f36,plain,(
    k1_tarski(sK3) != k3_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f670,plain,
    ( k1_tarski(sK3) = k3_xboole_0(sK0,sK2)
    | ~ r1_tarski(k1_tarski(sK3),sK0) ),
    inference(superposition,[],[f660,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f660,plain,(
    k3_xboole_0(sK0,sK2) = k3_xboole_0(k1_tarski(sK3),sK0) ),
    inference(superposition,[],[f637,f88])).

fof(f88,plain,(
    ! [X1] : k3_xboole_0(k1_tarski(sK3),X1) = k3_xboole_0(sK1,k3_xboole_0(X1,sK2)) ),
    inference(superposition,[],[f64,f45])).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f64,plain,(
    ! [X0] : k3_xboole_0(sK1,k3_xboole_0(sK2,X0)) = k3_xboole_0(k1_tarski(sK3),X0) ),
    inference(superposition,[],[f44,f34])).

fof(f34,plain,(
    k1_tarski(sK3) = k3_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f44,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f637,plain,(
    k3_xboole_0(sK0,sK2) = k3_xboole_0(sK1,k3_xboole_0(sK0,sK2)) ),
    inference(superposition,[],[f446,f125])).

fof(f125,plain,(
    k3_xboole_0(sK0,sK2) = k3_xboole_0(sK0,k1_tarski(sK3)) ),
    inference(superposition,[],[f61,f34])).

fof(f61,plain,(
    ! [X0] : k3_xboole_0(sK0,k3_xboole_0(sK1,X0)) = k3_xboole_0(sK0,X0) ),
    inference(superposition,[],[f44,f56])).

fof(f56,plain,(
    sK0 = k3_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f33,f50])).

fof(f33,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f446,plain,(
    ! [X3] : k3_xboole_0(X3,k1_tarski(sK3)) = k3_xboole_0(sK1,k3_xboole_0(X3,k1_tarski(sK3))) ),
    inference(superposition,[],[f116,f45])).

fof(f116,plain,(
    ! [X0] : k3_xboole_0(k1_tarski(sK3),X0) = k3_xboole_0(sK1,k3_xboole_0(k1_tarski(sK3),X0)) ),
    inference(superposition,[],[f44,f111])).

fof(f111,plain,(
    k1_tarski(sK3) = k3_xboole_0(sK1,k1_tarski(sK3)) ),
    inference(forward_demodulation,[],[f108,f46])).

fof(f46,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f108,plain,(
    k3_xboole_0(k1_tarski(sK3),k1_tarski(sK3)) = k3_xboole_0(sK1,k1_tarski(sK3)) ),
    inference(superposition,[],[f64,f100])).

fof(f100,plain,(
    k1_tarski(sK3) = k3_xboole_0(sK2,k1_tarski(sK3)) ),
    inference(superposition,[],[f95,f45])).

fof(f95,plain,(
    k1_tarski(sK3) = k3_xboole_0(k1_tarski(sK3),sK2) ),
    inference(forward_demodulation,[],[f90,f34])).

fof(f90,plain,(
    k3_xboole_0(sK1,sK2) = k3_xboole_0(k1_tarski(sK3),sK2) ),
    inference(superposition,[],[f64,f46])).

fof(f683,plain,(
    ~ r2_hidden(sK4(k1_tarski(sK3),sK0),sK0) ),
    inference(resolution,[],[f680,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK4(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n020.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 19:16:37 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.50  % (17276)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (17296)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.52  % (17285)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.52  % (17288)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.52  % (17286)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (17274)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.53  % (17297)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.53  % (17277)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.53  % (17275)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.53  % (17278)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (17289)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.54  % (17292)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.54  % (17299)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.54  % (17281)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.54  % (17279)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.40/0.54  % (17287)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.40/0.55  % (17302)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.40/0.55  % (17291)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.40/0.55  % (17301)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.40/0.55  % (17284)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.40/0.55  % (17291)Refutation not found, incomplete strategy% (17291)------------------------------
% 1.40/0.55  % (17291)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.55  % (17291)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.55  
% 1.40/0.55  % (17291)Memory used [KB]: 10618
% 1.40/0.55  % (17291)Time elapsed: 0.140 s
% 1.40/0.55  % (17291)------------------------------
% 1.40/0.55  % (17291)------------------------------
% 1.40/0.55  % (17303)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.40/0.55  % (17298)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.40/0.55  % (17293)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.40/0.55  % (17283)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.40/0.55  % (17282)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.40/0.55  % (17300)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.40/0.56  % (17295)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.40/0.56  % (17290)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.54/0.57  % (17280)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.54/0.58  % (17294)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.54/0.59  % (17274)Refutation found. Thanks to Tanya!
% 1.54/0.59  % SZS status Theorem for theBenchmark
% 1.54/0.59  % SZS output start Proof for theBenchmark
% 1.54/0.59  fof(f702,plain,(
% 1.54/0.59    $false),
% 1.54/0.59    inference(subsumption_resolution,[],[f700,f35])).
% 1.54/0.59  fof(f35,plain,(
% 1.54/0.59    r2_hidden(sK3,sK0)),
% 1.54/0.59    inference(cnf_transformation,[],[f22])).
% 1.54/0.59  fof(f22,plain,(
% 1.54/0.59    k1_tarski(sK3) != k3_xboole_0(sK0,sK2) & r2_hidden(sK3,sK0) & k1_tarski(sK3) = k3_xboole_0(sK1,sK2) & r1_tarski(sK0,sK1)),
% 1.54/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f21])).
% 1.54/0.59  fof(f21,plain,(
% 1.54/0.59    ? [X0,X1,X2,X3] : (k1_tarski(X3) != k3_xboole_0(X0,X2) & r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => (k1_tarski(sK3) != k3_xboole_0(sK0,sK2) & r2_hidden(sK3,sK0) & k1_tarski(sK3) = k3_xboole_0(sK1,sK2) & r1_tarski(sK0,sK1))),
% 1.54/0.59    introduced(choice_axiom,[])).
% 1.54/0.59  fof(f18,plain,(
% 1.54/0.59    ? [X0,X1,X2,X3] : (k1_tarski(X3) != k3_xboole_0(X0,X2) & r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1))),
% 1.54/0.59    inference(flattening,[],[f17])).
% 1.54/0.59  fof(f17,plain,(
% 1.54/0.59    ? [X0,X1,X2,X3] : (k1_tarski(X3) != k3_xboole_0(X0,X2) & (r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)))),
% 1.54/0.59    inference(ennf_transformation,[],[f15])).
% 1.54/0.59  fof(f15,negated_conjecture,(
% 1.54/0.59    ~! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k1_tarski(X3) = k3_xboole_0(X0,X2))),
% 1.54/0.59    inference(negated_conjecture,[],[f14])).
% 1.54/0.59  fof(f14,conjecture,(
% 1.54/0.59    ! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k1_tarski(X3) = k3_xboole_0(X0,X2))),
% 1.54/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_zfmisc_1)).
% 1.54/0.59  fof(f700,plain,(
% 1.54/0.59    ~r2_hidden(sK3,sK0)),
% 1.54/0.59    inference(backward_demodulation,[],[f683,f695])).
% 1.54/0.59  fof(f695,plain,(
% 1.54/0.59    sK3 = sK4(k1_tarski(sK3),sK0)),
% 1.54/0.59    inference(resolution,[],[f682,f53])).
% 1.54/0.59  fof(f53,plain,(
% 1.54/0.59    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k1_tarski(X0))) )),
% 1.54/0.59    inference(equality_resolution,[],[f40])).
% 1.54/0.59  fof(f40,plain,(
% 1.54/0.59    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.54/0.59    inference(cnf_transformation,[],[f30])).
% 1.54/0.59  fof(f30,plain,(
% 1.54/0.59    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.54/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f28,f29])).
% 1.54/0.59  fof(f29,plain,(
% 1.54/0.59    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1))))),
% 1.54/0.59    introduced(choice_axiom,[])).
% 1.54/0.59  fof(f28,plain,(
% 1.54/0.59    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.54/0.59    inference(rectify,[],[f27])).
% 1.54/0.59  fof(f27,plain,(
% 1.54/0.59    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.54/0.59    inference(nnf_transformation,[],[f10])).
% 1.54/0.59  fof(f10,axiom,(
% 1.54/0.59    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.54/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 1.54/0.59  fof(f682,plain,(
% 1.54/0.59    r2_hidden(sK4(k1_tarski(sK3),sK0),k1_tarski(sK3))),
% 1.54/0.59    inference(resolution,[],[f680,f38])).
% 1.54/0.59  fof(f38,plain,(
% 1.54/0.59    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK4(X0,X1),X0)) )),
% 1.54/0.59    inference(cnf_transformation,[],[f26])).
% 1.54/0.59  fof(f26,plain,(
% 1.54/0.59    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.54/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f25])).
% 1.54/0.59  fof(f25,plain,(
% 1.54/0.59    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 1.54/0.59    introduced(choice_axiom,[])).
% 1.54/0.59  fof(f24,plain,(
% 1.54/0.59    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.54/0.59    inference(rectify,[],[f23])).
% 1.54/0.59  fof(f23,plain,(
% 1.54/0.59    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.54/0.59    inference(nnf_transformation,[],[f19])).
% 1.54/0.59  fof(f19,plain,(
% 1.54/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.54/0.59    inference(ennf_transformation,[],[f2])).
% 1.54/0.59  fof(f2,axiom,(
% 1.54/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.54/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.54/0.59  fof(f680,plain,(
% 1.54/0.59    ~r1_tarski(k1_tarski(sK3),sK0)),
% 1.54/0.59    inference(subsumption_resolution,[],[f670,f36])).
% 1.54/0.59  fof(f36,plain,(
% 1.54/0.59    k1_tarski(sK3) != k3_xboole_0(sK0,sK2)),
% 1.54/0.59    inference(cnf_transformation,[],[f22])).
% 1.54/0.59  fof(f670,plain,(
% 1.54/0.59    k1_tarski(sK3) = k3_xboole_0(sK0,sK2) | ~r1_tarski(k1_tarski(sK3),sK0)),
% 1.54/0.59    inference(superposition,[],[f660,f50])).
% 1.54/0.59  fof(f50,plain,(
% 1.54/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.54/0.59    inference(cnf_transformation,[],[f20])).
% 1.54/0.59  fof(f20,plain,(
% 1.54/0.59    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.54/0.59    inference(ennf_transformation,[],[f7])).
% 1.54/0.59  fof(f7,axiom,(
% 1.54/0.59    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.54/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.54/0.59  fof(f660,plain,(
% 1.54/0.59    k3_xboole_0(sK0,sK2) = k3_xboole_0(k1_tarski(sK3),sK0)),
% 1.54/0.59    inference(superposition,[],[f637,f88])).
% 1.54/0.59  fof(f88,plain,(
% 1.54/0.59    ( ! [X1] : (k3_xboole_0(k1_tarski(sK3),X1) = k3_xboole_0(sK1,k3_xboole_0(X1,sK2))) )),
% 1.54/0.59    inference(superposition,[],[f64,f45])).
% 1.54/0.59  fof(f45,plain,(
% 1.54/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.54/0.59    inference(cnf_transformation,[],[f1])).
% 1.54/0.59  fof(f1,axiom,(
% 1.54/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.54/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.54/0.59  fof(f64,plain,(
% 1.54/0.59    ( ! [X0] : (k3_xboole_0(sK1,k3_xboole_0(sK2,X0)) = k3_xboole_0(k1_tarski(sK3),X0)) )),
% 1.54/0.59    inference(superposition,[],[f44,f34])).
% 1.54/0.59  fof(f34,plain,(
% 1.54/0.59    k1_tarski(sK3) = k3_xboole_0(sK1,sK2)),
% 1.54/0.59    inference(cnf_transformation,[],[f22])).
% 1.54/0.59  fof(f44,plain,(
% 1.54/0.59    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 1.54/0.59    inference(cnf_transformation,[],[f6])).
% 1.54/0.59  fof(f6,axiom,(
% 1.54/0.59    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 1.54/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).
% 1.54/0.59  fof(f637,plain,(
% 1.54/0.59    k3_xboole_0(sK0,sK2) = k3_xboole_0(sK1,k3_xboole_0(sK0,sK2))),
% 1.54/0.59    inference(superposition,[],[f446,f125])).
% 1.54/0.59  fof(f125,plain,(
% 1.54/0.59    k3_xboole_0(sK0,sK2) = k3_xboole_0(sK0,k1_tarski(sK3))),
% 1.54/0.59    inference(superposition,[],[f61,f34])).
% 1.54/0.59  fof(f61,plain,(
% 1.54/0.59    ( ! [X0] : (k3_xboole_0(sK0,k3_xboole_0(sK1,X0)) = k3_xboole_0(sK0,X0)) )),
% 1.54/0.59    inference(superposition,[],[f44,f56])).
% 1.54/0.59  fof(f56,plain,(
% 1.54/0.59    sK0 = k3_xboole_0(sK0,sK1)),
% 1.54/0.59    inference(resolution,[],[f33,f50])).
% 1.54/0.59  fof(f33,plain,(
% 1.54/0.59    r1_tarski(sK0,sK1)),
% 1.54/0.59    inference(cnf_transformation,[],[f22])).
% 1.54/0.59  fof(f446,plain,(
% 1.54/0.59    ( ! [X3] : (k3_xboole_0(X3,k1_tarski(sK3)) = k3_xboole_0(sK1,k3_xboole_0(X3,k1_tarski(sK3)))) )),
% 1.54/0.59    inference(superposition,[],[f116,f45])).
% 1.54/0.59  fof(f116,plain,(
% 1.54/0.59    ( ! [X0] : (k3_xboole_0(k1_tarski(sK3),X0) = k3_xboole_0(sK1,k3_xboole_0(k1_tarski(sK3),X0))) )),
% 1.54/0.59    inference(superposition,[],[f44,f111])).
% 1.54/0.59  fof(f111,plain,(
% 1.54/0.59    k1_tarski(sK3) = k3_xboole_0(sK1,k1_tarski(sK3))),
% 1.54/0.59    inference(forward_demodulation,[],[f108,f46])).
% 1.54/0.59  fof(f46,plain,(
% 1.54/0.59    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.54/0.59    inference(cnf_transformation,[],[f16])).
% 1.54/0.59  fof(f16,plain,(
% 1.54/0.59    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.54/0.59    inference(rectify,[],[f4])).
% 1.54/0.59  fof(f4,axiom,(
% 1.54/0.59    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.54/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.54/0.59  fof(f108,plain,(
% 1.54/0.59    k3_xboole_0(k1_tarski(sK3),k1_tarski(sK3)) = k3_xboole_0(sK1,k1_tarski(sK3))),
% 1.54/0.59    inference(superposition,[],[f64,f100])).
% 1.54/0.59  fof(f100,plain,(
% 1.54/0.59    k1_tarski(sK3) = k3_xboole_0(sK2,k1_tarski(sK3))),
% 1.54/0.59    inference(superposition,[],[f95,f45])).
% 1.54/0.59  fof(f95,plain,(
% 1.54/0.59    k1_tarski(sK3) = k3_xboole_0(k1_tarski(sK3),sK2)),
% 1.54/0.59    inference(forward_demodulation,[],[f90,f34])).
% 1.54/0.59  fof(f90,plain,(
% 1.54/0.59    k3_xboole_0(sK1,sK2) = k3_xboole_0(k1_tarski(sK3),sK2)),
% 1.54/0.59    inference(superposition,[],[f64,f46])).
% 1.54/0.59  fof(f683,plain,(
% 1.54/0.59    ~r2_hidden(sK4(k1_tarski(sK3),sK0),sK0)),
% 1.54/0.59    inference(resolution,[],[f680,f39])).
% 1.54/0.59  fof(f39,plain,(
% 1.54/0.59    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK4(X0,X1),X1)) )),
% 1.54/0.59    inference(cnf_transformation,[],[f26])).
% 1.54/0.59  % SZS output end Proof for theBenchmark
% 1.54/0.59  % (17274)------------------------------
% 1.54/0.59  % (17274)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.59  % (17274)Termination reason: Refutation
% 1.54/0.59  
% 1.54/0.59  % (17274)Memory used [KB]: 2046
% 1.54/0.59  % (17274)Time elapsed: 0.154 s
% 1.54/0.59  % (17274)------------------------------
% 1.54/0.59  % (17274)------------------------------
% 1.54/0.59  % (17273)Success in time 0.224 s
%------------------------------------------------------------------------------
