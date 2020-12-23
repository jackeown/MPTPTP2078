%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:35 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 160 expanded)
%              Number of leaves         :   14 (  49 expanded)
%              Depth                    :   15
%              Number of atoms          :  175 ( 542 expanded)
%              Number of equality atoms :  124 ( 370 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f132,plain,(
    $false ),
    inference(resolution,[],[f127,f59])).

% (20088)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
fof(f59,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f28,f29])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f127,plain,(
    ! [X5] : ~ r2_hidden(sK0,k1_tarski(X5)) ),
    inference(subsumption_resolution,[],[f126,f60])).

fof(f60,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f126,plain,(
    ! [X5] :
      ( ~ r2_hidden(sK0,k1_tarski(X5))
      | sK0 != X5 ) ),
    inference(backward_demodulation,[],[f117,f122])).

fof(f122,plain,(
    sK0 = sK1 ),
    inference(trivial_inequality_removal,[],[f121])).

fof(f121,plain,
    ( sK0 != sK0
    | sK0 = sK1 ),
    inference(superposition,[],[f119,f65])).

fof(f65,plain,
    ( sK0 = sK2
    | sK0 = sK1 ),
    inference(superposition,[],[f64,f63])).

fof(f63,plain,
    ( sK0 = k2_mcart_1(sK0)
    | sK0 = sK1 ),
    inference(backward_demodulation,[],[f33,f62])).

fof(f62,plain,(
    k1_mcart_1(sK0) = sK1 ),
    inference(superposition,[],[f45,f32])).

fof(f32,plain,(
    sK0 = k4_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ( sK0 = k2_mcart_1(sK0)
      | sK0 = k1_mcart_1(sK0) )
    & sK0 = k4_tarski(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f23,f22])).

fof(f22,plain,
    ( ? [X0] :
        ( ( k2_mcart_1(X0) = X0
          | k1_mcart_1(X0) = X0 )
        & ? [X1,X2] : k4_tarski(X1,X2) = X0 )
   => ( ( sK0 = k2_mcart_1(sK0)
        | sK0 = k1_mcart_1(sK0) )
      & ? [X2,X1] : k4_tarski(X1,X2) = sK0 ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X2,X1] : k4_tarski(X1,X2) = sK0
   => sK0 = k4_tarski(sK1,sK2) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0] :
      ( ( k2_mcart_1(X0) = X0
        | k1_mcart_1(X0) = X0 )
      & ? [X1,X2] : k4_tarski(X1,X2) = X0 ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ? [X1,X2] : k4_tarski(X1,X2) = X0
       => ( k2_mcart_1(X0) != X0
          & k1_mcart_1(X0) != X0 ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

fof(f45,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f33,plain,
    ( sK0 = k2_mcart_1(sK0)
    | sK0 = k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f64,plain,(
    k2_mcart_1(sK0) = sK2 ),
    inference(superposition,[],[f46,f32])).

fof(f46,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f16])).

fof(f119,plain,(
    sK0 != sK2 ),
    inference(resolution,[],[f115,f59])).

fof(f115,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK2,k1_tarski(X1))
      | sK0 != X1 ) ),
    inference(subsumption_resolution,[],[f111,f90])).

fof(f90,plain,(
    ! [X1] : k1_xboole_0 != k1_tarski(X1) ),
    inference(backward_demodulation,[],[f61,f89])).

fof(f89,plain,(
    ! [X6] : k1_xboole_0 = k4_xboole_0(k1_tarski(X6),k1_tarski(X6)) ),
    inference(forward_demodulation,[],[f85,f86])).

fof(f86,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f81,f38])).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f81,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k5_xboole_0(X0,X0) ),
    inference(superposition,[],[f44,f39])).

fof(f39,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f44,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f85,plain,(
    ! [X6] : k4_xboole_0(k1_tarski(X6),k1_tarski(X6)) = k5_xboole_0(k1_tarski(X6),k1_tarski(X6)) ),
    inference(superposition,[],[f44,f78])).

fof(f78,plain,(
    ! [X0] : k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X0)) ),
    inference(superposition,[],[f43,f34])).

fof(f34,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f43,plain,(
    ! [X0,X1] : k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_zfmisc_1)).

fof(f61,plain,(
    ! [X1] : k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 )
      & ( X0 != X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f111,plain,(
    ! [X1] :
      ( sK0 != X1
      | ~ r2_hidden(sK2,k1_tarski(X1))
      | k1_xboole_0 = k1_tarski(X1) ) ),
    inference(duplicate_literal_removal,[],[f102])).

fof(f102,plain,(
    ! [X1] :
      ( sK0 != X1
      | ~ r2_hidden(sK2,k1_tarski(X1))
      | k1_xboole_0 = k1_tarski(X1)
      | k1_xboole_0 = k1_tarski(X1) ) ),
    inference(superposition,[],[f93,f71])).

fof(f71,plain,(
    ! [X1] :
      ( sK3(k1_tarski(X1)) = X1
      | k1_xboole_0 = k1_tarski(X1) ) ),
    inference(resolution,[],[f60,f35])).

fof(f35,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( ! [X2,X3] :
            ( k4_tarski(X2,X3) != sK3(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK3(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f25])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] :
            ( k4_tarski(X2,X3) != sK3(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK3(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3] :
                  ~ ( k4_tarski(X2,X3) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

fof(f93,plain,(
    ! [X0] :
      ( sK0 != sK3(X0)
      | ~ r2_hidden(sK2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f37,f32])).

fof(f37,plain,(
    ! [X2,X0,X3] :
      ( k4_tarski(X2,X3) != sK3(X0)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f117,plain,(
    ! [X5] :
      ( sK0 != X5
      | ~ r2_hidden(sK1,k1_tarski(X5)) ) ),
    inference(subsumption_resolution,[],[f109,f90])).

fof(f109,plain,(
    ! [X5] :
      ( sK0 != X5
      | ~ r2_hidden(sK1,k1_tarski(X5))
      | k1_xboole_0 = k1_tarski(X5) ) ),
    inference(duplicate_literal_removal,[],[f104])).

fof(f104,plain,(
    ! [X5] :
      ( sK0 != X5
      | ~ r2_hidden(sK1,k1_tarski(X5))
      | k1_xboole_0 = k1_tarski(X5)
      | k1_xboole_0 = k1_tarski(X5) ) ),
    inference(superposition,[],[f91,f71])).

fof(f91,plain,(
    ! [X0] :
      ( sK0 != sK3(X0)
      | ~ r2_hidden(sK1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f36,f32])).

fof(f36,plain,(
    ! [X2,X0,X3] :
      ( k4_tarski(X2,X3) != sK3(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:44:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.56  % (20089)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.56  % (20089)Refutation not found, incomplete strategy% (20089)------------------------------
% 0.22/0.56  % (20089)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (20098)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.57  % (20089)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (20089)Memory used [KB]: 1663
% 0.22/0.57  % (20089)Time elapsed: 0.126 s
% 0.22/0.57  % (20089)------------------------------
% 0.22/0.57  % (20089)------------------------------
% 0.22/0.57  % (20113)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.57  % (20113)Refutation not found, incomplete strategy% (20113)------------------------------
% 0.22/0.57  % (20113)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (20105)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.57  % (20105)Refutation not found, incomplete strategy% (20105)------------------------------
% 0.22/0.57  % (20105)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (20113)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (20113)Memory used [KB]: 6268
% 0.22/0.57  % (20113)Time elapsed: 0.141 s
% 0.22/0.57  % (20113)------------------------------
% 0.22/0.57  % (20113)------------------------------
% 0.22/0.57  % (20106)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.57  % (20105)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (20105)Memory used [KB]: 1791
% 0.22/0.57  % (20105)Time elapsed: 0.141 s
% 0.22/0.57  % (20105)------------------------------
% 0.22/0.57  % (20105)------------------------------
% 0.22/0.57  % (20106)Refutation not found, incomplete strategy% (20106)------------------------------
% 0.22/0.57  % (20106)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (20106)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (20106)Memory used [KB]: 1663
% 0.22/0.57  % (20106)Time elapsed: 0.137 s
% 0.22/0.57  % (20106)------------------------------
% 0.22/0.57  % (20106)------------------------------
% 0.22/0.57  % (20093)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.57  % (20097)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.58  % (20097)Refutation found. Thanks to Tanya!
% 0.22/0.58  % SZS status Theorem for theBenchmark
% 0.22/0.58  % SZS output start Proof for theBenchmark
% 0.22/0.58  fof(f132,plain,(
% 0.22/0.58    $false),
% 0.22/0.58    inference(resolution,[],[f127,f59])).
% 0.22/0.58  % (20088)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.58  fof(f59,plain,(
% 0.22/0.58    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 0.22/0.58    inference(equality_resolution,[],[f58])).
% 0.22/0.58  fof(f58,plain,(
% 0.22/0.58    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 0.22/0.58    inference(equality_resolution,[],[f48])).
% 0.22/0.58  fof(f48,plain,(
% 0.22/0.58    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 0.22/0.58    inference(cnf_transformation,[],[f30])).
% 0.22/0.58  fof(f30,plain,(
% 0.22/0.58    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.22/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f28,f29])).
% 0.22/0.58  fof(f29,plain,(
% 0.22/0.58    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1))))),
% 0.22/0.58    introduced(choice_axiom,[])).
% 0.22/0.58  fof(f28,plain,(
% 0.22/0.58    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.22/0.58    inference(rectify,[],[f27])).
% 0.22/0.58  fof(f27,plain,(
% 0.22/0.58    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.22/0.58    inference(nnf_transformation,[],[f4])).
% 0.22/0.58  fof(f4,axiom,(
% 0.22/0.58    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 0.22/0.58  fof(f127,plain,(
% 0.22/0.58    ( ! [X5] : (~r2_hidden(sK0,k1_tarski(X5))) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f126,f60])).
% 0.22/0.58  fof(f60,plain,(
% 0.22/0.58    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 0.22/0.58    inference(equality_resolution,[],[f47])).
% 0.22/0.58  fof(f47,plain,(
% 0.22/0.58    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 0.22/0.58    inference(cnf_transformation,[],[f30])).
% 0.22/0.58  fof(f126,plain,(
% 0.22/0.58    ( ! [X5] : (~r2_hidden(sK0,k1_tarski(X5)) | sK0 != X5) )),
% 0.22/0.58    inference(backward_demodulation,[],[f117,f122])).
% 0.22/0.58  fof(f122,plain,(
% 0.22/0.58    sK0 = sK1),
% 0.22/0.58    inference(trivial_inequality_removal,[],[f121])).
% 0.22/0.58  fof(f121,plain,(
% 0.22/0.58    sK0 != sK0 | sK0 = sK1),
% 0.22/0.58    inference(superposition,[],[f119,f65])).
% 0.22/0.58  fof(f65,plain,(
% 0.22/0.58    sK0 = sK2 | sK0 = sK1),
% 0.22/0.58    inference(superposition,[],[f64,f63])).
% 0.22/0.58  fof(f63,plain,(
% 0.22/0.58    sK0 = k2_mcart_1(sK0) | sK0 = sK1),
% 0.22/0.58    inference(backward_demodulation,[],[f33,f62])).
% 0.22/0.58  fof(f62,plain,(
% 0.22/0.58    k1_mcart_1(sK0) = sK1),
% 0.22/0.58    inference(superposition,[],[f45,f32])).
% 0.22/0.58  fof(f32,plain,(
% 0.22/0.58    sK0 = k4_tarski(sK1,sK2)),
% 0.22/0.58    inference(cnf_transformation,[],[f24])).
% 0.22/0.58  fof(f24,plain,(
% 0.22/0.58    (sK0 = k2_mcart_1(sK0) | sK0 = k1_mcart_1(sK0)) & sK0 = k4_tarski(sK1,sK2)),
% 0.22/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f23,f22])).
% 0.22/0.58  fof(f22,plain,(
% 0.22/0.58    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0) => ((sK0 = k2_mcart_1(sK0) | sK0 = k1_mcart_1(sK0)) & ? [X2,X1] : k4_tarski(X1,X2) = sK0)),
% 0.22/0.58    introduced(choice_axiom,[])).
% 0.22/0.58  fof(f23,plain,(
% 0.22/0.58    ? [X2,X1] : k4_tarski(X1,X2) = sK0 => sK0 = k4_tarski(sK1,sK2)),
% 0.22/0.58    introduced(choice_axiom,[])).
% 0.22/0.58  fof(f20,plain,(
% 0.22/0.58    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0)),
% 0.22/0.58    inference(ennf_transformation,[],[f19])).
% 0.22/0.58  fof(f19,negated_conjecture,(
% 0.22/0.58    ~! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 0.22/0.58    inference(negated_conjecture,[],[f18])).
% 0.22/0.58  fof(f18,conjecture,(
% 0.22/0.58    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).
% 0.22/0.58  fof(f45,plain,(
% 0.22/0.58    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 0.22/0.58    inference(cnf_transformation,[],[f16])).
% 0.22/0.58  fof(f16,axiom,(
% 0.22/0.58    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).
% 0.22/0.58  fof(f33,plain,(
% 0.22/0.58    sK0 = k2_mcart_1(sK0) | sK0 = k1_mcart_1(sK0)),
% 0.22/0.58    inference(cnf_transformation,[],[f24])).
% 0.22/0.58  fof(f64,plain,(
% 0.22/0.58    k2_mcart_1(sK0) = sK2),
% 0.22/0.58    inference(superposition,[],[f46,f32])).
% 0.22/0.58  fof(f46,plain,(
% 0.22/0.58    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 0.22/0.58    inference(cnf_transformation,[],[f16])).
% 0.22/0.58  fof(f119,plain,(
% 0.22/0.58    sK0 != sK2),
% 0.22/0.58    inference(resolution,[],[f115,f59])).
% 0.22/0.58  fof(f115,plain,(
% 0.22/0.58    ( ! [X1] : (~r2_hidden(sK2,k1_tarski(X1)) | sK0 != X1) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f111,f90])).
% 0.22/0.58  fof(f90,plain,(
% 0.22/0.58    ( ! [X1] : (k1_xboole_0 != k1_tarski(X1)) )),
% 0.22/0.58    inference(backward_demodulation,[],[f61,f89])).
% 0.22/0.58  fof(f89,plain,(
% 0.22/0.58    ( ! [X6] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X6),k1_tarski(X6))) )),
% 0.22/0.58    inference(forward_demodulation,[],[f85,f86])).
% 0.22/0.58  fof(f86,plain,(
% 0.22/0.58    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.22/0.58    inference(forward_demodulation,[],[f81,f38])).
% 0.22/0.58  fof(f38,plain,(
% 0.22/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 0.22/0.58    inference(cnf_transformation,[],[f3])).
% 0.22/0.58  fof(f3,axiom,(
% 0.22/0.58    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 0.22/0.58  fof(f81,plain,(
% 0.22/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k5_xboole_0(X0,X0)) )),
% 0.22/0.58    inference(superposition,[],[f44,f39])).
% 0.22/0.58  fof(f39,plain,(
% 0.22/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 0.22/0.58    inference(cnf_transformation,[],[f2])).
% 0.22/0.58  fof(f2,axiom,(
% 0.22/0.58    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).
% 0.22/0.58  fof(f44,plain,(
% 0.22/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.58    inference(cnf_transformation,[],[f1])).
% 0.22/0.58  fof(f1,axiom,(
% 0.22/0.58    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.22/0.58  fof(f85,plain,(
% 0.22/0.58    ( ! [X6] : (k4_xboole_0(k1_tarski(X6),k1_tarski(X6)) = k5_xboole_0(k1_tarski(X6),k1_tarski(X6))) )),
% 0.22/0.58    inference(superposition,[],[f44,f78])).
% 0.22/0.58  fof(f78,plain,(
% 0.22/0.58    ( ! [X0] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X0))) )),
% 0.22/0.58    inference(superposition,[],[f43,f34])).
% 0.22/0.58  fof(f34,plain,(
% 0.22/0.58    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f5])).
% 0.22/0.58  fof(f5,axiom,(
% 0.22/0.58    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.58  fof(f43,plain,(
% 0.22/0.58    ( ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 0.22/0.58    inference(cnf_transformation,[],[f13])).
% 0.22/0.58  fof(f13,axiom,(
% 0.22/0.58    ! [X0,X1] : k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_zfmisc_1)).
% 0.22/0.58  fof(f61,plain,(
% 0.22/0.58    ( ! [X1] : (k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1))) )),
% 0.22/0.58    inference(equality_resolution,[],[f51])).
% 0.22/0.58  fof(f51,plain,(
% 0.22/0.58    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.22/0.58    inference(cnf_transformation,[],[f31])).
% 0.22/0.58  fof(f31,plain,(
% 0.22/0.58    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) & (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))),
% 0.22/0.58    inference(nnf_transformation,[],[f14])).
% 0.22/0.58  fof(f14,axiom,(
% 0.22/0.58    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 0.22/0.58  fof(f111,plain,(
% 0.22/0.58    ( ! [X1] : (sK0 != X1 | ~r2_hidden(sK2,k1_tarski(X1)) | k1_xboole_0 = k1_tarski(X1)) )),
% 0.22/0.58    inference(duplicate_literal_removal,[],[f102])).
% 0.22/0.58  fof(f102,plain,(
% 0.22/0.58    ( ! [X1] : (sK0 != X1 | ~r2_hidden(sK2,k1_tarski(X1)) | k1_xboole_0 = k1_tarski(X1) | k1_xboole_0 = k1_tarski(X1)) )),
% 0.22/0.58    inference(superposition,[],[f93,f71])).
% 0.22/0.58  fof(f71,plain,(
% 0.22/0.58    ( ! [X1] : (sK3(k1_tarski(X1)) = X1 | k1_xboole_0 = k1_tarski(X1)) )),
% 0.22/0.58    inference(resolution,[],[f60,f35])).
% 0.22/0.58  fof(f35,plain,(
% 0.22/0.58    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 0.22/0.58    inference(cnf_transformation,[],[f26])).
% 0.22/0.58  fof(f26,plain,(
% 0.22/0.58    ! [X0] : ((! [X2,X3] : (k4_tarski(X2,X3) != sK3(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK3(X0),X0)) | k1_xboole_0 = X0)),
% 0.22/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f25])).
% 0.22/0.58  fof(f25,plain,(
% 0.22/0.58    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X3,X2] : (k4_tarski(X2,X3) != sK3(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK3(X0),X0)))),
% 0.22/0.58    introduced(choice_axiom,[])).
% 0.22/0.58  fof(f21,plain,(
% 0.22/0.58    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.22/0.58    inference(ennf_transformation,[],[f17])).
% 0.22/0.58  fof(f17,axiom,(
% 0.22/0.58    ! [X0] : ~(! [X1] : ~(! [X2,X3] : ~(k4_tarski(X2,X3) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).
% 0.22/0.58  fof(f93,plain,(
% 0.22/0.58    ( ! [X0] : (sK0 != sK3(X0) | ~r2_hidden(sK2,X0) | k1_xboole_0 = X0) )),
% 0.22/0.58    inference(superposition,[],[f37,f32])).
% 0.22/0.58  fof(f37,plain,(
% 0.22/0.58    ( ! [X2,X0,X3] : (k4_tarski(X2,X3) != sK3(X0) | ~r2_hidden(X3,X0) | k1_xboole_0 = X0) )),
% 0.22/0.58    inference(cnf_transformation,[],[f26])).
% 0.22/0.58  fof(f117,plain,(
% 0.22/0.58    ( ! [X5] : (sK0 != X5 | ~r2_hidden(sK1,k1_tarski(X5))) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f109,f90])).
% 0.22/0.58  fof(f109,plain,(
% 0.22/0.58    ( ! [X5] : (sK0 != X5 | ~r2_hidden(sK1,k1_tarski(X5)) | k1_xboole_0 = k1_tarski(X5)) )),
% 0.22/0.58    inference(duplicate_literal_removal,[],[f104])).
% 0.22/0.58  fof(f104,plain,(
% 0.22/0.58    ( ! [X5] : (sK0 != X5 | ~r2_hidden(sK1,k1_tarski(X5)) | k1_xboole_0 = k1_tarski(X5) | k1_xboole_0 = k1_tarski(X5)) )),
% 0.22/0.58    inference(superposition,[],[f91,f71])).
% 0.22/0.58  fof(f91,plain,(
% 0.22/0.58    ( ! [X0] : (sK0 != sK3(X0) | ~r2_hidden(sK1,X0) | k1_xboole_0 = X0) )),
% 0.22/0.58    inference(superposition,[],[f36,f32])).
% 0.22/0.58  fof(f36,plain,(
% 0.22/0.58    ( ! [X2,X0,X3] : (k4_tarski(X2,X3) != sK3(X0) | ~r2_hidden(X2,X0) | k1_xboole_0 = X0) )),
% 0.22/0.58    inference(cnf_transformation,[],[f26])).
% 0.22/0.58  % SZS output end Proof for theBenchmark
% 0.22/0.58  % (20097)------------------------------
% 0.22/0.58  % (20097)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (20097)Termination reason: Refutation
% 0.22/0.58  
% 0.22/0.58  % (20097)Memory used [KB]: 1791
% 0.22/0.58  % (20097)Time elapsed: 0.151 s
% 0.22/0.58  % (20097)------------------------------
% 0.22/0.58  % (20097)------------------------------
% 0.22/0.59  % (20087)Success in time 0.21 s
%------------------------------------------------------------------------------
