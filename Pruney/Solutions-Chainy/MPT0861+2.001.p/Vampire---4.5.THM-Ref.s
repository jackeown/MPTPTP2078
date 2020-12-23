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
% DateTime   : Thu Dec  3 12:58:23 EST 2020

% Result     : Theorem 1.83s
% Output     : Refutation 1.83s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 233 expanded)
%              Number of leaves         :   14 (  67 expanded)
%              Depth                    :   14
%              Number of atoms          :  246 ( 581 expanded)
%              Number of equality atoms :   73 ( 273 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f138,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f83,f83,f134])).

fof(f134,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X2,X3) ) ),
    inference(subsumption_resolution,[],[f131,f91])).

fof(f91,plain,(
    sK1 != k1_mcart_1(sK0) ),
    inference(trivial_inequality_removal,[],[f90])).

fof(f90,plain,
    ( sK3 != sK3
    | sK1 != k1_mcart_1(sK0) ),
    inference(superposition,[],[f34,f87])).

fof(f87,plain,(
    sK3 = k2_mcart_1(sK0) ),
    inference(resolution,[],[f64,f63])).

fof(f63,plain,(
    r2_hidden(sK0,k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK2),k2_enumset1(sK3,sK3,sK3,sK3))) ),
    inference(definition_unfolding,[],[f33,f61,f62])).

fof(f62,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f36,f61])).

fof(f36,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

% (31340)Refutation not found, incomplete strategy% (31340)------------------------------
% (31340)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (31340)Termination reason: Refutation not found, incomplete strategy

% (31340)Memory used [KB]: 1663
% (31340)Time elapsed: 0.180 s
% (31340)------------------------------
% (31340)------------------------------
fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f61,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f37,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f37,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f33,plain,(
    r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),k1_tarski(sK3))) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ( sK3 != k2_mcart_1(sK0)
      | ( sK2 != k1_mcart_1(sK0)
        & sK1 != k1_mcart_1(sK0) ) )
    & r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),k1_tarski(sK3))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f22])).

fof(f22,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( k2_mcart_1(X0) != X3
          | ( k1_mcart_1(X0) != X2
            & k1_mcart_1(X0) != X1 ) )
        & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))) )
   => ( ( sK3 != k2_mcart_1(sK0)
        | ( sK2 != k1_mcart_1(sK0)
          & sK1 != k1_mcart_1(sK0) ) )
      & r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),k1_tarski(sK3))) ) ),
    introduced(choice_axiom,[])).

% (31325)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% (31334)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% (31325)Refutation not found, incomplete strategy% (31325)------------------------------
% (31325)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (31325)Termination reason: Refutation not found, incomplete strategy

% (31325)Memory used [KB]: 1663
% (31325)Time elapsed: 0.181 s
% (31325)------------------------------
% (31325)------------------------------
% (31321)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% (31331)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% (31327)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% (31336)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% (31337)Refutation not found, incomplete strategy% (31337)------------------------------
% (31337)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (31337)Termination reason: Refutation not found, incomplete strategy

% (31337)Memory used [KB]: 6140
% (31337)Time elapsed: 0.190 s
% (31337)------------------------------
% (31337)------------------------------
% (31321)Refutation not found, incomplete strategy% (31321)------------------------------
% (31321)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( ( k2_mcart_1(X0) != X3
        | ( k1_mcart_1(X0) != X2
          & k1_mcart_1(X0) != X1 ) )
      & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3)))
       => ( k2_mcart_1(X0) = X3
          & ( k1_mcart_1(X0) = X2
            | k1_mcart_1(X0) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3)))
     => ( k2_mcart_1(X0) = X3
        & ( k1_mcart_1(X0) = X2
          | k1_mcart_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_mcart_1)).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,k2_enumset1(X2,X2,X2,X2)))
      | k2_mcart_1(X0) = X2 ) ),
    inference(definition_unfolding,[],[f47,f62])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k2_mcart_1(X0) = X2
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k2_mcart_1(X0) = X2
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2)))
     => ( k2_mcart_1(X0) = X2
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_mcart_1)).

fof(f34,plain,
    ( sK3 != k2_mcart_1(sK0)
    | sK1 != k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f131,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,X1)
      | sK1 = k1_mcart_1(sK0)
      | ~ r2_hidden(X2,X3) ) ),
    inference(resolution,[],[f127,f102])).

fof(f102,plain,(
    ! [X10,X8,X11,X9] :
      ( ~ r2_hidden(X8,k2_enumset1(X9,X9,X9,X9))
      | X8 = X9
      | ~ r2_hidden(X10,X11) ) ),
    inference(forward_demodulation,[],[f98,f39])).

fof(f39,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f98,plain,(
    ! [X10,X8,X11,X9] :
      ( ~ r2_hidden(X8,k2_enumset1(X9,X9,X9,X9))
      | ~ r2_hidden(X10,X11)
      | k2_mcart_1(k4_tarski(X10,X8)) = X9 ) ),
    inference(resolution,[],[f79,f64])).

fof(f79,plain,(
    ! [X4,X2,X3,X1] :
      ( r2_hidden(k4_tarski(X3,X4),k2_zfmisc_1(X1,X2))
      | ~ r2_hidden(X4,X2)
      | ~ r2_hidden(X3,X1) ) ),
    inference(forward_demodulation,[],[f78,f38])).

fof(f38,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f78,plain,(
    ! [X4,X2,X3,X1] :
      ( ~ r2_hidden(X4,X2)
      | r2_hidden(k4_tarski(X3,X4),k2_zfmisc_1(X1,X2))
      | ~ r2_hidden(k1_mcart_1(k4_tarski(X3,X4)),X1) ) ),
    inference(forward_demodulation,[],[f74,f39])).

fof(f74,plain,(
    ! [X4,X2,X3,X1] :
      ( r2_hidden(k4_tarski(X3,X4),k2_zfmisc_1(X1,X2))
      | ~ r2_hidden(k2_mcart_1(k4_tarski(X3,X4)),X2)
      | ~ r2_hidden(k1_mcart_1(k4_tarski(X3,X4)),X1) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | k4_tarski(X3,X4) != X0
      | ~ r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | ! [X3,X4] : k4_tarski(X3,X4) != X0
      | ~ r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | ! [X3,X4] : k4_tarski(X3,X4) != X0
      | ~ r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
     => ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
        | ! [X3,X4] : k4_tarski(X3,X4) != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_mcart_1)).

fof(f127,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1,k2_enumset1(k1_mcart_1(sK0),k1_mcart_1(sK0),k1_mcart_1(sK0),k1_mcart_1(sK0)))
      | ~ r2_hidden(X0,X1) ) ),
    inference(subsumption_resolution,[],[f125,f92])).

fof(f92,plain,(
    sK2 != k1_mcart_1(sK0) ),
    inference(trivial_inequality_removal,[],[f89])).

fof(f89,plain,
    ( sK3 != sK3
    | sK2 != k1_mcart_1(sK0) ),
    inference(superposition,[],[f35,f87])).

fof(f35,plain,
    ( sK3 != k2_mcart_1(sK0)
    | sK2 != k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f125,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1,k2_enumset1(k1_mcart_1(sK0),k1_mcart_1(sK0),k1_mcart_1(sK0),k1_mcart_1(sK0)))
      | sK2 = k1_mcart_1(sK0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f122,f102])).

fof(f122,plain,(
    ! [X0] :
      ( r2_hidden(sK2,k2_enumset1(X0,X0,X0,k1_mcart_1(sK0)))
      | r2_hidden(sK1,k2_enumset1(X0,X0,X0,k1_mcart_1(sK0))) ) ),
    inference(resolution,[],[f111,f83])).

fof(f111,plain,(
    ! [X6] :
      ( ~ r2_hidden(k1_mcart_1(sK0),X6)
      | r2_hidden(sK2,X6)
      | r2_hidden(sK1,X6) ) ),
    inference(resolution,[],[f108,f81])).

fof(f81,plain,(
    r2_hidden(k1_mcart_1(sK0),k2_enumset1(sK1,sK1,sK1,sK2)) ),
    inference(resolution,[],[f44,f63])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f108,plain,(
    ! [X10,X8,X11,X9] :
      ( ~ r2_hidden(X11,k2_enumset1(X9,X9,X9,X10))
      | ~ r2_hidden(X11,X8)
      | r2_hidden(X10,X8)
      | r2_hidden(X9,X8) ) ),
    inference(superposition,[],[f76,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X2,k2_enumset1(X0,X0,X0,X1)) = X2
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f60,f61])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X2,k2_tarski(X0,X1)) = X2
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X2,k2_tarski(X0,X1)) = X2
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_zfmisc_1)).

fof(f76,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f28,f29])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f83,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_enumset1(X1,X1,X1,X0)) ),
    inference(resolution,[],[f69,f72])).

fof(f72,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_enumset1(X0,X0,X0,X1),X2)
      | r2_hidden(X1,X2) ) ),
    inference(definition_unfolding,[],[f58,f61])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:28:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.54  % (31326)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.54  % (31339)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.55  % (31318)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.55  % (31339)Refutation not found, incomplete strategy% (31339)------------------------------
% 0.20/0.55  % (31339)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (31322)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.55  % (31339)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (31339)Memory used [KB]: 10746
% 0.20/0.55  % (31339)Time elapsed: 0.084 s
% 0.20/0.55  % (31339)------------------------------
% 0.20/0.55  % (31339)------------------------------
% 0.20/0.56  % (31338)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.56  % (31330)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.56  % (31338)Refutation not found, incomplete strategy% (31338)------------------------------
% 0.20/0.56  % (31338)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (31315)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.56  % (31317)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.57  % (31319)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.57  % (31338)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.57  
% 0.20/0.57  % (31338)Memory used [KB]: 6140
% 0.20/0.57  % (31338)Time elapsed: 0.142 s
% 0.20/0.57  % (31338)------------------------------
% 0.20/0.57  % (31338)------------------------------
% 0.20/0.57  % (31333)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.57  % (31313)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.58  % (31316)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.58  % (31314)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.58  % (31312)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.58  % (31312)Refutation not found, incomplete strategy% (31312)------------------------------
% 0.20/0.58  % (31312)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.58  % (31312)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.58  
% 0.20/0.58  % (31312)Memory used [KB]: 1663
% 0.20/0.58  % (31312)Time elapsed: 0.157 s
% 0.20/0.58  % (31312)------------------------------
% 0.20/0.58  % (31312)------------------------------
% 0.20/0.59  % (31311)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.59  % (31324)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.59  % (31337)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.60  % (31332)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.60  % (31329)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.83/0.60  % (31329)Refutation not found, incomplete strategy% (31329)------------------------------
% 1.83/0.60  % (31329)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.83/0.60  % (31329)Termination reason: Refutation not found, incomplete strategy
% 1.83/0.60  
% 1.83/0.60  % (31329)Memory used [KB]: 1663
% 1.83/0.60  % (31329)Time elapsed: 0.180 s
% 1.83/0.60  % (31329)------------------------------
% 1.83/0.60  % (31329)------------------------------
% 1.83/0.60  % (31340)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.83/0.60  % (31333)Refutation found. Thanks to Tanya!
% 1.83/0.60  % SZS status Theorem for theBenchmark
% 1.83/0.60  % SZS output start Proof for theBenchmark
% 1.83/0.60  fof(f138,plain,(
% 1.83/0.60    $false),
% 1.83/0.60    inference(unit_resulting_resolution,[],[f83,f83,f134])).
% 1.83/0.60  fof(f134,plain,(
% 1.83/0.60    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,X1) | ~r2_hidden(X2,X3)) )),
% 1.83/0.60    inference(subsumption_resolution,[],[f131,f91])).
% 1.83/0.60  fof(f91,plain,(
% 1.83/0.60    sK1 != k1_mcart_1(sK0)),
% 1.83/0.60    inference(trivial_inequality_removal,[],[f90])).
% 1.83/0.60  fof(f90,plain,(
% 1.83/0.60    sK3 != sK3 | sK1 != k1_mcart_1(sK0)),
% 1.83/0.60    inference(superposition,[],[f34,f87])).
% 1.83/0.60  fof(f87,plain,(
% 1.83/0.60    sK3 = k2_mcart_1(sK0)),
% 1.83/0.60    inference(resolution,[],[f64,f63])).
% 1.83/0.60  fof(f63,plain,(
% 1.83/0.60    r2_hidden(sK0,k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK2),k2_enumset1(sK3,sK3,sK3,sK3)))),
% 1.83/0.60    inference(definition_unfolding,[],[f33,f61,f62])).
% 1.83/0.60  fof(f62,plain,(
% 1.83/0.60    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.83/0.60    inference(definition_unfolding,[],[f36,f61])).
% 1.83/0.60  fof(f36,plain,(
% 1.83/0.60    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.83/0.60    inference(cnf_transformation,[],[f3])).
% 1.83/0.60  % (31340)Refutation not found, incomplete strategy% (31340)------------------------------
% 1.83/0.60  % (31340)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.83/0.60  % (31340)Termination reason: Refutation not found, incomplete strategy
% 1.83/0.60  
% 1.83/0.60  % (31340)Memory used [KB]: 1663
% 1.83/0.60  % (31340)Time elapsed: 0.180 s
% 1.83/0.60  % (31340)------------------------------
% 1.83/0.60  % (31340)------------------------------
% 1.83/0.60  fof(f3,axiom,(
% 1.83/0.60    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.83/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.83/0.60  fof(f61,plain,(
% 1.83/0.60    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.83/0.60    inference(definition_unfolding,[],[f37,f43])).
% 1.83/0.60  fof(f43,plain,(
% 1.83/0.60    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.83/0.60    inference(cnf_transformation,[],[f5])).
% 1.83/0.60  fof(f5,axiom,(
% 1.83/0.60    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.83/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.83/0.60  fof(f37,plain,(
% 1.83/0.60    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.83/0.60    inference(cnf_transformation,[],[f4])).
% 1.83/0.60  fof(f4,axiom,(
% 1.83/0.60    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.83/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.83/0.60  fof(f33,plain,(
% 1.83/0.60    r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),k1_tarski(sK3)))),
% 1.83/0.60    inference(cnf_transformation,[],[f23])).
% 1.83/0.60  fof(f23,plain,(
% 1.83/0.60    (sK3 != k2_mcart_1(sK0) | (sK2 != k1_mcart_1(sK0) & sK1 != k1_mcart_1(sK0))) & r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),k1_tarski(sK3)))),
% 1.83/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f22])).
% 1.83/0.60  fof(f22,plain,(
% 1.83/0.60    ? [X0,X1,X2,X3] : ((k2_mcart_1(X0) != X3 | (k1_mcart_1(X0) != X2 & k1_mcart_1(X0) != X1)) & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3)))) => ((sK3 != k2_mcart_1(sK0) | (sK2 != k1_mcart_1(sK0) & sK1 != k1_mcart_1(sK0))) & r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),k1_tarski(sK3))))),
% 1.83/0.60    introduced(choice_axiom,[])).
% 1.83/0.60  % (31325)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.83/0.60  % (31334)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.83/0.60  % (31325)Refutation not found, incomplete strategy% (31325)------------------------------
% 1.83/0.60  % (31325)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.83/0.60  % (31325)Termination reason: Refutation not found, incomplete strategy
% 1.83/0.60  
% 1.83/0.60  % (31325)Memory used [KB]: 1663
% 1.83/0.60  % (31325)Time elapsed: 0.181 s
% 1.83/0.60  % (31325)------------------------------
% 1.83/0.60  % (31325)------------------------------
% 1.83/0.60  % (31321)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.83/0.61  % (31331)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.83/0.61  % (31327)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.83/0.61  % (31336)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.83/0.61  % (31337)Refutation not found, incomplete strategy% (31337)------------------------------
% 1.83/0.61  % (31337)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.83/0.61  % (31337)Termination reason: Refutation not found, incomplete strategy
% 1.83/0.61  
% 1.83/0.61  % (31337)Memory used [KB]: 6140
% 1.83/0.61  % (31337)Time elapsed: 0.190 s
% 1.83/0.61  % (31337)------------------------------
% 1.83/0.61  % (31337)------------------------------
% 1.83/0.61  % (31321)Refutation not found, incomplete strategy% (31321)------------------------------
% 1.83/0.61  % (31321)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.83/0.61  fof(f15,plain,(
% 1.83/0.61    ? [X0,X1,X2,X3] : ((k2_mcart_1(X0) != X3 | (k1_mcart_1(X0) != X2 & k1_mcart_1(X0) != X1)) & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))))),
% 1.83/0.61    inference(ennf_transformation,[],[f14])).
% 1.83/0.61  fof(f14,negated_conjecture,(
% 1.83/0.61    ~! [X0,X1,X2,X3] : (r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))) => (k2_mcart_1(X0) = X3 & (k1_mcart_1(X0) = X2 | k1_mcart_1(X0) = X1)))),
% 1.83/0.61    inference(negated_conjecture,[],[f13])).
% 1.83/0.61  fof(f13,conjecture,(
% 1.83/0.61    ! [X0,X1,X2,X3] : (r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))) => (k2_mcart_1(X0) = X3 & (k1_mcart_1(X0) = X2 | k1_mcart_1(X0) = X1)))),
% 1.83/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_mcart_1)).
% 1.83/0.62  fof(f64,plain,(
% 1.83/0.62    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,k2_enumset1(X2,X2,X2,X2))) | k2_mcart_1(X0) = X2) )),
% 1.83/0.62    inference(definition_unfolding,[],[f47,f62])).
% 1.83/0.62  fof(f47,plain,(
% 1.83/0.62    ( ! [X2,X0,X1] : (k2_mcart_1(X0) = X2 | ~r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2)))) )),
% 1.83/0.62    inference(cnf_transformation,[],[f17])).
% 1.83/0.62  fof(f17,plain,(
% 1.83/0.62    ! [X0,X1,X2] : ((k2_mcart_1(X0) = X2 & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2))))),
% 1.83/0.62    inference(ennf_transformation,[],[f11])).
% 1.83/0.62  fof(f11,axiom,(
% 1.83/0.62    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2))) => (k2_mcart_1(X0) = X2 & r2_hidden(k1_mcart_1(X0),X1)))),
% 1.83/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_mcart_1)).
% 1.83/0.62  fof(f34,plain,(
% 1.83/0.62    sK3 != k2_mcart_1(sK0) | sK1 != k1_mcart_1(sK0)),
% 1.83/0.62    inference(cnf_transformation,[],[f23])).
% 1.83/0.62  fof(f131,plain,(
% 1.83/0.62    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,X1) | sK1 = k1_mcart_1(sK0) | ~r2_hidden(X2,X3)) )),
% 1.83/0.62    inference(resolution,[],[f127,f102])).
% 1.83/0.62  fof(f102,plain,(
% 1.83/0.62    ( ! [X10,X8,X11,X9] : (~r2_hidden(X8,k2_enumset1(X9,X9,X9,X9)) | X8 = X9 | ~r2_hidden(X10,X11)) )),
% 1.83/0.62    inference(forward_demodulation,[],[f98,f39])).
% 1.83/0.62  fof(f39,plain,(
% 1.83/0.62    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 1.83/0.62    inference(cnf_transformation,[],[f12])).
% 1.83/0.62  fof(f12,axiom,(
% 1.83/0.62    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 1.83/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).
% 1.83/0.62  fof(f98,plain,(
% 1.83/0.62    ( ! [X10,X8,X11,X9] : (~r2_hidden(X8,k2_enumset1(X9,X9,X9,X9)) | ~r2_hidden(X10,X11) | k2_mcart_1(k4_tarski(X10,X8)) = X9) )),
% 1.83/0.62    inference(resolution,[],[f79,f64])).
% 1.83/0.62  fof(f79,plain,(
% 1.83/0.62    ( ! [X4,X2,X3,X1] : (r2_hidden(k4_tarski(X3,X4),k2_zfmisc_1(X1,X2)) | ~r2_hidden(X4,X2) | ~r2_hidden(X3,X1)) )),
% 1.83/0.62    inference(forward_demodulation,[],[f78,f38])).
% 1.83/0.62  fof(f38,plain,(
% 1.83/0.62    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 1.83/0.62    inference(cnf_transformation,[],[f12])).
% 1.83/0.62  fof(f78,plain,(
% 1.83/0.62    ( ! [X4,X2,X3,X1] : (~r2_hidden(X4,X2) | r2_hidden(k4_tarski(X3,X4),k2_zfmisc_1(X1,X2)) | ~r2_hidden(k1_mcart_1(k4_tarski(X3,X4)),X1)) )),
% 1.83/0.62    inference(forward_demodulation,[],[f74,f39])).
% 1.83/0.62  fof(f74,plain,(
% 1.83/0.62    ( ! [X4,X2,X3,X1] : (r2_hidden(k4_tarski(X3,X4),k2_zfmisc_1(X1,X2)) | ~r2_hidden(k2_mcart_1(k4_tarski(X3,X4)),X2) | ~r2_hidden(k1_mcart_1(k4_tarski(X3,X4)),X1)) )),
% 1.83/0.62    inference(equality_resolution,[],[f50])).
% 1.83/0.62  fof(f50,plain,(
% 1.83/0.62    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) | k4_tarski(X3,X4) != X0 | ~r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(k1_mcart_1(X0),X1)) )),
% 1.83/0.62    inference(cnf_transformation,[],[f20])).
% 1.83/0.62  fof(f20,plain,(
% 1.83/0.62    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) | ! [X3,X4] : k4_tarski(X3,X4) != X0 | ~r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(k1_mcart_1(X0),X1))),
% 1.83/0.62    inference(flattening,[],[f19])).
% 1.83/0.62  fof(f19,plain,(
% 1.83/0.62    ! [X0,X1,X2] : ((r2_hidden(X0,k2_zfmisc_1(X1,X2)) | ! [X3,X4] : k4_tarski(X3,X4) != X0) | (~r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(k1_mcart_1(X0),X1)))),
% 1.83/0.62    inference(ennf_transformation,[],[f9])).
% 1.83/0.62  fof(f9,axiom,(
% 1.83/0.62    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) => (r2_hidden(X0,k2_zfmisc_1(X1,X2)) | ! [X3,X4] : k4_tarski(X3,X4) != X0))),
% 1.83/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_mcart_1)).
% 1.83/0.62  fof(f127,plain,(
% 1.83/0.62    ( ! [X0,X1] : (r2_hidden(sK1,k2_enumset1(k1_mcart_1(sK0),k1_mcart_1(sK0),k1_mcart_1(sK0),k1_mcart_1(sK0))) | ~r2_hidden(X0,X1)) )),
% 1.83/0.62    inference(subsumption_resolution,[],[f125,f92])).
% 1.83/0.62  fof(f92,plain,(
% 1.83/0.62    sK2 != k1_mcart_1(sK0)),
% 1.83/0.62    inference(trivial_inequality_removal,[],[f89])).
% 1.83/0.62  fof(f89,plain,(
% 1.83/0.62    sK3 != sK3 | sK2 != k1_mcart_1(sK0)),
% 1.83/0.62    inference(superposition,[],[f35,f87])).
% 1.83/0.62  fof(f35,plain,(
% 1.83/0.62    sK3 != k2_mcart_1(sK0) | sK2 != k1_mcart_1(sK0)),
% 1.83/0.62    inference(cnf_transformation,[],[f23])).
% 1.83/0.62  fof(f125,plain,(
% 1.83/0.62    ( ! [X0,X1] : (r2_hidden(sK1,k2_enumset1(k1_mcart_1(sK0),k1_mcart_1(sK0),k1_mcart_1(sK0),k1_mcart_1(sK0))) | sK2 = k1_mcart_1(sK0) | ~r2_hidden(X0,X1)) )),
% 1.83/0.62    inference(resolution,[],[f122,f102])).
% 1.83/0.62  fof(f122,plain,(
% 1.83/0.62    ( ! [X0] : (r2_hidden(sK2,k2_enumset1(X0,X0,X0,k1_mcart_1(sK0))) | r2_hidden(sK1,k2_enumset1(X0,X0,X0,k1_mcart_1(sK0)))) )),
% 1.83/0.62    inference(resolution,[],[f111,f83])).
% 1.83/0.62  fof(f111,plain,(
% 1.83/0.62    ( ! [X6] : (~r2_hidden(k1_mcart_1(sK0),X6) | r2_hidden(sK2,X6) | r2_hidden(sK1,X6)) )),
% 1.83/0.62    inference(resolution,[],[f108,f81])).
% 1.83/0.62  fof(f81,plain,(
% 1.83/0.62    r2_hidden(k1_mcart_1(sK0),k2_enumset1(sK1,sK1,sK1,sK2))),
% 1.83/0.62    inference(resolution,[],[f44,f63])).
% 1.83/0.62  fof(f44,plain,(
% 1.83/0.62    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 1.83/0.62    inference(cnf_transformation,[],[f16])).
% 1.83/0.62  fof(f16,plain,(
% 1.83/0.62    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 1.83/0.62    inference(ennf_transformation,[],[f8])).
% 1.83/0.62  fof(f8,axiom,(
% 1.83/0.62    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 1.83/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).
% 1.83/0.62  fof(f108,plain,(
% 1.83/0.62    ( ! [X10,X8,X11,X9] : (~r2_hidden(X11,k2_enumset1(X9,X9,X9,X10)) | ~r2_hidden(X11,X8) | r2_hidden(X10,X8) | r2_hidden(X9,X8)) )),
% 1.83/0.62    inference(superposition,[],[f76,f71])).
% 1.83/0.62  fof(f71,plain,(
% 1.83/0.62    ( ! [X2,X0,X1] : (k4_xboole_0(X2,k2_enumset1(X0,X0,X0,X1)) = X2 | r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 1.83/0.62    inference(definition_unfolding,[],[f60,f61])).
% 1.83/0.62  fof(f60,plain,(
% 1.83/0.62    ( ! [X2,X0,X1] : (k4_xboole_0(X2,k2_tarski(X0,X1)) = X2 | r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 1.83/0.62    inference(cnf_transformation,[],[f21])).
% 1.83/0.62  fof(f21,plain,(
% 1.83/0.62    ! [X0,X1,X2] : (k4_xboole_0(X2,k2_tarski(X0,X1)) = X2 | r2_hidden(X1,X2) | r2_hidden(X0,X2))),
% 1.83/0.62    inference(ennf_transformation,[],[f6])).
% 1.83/0.62  fof(f6,axiom,(
% 1.83/0.62    ! [X0,X1,X2] : ~(k4_xboole_0(X2,k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 1.83/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_zfmisc_1)).
% 1.83/0.62  fof(f76,plain,(
% 1.83/0.62    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 1.83/0.62    inference(equality_resolution,[],[f52])).
% 1.83/0.62  fof(f52,plain,(
% 1.83/0.62    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.83/0.62    inference(cnf_transformation,[],[f30])).
% 1.83/0.62  fof(f30,plain,(
% 1.83/0.62    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.83/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f28,f29])).
% 1.83/0.62  fof(f29,plain,(
% 1.83/0.62    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 1.83/0.62    introduced(choice_axiom,[])).
% 1.83/0.62  fof(f28,plain,(
% 1.83/0.62    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.83/0.62    inference(rectify,[],[f27])).
% 1.83/0.62  fof(f27,plain,(
% 1.83/0.62    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.83/0.62    inference(flattening,[],[f26])).
% 1.83/0.62  fof(f26,plain,(
% 1.83/0.62    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.83/0.62    inference(nnf_transformation,[],[f1])).
% 1.83/0.62  fof(f1,axiom,(
% 1.83/0.62    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.83/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.83/0.62  fof(f83,plain,(
% 1.83/0.62    ( ! [X0,X1] : (r2_hidden(X0,k2_enumset1(X1,X1,X1,X0))) )),
% 1.83/0.62    inference(resolution,[],[f69,f72])).
% 1.83/0.62  fof(f72,plain,(
% 1.83/0.62    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.83/0.62    inference(equality_resolution,[],[f41])).
% 1.83/0.62  fof(f41,plain,(
% 1.83/0.62    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.83/0.62    inference(cnf_transformation,[],[f25])).
% 1.83/0.62  fof(f25,plain,(
% 1.83/0.62    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.83/0.62    inference(flattening,[],[f24])).
% 1.83/0.62  fof(f24,plain,(
% 1.83/0.62    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.83/0.62    inference(nnf_transformation,[],[f2])).
% 1.83/0.62  fof(f2,axiom,(
% 1.83/0.62    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.83/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.83/0.62  fof(f69,plain,(
% 1.83/0.62    ( ! [X2,X0,X1] : (~r1_tarski(k2_enumset1(X0,X0,X0,X1),X2) | r2_hidden(X1,X2)) )),
% 1.83/0.62    inference(definition_unfolding,[],[f58,f61])).
% 1.83/0.62  fof(f58,plain,(
% 1.83/0.62    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 1.83/0.62    inference(cnf_transformation,[],[f32])).
% 1.83/0.62  fof(f32,plain,(
% 1.83/0.62    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.83/0.62    inference(flattening,[],[f31])).
% 1.83/0.62  fof(f31,plain,(
% 1.83/0.62    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.83/0.62    inference(nnf_transformation,[],[f7])).
% 1.83/0.62  fof(f7,axiom,(
% 1.83/0.62    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.83/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 1.83/0.62  % SZS output end Proof for theBenchmark
% 1.83/0.62  % (31333)------------------------------
% 1.83/0.62  % (31333)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.83/0.62  % (31333)Termination reason: Refutation
% 1.83/0.62  
% 1.83/0.62  % (31333)Memory used [KB]: 6268
% 1.83/0.62  % (31333)Time elapsed: 0.188 s
% 1.83/0.62  % (31333)------------------------------
% 1.83/0.62  % (31333)------------------------------
% 1.99/0.62  % (31310)Success in time 0.258 s
%------------------------------------------------------------------------------
