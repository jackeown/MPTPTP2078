%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:35 EST 2020

% Result     : Theorem 1.32s
% Output     : Refutation 1.32s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 146 expanded)
%              Number of leaves         :   13 (  45 expanded)
%              Depth                    :   13
%              Number of atoms          :  170 ( 488 expanded)
%              Number of equality atoms :  121 ( 337 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f113,plain,(
    $false ),
    inference(subsumption_resolution,[],[f112,f100])).

fof(f100,plain,(
    sK0 != sK1 ),
    inference(resolution,[],[f94,f56])).

fof(f56,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f27,f28])).

fof(f28,plain,(
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

fof(f27,plain,(
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
    inference(rectify,[],[f26])).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f94,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK1,k1_tarski(X0))
      | sK0 != X0 ) ),
    inference(subsumption_resolution,[],[f93,f78])).

% (19962)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
fof(f78,plain,(
    ! [X1] : k1_xboole_0 != k1_tarski(X1) ),
    inference(backward_demodulation,[],[f58,f76])).

fof(f76,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f75,f33])).

fof(f33,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f75,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f43,f73])).

fof(f73,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f71,f34])).

fof(f34,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f71,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f42,f33])).

fof(f42,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f58,plain,(
    ! [X1] : k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 )
      & ( X0 != X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f93,plain,(
    ! [X0] :
      ( sK0 != X0
      | ~ r2_hidden(sK1,k1_tarski(X0))
      | k1_xboole_0 = k1_tarski(X0) ) ),
    inference(duplicate_literal_removal,[],[f92])).

fof(f92,plain,(
    ! [X0] :
      ( sK0 != X0
      | ~ r2_hidden(sK1,k1_tarski(X0))
      | k1_xboole_0 = k1_tarski(X0)
      | k1_xboole_0 = k1_tarski(X0) ) ),
    inference(superposition,[],[f87,f65])).

fof(f65,plain,(
    ! [X1] :
      ( sK3(k1_tarski(X1)) = X1
      | k1_xboole_0 = k1_tarski(X1) ) ),
    inference(resolution,[],[f57,f36])).

fof(f36,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( ! [X2,X3] :
            ( k4_tarski(X2,X3) != sK3(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK3(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f20,f24])).

% (19962)Refutation not found, incomplete strategy% (19962)------------------------------
% (19962)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (19962)Termination reason: Refutation not found, incomplete strategy

% (19962)Memory used [KB]: 1663
% (19962)Time elapsed: 0.002 s
% (19962)------------------------------
% (19962)------------------------------
fof(f24,plain,(
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

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3] :
                  ~ ( k4_tarski(X2,X3) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).

fof(f57,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f87,plain,(
    ! [X0] :
      ( sK0 != sK3(X0)
      | ~ r2_hidden(sK1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f37,f31])).

fof(f31,plain,(
    sK0 = k4_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ( sK0 = k2_mcart_1(sK0)
      | sK0 = k1_mcart_1(sK0) )
    & sK0 = k4_tarski(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f22,f21])).

fof(f21,plain,
    ( ? [X0] :
        ( ( k2_mcart_1(X0) = X0
          | k1_mcart_1(X0) = X0 )
        & ? [X1,X2] : k4_tarski(X1,X2) = X0 )
   => ( ( sK0 = k2_mcart_1(sK0)
        | sK0 = k1_mcart_1(sK0) )
      & ? [X2,X1] : k4_tarski(X1,X2) = sK0 ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X2,X1] : k4_tarski(X1,X2) = sK0
   => sK0 = k4_tarski(sK1,sK2) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0] :
      ( ( k2_mcart_1(X0) = X0
        | k1_mcart_1(X0) = X0 )
      & ? [X1,X2] : k4_tarski(X1,X2) = X0 ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ? [X1,X2] : k4_tarski(X1,X2) = X0
       => ( k2_mcart_1(X0) != X0
          & k1_mcart_1(X0) != X0 ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

fof(f37,plain,(
    ! [X2,X0,X3] :
      ( k4_tarski(X2,X3) != sK3(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f112,plain,(
    sK0 = sK1 ),
    inference(trivial_inequality_removal,[],[f111])).

fof(f111,plain,
    ( sK0 != sK0
    | sK0 = sK1 ),
    inference(superposition,[],[f107,f62])).

fof(f62,plain,
    ( sK0 = sK2
    | sK0 = sK1 ),
    inference(superposition,[],[f61,f60])).

fof(f60,plain,
    ( sK0 = k2_mcart_1(sK0)
    | sK0 = sK1 ),
    inference(backward_demodulation,[],[f32,f59])).

fof(f59,plain,(
    k1_mcart_1(sK0) = sK1 ),
    inference(superposition,[],[f44,f31])).

fof(f44,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f32,plain,
    ( sK0 = k2_mcart_1(sK0)
    | sK0 = k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f61,plain,(
    k2_mcart_1(sK0) = sK2 ),
    inference(superposition,[],[f45,f31])).

fof(f45,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f14])).

fof(f107,plain,(
    sK0 != sK2 ),
    inference(resolution,[],[f104,f56])).

fof(f104,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2,k1_tarski(X0))
      | sK0 != X0 ) ),
    inference(subsumption_resolution,[],[f103,f78])).

fof(f103,plain,(
    ! [X0] :
      ( sK0 != X0
      | ~ r2_hidden(sK2,k1_tarski(X0))
      | k1_xboole_0 = k1_tarski(X0) ) ),
    inference(duplicate_literal_removal,[],[f102])).

fof(f102,plain,(
    ! [X0] :
      ( sK0 != X0
      | ~ r2_hidden(sK2,k1_tarski(X0))
      | k1_xboole_0 = k1_tarski(X0)
      | k1_xboole_0 = k1_tarski(X0) ) ),
    inference(superposition,[],[f95,f65])).

fof(f95,plain,(
    ! [X0] :
      ( sK0 != sK3(X0)
      | ~ r2_hidden(sK2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f38,f31])).

fof(f38,plain,(
    ! [X2,X0,X3] :
      ( k4_tarski(X2,X3) != sK3(X0)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:45:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (19940)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.51  % (19948)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.52  % (19935)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.52  % (19950)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.52  % (19950)Refutation not found, incomplete strategy% (19950)------------------------------
% 0.22/0.52  % (19950)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (19950)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (19950)Memory used [KB]: 1791
% 0.22/0.52  % (19950)Time elapsed: 0.096 s
% 0.22/0.52  % (19950)------------------------------
% 0.22/0.52  % (19950)------------------------------
% 0.22/0.52  % (19934)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.53  % (19942)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.53  % (19934)Refutation not found, incomplete strategy% (19934)------------------------------
% 0.22/0.53  % (19934)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (19934)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (19934)Memory used [KB]: 1663
% 0.22/0.53  % (19934)Time elapsed: 0.109 s
% 0.22/0.53  % (19934)------------------------------
% 0.22/0.53  % (19934)------------------------------
% 1.32/0.53  % (19942)Refutation found. Thanks to Tanya!
% 1.32/0.53  % SZS status Theorem for theBenchmark
% 1.32/0.53  % SZS output start Proof for theBenchmark
% 1.32/0.53  fof(f113,plain,(
% 1.32/0.53    $false),
% 1.32/0.53    inference(subsumption_resolution,[],[f112,f100])).
% 1.32/0.53  fof(f100,plain,(
% 1.32/0.53    sK0 != sK1),
% 1.32/0.53    inference(resolution,[],[f94,f56])).
% 1.32/0.53  fof(f56,plain,(
% 1.32/0.53    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 1.32/0.53    inference(equality_resolution,[],[f55])).
% 1.32/0.53  fof(f55,plain,(
% 1.32/0.53    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 1.32/0.53    inference(equality_resolution,[],[f47])).
% 1.32/0.53  fof(f47,plain,(
% 1.32/0.53    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 1.32/0.53    inference(cnf_transformation,[],[f29])).
% 1.32/0.53  fof(f29,plain,(
% 1.32/0.53    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.32/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f27,f28])).
% 1.32/0.53  fof(f28,plain,(
% 1.32/0.53    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1))))),
% 1.32/0.53    introduced(choice_axiom,[])).
% 1.32/0.53  fof(f27,plain,(
% 1.32/0.53    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.32/0.53    inference(rectify,[],[f26])).
% 1.32/0.53  fof(f26,plain,(
% 1.32/0.53    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.32/0.53    inference(nnf_transformation,[],[f6])).
% 1.32/0.53  fof(f6,axiom,(
% 1.32/0.53    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.32/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 1.32/0.53  fof(f94,plain,(
% 1.32/0.53    ( ! [X0] : (~r2_hidden(sK1,k1_tarski(X0)) | sK0 != X0) )),
% 1.32/0.53    inference(subsumption_resolution,[],[f93,f78])).
% 1.32/0.53  % (19962)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.32/0.53  fof(f78,plain,(
% 1.32/0.53    ( ! [X1] : (k1_xboole_0 != k1_tarski(X1)) )),
% 1.32/0.53    inference(backward_demodulation,[],[f58,f76])).
% 1.32/0.53  fof(f76,plain,(
% 1.32/0.53    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.32/0.53    inference(forward_demodulation,[],[f75,f33])).
% 1.32/0.53  fof(f33,plain,(
% 1.32/0.53    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.32/0.53    inference(cnf_transformation,[],[f3])).
% 1.32/0.53  fof(f3,axiom,(
% 1.32/0.53    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.32/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 1.32/0.53  fof(f75,plain,(
% 1.32/0.53    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0)) )),
% 1.32/0.53    inference(superposition,[],[f43,f73])).
% 1.32/0.53  fof(f73,plain,(
% 1.32/0.53    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.32/0.53    inference(forward_demodulation,[],[f71,f34])).
% 1.32/0.53  fof(f34,plain,(
% 1.32/0.53    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.32/0.53    inference(cnf_transformation,[],[f5])).
% 1.32/0.53  fof(f5,axiom,(
% 1.32/0.53    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.32/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 1.32/0.53  fof(f71,plain,(
% 1.32/0.53    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0)) )),
% 1.32/0.53    inference(superposition,[],[f42,f33])).
% 1.32/0.53  fof(f42,plain,(
% 1.32/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.32/0.53    inference(cnf_transformation,[],[f2])).
% 1.32/0.53  fof(f2,axiom,(
% 1.32/0.53    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.32/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.32/0.53  fof(f43,plain,(
% 1.32/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.32/0.53    inference(cnf_transformation,[],[f4])).
% 1.32/0.53  fof(f4,axiom,(
% 1.32/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.32/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.32/0.53  fof(f58,plain,(
% 1.32/0.53    ( ! [X1] : (k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1))) )),
% 1.32/0.53    inference(equality_resolution,[],[f50])).
% 1.32/0.53  fof(f50,plain,(
% 1.32/0.53    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 1.32/0.53    inference(cnf_transformation,[],[f30])).
% 1.32/0.53  fof(f30,plain,(
% 1.32/0.53    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) & (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))),
% 1.32/0.53    inference(nnf_transformation,[],[f12])).
% 1.32/0.53  fof(f12,axiom,(
% 1.32/0.53    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 1.32/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 1.32/0.53  fof(f93,plain,(
% 1.32/0.53    ( ! [X0] : (sK0 != X0 | ~r2_hidden(sK1,k1_tarski(X0)) | k1_xboole_0 = k1_tarski(X0)) )),
% 1.32/0.53    inference(duplicate_literal_removal,[],[f92])).
% 1.32/0.53  fof(f92,plain,(
% 1.32/0.53    ( ! [X0] : (sK0 != X0 | ~r2_hidden(sK1,k1_tarski(X0)) | k1_xboole_0 = k1_tarski(X0) | k1_xboole_0 = k1_tarski(X0)) )),
% 1.32/0.53    inference(superposition,[],[f87,f65])).
% 1.32/0.53  fof(f65,plain,(
% 1.32/0.53    ( ! [X1] : (sK3(k1_tarski(X1)) = X1 | k1_xboole_0 = k1_tarski(X1)) )),
% 1.32/0.53    inference(resolution,[],[f57,f36])).
% 1.32/0.53  fof(f36,plain,(
% 1.32/0.53    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 1.32/0.53    inference(cnf_transformation,[],[f25])).
% 1.32/0.53  fof(f25,plain,(
% 1.32/0.53    ! [X0] : ((! [X2,X3] : (k4_tarski(X2,X3) != sK3(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK3(X0),X0)) | k1_xboole_0 = X0)),
% 1.32/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f20,f24])).
% 1.32/0.53  % (19962)Refutation not found, incomplete strategy% (19962)------------------------------
% 1.32/0.53  % (19962)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.53  % (19962)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.53  
% 1.32/0.53  % (19962)Memory used [KB]: 1663
% 1.32/0.53  % (19962)Time elapsed: 0.002 s
% 1.32/0.53  % (19962)------------------------------
% 1.32/0.53  % (19962)------------------------------
% 1.32/0.53  fof(f24,plain,(
% 1.32/0.53    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X3,X2] : (k4_tarski(X2,X3) != sK3(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK3(X0),X0)))),
% 1.32/0.53    introduced(choice_axiom,[])).
% 1.32/0.53  fof(f20,plain,(
% 1.32/0.53    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 1.32/0.53    inference(ennf_transformation,[],[f15])).
% 1.32/0.53  fof(f15,axiom,(
% 1.32/0.53    ! [X0] : ~(! [X1] : ~(! [X2,X3] : ~(k4_tarski(X2,X3) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 1.32/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).
% 1.32/0.53  fof(f57,plain,(
% 1.32/0.53    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 1.32/0.53    inference(equality_resolution,[],[f46])).
% 1.32/0.53  fof(f46,plain,(
% 1.32/0.53    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.32/0.53    inference(cnf_transformation,[],[f29])).
% 1.32/0.53  fof(f87,plain,(
% 1.32/0.53    ( ! [X0] : (sK0 != sK3(X0) | ~r2_hidden(sK1,X0) | k1_xboole_0 = X0) )),
% 1.32/0.53    inference(superposition,[],[f37,f31])).
% 1.32/0.53  fof(f31,plain,(
% 1.32/0.53    sK0 = k4_tarski(sK1,sK2)),
% 1.32/0.53    inference(cnf_transformation,[],[f23])).
% 1.32/0.53  fof(f23,plain,(
% 1.32/0.53    (sK0 = k2_mcart_1(sK0) | sK0 = k1_mcart_1(sK0)) & sK0 = k4_tarski(sK1,sK2)),
% 1.32/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f22,f21])).
% 1.32/0.53  fof(f21,plain,(
% 1.32/0.53    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0) => ((sK0 = k2_mcart_1(sK0) | sK0 = k1_mcart_1(sK0)) & ? [X2,X1] : k4_tarski(X1,X2) = sK0)),
% 1.32/0.53    introduced(choice_axiom,[])).
% 1.32/0.53  fof(f22,plain,(
% 1.32/0.53    ? [X2,X1] : k4_tarski(X1,X2) = sK0 => sK0 = k4_tarski(sK1,sK2)),
% 1.32/0.53    introduced(choice_axiom,[])).
% 1.32/0.53  fof(f19,plain,(
% 1.32/0.53    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0)),
% 1.32/0.53    inference(ennf_transformation,[],[f17])).
% 1.32/0.53  fof(f17,negated_conjecture,(
% 1.32/0.53    ~! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 1.32/0.53    inference(negated_conjecture,[],[f16])).
% 1.32/0.53  fof(f16,conjecture,(
% 1.32/0.53    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 1.32/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).
% 1.32/0.53  fof(f37,plain,(
% 1.32/0.53    ( ! [X2,X0,X3] : (k4_tarski(X2,X3) != sK3(X0) | ~r2_hidden(X2,X0) | k1_xboole_0 = X0) )),
% 1.32/0.53    inference(cnf_transformation,[],[f25])).
% 1.32/0.53  fof(f112,plain,(
% 1.32/0.53    sK0 = sK1),
% 1.32/0.53    inference(trivial_inequality_removal,[],[f111])).
% 1.32/0.53  fof(f111,plain,(
% 1.32/0.53    sK0 != sK0 | sK0 = sK1),
% 1.32/0.53    inference(superposition,[],[f107,f62])).
% 1.32/0.53  fof(f62,plain,(
% 1.32/0.53    sK0 = sK2 | sK0 = sK1),
% 1.32/0.53    inference(superposition,[],[f61,f60])).
% 1.32/0.53  fof(f60,plain,(
% 1.32/0.53    sK0 = k2_mcart_1(sK0) | sK0 = sK1),
% 1.32/0.53    inference(backward_demodulation,[],[f32,f59])).
% 1.32/0.53  fof(f59,plain,(
% 1.32/0.53    k1_mcart_1(sK0) = sK1),
% 1.32/0.53    inference(superposition,[],[f44,f31])).
% 1.32/0.53  fof(f44,plain,(
% 1.32/0.53    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 1.32/0.53    inference(cnf_transformation,[],[f14])).
% 1.32/0.53  fof(f14,axiom,(
% 1.32/0.53    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 1.32/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).
% 1.32/0.53  fof(f32,plain,(
% 1.32/0.53    sK0 = k2_mcart_1(sK0) | sK0 = k1_mcart_1(sK0)),
% 1.32/0.53    inference(cnf_transformation,[],[f23])).
% 1.32/0.53  fof(f61,plain,(
% 1.32/0.53    k2_mcart_1(sK0) = sK2),
% 1.32/0.53    inference(superposition,[],[f45,f31])).
% 1.32/0.53  fof(f45,plain,(
% 1.32/0.53    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 1.32/0.53    inference(cnf_transformation,[],[f14])).
% 1.32/0.53  fof(f107,plain,(
% 1.32/0.53    sK0 != sK2),
% 1.32/0.53    inference(resolution,[],[f104,f56])).
% 1.32/0.53  fof(f104,plain,(
% 1.32/0.53    ( ! [X0] : (~r2_hidden(sK2,k1_tarski(X0)) | sK0 != X0) )),
% 1.32/0.53    inference(subsumption_resolution,[],[f103,f78])).
% 1.32/0.53  fof(f103,plain,(
% 1.32/0.53    ( ! [X0] : (sK0 != X0 | ~r2_hidden(sK2,k1_tarski(X0)) | k1_xboole_0 = k1_tarski(X0)) )),
% 1.32/0.53    inference(duplicate_literal_removal,[],[f102])).
% 1.32/0.53  fof(f102,plain,(
% 1.32/0.53    ( ! [X0] : (sK0 != X0 | ~r2_hidden(sK2,k1_tarski(X0)) | k1_xboole_0 = k1_tarski(X0) | k1_xboole_0 = k1_tarski(X0)) )),
% 1.32/0.53    inference(superposition,[],[f95,f65])).
% 1.32/0.53  fof(f95,plain,(
% 1.32/0.53    ( ! [X0] : (sK0 != sK3(X0) | ~r2_hidden(sK2,X0) | k1_xboole_0 = X0) )),
% 1.32/0.53    inference(superposition,[],[f38,f31])).
% 1.32/0.53  fof(f38,plain,(
% 1.32/0.53    ( ! [X2,X0,X3] : (k4_tarski(X2,X3) != sK3(X0) | ~r2_hidden(X3,X0) | k1_xboole_0 = X0) )),
% 1.32/0.53    inference(cnf_transformation,[],[f25])).
% 1.32/0.53  % SZS output end Proof for theBenchmark
% 1.32/0.53  % (19942)------------------------------
% 1.32/0.53  % (19942)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.53  % (19942)Termination reason: Refutation
% 1.32/0.53  
% 1.32/0.53  % (19942)Memory used [KB]: 1791
% 1.32/0.53  % (19942)Time elapsed: 0.116 s
% 1.32/0.53  % (19942)------------------------------
% 1.32/0.53  % (19942)------------------------------
% 1.32/0.54  % (19932)Success in time 0.172 s
%------------------------------------------------------------------------------
