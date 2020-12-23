%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:25 EST 2020

% Result     : Theorem 1.25s
% Output     : Refutation 1.25s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 154 expanded)
%              Number of leaves         :   10 (  49 expanded)
%              Depth                    :   10
%              Number of atoms          :  120 ( 330 expanded)
%              Number of equality atoms :   63 ( 231 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f64,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f36,f48,f47,f43,f61])).

fof(f61,plain,(
    ! [X14,X12,X15,X13,X16] :
      ( ~ r2_hidden(X12,k2_enumset1(X13,X13,X13,X14))
      | X12 = X13
      | X12 = X14
      | ~ r2_hidden(X15,X16) ) ),
    inference(forward_demodulation,[],[f60,f25])).

fof(f25,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f60,plain,(
    ! [X14,X12,X15,X13,X16] :
      ( X12 = X13
      | ~ r2_hidden(X12,k2_enumset1(X13,X13,X13,X14))
      | ~ r2_hidden(X15,X16)
      | k2_mcart_1(k4_tarski(X15,X12)) = X14 ) ),
    inference(forward_demodulation,[],[f56,f25])).

fof(f56,plain,(
    ! [X14,X12,X15,X13,X16] :
      ( ~ r2_hidden(X12,k2_enumset1(X13,X13,X13,X14))
      | ~ r2_hidden(X15,X16)
      | k2_mcart_1(k4_tarski(X15,X12)) = X13
      | k2_mcart_1(k4_tarski(X15,X12)) = X14 ) ),
    inference(resolution,[],[f52,f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,k2_enumset1(X2,X2,X2,X3)))
      | k2_mcart_1(X0) = X2
      | k2_mcart_1(X0) = X3 ) ),
    inference(definition_unfolding,[],[f33,f34])).

fof(f34,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f23,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f23,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(X0) = X3
      | k2_mcart_1(X0) = X2
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k2_mcart_1(X0) = X3
          | k2_mcart_1(X0) = X2 )
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3)))
     => ( ( k2_mcart_1(X0) = X3
          | k2_mcart_1(X0) = X2 )
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_mcart_1)).

fof(f52,plain,(
    ! [X4,X2,X3,X1] :
      ( r2_hidden(k4_tarski(X3,X4),k2_zfmisc_1(X1,X2))
      | ~ r2_hidden(X4,X2)
      | ~ r2_hidden(X3,X1) ) ),
    inference(forward_demodulation,[],[f51,f24])).

fof(f24,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f51,plain,(
    ! [X4,X2,X3,X1] :
      ( ~ r2_hidden(X4,X2)
      | r2_hidden(k4_tarski(X3,X4),k2_zfmisc_1(X1,X2))
      | ~ r2_hidden(k1_mcart_1(k4_tarski(X3,X4)),X1) ) ),
    inference(forward_demodulation,[],[f41,f25])).

fof(f41,plain,(
    ! [X4,X2,X3,X1] :
      ( r2_hidden(k4_tarski(X3,X4),k2_zfmisc_1(X1,X2))
      | ~ r2_hidden(k2_mcart_1(k4_tarski(X3,X4)),X2)
      | ~ r2_hidden(k1_mcart_1(k4_tarski(X3,X4)),X1) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | k4_tarski(X3,X4) != X0
      | ~ r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f15])).

% (3185)Refutation not found, incomplete strategy% (3185)------------------------------
% (3185)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | ! [X3,X4] : k4_tarski(X3,X4) != X0
      | ~ r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(flattening,[],[f14])).

% (3185)Termination reason: Refutation not found, incomplete strategy

% (3185)Memory used [KB]: 10618
% (3185)Time elapsed: 0.116 s
% (3185)------------------------------
% (3185)------------------------------
fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | ! [X3,X4] : k4_tarski(X3,X4) != X0
      | ~ r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
     => ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
        | ! [X3,X4] : k4_tarski(X3,X4) != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_mcart_1)).

fof(f43,plain,(
    r2_hidden(k1_mcart_1(sK0),k2_enumset1(sK1,sK1,sK1,sK2)) ),
    inference(resolution,[],[f36,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f47,plain,(
    sK1 != k1_mcart_1(sK0) ),
    inference(trivial_inequality_removal,[],[f46])).

fof(f46,plain,
    ( sK3 != sK3
    | sK1 != k1_mcart_1(sK0) ),
    inference(superposition,[],[f20,f44])).

fof(f44,plain,(
    sK3 = k2_mcart_1(sK0) ),
    inference(resolution,[],[f37,f36])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,k2_enumset1(X2,X2,X2,X2)))
      | k2_mcart_1(X0) = X2 ) ),
    inference(definition_unfolding,[],[f30,f35])).

fof(f35,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f22,f34])).

fof(f22,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k2_mcart_1(X0) = X2
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( k2_mcart_1(X0) = X2
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2)))
     => ( k2_mcart_1(X0) = X2
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_mcart_1)).

fof(f20,plain,
    ( sK3 != k2_mcart_1(sK0)
    | sK1 != k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ( sK3 != k2_mcart_1(sK0)
      | ( sK2 != k1_mcart_1(sK0)
        & sK1 != k1_mcart_1(sK0) ) )
    & r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),k1_tarski(sK3))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f17])).

fof(f17,plain,
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

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( ( k2_mcart_1(X0) != X3
        | ( k1_mcart_1(X0) != X2
          & k1_mcart_1(X0) != X1 ) )
      & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3)))
       => ( k2_mcart_1(X0) = X3
          & ( k1_mcart_1(X0) = X2
            | k1_mcart_1(X0) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3)))
     => ( k2_mcart_1(X0) = X3
        & ( k1_mcart_1(X0) = X2
          | k1_mcart_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_mcart_1)).

fof(f48,plain,(
    sK2 != k1_mcart_1(sK0) ),
    inference(trivial_inequality_removal,[],[f45])).

fof(f45,plain,
    ( sK3 != sK3
    | sK2 != k1_mcart_1(sK0) ),
    inference(superposition,[],[f21,f44])).

fof(f21,plain,
    ( sK3 != k2_mcart_1(sK0)
    | sK2 != k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f36,plain,(
    r2_hidden(sK0,k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK2),k2_enumset1(sK3,sK3,sK3,sK3))) ),
    inference(definition_unfolding,[],[f19,f34,f35])).

fof(f19,plain,(
    r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),k1_tarski(sK3))) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:52:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.22/0.50  % (3192)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.50  % (3193)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.50  % (3183)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.50  % (3208)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.51  % (3200)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.51  % (3192)Refutation not found, incomplete strategy% (3192)------------------------------
% 0.22/0.51  % (3192)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (3192)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (3192)Memory used [KB]: 10746
% 0.22/0.51  % (3192)Time elapsed: 0.094 s
% 0.22/0.51  % (3192)------------------------------
% 0.22/0.51  % (3192)------------------------------
% 0.22/0.51  % (3187)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.25/0.52  % (3187)Refutation not found, incomplete strategy% (3187)------------------------------
% 1.25/0.52  % (3187)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.52  % (3187)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.52  
% 1.25/0.52  % (3187)Memory used [KB]: 6140
% 1.25/0.52  % (3187)Time elapsed: 0.108 s
% 1.25/0.52  % (3187)------------------------------
% 1.25/0.52  % (3187)------------------------------
% 1.25/0.52  % (3191)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.25/0.52  % (3200)Refutation not found, incomplete strategy% (3200)------------------------------
% 1.25/0.52  % (3200)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.52  % (3190)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.25/0.52  % (3200)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.52  
% 1.25/0.52  % (3200)Memory used [KB]: 10618
% 1.25/0.52  % (3200)Time elapsed: 0.105 s
% 1.25/0.52  % (3200)------------------------------
% 1.25/0.52  % (3200)------------------------------
% 1.25/0.52  % (3191)Refutation not found, incomplete strategy% (3191)------------------------------
% 1.25/0.52  % (3191)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.52  % (3191)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.52  
% 1.25/0.52  % (3191)Memory used [KB]: 10618
% 1.25/0.52  % (3191)Time elapsed: 0.106 s
% 1.25/0.52  % (3191)------------------------------
% 1.25/0.52  % (3191)------------------------------
% 1.25/0.52  % (3208)Refutation not found, incomplete strategy% (3208)------------------------------
% 1.25/0.52  % (3208)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.52  % (3205)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.25/0.52  % (3208)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.52  
% 1.25/0.52  % (3208)Memory used [KB]: 6268
% 1.25/0.52  % (3208)Time elapsed: 0.106 s
% 1.25/0.52  % (3208)------------------------------
% 1.25/0.52  % (3208)------------------------------
% 1.25/0.52  % (3201)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.25/0.52  % (3205)Refutation not found, incomplete strategy% (3205)------------------------------
% 1.25/0.52  % (3205)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.52  % (3205)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.52  
% 1.25/0.52  % (3205)Memory used [KB]: 10746
% 1.25/0.52  % (3205)Time elapsed: 0.074 s
% 1.25/0.52  % (3205)------------------------------
% 1.25/0.52  % (3205)------------------------------
% 1.25/0.52  % (3183)Refutation not found, incomplete strategy% (3183)------------------------------
% 1.25/0.52  % (3183)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.52  % (3183)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.52  
% 1.25/0.52  % (3183)Memory used [KB]: 1663
% 1.25/0.52  % (3183)Time elapsed: 0.101 s
% 1.25/0.52  % (3183)------------------------------
% 1.25/0.52  % (3183)------------------------------
% 1.25/0.52  % (3204)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.25/0.53  % (3209)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.25/0.53  % (3196)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.25/0.53  % (3185)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.25/0.53  % (3212)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.25/0.53  % (3197)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.25/0.53  % (3212)Refutation found. Thanks to Tanya!
% 1.25/0.53  % SZS status Theorem for theBenchmark
% 1.25/0.53  % SZS output start Proof for theBenchmark
% 1.25/0.53  fof(f64,plain,(
% 1.25/0.53    $false),
% 1.25/0.53    inference(unit_resulting_resolution,[],[f36,f48,f47,f43,f61])).
% 1.25/0.53  fof(f61,plain,(
% 1.25/0.53    ( ! [X14,X12,X15,X13,X16] : (~r2_hidden(X12,k2_enumset1(X13,X13,X13,X14)) | X12 = X13 | X12 = X14 | ~r2_hidden(X15,X16)) )),
% 1.25/0.53    inference(forward_demodulation,[],[f60,f25])).
% 1.25/0.53  fof(f25,plain,(
% 1.25/0.53    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 1.25/0.53    inference(cnf_transformation,[],[f8])).
% 1.25/0.53  fof(f8,axiom,(
% 1.25/0.53    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 1.25/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).
% 1.25/0.53  fof(f60,plain,(
% 1.25/0.53    ( ! [X14,X12,X15,X13,X16] : (X12 = X13 | ~r2_hidden(X12,k2_enumset1(X13,X13,X13,X14)) | ~r2_hidden(X15,X16) | k2_mcart_1(k4_tarski(X15,X12)) = X14) )),
% 1.25/0.53    inference(forward_demodulation,[],[f56,f25])).
% 1.25/0.53  fof(f56,plain,(
% 1.25/0.53    ( ! [X14,X12,X15,X13,X16] : (~r2_hidden(X12,k2_enumset1(X13,X13,X13,X14)) | ~r2_hidden(X15,X16) | k2_mcart_1(k4_tarski(X15,X12)) = X13 | k2_mcart_1(k4_tarski(X15,X12)) = X14) )),
% 1.25/0.53    inference(resolution,[],[f52,f39])).
% 1.25/0.53  fof(f39,plain,(
% 1.25/0.53    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,k2_enumset1(X2,X2,X2,X3))) | k2_mcart_1(X0) = X2 | k2_mcart_1(X0) = X3) )),
% 1.25/0.53    inference(definition_unfolding,[],[f33,f34])).
% 1.25/0.53  fof(f34,plain,(
% 1.25/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.25/0.53    inference(definition_unfolding,[],[f23,f26])).
% 1.25/0.53  fof(f26,plain,(
% 1.25/0.53    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.25/0.53    inference(cnf_transformation,[],[f3])).
% 1.25/0.53  fof(f3,axiom,(
% 1.25/0.53    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.25/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.25/0.53  fof(f23,plain,(
% 1.25/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.25/0.53    inference(cnf_transformation,[],[f2])).
% 1.25/0.53  fof(f2,axiom,(
% 1.25/0.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.25/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.25/0.53  fof(f33,plain,(
% 1.25/0.53    ( ! [X2,X0,X3,X1] : (k2_mcart_1(X0) = X3 | k2_mcart_1(X0) = X2 | ~r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3)))) )),
% 1.25/0.53    inference(cnf_transformation,[],[f16])).
% 1.25/0.53  fof(f16,plain,(
% 1.25/0.53    ! [X0,X1,X2,X3] : (((k2_mcart_1(X0) = X3 | k2_mcart_1(X0) = X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3))))),
% 1.25/0.53    inference(ennf_transformation,[],[f7])).
% 1.25/0.53  fof(f7,axiom,(
% 1.25/0.53    ! [X0,X1,X2,X3] : (r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3))) => ((k2_mcart_1(X0) = X3 | k2_mcart_1(X0) = X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 1.25/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_mcart_1)).
% 1.25/0.53  fof(f52,plain,(
% 1.25/0.53    ( ! [X4,X2,X3,X1] : (r2_hidden(k4_tarski(X3,X4),k2_zfmisc_1(X1,X2)) | ~r2_hidden(X4,X2) | ~r2_hidden(X3,X1)) )),
% 1.25/0.53    inference(forward_demodulation,[],[f51,f24])).
% 1.25/0.53  fof(f24,plain,(
% 1.25/0.53    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 1.25/0.53    inference(cnf_transformation,[],[f8])).
% 1.25/0.53  fof(f51,plain,(
% 1.25/0.53    ( ! [X4,X2,X3,X1] : (~r2_hidden(X4,X2) | r2_hidden(k4_tarski(X3,X4),k2_zfmisc_1(X1,X2)) | ~r2_hidden(k1_mcart_1(k4_tarski(X3,X4)),X1)) )),
% 1.25/0.53    inference(forward_demodulation,[],[f41,f25])).
% 1.25/0.53  fof(f41,plain,(
% 1.25/0.53    ( ! [X4,X2,X3,X1] : (r2_hidden(k4_tarski(X3,X4),k2_zfmisc_1(X1,X2)) | ~r2_hidden(k2_mcart_1(k4_tarski(X3,X4)),X2) | ~r2_hidden(k1_mcart_1(k4_tarski(X3,X4)),X1)) )),
% 1.25/0.53    inference(equality_resolution,[],[f31])).
% 1.25/0.53  fof(f31,plain,(
% 1.25/0.53    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) | k4_tarski(X3,X4) != X0 | ~r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(k1_mcart_1(X0),X1)) )),
% 1.25/0.53    inference(cnf_transformation,[],[f15])).
% 1.25/0.53  % (3185)Refutation not found, incomplete strategy% (3185)------------------------------
% 1.25/0.53  % (3185)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.53  fof(f15,plain,(
% 1.25/0.53    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) | ! [X3,X4] : k4_tarski(X3,X4) != X0 | ~r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(k1_mcart_1(X0),X1))),
% 1.25/0.53    inference(flattening,[],[f14])).
% 1.25/0.53  % (3185)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.53  
% 1.25/0.53  % (3185)Memory used [KB]: 10618
% 1.25/0.53  % (3185)Time elapsed: 0.116 s
% 1.25/0.53  % (3185)------------------------------
% 1.25/0.53  % (3185)------------------------------
% 1.25/0.53  fof(f14,plain,(
% 1.25/0.53    ! [X0,X1,X2] : ((r2_hidden(X0,k2_zfmisc_1(X1,X2)) | ! [X3,X4] : k4_tarski(X3,X4) != X0) | (~r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(k1_mcart_1(X0),X1)))),
% 1.25/0.53    inference(ennf_transformation,[],[f5])).
% 1.25/0.53  fof(f5,axiom,(
% 1.25/0.53    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) => (r2_hidden(X0,k2_zfmisc_1(X1,X2)) | ! [X3,X4] : k4_tarski(X3,X4) != X0))),
% 1.25/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_mcart_1)).
% 1.25/0.53  fof(f43,plain,(
% 1.25/0.53    r2_hidden(k1_mcart_1(sK0),k2_enumset1(sK1,sK1,sK1,sK2))),
% 1.25/0.53    inference(resolution,[],[f36,f27])).
% 1.25/0.53  fof(f27,plain,(
% 1.25/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 1.25/0.53    inference(cnf_transformation,[],[f12])).
% 1.25/0.53  fof(f12,plain,(
% 1.25/0.53    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 1.25/0.53    inference(ennf_transformation,[],[f4])).
% 1.25/0.53  fof(f4,axiom,(
% 1.25/0.53    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 1.25/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).
% 1.25/0.53  fof(f47,plain,(
% 1.25/0.53    sK1 != k1_mcart_1(sK0)),
% 1.25/0.53    inference(trivial_inequality_removal,[],[f46])).
% 1.25/0.53  fof(f46,plain,(
% 1.25/0.53    sK3 != sK3 | sK1 != k1_mcart_1(sK0)),
% 1.25/0.53    inference(superposition,[],[f20,f44])).
% 1.25/0.53  fof(f44,plain,(
% 1.25/0.53    sK3 = k2_mcart_1(sK0)),
% 1.25/0.53    inference(resolution,[],[f37,f36])).
% 1.25/0.53  fof(f37,plain,(
% 1.25/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,k2_enumset1(X2,X2,X2,X2))) | k2_mcart_1(X0) = X2) )),
% 1.25/0.53    inference(definition_unfolding,[],[f30,f35])).
% 1.25/0.53  fof(f35,plain,(
% 1.25/0.53    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.25/0.53    inference(definition_unfolding,[],[f22,f34])).
% 1.25/0.53  fof(f22,plain,(
% 1.25/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.25/0.53    inference(cnf_transformation,[],[f1])).
% 1.25/0.53  fof(f1,axiom,(
% 1.25/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.25/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.25/0.53  fof(f30,plain,(
% 1.25/0.53    ( ! [X2,X0,X1] : (k2_mcart_1(X0) = X2 | ~r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2)))) )),
% 1.25/0.53    inference(cnf_transformation,[],[f13])).
% 1.25/0.53  fof(f13,plain,(
% 1.25/0.53    ! [X0,X1,X2] : ((k2_mcart_1(X0) = X2 & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2))))),
% 1.25/0.53    inference(ennf_transformation,[],[f6])).
% 1.25/0.53  fof(f6,axiom,(
% 1.25/0.53    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2))) => (k2_mcart_1(X0) = X2 & r2_hidden(k1_mcart_1(X0),X1)))),
% 1.25/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_mcart_1)).
% 1.25/0.53  fof(f20,plain,(
% 1.25/0.53    sK3 != k2_mcart_1(sK0) | sK1 != k1_mcart_1(sK0)),
% 1.25/0.53    inference(cnf_transformation,[],[f18])).
% 1.25/0.53  fof(f18,plain,(
% 1.25/0.53    (sK3 != k2_mcart_1(sK0) | (sK2 != k1_mcart_1(sK0) & sK1 != k1_mcart_1(sK0))) & r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),k1_tarski(sK3)))),
% 1.25/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f17])).
% 1.25/0.53  fof(f17,plain,(
% 1.25/0.53    ? [X0,X1,X2,X3] : ((k2_mcart_1(X0) != X3 | (k1_mcart_1(X0) != X2 & k1_mcart_1(X0) != X1)) & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3)))) => ((sK3 != k2_mcart_1(sK0) | (sK2 != k1_mcart_1(sK0) & sK1 != k1_mcart_1(sK0))) & r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),k1_tarski(sK3))))),
% 1.25/0.53    introduced(choice_axiom,[])).
% 1.25/0.53  fof(f11,plain,(
% 1.25/0.53    ? [X0,X1,X2,X3] : ((k2_mcart_1(X0) != X3 | (k1_mcart_1(X0) != X2 & k1_mcart_1(X0) != X1)) & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))))),
% 1.25/0.53    inference(ennf_transformation,[],[f10])).
% 1.25/0.53  fof(f10,negated_conjecture,(
% 1.25/0.53    ~! [X0,X1,X2,X3] : (r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))) => (k2_mcart_1(X0) = X3 & (k1_mcart_1(X0) = X2 | k1_mcart_1(X0) = X1)))),
% 1.25/0.53    inference(negated_conjecture,[],[f9])).
% 1.25/0.53  fof(f9,conjecture,(
% 1.25/0.53    ! [X0,X1,X2,X3] : (r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))) => (k2_mcart_1(X0) = X3 & (k1_mcart_1(X0) = X2 | k1_mcart_1(X0) = X1)))),
% 1.25/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_mcart_1)).
% 1.25/0.53  fof(f48,plain,(
% 1.25/0.53    sK2 != k1_mcart_1(sK0)),
% 1.25/0.53    inference(trivial_inequality_removal,[],[f45])).
% 1.25/0.53  fof(f45,plain,(
% 1.25/0.53    sK3 != sK3 | sK2 != k1_mcart_1(sK0)),
% 1.25/0.53    inference(superposition,[],[f21,f44])).
% 1.25/0.53  fof(f21,plain,(
% 1.25/0.53    sK3 != k2_mcart_1(sK0) | sK2 != k1_mcart_1(sK0)),
% 1.25/0.53    inference(cnf_transformation,[],[f18])).
% 1.25/0.53  fof(f36,plain,(
% 1.25/0.53    r2_hidden(sK0,k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK2),k2_enumset1(sK3,sK3,sK3,sK3)))),
% 1.25/0.53    inference(definition_unfolding,[],[f19,f34,f35])).
% 1.25/0.53  fof(f19,plain,(
% 1.25/0.53    r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),k1_tarski(sK3)))),
% 1.25/0.53    inference(cnf_transformation,[],[f18])).
% 1.25/0.53  % SZS output end Proof for theBenchmark
% 1.25/0.53  % (3212)------------------------------
% 1.25/0.53  % (3212)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.53  % (3212)Termination reason: Refutation
% 1.25/0.53  
% 1.25/0.53  % (3212)Memory used [KB]: 1663
% 1.25/0.53  % (3212)Time elapsed: 0.122 s
% 1.25/0.53  % (3212)------------------------------
% 1.25/0.53  % (3212)------------------------------
% 1.25/0.53  % (3204)Refutation not found, incomplete strategy% (3204)------------------------------
% 1.25/0.53  % (3204)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.53  % (3204)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.53  
% 1.36/0.53  % (3182)Success in time 0.175 s
%------------------------------------------------------------------------------
