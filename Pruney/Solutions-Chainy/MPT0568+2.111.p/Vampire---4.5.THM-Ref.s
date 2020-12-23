%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:24 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   56 (  77 expanded)
%              Number of leaves         :   14 (  21 expanded)
%              Depth                    :   12
%              Number of atoms          :  151 ( 255 expanded)
%              Number of equality atoms :   43 (  61 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f181,plain,(
    $false ),
    inference(subsumption_resolution,[],[f28,f173])).

fof(f173,plain,(
    ! [X2] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X2) ),
    inference(superposition,[],[f162,f51])).

fof(f51,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f48,f32])).

fof(f32,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f48,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f37,f42])).

fof(f42,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f37,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f162,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k10_relat_1(k1_xboole_0,X1)) = X0 ),
    inference(resolution,[],[f158,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X1,X0) = X1 ) ),
    inference(resolution,[],[f83,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f83,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0)
      | r1_xboole_0(X1,X0) ) ),
    inference(resolution,[],[f62,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
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

fof(f62,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(sK2(X3,X4),X5)
      | ~ r1_xboole_0(X4,X5)
      | r1_xboole_0(X3,X4) ) ),
    inference(resolution,[],[f47,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f158,plain,(
    ! [X0,X1] : r1_xboole_0(k10_relat_1(k1_xboole_0,X0),X1) ),
    inference(resolution,[],[f157,f45])).

fof(f157,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k10_relat_1(k1_xboole_0,X1)) ),
    inference(subsumption_resolution,[],[f156,f53])).

fof(f53,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f39,f49])).

fof(f49,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f39,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f156,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k10_relat_1(k1_xboole_0,X1))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f155,f52])).

fof(f52,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f38,f49])).

fof(f38,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f155,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(X0,k10_relat_1(k1_xboole_0,X1))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[],[f33,f44])).

fof(f44,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK1(X0,X1,X2),k2_relat_1(X2))
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ( r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(X0,sK1(X0,X1,X2)),X2)
            & r2_hidden(sK1(X0,X1,X2),k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f22,f23])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X0,X4),X2)
          & r2_hidden(X4,k2_relat_1(X2)) )
     => ( r2_hidden(sK1(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X0,sK1(X0,X1,X2)),X2)
        & r2_hidden(sK1(X0,X1,X2),k2_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X0,X4),X2)
              & r2_hidden(X4,k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X0,X3),X2)
              & r2_hidden(X3,k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

fof(f28,plain,(
    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f17])).

fof(f17,plain,
    ( ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0)
   => k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:37:14 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.53  % (29239)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.53  % (29253)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (29253)Refutation not found, incomplete strategy% (29253)------------------------------
% 0.21/0.53  % (29253)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (29253)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (29253)Memory used [KB]: 1663
% 0.21/0.53  % (29253)Time elapsed: 0.112 s
% 0.21/0.53  % (29253)------------------------------
% 0.21/0.53  % (29253)------------------------------
% 0.21/0.54  % (29245)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (29231)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (29238)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.54  % (29238)Refutation not found, incomplete strategy% (29238)------------------------------
% 0.21/0.54  % (29238)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (29238)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (29238)Memory used [KB]: 10618
% 0.21/0.54  % (29238)Time elapsed: 0.127 s
% 0.21/0.54  % (29238)------------------------------
% 0.21/0.54  % (29238)------------------------------
% 0.21/0.55  % (29235)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.55  % (29230)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.55  % (29240)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.55  % (29230)Refutation not found, incomplete strategy% (29230)------------------------------
% 0.21/0.55  % (29230)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (29230)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (29230)Memory used [KB]: 1663
% 0.21/0.55  % (29230)Time elapsed: 0.124 s
% 0.21/0.55  % (29230)------------------------------
% 0.21/0.55  % (29230)------------------------------
% 0.21/0.56  % (29237)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.56  % (29239)Refutation not found, incomplete strategy% (29239)------------------------------
% 0.21/0.56  % (29239)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (29239)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (29239)Memory used [KB]: 10618
% 0.21/0.56  % (29239)Time elapsed: 0.143 s
% 0.21/0.56  % (29239)------------------------------
% 0.21/0.56  % (29239)------------------------------
% 0.21/0.56  % (29233)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.57  % (29235)Refutation found. Thanks to Tanya!
% 0.21/0.57  % SZS status Theorem for theBenchmark
% 0.21/0.57  % SZS output start Proof for theBenchmark
% 0.21/0.57  fof(f181,plain,(
% 0.21/0.57    $false),
% 0.21/0.57    inference(subsumption_resolution,[],[f28,f173])).
% 0.21/0.57  fof(f173,plain,(
% 0.21/0.57    ( ! [X2] : (k1_xboole_0 = k10_relat_1(k1_xboole_0,X2)) )),
% 0.21/0.57    inference(superposition,[],[f162,f51])).
% 0.21/0.57  fof(f51,plain,(
% 0.21/0.57    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.21/0.57    inference(forward_demodulation,[],[f48,f32])).
% 0.21/0.57  fof(f32,plain,(
% 0.21/0.57    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.57    inference(cnf_transformation,[],[f3])).
% 0.21/0.57  fof(f3,axiom,(
% 0.21/0.57    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.57  fof(f48,plain,(
% 0.21/0.57    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 0.21/0.57    inference(definition_unfolding,[],[f37,f42])).
% 0.21/0.57  fof(f42,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f4])).
% 0.21/0.57  fof(f4,axiom,(
% 0.21/0.57    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.57  fof(f37,plain,(
% 0.21/0.57    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f2])).
% 0.21/0.57  fof(f2,axiom,(
% 0.21/0.57    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.21/0.57  fof(f162,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,k10_relat_1(k1_xboole_0,X1)) = X0) )),
% 0.21/0.57    inference(resolution,[],[f158,f86])).
% 0.21/0.57  fof(f86,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X1,X0) = X1) )),
% 0.21/0.57    inference(resolution,[],[f83,f40])).
% 0.21/0.57  fof(f40,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 0.21/0.57    inference(cnf_transformation,[],[f25])).
% 0.21/0.57  fof(f25,plain,(
% 0.21/0.57    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.57    inference(nnf_transformation,[],[f5])).
% 0.21/0.57  fof(f5,axiom,(
% 0.21/0.57    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.21/0.57  fof(f83,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.57    inference(duplicate_literal_removal,[],[f80])).
% 0.21/0.57  fof(f80,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) | r1_xboole_0(X1,X0)) )),
% 0.21/0.57    inference(resolution,[],[f62,f45])).
% 0.21/0.57  fof(f45,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f27])).
% 0.21/0.57  fof(f27,plain,(
% 0.21/0.57    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f26])).
% 0.21/0.57  fof(f26,plain,(
% 0.21/0.57    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f16,plain,(
% 0.21/0.57    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.57    inference(ennf_transformation,[],[f13])).
% 0.21/0.57  fof(f13,plain,(
% 0.21/0.57    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.57    inference(rectify,[],[f1])).
% 0.21/0.57  fof(f1,axiom,(
% 0.21/0.57    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.21/0.57  fof(f62,plain,(
% 0.21/0.57    ( ! [X4,X5,X3] : (~r2_hidden(sK2(X3,X4),X5) | ~r1_xboole_0(X4,X5) | r1_xboole_0(X3,X4)) )),
% 0.21/0.57    inference(resolution,[],[f47,f46])).
% 0.21/0.57  fof(f46,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f27])).
% 0.21/0.57  fof(f47,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f27])).
% 0.21/0.57  fof(f158,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r1_xboole_0(k10_relat_1(k1_xboole_0,X0),X1)) )),
% 0.21/0.57    inference(resolution,[],[f157,f45])).
% 0.21/0.57  fof(f157,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~r2_hidden(X0,k10_relat_1(k1_xboole_0,X1))) )),
% 0.21/0.57    inference(subsumption_resolution,[],[f156,f53])).
% 0.21/0.57  fof(f53,plain,(
% 0.21/0.57    v1_relat_1(k1_xboole_0)),
% 0.21/0.57    inference(superposition,[],[f39,f49])).
% 0.21/0.57  fof(f49,plain,(
% 0.21/0.57    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.57    inference(equality_resolution,[],[f31])).
% 0.21/0.57  fof(f31,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.21/0.57    inference(cnf_transformation,[],[f20])).
% 0.21/0.57  fof(f20,plain,(
% 0.21/0.57    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.57    inference(flattening,[],[f19])).
% 0.21/0.57  fof(f19,plain,(
% 0.21/0.57    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.57    inference(nnf_transformation,[],[f6])).
% 0.21/0.57  fof(f6,axiom,(
% 0.21/0.57    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.57  fof(f39,plain,(
% 0.21/0.57    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f8])).
% 0.21/0.57  fof(f8,axiom,(
% 0.21/0.57    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.57  fof(f156,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~r2_hidden(X0,k10_relat_1(k1_xboole_0,X1)) | ~v1_relat_1(k1_xboole_0)) )),
% 0.21/0.57    inference(subsumption_resolution,[],[f155,f52])).
% 0.21/0.57  fof(f52,plain,(
% 0.21/0.57    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.57    inference(superposition,[],[f38,f49])).
% 0.21/0.57  fof(f38,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f7])).
% 0.21/0.57  fof(f7,axiom,(
% 0.21/0.57    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 0.21/0.57  fof(f155,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1,k1_xboole_0),k1_xboole_0) | ~r2_hidden(X0,k10_relat_1(k1_xboole_0,X1)) | ~v1_relat_1(k1_xboole_0)) )),
% 0.21/0.57    inference(superposition,[],[f33,f44])).
% 0.21/0.57  fof(f44,plain,(
% 0.21/0.57    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.57    inference(cnf_transformation,[],[f10])).
% 0.21/0.57  fof(f10,axiom,(
% 0.21/0.57    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.57  fof(f33,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (r2_hidden(sK1(X0,X1,X2),k2_relat_1(X2)) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f24])).
% 0.21/0.57  fof(f24,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK1(X0,X1,X2)),X2) & r2_hidden(sK1(X0,X1,X2),k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.21/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f22,f23])).
% 0.21/0.57  fof(f23,plain,(
% 0.21/0.57    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) => (r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK1(X0,X1,X2)),X2) & r2_hidden(sK1(X0,X1,X2),k2_relat_1(X2))))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f22,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.21/0.57    inference(rectify,[],[f21])).
% 0.21/0.57  fof(f21,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.21/0.57    inference(nnf_transformation,[],[f15])).
% 0.21/0.57  fof(f15,plain,(
% 0.21/0.57    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.21/0.57    inference(ennf_transformation,[],[f9])).
% 0.21/0.57  fof(f9,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).
% 0.21/0.57  fof(f28,plain,(
% 0.21/0.57    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)),
% 0.21/0.57    inference(cnf_transformation,[],[f18])).
% 0.21/0.57  fof(f18,plain,(
% 0.21/0.57    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)),
% 0.21/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f17])).
% 0.21/0.57  fof(f17,plain,(
% 0.21/0.57    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0) => k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f14,plain,(
% 0.21/0.57    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0)),
% 0.21/0.57    inference(ennf_transformation,[],[f12])).
% 0.21/0.57  fof(f12,negated_conjecture,(
% 0.21/0.57    ~! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 0.21/0.57    inference(negated_conjecture,[],[f11])).
% 0.21/0.57  fof(f11,conjecture,(
% 0.21/0.57    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).
% 0.21/0.57  % SZS output end Proof for theBenchmark
% 0.21/0.57  % (29235)------------------------------
% 0.21/0.57  % (29235)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (29235)Termination reason: Refutation
% 0.21/0.57  
% 0.21/0.57  % (29235)Memory used [KB]: 6268
% 0.21/0.57  % (29235)Time elapsed: 0.133 s
% 0.21/0.57  % (29235)------------------------------
% 0.21/0.57  % (29235)------------------------------
% 0.21/0.57  % (29229)Success in time 0.203 s
%------------------------------------------------------------------------------
