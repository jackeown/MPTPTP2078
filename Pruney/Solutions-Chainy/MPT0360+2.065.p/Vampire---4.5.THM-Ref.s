%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:57 EST 2020

% Result     : Theorem 1.20s
% Output     : Refutation 1.20s
% Verified   : 
% Statistics : Number of formulae       :   44 (  62 expanded)
%              Number of leaves         :   11 (  17 expanded)
%              Depth                    :   12
%              Number of atoms          :  100 ( 184 expanded)
%              Number of equality atoms :   26 (  47 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f56,plain,(
    $false ),
    inference(subsumption_resolution,[],[f55,f27])).

fof(f27,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( k1_xboole_0 != sK1
    & r1_tarski(sK1,k3_subset_1(sK0,sK2))
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != X1
        & r1_tarski(X1,k3_subset_1(X0,X2))
        & r1_tarski(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X0)) )
   => ( k1_xboole_0 != sK1
      & r1_tarski(sK1,k3_subset_1(sK0,sK2))
      & r1_tarski(sK1,sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X0))
       => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
            & r1_tarski(X1,X2) )
         => k1_xboole_0 = X1 ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
          & r1_tarski(X1,X2) )
       => k1_xboole_0 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_subset_1)).

fof(f55,plain,(
    k1_xboole_0 = sK1 ),
    inference(resolution,[],[f54,f29])).

fof(f29,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f13,f19])).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f54,plain,(
    ! [X2] : ~ r2_hidden(X2,sK1) ),
    inference(forward_demodulation,[],[f53,f28])).

fof(f28,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f53,plain,(
    ! [X2] : ~ r2_hidden(X2,k4_xboole_0(sK1,k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f51,f44])).

fof(f44,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f42,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f42,plain,(
    r1_tarski(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(backward_demodulation,[],[f26,f41])).

fof(f41,plain,(
    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) ),
    inference(resolution,[],[f24,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f24,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f26,plain,(
    r1_tarski(sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f51,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k4_xboole_0(sK1,k1_xboole_0))
      | ~ r1_xboole_0(sK1,sK2) ) ),
    inference(superposition,[],[f38,f40])).

fof(f40,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f25,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

% (8431)Refutation not found, incomplete strategy% (8431)------------------------------
% (8431)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (8431)Termination reason: Refutation not found, incomplete strategy

% (8431)Memory used [KB]: 10618
% (8431)Time elapsed: 0.125 s
% (8431)------------------------------
% (8431)------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f25,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f32,f30])).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f14,f21])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n016.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 20:44:49 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.51  % (8419)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.51  % (8419)Refutation not found, incomplete strategy% (8419)------------------------------
% 0.22/0.51  % (8419)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (8419)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (8419)Memory used [KB]: 1663
% 0.22/0.51  % (8419)Time elapsed: 0.100 s
% 0.22/0.51  % (8419)------------------------------
% 0.22/0.51  % (8419)------------------------------
% 0.22/0.52  % (8432)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.20/0.52  % (8440)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.20/0.53  % (8439)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.20/0.53  % (8432)Refutation not found, incomplete strategy% (8432)------------------------------
% 1.20/0.53  % (8432)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.20/0.53  % (8441)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.20/0.53  % (8432)Termination reason: Refutation not found, incomplete strategy
% 1.20/0.53  
% 1.20/0.53  % (8432)Memory used [KB]: 10618
% 1.20/0.53  % (8432)Time elapsed: 0.112 s
% 1.20/0.53  % (8432)------------------------------
% 1.20/0.53  % (8432)------------------------------
% 1.20/0.53  % (8429)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.20/0.53  % (8431)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.20/0.53  % (8429)Refutation found. Thanks to Tanya!
% 1.20/0.53  % SZS status Theorem for theBenchmark
% 1.20/0.53  % SZS output start Proof for theBenchmark
% 1.20/0.53  fof(f56,plain,(
% 1.20/0.53    $false),
% 1.20/0.53    inference(subsumption_resolution,[],[f55,f27])).
% 1.20/0.53  fof(f27,plain,(
% 1.20/0.53    k1_xboole_0 != sK1),
% 1.20/0.53    inference(cnf_transformation,[],[f18])).
% 1.20/0.53  fof(f18,plain,(
% 1.20/0.53    k1_xboole_0 != sK1 & r1_tarski(sK1,k3_subset_1(sK0,sK2)) & r1_tarski(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 1.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f17])).
% 1.20/0.53  fof(f17,plain,(
% 1.20/0.53    ? [X0,X1,X2] : (k1_xboole_0 != X1 & r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(X0))) => (k1_xboole_0 != sK1 & r1_tarski(sK1,k3_subset_1(sK0,sK2)) & r1_tarski(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 1.20/0.53    introduced(choice_axiom,[])).
% 1.20/0.53  fof(f12,plain,(
% 1.20/0.53    ? [X0,X1,X2] : (k1_xboole_0 != X1 & r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.20/0.53    inference(flattening,[],[f11])).
% 1.20/0.53  fof(f11,plain,(
% 1.20/0.53    ? [X0,X1,X2] : ((k1_xboole_0 != X1 & (r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.20/0.53    inference(ennf_transformation,[],[f9])).
% 1.20/0.53  fof(f9,negated_conjecture,(
% 1.20/0.53    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 1.20/0.53    inference(negated_conjecture,[],[f8])).
% 1.20/0.53  fof(f8,conjecture,(
% 1.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 1.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_subset_1)).
% 1.20/0.53  fof(f55,plain,(
% 1.20/0.53    k1_xboole_0 = sK1),
% 1.20/0.53    inference(resolution,[],[f54,f29])).
% 1.20/0.53  fof(f29,plain,(
% 1.20/0.53    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 1.20/0.53    inference(cnf_transformation,[],[f20])).
% 1.20/0.53  fof(f20,plain,(
% 1.20/0.53    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 1.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f13,f19])).
% 1.20/0.53  fof(f19,plain,(
% 1.20/0.53    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 1.20/0.53    introduced(choice_axiom,[])).
% 1.20/0.53  fof(f13,plain,(
% 1.20/0.53    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.20/0.53    inference(ennf_transformation,[],[f2])).
% 1.20/0.53  fof(f2,axiom,(
% 1.20/0.53    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.20/0.53  fof(f54,plain,(
% 1.20/0.53    ( ! [X2] : (~r2_hidden(X2,sK1)) )),
% 1.20/0.53    inference(forward_demodulation,[],[f53,f28])).
% 1.20/0.53  fof(f28,plain,(
% 1.20/0.53    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.20/0.53    inference(cnf_transformation,[],[f5])).
% 1.20/0.53  fof(f5,axiom,(
% 1.20/0.53    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.20/0.53  fof(f53,plain,(
% 1.20/0.53    ( ! [X2] : (~r2_hidden(X2,k4_xboole_0(sK1,k1_xboole_0))) )),
% 1.20/0.53    inference(subsumption_resolution,[],[f51,f44])).
% 1.20/0.53  fof(f44,plain,(
% 1.20/0.53    r1_xboole_0(sK1,sK2)),
% 1.20/0.53    inference(resolution,[],[f42,f37])).
% 1.20/0.53  fof(f37,plain,(
% 1.20/0.53    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 1.20/0.53    inference(cnf_transformation,[],[f16])).
% 1.20/0.53  fof(f16,plain,(
% 1.20/0.53    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 1.20/0.53    inference(ennf_transformation,[],[f4])).
% 1.20/0.53  fof(f4,axiom,(
% 1.20/0.53    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 1.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).
% 1.20/0.53  fof(f42,plain,(
% 1.20/0.53    r1_tarski(sK1,k4_xboole_0(sK0,sK2))),
% 1.20/0.53    inference(backward_demodulation,[],[f26,f41])).
% 1.20/0.53  fof(f41,plain,(
% 1.20/0.53    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)),
% 1.20/0.53    inference(resolution,[],[f24,f33])).
% 1.20/0.53  fof(f33,plain,(
% 1.20/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 1.20/0.53    inference(cnf_transformation,[],[f15])).
% 1.20/0.53  fof(f15,plain,(
% 1.20/0.53    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.20/0.53    inference(ennf_transformation,[],[f7])).
% 1.20/0.53  fof(f7,axiom,(
% 1.20/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 1.20/0.53  fof(f24,plain,(
% 1.20/0.53    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 1.20/0.53    inference(cnf_transformation,[],[f18])).
% 1.20/0.53  fof(f26,plain,(
% 1.20/0.53    r1_tarski(sK1,k3_subset_1(sK0,sK2))),
% 1.20/0.53    inference(cnf_transformation,[],[f18])).
% 1.20/0.53  fof(f51,plain,(
% 1.20/0.53    ( ! [X2] : (~r2_hidden(X2,k4_xboole_0(sK1,k1_xboole_0)) | ~r1_xboole_0(sK1,sK2)) )),
% 1.20/0.53    inference(superposition,[],[f38,f40])).
% 1.20/0.53  fof(f40,plain,(
% 1.20/0.53    k1_xboole_0 = k4_xboole_0(sK1,sK2)),
% 1.20/0.53    inference(resolution,[],[f25,f35])).
% 1.20/0.53  fof(f35,plain,(
% 1.20/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) )),
% 1.20/0.53    inference(cnf_transformation,[],[f23])).
% 1.20/0.53  fof(f23,plain,(
% 1.20/0.53    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 1.20/0.53    inference(nnf_transformation,[],[f3])).
% 1.20/0.53  % (8431)Refutation not found, incomplete strategy% (8431)------------------------------
% 1.20/0.53  % (8431)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.20/0.53  % (8431)Termination reason: Refutation not found, incomplete strategy
% 1.20/0.53  
% 1.20/0.53  % (8431)Memory used [KB]: 10618
% 1.20/0.53  % (8431)Time elapsed: 0.125 s
% 1.20/0.53  % (8431)------------------------------
% 1.20/0.53  % (8431)------------------------------
% 1.20/0.53  fof(f3,axiom,(
% 1.20/0.53    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 1.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.20/0.53  fof(f25,plain,(
% 1.20/0.53    r1_tarski(sK1,sK2)),
% 1.20/0.53    inference(cnf_transformation,[],[f18])).
% 1.20/0.53  fof(f38,plain,(
% 1.20/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~r1_xboole_0(X0,X1)) )),
% 1.20/0.53    inference(definition_unfolding,[],[f32,f30])).
% 1.20/0.53  fof(f30,plain,(
% 1.20/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.20/0.53    inference(cnf_transformation,[],[f6])).
% 1.20/0.53  fof(f6,axiom,(
% 1.20/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.20/0.53  fof(f32,plain,(
% 1.20/0.53    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 1.20/0.53    inference(cnf_transformation,[],[f22])).
% 1.20/0.53  fof(f22,plain,(
% 1.20/0.53    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f14,f21])).
% 1.20/0.53  fof(f21,plain,(
% 1.20/0.53    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 1.20/0.53    introduced(choice_axiom,[])).
% 1.20/0.53  fof(f14,plain,(
% 1.20/0.53    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.20/0.53    inference(ennf_transformation,[],[f10])).
% 1.20/0.53  fof(f10,plain,(
% 1.20/0.53    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.20/0.53    inference(rectify,[],[f1])).
% 1.20/0.53  fof(f1,axiom,(
% 1.20/0.53    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.20/0.53  % SZS output end Proof for theBenchmark
% 1.20/0.53  % (8429)------------------------------
% 1.20/0.53  % (8429)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.20/0.53  % (8429)Termination reason: Refutation
% 1.20/0.53  
% 1.20/0.53  % (8429)Memory used [KB]: 10618
% 1.20/0.53  % (8429)Time elapsed: 0.110 s
% 1.20/0.53  % (8429)------------------------------
% 1.20/0.53  % (8429)------------------------------
% 1.34/0.54  % (8415)Success in time 0.166 s
%------------------------------------------------------------------------------
