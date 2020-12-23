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
% DateTime   : Thu Dec  3 12:37:51 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   41 ( 297 expanded)
%              Number of leaves         :    8 (  88 expanded)
%              Depth                    :   11
%              Number of atoms          :   97 (1272 expanded)
%              Number of equality atoms :   85 (1175 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f96,plain,(
    $false ),
    inference(subsumption_resolution,[],[f95,f93])).

fof(f93,plain,(
    k1_xboole_0 != k1_tarski(sK0) ),
    inference(backward_demodulation,[],[f85,f91])).

fof(f91,plain,(
    k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f68,f85])).

fof(f68,plain,
    ( k1_xboole_0 = sK2
    | sK2 = k1_tarski(sK0) ),
    inference(resolution,[],[f27,f47])).

fof(f47,plain,(
    r1_tarski(sK2,k1_tarski(sK0)) ),
    inference(superposition,[],[f45,f16])).

fof(f16,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ( k1_xboole_0 != sK2
      | sK1 != k1_tarski(sK0) )
    & ( sK2 != k1_tarski(sK0)
      | k1_xboole_0 != sK1 )
    & ( sK2 != k1_tarski(sK0)
      | sK1 != k1_tarski(sK0) )
    & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f12])).

% (4605)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
fof(f12,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_xboole_0 != X2
          | k1_tarski(X0) != X1 )
        & ( k1_tarski(X0) != X2
          | k1_xboole_0 != X1 )
        & ( k1_tarski(X0) != X2
          | k1_tarski(X0) != X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) )
   => ( ( k1_xboole_0 != sK2
        | sK1 != k1_tarski(sK0) )
      & ( sK2 != k1_tarski(sK0)
        | k1_xboole_0 != sK1 )
      & ( sK2 != k1_tarski(sK0)
        | sK1 != k1_tarski(sK0) )
      & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

% (4601)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f45,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f22,f43])).

fof(f43,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2) ),
    inference(superposition,[],[f36,f24])).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f36,plain,(
    ! [X2,X1] : k2_xboole_0(X1,X2) = k3_tarski(k2_tarski(X2,X1)) ),
    inference(superposition,[],[f24,f23])).

fof(f23,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

% (4589)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
fof(f22,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f85,plain,(
    sK2 != k1_tarski(sK0) ),
    inference(subsumption_resolution,[],[f18,f84])).

fof(f84,plain,(
    k1_xboole_0 = sK1 ),
    inference(global_subsumption,[],[f19,f17,f67,f68])).

fof(f67,plain,
    ( sK1 = k1_tarski(sK0)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f27,f34])).

fof(f34,plain,(
    r1_tarski(sK1,k1_tarski(sK0)) ),
    inference(superposition,[],[f22,f16])).

fof(f17,plain,
    ( sK2 != k1_tarski(sK0)
    | sK1 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f19,plain,
    ( sK1 != k1_tarski(sK0)
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f13])).

fof(f18,plain,
    ( sK2 != k1_tarski(sK0)
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f13])).

fof(f95,plain,(
    k1_xboole_0 = k1_tarski(sK0) ),
    inference(forward_demodulation,[],[f94,f91])).

fof(f94,plain,(
    sK2 = k1_tarski(sK0) ),
    inference(forward_demodulation,[],[f86,f59])).

fof(f59,plain,(
    ! [X1] : k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f57,f43])).

fof(f57,plain,(
    ! [X2] : k2_xboole_0(X2,k1_xboole_0) = X2 ),
    inference(forward_demodulation,[],[f55,f20])).

fof(f20,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f55,plain,(
    ! [X2] : k2_xboole_0(X2,k1_xboole_0) = k4_xboole_0(X2,k1_xboole_0) ),
    inference(superposition,[],[f26,f20])).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f86,plain,(
    k1_tarski(sK0) = k2_xboole_0(k1_xboole_0,sK2) ),
    inference(backward_demodulation,[],[f16,f84])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:34:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (4591)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.50  % (4596)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.51  % (4609)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.51  % (4590)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.51  % (4596)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f96,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(subsumption_resolution,[],[f95,f93])).
% 0.20/0.51  fof(f93,plain,(
% 0.20/0.51    k1_xboole_0 != k1_tarski(sK0)),
% 0.20/0.51    inference(backward_demodulation,[],[f85,f91])).
% 0.20/0.51  fof(f91,plain,(
% 0.20/0.51    k1_xboole_0 = sK2),
% 0.20/0.51    inference(subsumption_resolution,[],[f68,f85])).
% 0.20/0.51  fof(f68,plain,(
% 0.20/0.51    k1_xboole_0 = sK2 | sK2 = k1_tarski(sK0)),
% 0.20/0.51    inference(resolution,[],[f27,f47])).
% 0.20/0.51  fof(f47,plain,(
% 0.20/0.51    r1_tarski(sK2,k1_tarski(sK0))),
% 0.20/0.51    inference(superposition,[],[f45,f16])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 0.20/0.51    inference(cnf_transformation,[],[f13])).
% 0.20/0.51  fof(f13,plain,(
% 0.20/0.51    (k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f12])).
% 0.20/0.51  % (4605)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.51  fof(f12,plain,(
% 0.20/0.51    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2)) => ((k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  % (4601)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  fof(f11,plain,(
% 0.20/0.51    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.20/0.51    inference(ennf_transformation,[],[f10])).
% 0.20/0.51  fof(f10,negated_conjecture,(
% 0.20/0.51    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.20/0.51    inference(negated_conjecture,[],[f9])).
% 0.20/0.51  fof(f9,conjecture,(
% 0.20/0.51    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 0.20/0.51  fof(f45,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X0))) )),
% 0.20/0.51    inference(superposition,[],[f22,f43])).
% 0.20/0.51  fof(f43,plain,(
% 0.20/0.51    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2)) )),
% 0.20/0.51    inference(superposition,[],[f36,f24])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,axiom,(
% 0.20/0.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.20/0.51  fof(f36,plain,(
% 0.20/0.51    ( ! [X2,X1] : (k2_xboole_0(X1,X2) = k3_tarski(k2_tarski(X2,X1))) )),
% 0.20/0.51    inference(superposition,[],[f24,f23])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.20/0.51  % (4589)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r1_tarski(X0,k1_tarski(X1)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f15])).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 0.20/0.51    inference(flattening,[],[f14])).
% 0.20/0.51  fof(f14,plain,(
% 0.20/0.51    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 0.20/0.51    inference(nnf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,axiom,(
% 0.20/0.51    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 0.20/0.51  fof(f85,plain,(
% 0.20/0.51    sK2 != k1_tarski(sK0)),
% 0.20/0.51    inference(subsumption_resolution,[],[f18,f84])).
% 0.20/0.51  fof(f84,plain,(
% 0.20/0.51    k1_xboole_0 = sK1),
% 0.20/0.51    inference(global_subsumption,[],[f19,f17,f67,f68])).
% 0.20/0.51  fof(f67,plain,(
% 0.20/0.51    sK1 = k1_tarski(sK0) | k1_xboole_0 = sK1),
% 0.20/0.51    inference(resolution,[],[f27,f34])).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    r1_tarski(sK1,k1_tarski(sK0))),
% 0.20/0.51    inference(superposition,[],[f22,f16])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f13])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    sK1 != k1_tarski(sK0) | k1_xboole_0 != sK2),
% 0.20/0.51    inference(cnf_transformation,[],[f13])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1),
% 0.20/0.51    inference(cnf_transformation,[],[f13])).
% 0.20/0.51  fof(f95,plain,(
% 0.20/0.51    k1_xboole_0 = k1_tarski(sK0)),
% 0.20/0.51    inference(forward_demodulation,[],[f94,f91])).
% 0.20/0.51  fof(f94,plain,(
% 0.20/0.51    sK2 = k1_tarski(sK0)),
% 0.20/0.51    inference(forward_demodulation,[],[f86,f59])).
% 0.20/0.51  fof(f59,plain,(
% 0.20/0.51    ( ! [X1] : (k2_xboole_0(k1_xboole_0,X1) = X1) )),
% 0.20/0.51    inference(superposition,[],[f57,f43])).
% 0.20/0.51  fof(f57,plain,(
% 0.20/0.51    ( ! [X2] : (k2_xboole_0(X2,k1_xboole_0) = X2) )),
% 0.20/0.51    inference(forward_demodulation,[],[f55,f20])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.20/0.51  fof(f55,plain,(
% 0.20/0.51    ( ! [X2] : (k2_xboole_0(X2,k1_xboole_0) = k4_xboole_0(X2,k1_xboole_0)) )),
% 0.20/0.51    inference(superposition,[],[f26,f20])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).
% 0.20/0.51  fof(f86,plain,(
% 0.20/0.51    k1_tarski(sK0) = k2_xboole_0(k1_xboole_0,sK2)),
% 0.20/0.51    inference(backward_demodulation,[],[f16,f84])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (4596)------------------------------
% 0.20/0.51  % (4596)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (4596)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (4596)Memory used [KB]: 6268
% 0.20/0.51  % (4596)Time elapsed: 0.097 s
% 0.20/0.51  % (4596)------------------------------
% 0.20/0.51  % (4596)------------------------------
% 0.20/0.51  % (4597)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.51  % (4610)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.52  % (4588)Success in time 0.159 s
%------------------------------------------------------------------------------
