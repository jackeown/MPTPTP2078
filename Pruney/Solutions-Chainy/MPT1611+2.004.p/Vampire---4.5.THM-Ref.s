%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:39 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   50 (  59 expanded)
%              Number of leaves         :   12 (  16 expanded)
%              Depth                    :   12
%              Number of atoms          :  105 ( 114 expanded)
%              Number of equality atoms :   32 (  41 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f74,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f73])).

fof(f73,plain,(
    sK0 != sK0 ),
    inference(superposition,[],[f40,f71])).

fof(f71,plain,(
    ! [X0] : k4_yellow_0(k2_yellow_1(k9_setfam_1(X0))) = X0 ),
    inference(global_subsumption,[],[f70])).

fof(f70,plain,(
    ! [X0] : k4_yellow_0(k2_yellow_1(k9_setfam_1(X0))) = X0 ),
    inference(subsumption_resolution,[],[f69,f45])).

fof(f45,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    ! [X0] :
      ( ~ r1_tarski(X0,X0)
      | k4_yellow_0(k2_yellow_1(k9_setfam_1(X0))) = X0 ) ),
    inference(forward_demodulation,[],[f68,f42])).

fof(f42,plain,(
    ! [X0] : k3_tarski(k9_setfam_1(X0)) = X0 ),
    inference(definition_unfolding,[],[f29,f28])).

fof(f28,plain,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

fof(f29,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(f68,plain,(
    ! [X0] :
      ( k4_yellow_0(k2_yellow_1(k9_setfam_1(X0))) = X0
      | ~ r1_tarski(k3_tarski(k9_setfam_1(X0)),X0) ) ),
    inference(forward_demodulation,[],[f66,f42])).

fof(f66,plain,(
    ! [X0] :
      ( k3_tarski(k9_setfam_1(X0)) = k4_yellow_0(k2_yellow_1(k9_setfam_1(X0)))
      | ~ r1_tarski(k3_tarski(k9_setfam_1(X0)),X0) ) ),
    inference(resolution,[],[f65,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,k9_setfam_1(X0))
      | ~ r1_tarski(X1,X0) ) ),
    inference(subsumption_resolution,[],[f49,f41])).

fof(f41,plain,(
    ! [X0] : ~ v1_xboole_0(k9_setfam_1(X0)) ),
    inference(definition_unfolding,[],[f27,f28])).

fof(f27,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f49,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k9_setfam_1(X0))
      | r2_hidden(X1,k9_setfam_1(X0))
      | ~ r1_tarski(X1,X0) ) ),
    inference(resolution,[],[f34,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k9_setfam_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f39,f28])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f65,plain,(
    ! [X0] :
      ( ~ r2_hidden(k3_tarski(X0),X0)
      | k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) ) ),
    inference(subsumption_resolution,[],[f31,f32])).

fof(f32,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK1(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f21])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f31,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k3_tarski(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k3_tarski(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k3_tarski(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( r2_hidden(k3_tarski(X0),X0)
       => k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow_1)).

fof(f40,plain,(
    sK0 != k4_yellow_0(k2_yellow_1(k9_setfam_1(sK0))) ),
    inference(definition_unfolding,[],[f26,f30])).

fof(f30,plain,(
    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow_1)).

fof(f26,plain,(
    sK0 != k4_yellow_0(k3_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    sK0 != k4_yellow_0(k3_yellow_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f17])).

fof(f17,plain,
    ( ? [X0] : k4_yellow_0(k3_yellow_1(X0)) != X0
   => sK0 != k4_yellow_0(k3_yellow_1(sK0)) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] : k4_yellow_0(k3_yellow_1(X0)) != X0 ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] : k4_yellow_0(k3_yellow_1(X0)) = X0 ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] : k4_yellow_0(k3_yellow_1(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_yellow_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:11:31 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.50  % (22326)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.50  % (22319)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (22319)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.51  % (22328)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.51  % (22335)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.51  % (22334)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f74,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(trivial_inequality_removal,[],[f73])).
% 0.20/0.51  fof(f73,plain,(
% 0.20/0.51    sK0 != sK0),
% 0.20/0.51    inference(superposition,[],[f40,f71])).
% 0.20/0.51  fof(f71,plain,(
% 0.20/0.51    ( ! [X0] : (k4_yellow_0(k2_yellow_1(k9_setfam_1(X0))) = X0) )),
% 0.20/0.51    inference(global_subsumption,[],[f70])).
% 0.20/0.51  fof(f70,plain,(
% 0.20/0.51    ( ! [X0] : (k4_yellow_0(k2_yellow_1(k9_setfam_1(X0))) = X0) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f69,f45])).
% 0.20/0.51  fof(f45,plain,(
% 0.20/0.51    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.51    inference(equality_resolution,[],[f36])).
% 0.20/0.51  fof(f36,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.20/0.51    inference(cnf_transformation,[],[f24])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.51    inference(flattening,[],[f23])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.51    inference(nnf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.51  fof(f69,plain,(
% 0.20/0.51    ( ! [X0] : (~r1_tarski(X0,X0) | k4_yellow_0(k2_yellow_1(k9_setfam_1(X0))) = X0) )),
% 0.20/0.51    inference(forward_demodulation,[],[f68,f42])).
% 0.20/0.51  fof(f42,plain,(
% 0.20/0.51    ( ! [X0] : (k3_tarski(k9_setfam_1(X0)) = X0) )),
% 0.20/0.51    inference(definition_unfolding,[],[f29,f28])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    ( ! [X0] : (k1_zfmisc_1(X0) = k9_setfam_1(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,axiom,(
% 0.20/0.51    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).
% 0.20/0.51  fof(f68,plain,(
% 0.20/0.51    ( ! [X0] : (k4_yellow_0(k2_yellow_1(k9_setfam_1(X0))) = X0 | ~r1_tarski(k3_tarski(k9_setfam_1(X0)),X0)) )),
% 0.20/0.51    inference(forward_demodulation,[],[f66,f42])).
% 0.20/0.51  fof(f66,plain,(
% 0.20/0.51    ( ! [X0] : (k3_tarski(k9_setfam_1(X0)) = k4_yellow_0(k2_yellow_1(k9_setfam_1(X0))) | ~r1_tarski(k3_tarski(k9_setfam_1(X0)),X0)) )),
% 0.20/0.51    inference(resolution,[],[f65,f50])).
% 0.20/0.51  fof(f50,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r2_hidden(X1,k9_setfam_1(X0)) | ~r1_tarski(X1,X0)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f49,f41])).
% 0.20/0.51  fof(f41,plain,(
% 0.20/0.51    ( ! [X0] : (~v1_xboole_0(k9_setfam_1(X0))) )),
% 0.20/0.51    inference(definition_unfolding,[],[f27,f28])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.20/0.51  fof(f49,plain,(
% 0.20/0.51    ( ! [X0,X1] : (v1_xboole_0(k9_setfam_1(X0)) | r2_hidden(X1,k9_setfam_1(X0)) | ~r1_tarski(X1,X0)) )),
% 0.20/0.51    inference(resolution,[],[f34,f43])).
% 0.20/0.51  fof(f43,plain,(
% 0.20/0.51    ( ! [X0,X1] : (m1_subset_1(X0,k9_setfam_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f39,f28])).
% 0.20/0.51  fof(f39,plain,(
% 0.20/0.51    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f25])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.51    inference(nnf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,axiom,(
% 0.20/0.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f16])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.20/0.51    inference(flattening,[],[f15])).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.20/0.51  fof(f65,plain,(
% 0.20/0.51    ( ! [X0] : (~r2_hidden(k3_tarski(X0),X0) | k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f31,f32])).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK1(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f21])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.51    inference(rectify,[],[f19])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.51    inference(nnf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    ( ! [X0] : (k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k3_tarski(X0),X0) | v1_xboole_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f14])).
% 0.20/0.51  fof(f14,plain,(
% 0.20/0.51    ! [X0] : (k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k3_tarski(X0),X0) | v1_xboole_0(X0))),
% 0.20/0.51    inference(flattening,[],[f13])).
% 0.20/0.51  fof(f13,plain,(
% 0.20/0.51    ! [X0] : ((k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k3_tarski(X0),X0)) | v1_xboole_0(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,axiom,(
% 0.20/0.51    ! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k3_tarski(X0),X0) => k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow_1)).
% 0.20/0.51  fof(f40,plain,(
% 0.20/0.51    sK0 != k4_yellow_0(k2_yellow_1(k9_setfam_1(sK0)))),
% 0.20/0.51    inference(definition_unfolding,[],[f26,f30])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    ( ! [X0] : (k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f9])).
% 0.20/0.51  fof(f9,axiom,(
% 0.20/0.51    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow_1)).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    sK0 != k4_yellow_0(k3_yellow_1(sK0))),
% 0.20/0.51    inference(cnf_transformation,[],[f18])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    sK0 != k4_yellow_0(k3_yellow_1(sK0))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ? [X0] : k4_yellow_0(k3_yellow_1(X0)) != X0 => sK0 != k4_yellow_0(k3_yellow_1(sK0))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f12,plain,(
% 0.20/0.51    ? [X0] : k4_yellow_0(k3_yellow_1(X0)) != X0),
% 0.20/0.51    inference(ennf_transformation,[],[f11])).
% 0.20/0.51  fof(f11,negated_conjecture,(
% 0.20/0.51    ~! [X0] : k4_yellow_0(k3_yellow_1(X0)) = X0),
% 0.20/0.51    inference(negated_conjecture,[],[f10])).
% 0.20/0.51  fof(f10,conjecture,(
% 0.20/0.51    ! [X0] : k4_yellow_0(k3_yellow_1(X0)) = X0),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_yellow_1)).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (22319)------------------------------
% 0.20/0.51  % (22319)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (22319)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (22319)Memory used [KB]: 10746
% 0.20/0.51  % (22319)Time elapsed: 0.089 s
% 0.20/0.51  % (22319)------------------------------
% 0.20/0.51  % (22319)------------------------------
% 0.20/0.51  % (22309)Success in time 0.147 s
%------------------------------------------------------------------------------
