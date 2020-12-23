%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:41 EST 2020

% Result     : Theorem 1.32s
% Output     : Refutation 1.44s
% Verified   : 
% Statistics : Number of formulae       :   46 (  57 expanded)
%              Number of leaves         :   12 (  17 expanded)
%              Depth                    :   14
%              Number of atoms          :  102 ( 113 expanded)
%              Number of equality atoms :   41 (  52 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f62,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f61])).

fof(f61,plain,(
    sK0 != sK0 ),
    inference(superposition,[],[f38,f57])).

fof(f57,plain,(
    ! [X0] : k4_yellow_0(k3_lattice3(k1_lattice3(X0))) = X0 ),
    inference(subsumption_resolution,[],[f56,f48])).

fof(f48,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(superposition,[],[f32,f31])).

fof(f31,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f32,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f56,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,X0)
      | k4_yellow_0(k3_lattice3(k1_lattice3(X0))) = X0 ) ),
    inference(forward_demodulation,[],[f55,f40])).

fof(f40,plain,(
    ! [X0] : k3_tarski(k9_setfam_1(X0)) = X0 ),
    inference(definition_unfolding,[],[f27,f26])).

fof(f26,plain,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

fof(f27,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(f55,plain,(
    ! [X0] :
      ( k4_yellow_0(k3_lattice3(k1_lattice3(X0))) = X0
      | ~ r1_tarski(k3_tarski(k9_setfam_1(X0)),X0) ) ),
    inference(forward_demodulation,[],[f54,f40])).

fof(f54,plain,(
    ! [X0] :
      ( k3_tarski(k9_setfam_1(X0)) = k4_yellow_0(k3_lattice3(k1_lattice3(X0)))
      | ~ r1_tarski(k3_tarski(k9_setfam_1(X0)),X0) ) ),
    inference(forward_demodulation,[],[f53,f41])).

fof(f41,plain,(
    ! [X0] : k3_lattice3(k1_lattice3(X0)) = k2_yellow_1(k9_setfam_1(X0)) ),
    inference(definition_unfolding,[],[f29,f28])).

fof(f28,plain,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_yellow_1)).

fof(f29,plain,(
    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_yellow_1)).

fof(f53,plain,(
    ! [X0] :
      ( k3_tarski(k9_setfam_1(X0)) = k4_yellow_0(k2_yellow_1(k9_setfam_1(X0)))
      | ~ r1_tarski(k3_tarski(k9_setfam_1(X0)),X0) ) ),
    inference(subsumption_resolution,[],[f51,f39])).

fof(f39,plain,(
    ! [X0] : ~ v1_xboole_0(k9_setfam_1(X0)) ),
    inference(definition_unfolding,[],[f25,f26])).

fof(f25,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

% (10043)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
fof(f6,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f51,plain,(
    ! [X0] :
      ( k3_tarski(k9_setfam_1(X0)) = k4_yellow_0(k2_yellow_1(k9_setfam_1(X0)))
      | v1_xboole_0(k9_setfam_1(X0))
      | ~ r1_tarski(k3_tarski(k9_setfam_1(X0)),X0) ) ),
    inference(resolution,[],[f30,f46])).

fof(f46,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k9_setfam_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k9_setfam_1(X0) != X1 ) ),
    inference(definition_unfolding,[],[f35,f26])).

fof(f35,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK1(X0,X1),X0)
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( r1_tarski(sK1(X0,X1),X0)
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f21,f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK1(X0,X1),X0)
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( r1_tarski(sK1(X0,X1),X0)
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f30,plain,(
    ! [X0] :
      ( ~ r2_hidden(k3_tarski(X0),X0)
      | k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k3_tarski(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k3_tarski(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( r2_hidden(k3_tarski(X0),X0)
       => k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_yellow_1)).

fof(f38,plain,(
    sK0 != k4_yellow_0(k3_lattice3(k1_lattice3(sK0))) ),
    inference(definition_unfolding,[],[f24,f28])).

fof(f24,plain,(
    sK0 != k4_yellow_0(k3_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    sK0 != k4_yellow_0(k3_yellow_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f18])).

fof(f18,plain,
    ( ? [X0] : k4_yellow_0(k3_yellow_1(X0)) != X0
   => sK0 != k4_yellow_0(k3_yellow_1(sK0)) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] : k4_yellow_0(k3_yellow_1(X0)) != X0 ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] : k4_yellow_0(k3_yellow_1(X0)) = X0 ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] : k4_yellow_0(k3_yellow_1(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_yellow_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:18:30 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.32/0.53  % (10025)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.32/0.53  % (10027)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.32/0.53  % (10025)Refutation found. Thanks to Tanya!
% 1.32/0.53  % SZS status Theorem for theBenchmark
% 1.32/0.53  % (10041)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.32/0.54  % (10033)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.32/0.54  % SZS output start Proof for theBenchmark
% 1.32/0.54  fof(f62,plain,(
% 1.32/0.54    $false),
% 1.32/0.54    inference(trivial_inequality_removal,[],[f61])).
% 1.32/0.54  fof(f61,plain,(
% 1.32/0.54    sK0 != sK0),
% 1.32/0.54    inference(superposition,[],[f38,f57])).
% 1.32/0.54  fof(f57,plain,(
% 1.32/0.54    ( ! [X0] : (k4_yellow_0(k3_lattice3(k1_lattice3(X0))) = X0) )),
% 1.32/0.54    inference(subsumption_resolution,[],[f56,f48])).
% 1.32/0.54  fof(f48,plain,(
% 1.32/0.54    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 1.32/0.54    inference(superposition,[],[f32,f31])).
% 1.32/0.54  fof(f31,plain,(
% 1.32/0.54    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.32/0.54    inference(cnf_transformation,[],[f13])).
% 1.32/0.54  fof(f13,plain,(
% 1.32/0.54    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.32/0.54    inference(rectify,[],[f1])).
% 1.32/0.54  fof(f1,axiom,(
% 1.32/0.54    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.32/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.32/0.54  fof(f32,plain,(
% 1.32/0.54    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f2])).
% 1.32/0.54  fof(f2,axiom,(
% 1.32/0.54    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.32/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.32/0.54  fof(f56,plain,(
% 1.32/0.54    ( ! [X0] : (~r1_tarski(X0,X0) | k4_yellow_0(k3_lattice3(k1_lattice3(X0))) = X0) )),
% 1.32/0.54    inference(forward_demodulation,[],[f55,f40])).
% 1.32/0.54  fof(f40,plain,(
% 1.32/0.54    ( ! [X0] : (k3_tarski(k9_setfam_1(X0)) = X0) )),
% 1.32/0.54    inference(definition_unfolding,[],[f27,f26])).
% 1.32/0.54  fof(f26,plain,(
% 1.32/0.54    ( ! [X0] : (k1_zfmisc_1(X0) = k9_setfam_1(X0)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f7])).
% 1.32/0.54  fof(f7,axiom,(
% 1.32/0.54    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0)),
% 1.32/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).
% 1.32/0.54  fof(f27,plain,(
% 1.32/0.54    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 1.32/0.54    inference(cnf_transformation,[],[f5])).
% 1.32/0.54  fof(f5,axiom,(
% 1.32/0.54    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 1.32/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).
% 1.32/0.54  fof(f55,plain,(
% 1.32/0.54    ( ! [X0] : (k4_yellow_0(k3_lattice3(k1_lattice3(X0))) = X0 | ~r1_tarski(k3_tarski(k9_setfam_1(X0)),X0)) )),
% 1.32/0.54    inference(forward_demodulation,[],[f54,f40])).
% 1.32/0.54  fof(f54,plain,(
% 1.32/0.54    ( ! [X0] : (k3_tarski(k9_setfam_1(X0)) = k4_yellow_0(k3_lattice3(k1_lattice3(X0))) | ~r1_tarski(k3_tarski(k9_setfam_1(X0)),X0)) )),
% 1.32/0.54    inference(forward_demodulation,[],[f53,f41])).
% 1.32/0.54  fof(f41,plain,(
% 1.32/0.54    ( ! [X0] : (k3_lattice3(k1_lattice3(X0)) = k2_yellow_1(k9_setfam_1(X0))) )),
% 1.32/0.54    inference(definition_unfolding,[],[f29,f28])).
% 1.32/0.54  fof(f28,plain,(
% 1.32/0.54    ( ! [X0] : (k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))) )),
% 1.32/0.54    inference(cnf_transformation,[],[f8])).
% 1.32/0.54  fof(f8,axiom,(
% 1.32/0.54    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))),
% 1.32/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_yellow_1)).
% 1.32/0.54  fof(f29,plain,(
% 1.32/0.54    ( ! [X0] : (k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0))) )),
% 1.32/0.54    inference(cnf_transformation,[],[f10])).
% 1.32/0.55  fof(f10,axiom,(
% 1.32/0.55    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0))),
% 1.32/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_yellow_1)).
% 1.32/0.55  fof(f53,plain,(
% 1.32/0.55    ( ! [X0] : (k3_tarski(k9_setfam_1(X0)) = k4_yellow_0(k2_yellow_1(k9_setfam_1(X0))) | ~r1_tarski(k3_tarski(k9_setfam_1(X0)),X0)) )),
% 1.32/0.55    inference(subsumption_resolution,[],[f51,f39])).
% 1.32/0.55  fof(f39,plain,(
% 1.32/0.55    ( ! [X0] : (~v1_xboole_0(k9_setfam_1(X0))) )),
% 1.32/0.55    inference(definition_unfolding,[],[f25,f26])).
% 1.32/0.55  fof(f25,plain,(
% 1.32/0.55    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.32/0.55    inference(cnf_transformation,[],[f6])).
% 1.32/0.55  % (10043)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.32/0.55  fof(f6,axiom,(
% 1.32/0.55    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.32/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.32/0.55  fof(f51,plain,(
% 1.32/0.55    ( ! [X0] : (k3_tarski(k9_setfam_1(X0)) = k4_yellow_0(k2_yellow_1(k9_setfam_1(X0))) | v1_xboole_0(k9_setfam_1(X0)) | ~r1_tarski(k3_tarski(k9_setfam_1(X0)),X0)) )),
% 1.32/0.55    inference(resolution,[],[f30,f46])).
% 1.32/0.55  fof(f46,plain,(
% 1.32/0.55    ( ! [X0,X3] : (r2_hidden(X3,k9_setfam_1(X0)) | ~r1_tarski(X3,X0)) )),
% 1.32/0.55    inference(equality_resolution,[],[f44])).
% 1.32/0.55  fof(f44,plain,(
% 1.32/0.55    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k9_setfam_1(X0) != X1) )),
% 1.32/0.55    inference(definition_unfolding,[],[f35,f26])).
% 1.32/0.55  fof(f35,plain,(
% 1.32/0.55    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 1.32/0.55    inference(cnf_transformation,[],[f23])).
% 1.32/0.55  fof(f23,plain,(
% 1.32/0.55    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK1(X0,X1),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r1_tarski(sK1(X0,X1),X0) | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.32/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f21,f22])).
% 1.32/0.55  fof(f22,plain,(
% 1.32/0.55    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK1(X0,X1),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r1_tarski(sK1(X0,X1),X0) | r2_hidden(sK1(X0,X1),X1))))),
% 1.32/0.55    introduced(choice_axiom,[])).
% 1.32/0.55  fof(f21,plain,(
% 1.32/0.55    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.32/0.55    inference(rectify,[],[f20])).
% 1.32/0.55  fof(f20,plain,(
% 1.32/0.55    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.32/0.55    inference(nnf_transformation,[],[f3])).
% 1.32/0.55  fof(f3,axiom,(
% 1.32/0.55    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.32/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.32/0.55  fof(f30,plain,(
% 1.32/0.55    ( ! [X0] : (~r2_hidden(k3_tarski(X0),X0) | k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | v1_xboole_0(X0)) )),
% 1.32/0.55    inference(cnf_transformation,[],[f16])).
% 1.44/0.55  fof(f16,plain,(
% 1.44/0.55    ! [X0] : (k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k3_tarski(X0),X0) | v1_xboole_0(X0))),
% 1.44/0.55    inference(flattening,[],[f15])).
% 1.44/0.55  fof(f15,plain,(
% 1.44/0.55    ! [X0] : ((k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k3_tarski(X0),X0)) | v1_xboole_0(X0))),
% 1.44/0.55    inference(ennf_transformation,[],[f9])).
% 1.44/0.55  fof(f9,axiom,(
% 1.44/0.55    ! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k3_tarski(X0),X0) => k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))))),
% 1.44/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_yellow_1)).
% 1.44/0.55  fof(f38,plain,(
% 1.44/0.55    sK0 != k4_yellow_0(k3_lattice3(k1_lattice3(sK0)))),
% 1.44/0.55    inference(definition_unfolding,[],[f24,f28])).
% 1.44/0.55  fof(f24,plain,(
% 1.44/0.55    sK0 != k4_yellow_0(k3_yellow_1(sK0))),
% 1.44/0.55    inference(cnf_transformation,[],[f19])).
% 1.44/0.55  fof(f19,plain,(
% 1.44/0.55    sK0 != k4_yellow_0(k3_yellow_1(sK0))),
% 1.44/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f18])).
% 1.44/0.55  fof(f18,plain,(
% 1.44/0.55    ? [X0] : k4_yellow_0(k3_yellow_1(X0)) != X0 => sK0 != k4_yellow_0(k3_yellow_1(sK0))),
% 1.44/0.55    introduced(choice_axiom,[])).
% 1.44/0.55  fof(f14,plain,(
% 1.44/0.55    ? [X0] : k4_yellow_0(k3_yellow_1(X0)) != X0),
% 1.44/0.55    inference(ennf_transformation,[],[f12])).
% 1.44/0.55  fof(f12,negated_conjecture,(
% 1.44/0.55    ~! [X0] : k4_yellow_0(k3_yellow_1(X0)) = X0),
% 1.44/0.55    inference(negated_conjecture,[],[f11])).
% 1.44/0.55  fof(f11,conjecture,(
% 1.44/0.55    ! [X0] : k4_yellow_0(k3_yellow_1(X0)) = X0),
% 1.44/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_yellow_1)).
% 1.44/0.55  % SZS output end Proof for theBenchmark
% 1.44/0.55  % (10025)------------------------------
% 1.44/0.55  % (10025)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.55  % (10025)Termination reason: Refutation
% 1.44/0.55  
% 1.44/0.55  % (10025)Memory used [KB]: 10618
% 1.44/0.55  % (10025)Time elapsed: 0.109 s
% 1.44/0.55  % (10025)------------------------------
% 1.44/0.55  % (10025)------------------------------
% 1.44/0.55  % (10018)Success in time 0.184 s
%------------------------------------------------------------------------------
