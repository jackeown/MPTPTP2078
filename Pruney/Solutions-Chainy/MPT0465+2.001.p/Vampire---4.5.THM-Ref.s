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
% DateTime   : Thu Dec  3 12:47:30 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   47 (  99 expanded)
%              Number of leaves         :   12 (  39 expanded)
%              Depth                    :   18
%              Number of atoms          :  110 ( 333 expanded)
%              Number of equality atoms :    9 (  16 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f88,plain,(
    $false ),
    inference(subsumption_resolution,[],[f87,f26])).

fof(f26,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ~ r1_tarski(k6_subset_1(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)),k5_relat_1(sK0,k6_subset_1(sK1,sK2)))
    & v1_relat_1(sK2)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f23,f22,f21])).

fof(f21,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k6_subset_1(k5_relat_1(X0,X1),k5_relat_1(X0,X2)),k5_relat_1(X0,k6_subset_1(X1,X2)))
                & v1_relat_1(X2) )
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k6_subset_1(k5_relat_1(sK0,X1),k5_relat_1(sK0,X2)),k5_relat_1(sK0,k6_subset_1(X1,X2)))
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k6_subset_1(k5_relat_1(sK0,X1),k5_relat_1(sK0,X2)),k5_relat_1(sK0,k6_subset_1(X1,X2)))
            & v1_relat_1(X2) )
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ~ r1_tarski(k6_subset_1(k5_relat_1(sK0,sK1),k5_relat_1(sK0,X2)),k5_relat_1(sK0,k6_subset_1(sK1,X2)))
          & v1_relat_1(X2) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k6_subset_1(k5_relat_1(sK0,sK1),k5_relat_1(sK0,X2)),k5_relat_1(sK0,k6_subset_1(sK1,X2)))
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k6_subset_1(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)),k5_relat_1(sK0,k6_subset_1(sK1,sK2)))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k6_subset_1(k5_relat_1(X0,X1),k5_relat_1(X0,X2)),k5_relat_1(X0,k6_subset_1(X1,X2)))
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ! [X2] :
                ( v1_relat_1(X2)
               => r1_tarski(k6_subset_1(k5_relat_1(X0,X1),k5_relat_1(X0,X2)),k5_relat_1(X0,k6_subset_1(X1,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => r1_tarski(k6_subset_1(k5_relat_1(X0,X1),k5_relat_1(X0,X2)),k5_relat_1(X0,k6_subset_1(X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_relat_1)).

fof(f87,plain,(
    ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f86,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k4_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f31,f41])).

fof(f41,plain,(
    ! [X0,X1] : m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f33,f34])).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f33,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f86,plain,(
    ~ v1_relat_1(k4_xboole_0(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f85,f25])).

fof(f25,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f85,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k4_xboole_0(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f84,f26])).

fof(f84,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k4_xboole_0(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f79,f27])).

fof(f27,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f79,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k4_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f64,f68])).

fof(f68,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,sK1),k5_relat_1(sK0,k2_xboole_0(sK1,sK2)))
    | ~ v1_relat_1(k4_xboole_0(sK1,sK2)) ),
    inference(forward_demodulation,[],[f67,f35])).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f67,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,sK1),k5_relat_1(sK0,k2_xboole_0(sK2,sK1)))
    | ~ v1_relat_1(k4_xboole_0(sK1,sK2)) ),
    inference(forward_demodulation,[],[f66,f36])).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f66,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,sK1),k5_relat_1(sK0,k2_xboole_0(sK2,k4_xboole_0(sK1,sK2))))
    | ~ v1_relat_1(k4_xboole_0(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f65,f25])).

fof(f65,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,sK1),k5_relat_1(sK0,k2_xboole_0(sK2,k4_xboole_0(sK1,sK2))))
    | ~ v1_relat_1(k4_xboole_0(sK1,sK2))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f58,f27])).

fof(f58,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,sK1),k5_relat_1(sK0,k2_xboole_0(sK2,k4_xboole_0(sK1,sK2))))
    | ~ v1_relat_1(k4_xboole_0(sK1,sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK0) ),
    inference(superposition,[],[f52,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_relat_1)).

fof(f52,plain,(
    ~ r1_tarski(k5_relat_1(sK0,sK1),k2_xboole_0(k5_relat_1(sK0,sK2),k5_relat_1(sK0,k4_xboole_0(sK1,sK2)))) ),
    inference(resolution,[],[f38,f40])).

fof(f40,plain,(
    ~ r1_tarski(k4_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)),k5_relat_1(sK0,k4_xboole_0(sK1,sK2))) ),
    inference(forward_demodulation,[],[f39,f34])).

fof(f39,plain,(
    ~ r1_tarski(k6_subset_1(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)),k5_relat_1(sK0,k4_xboole_0(sK1,sK2))) ),
    inference(forward_demodulation,[],[f28,f34])).

fof(f28,plain,(
    ~ r1_tarski(k6_subset_1(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)),k5_relat_1(sK0,k6_subset_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f24])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f64,plain,(
    ! [X17,X15,X16] :
      ( r1_tarski(k5_relat_1(X15,X16),k5_relat_1(X15,k2_xboole_0(X16,X17)))
      | ~ v1_relat_1(X17)
      | ~ v1_relat_1(X16)
      | ~ v1_relat_1(X15) ) ),
    inference(superposition,[],[f32,f29])).

fof(f32,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:16:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.41  % (24419)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.46  % (24421)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.46  % (24412)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.46  % (24411)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.46  % (24411)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f88,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(subsumption_resolution,[],[f87,f26])).
% 0.21/0.46  fof(f26,plain,(
% 0.21/0.46    v1_relat_1(sK1)),
% 0.21/0.46    inference(cnf_transformation,[],[f24])).
% 0.21/0.46  fof(f24,plain,(
% 0.21/0.46    ((~r1_tarski(k6_subset_1(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)),k5_relat_1(sK0,k6_subset_1(sK1,sK2))) & v1_relat_1(sK2)) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f23,f22,f21])).
% 0.21/0.46  fof(f21,plain,(
% 0.21/0.46    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k6_subset_1(k5_relat_1(X0,X1),k5_relat_1(X0,X2)),k5_relat_1(X0,k6_subset_1(X1,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k6_subset_1(k5_relat_1(sK0,X1),k5_relat_1(sK0,X2)),k5_relat_1(sK0,k6_subset_1(X1,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f22,plain,(
% 0.21/0.46    ? [X1] : (? [X2] : (~r1_tarski(k6_subset_1(k5_relat_1(sK0,X1),k5_relat_1(sK0,X2)),k5_relat_1(sK0,k6_subset_1(X1,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) => (? [X2] : (~r1_tarski(k6_subset_1(k5_relat_1(sK0,sK1),k5_relat_1(sK0,X2)),k5_relat_1(sK0,k6_subset_1(sK1,X2))) & v1_relat_1(X2)) & v1_relat_1(sK1))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f23,plain,(
% 0.21/0.46    ? [X2] : (~r1_tarski(k6_subset_1(k5_relat_1(sK0,sK1),k5_relat_1(sK0,X2)),k5_relat_1(sK0,k6_subset_1(sK1,X2))) & v1_relat_1(X2)) => (~r1_tarski(k6_subset_1(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)),k5_relat_1(sK0,k6_subset_1(sK1,sK2))) & v1_relat_1(sK2))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f13,plain,(
% 0.21/0.46    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k6_subset_1(k5_relat_1(X0,X1),k5_relat_1(X0,X2)),k5_relat_1(X0,k6_subset_1(X1,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f12])).
% 0.21/0.46  fof(f12,negated_conjecture,(
% 0.21/0.46    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => r1_tarski(k6_subset_1(k5_relat_1(X0,X1),k5_relat_1(X0,X2)),k5_relat_1(X0,k6_subset_1(X1,X2))))))),
% 0.21/0.46    inference(negated_conjecture,[],[f11])).
% 0.21/0.46  fof(f11,conjecture,(
% 0.21/0.46    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => r1_tarski(k6_subset_1(k5_relat_1(X0,X1),k5_relat_1(X0,X2)),k5_relat_1(X0,k6_subset_1(X1,X2))))))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_relat_1)).
% 0.21/0.46  fof(f87,plain,(
% 0.21/0.46    ~v1_relat_1(sK1)),
% 0.21/0.46    inference(resolution,[],[f86,f46])).
% 0.21/0.46  fof(f46,plain,(
% 0.21/0.46    ( ! [X0,X1] : (v1_relat_1(k4_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.46    inference(resolution,[],[f31,f41])).
% 0.21/0.46  fof(f41,plain,(
% 0.21/0.46    ( ! [X0,X1] : (m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))) )),
% 0.21/0.46    inference(forward_demodulation,[],[f33,f34])).
% 0.21/0.46  fof(f34,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f6])).
% 0.21/0.46  fof(f6,axiom,(
% 0.21/0.46    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.21/0.46  fof(f33,plain,(
% 0.21/0.46    ( ! [X0,X1] : (m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f5])).
% 0.21/0.46  fof(f5,axiom,(
% 0.21/0.46    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).
% 0.21/0.46  fof(f31,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f17])).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f7])).
% 0.21/0.46  fof(f7,axiom,(
% 0.21/0.46    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.46  fof(f86,plain,(
% 0.21/0.46    ~v1_relat_1(k4_xboole_0(sK1,sK2))),
% 0.21/0.46    inference(subsumption_resolution,[],[f85,f25])).
% 0.21/0.46  fof(f25,plain,(
% 0.21/0.46    v1_relat_1(sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f24])).
% 0.21/0.46  fof(f85,plain,(
% 0.21/0.46    ~v1_relat_1(sK0) | ~v1_relat_1(k4_xboole_0(sK1,sK2))),
% 0.21/0.46    inference(subsumption_resolution,[],[f84,f26])).
% 0.21/0.46  fof(f84,plain,(
% 0.21/0.46    ~v1_relat_1(sK1) | ~v1_relat_1(sK0) | ~v1_relat_1(k4_xboole_0(sK1,sK2))),
% 0.21/0.46    inference(subsumption_resolution,[],[f79,f27])).
% 0.21/0.46  fof(f27,plain,(
% 0.21/0.46    v1_relat_1(sK2)),
% 0.21/0.46    inference(cnf_transformation,[],[f24])).
% 0.21/0.46  fof(f79,plain,(
% 0.21/0.46    ~v1_relat_1(sK2) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0) | ~v1_relat_1(k4_xboole_0(sK1,sK2))),
% 0.21/0.46    inference(resolution,[],[f64,f68])).
% 0.21/0.46  fof(f68,plain,(
% 0.21/0.46    ~r1_tarski(k5_relat_1(sK0,sK1),k5_relat_1(sK0,k2_xboole_0(sK1,sK2))) | ~v1_relat_1(k4_xboole_0(sK1,sK2))),
% 0.21/0.46    inference(forward_demodulation,[],[f67,f35])).
% 0.21/0.46  fof(f35,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.46  fof(f67,plain,(
% 0.21/0.46    ~r1_tarski(k5_relat_1(sK0,sK1),k5_relat_1(sK0,k2_xboole_0(sK2,sK1))) | ~v1_relat_1(k4_xboole_0(sK1,sK2))),
% 0.21/0.46    inference(forward_demodulation,[],[f66,f36])).
% 0.21/0.46  fof(f36,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.21/0.46  fof(f66,plain,(
% 0.21/0.46    ~r1_tarski(k5_relat_1(sK0,sK1),k5_relat_1(sK0,k2_xboole_0(sK2,k4_xboole_0(sK1,sK2)))) | ~v1_relat_1(k4_xboole_0(sK1,sK2))),
% 0.21/0.46    inference(subsumption_resolution,[],[f65,f25])).
% 0.21/0.46  fof(f65,plain,(
% 0.21/0.46    ~r1_tarski(k5_relat_1(sK0,sK1),k5_relat_1(sK0,k2_xboole_0(sK2,k4_xboole_0(sK1,sK2)))) | ~v1_relat_1(k4_xboole_0(sK1,sK2)) | ~v1_relat_1(sK0)),
% 0.21/0.46    inference(subsumption_resolution,[],[f58,f27])).
% 0.21/0.46  fof(f58,plain,(
% 0.21/0.46    ~r1_tarski(k5_relat_1(sK0,sK1),k5_relat_1(sK0,k2_xboole_0(sK2,k4_xboole_0(sK1,sK2)))) | ~v1_relat_1(k4_xboole_0(sK1,sK2)) | ~v1_relat_1(sK2) | ~v1_relat_1(sK0)),
% 0.21/0.46    inference(superposition,[],[f52,f29])).
% 0.21/0.46  fof(f29,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (k5_relat_1(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2)) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f14])).
% 0.21/0.46  fof(f14,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f10])).
% 0.21/0.46  fof(f10,axiom,(
% 0.21/0.46    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2)))))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_relat_1)).
% 0.21/0.46  fof(f52,plain,(
% 0.21/0.46    ~r1_tarski(k5_relat_1(sK0,sK1),k2_xboole_0(k5_relat_1(sK0,sK2),k5_relat_1(sK0,k4_xboole_0(sK1,sK2))))),
% 0.21/0.46    inference(resolution,[],[f38,f40])).
% 0.21/0.46  fof(f40,plain,(
% 0.21/0.46    ~r1_tarski(k4_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)),k5_relat_1(sK0,k4_xboole_0(sK1,sK2)))),
% 0.21/0.46    inference(forward_demodulation,[],[f39,f34])).
% 0.21/0.46  fof(f39,plain,(
% 0.21/0.46    ~r1_tarski(k6_subset_1(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)),k5_relat_1(sK0,k4_xboole_0(sK1,sK2)))),
% 0.21/0.46    inference(forward_demodulation,[],[f28,f34])).
% 0.21/0.46  fof(f28,plain,(
% 0.21/0.46    ~r1_tarski(k6_subset_1(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)),k5_relat_1(sK0,k6_subset_1(sK1,sK2)))),
% 0.21/0.46    inference(cnf_transformation,[],[f24])).
% 0.21/0.46  fof(f38,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f20])).
% 0.21/0.46  fof(f20,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.21/0.46    inference(ennf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).
% 0.21/0.46  fof(f64,plain,(
% 0.21/0.46    ( ! [X17,X15,X16] : (r1_tarski(k5_relat_1(X15,X16),k5_relat_1(X15,k2_xboole_0(X16,X17))) | ~v1_relat_1(X17) | ~v1_relat_1(X16) | ~v1_relat_1(X15)) )),
% 0.21/0.46    inference(superposition,[],[f32,f29])).
% 0.21/0.46  fof(f32,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f4])).
% 0.21/0.46  fof(f4,axiom,(
% 0.21/0.46    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (24411)------------------------------
% 0.21/0.46  % (24411)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (24411)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (24411)Memory used [KB]: 1663
% 0.21/0.46  % (24411)Time elapsed: 0.053 s
% 0.21/0.46  % (24411)------------------------------
% 0.21/0.46  % (24411)------------------------------
% 0.21/0.47  % (24407)Success in time 0.111 s
%------------------------------------------------------------------------------
