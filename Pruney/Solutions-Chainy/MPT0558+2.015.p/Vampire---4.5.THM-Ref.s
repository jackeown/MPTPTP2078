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
% DateTime   : Thu Dec  3 12:49:58 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 106 expanded)
%              Number of leaves         :    9 (  35 expanded)
%              Depth                    :   10
%              Number of atoms          :  105 ( 305 expanded)
%              Number of equality atoms :   37 ( 104 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f293,plain,(
    $false ),
    inference(global_subsumption,[],[f23,f292])).

fof(f292,plain,(
    k2_relat_1(k5_relat_1(sK0,sK1)) = k9_relat_1(sK1,k2_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f290,f36])).

fof(f36,plain,(
    k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0)) ),
    inference(superposition,[],[f33,f30])).

fof(f30,plain,(
    sK0 = k7_relat_1(sK0,k1_relat_1(sK0)) ),
    inference(resolution,[],[f24,f21])).

fof(f21,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( k2_relat_1(k5_relat_1(sK0,sK1)) != k9_relat_1(sK1,k2_relat_1(sK0))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f19,f18])).

fof(f18,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k2_relat_1(k5_relat_1(X0,X1)) != k9_relat_1(X1,k2_relat_1(X0))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( k2_relat_1(k5_relat_1(sK0,X1)) != k9_relat_1(X1,k2_relat_1(sK0))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X1] :
        ( k2_relat_1(k5_relat_1(sK0,X1)) != k9_relat_1(X1,k2_relat_1(sK0))
        & v1_relat_1(X1) )
   => ( k2_relat_1(k5_relat_1(sK0,sK1)) != k9_relat_1(sK1,k2_relat_1(sK0))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) != k9_relat_1(X1,k2_relat_1(X0))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

fof(f33,plain,(
    ! [X0] : k2_relat_1(k7_relat_1(sK0,X0)) = k9_relat_1(sK0,X0) ),
    inference(resolution,[],[f26,f21])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f290,plain,(
    k2_relat_1(k5_relat_1(sK0,sK1)) = k9_relat_1(sK1,k9_relat_1(sK0,k1_relat_1(sK0))) ),
    inference(superposition,[],[f288,f50])).

fof(f50,plain,(
    k5_relat_1(sK0,sK1) = k7_relat_1(k5_relat_1(sK0,sK1),k1_relat_1(sK0)) ),
    inference(resolution,[],[f41,f21])).

fof(f41,plain,(
    ! [X1] :
      ( ~ v1_relat_1(X1)
      | k5_relat_1(X1,sK1) = k7_relat_1(k5_relat_1(X1,sK1),k1_relat_1(X1)) ) ),
    inference(resolution,[],[f39,f22])).

fof(f22,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k5_relat_1(X0,X1) = k7_relat_1(k5_relat_1(X0,X1),k1_relat_1(X0)) ) ),
    inference(global_subsumption,[],[f29,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X0,X1) = k7_relat_1(k5_relat_1(X0,X1),k1_relat_1(X0))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f27,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | k7_relat_1(X1,X0) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

fof(f29,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f288,plain,(
    ! [X0] : k9_relat_1(sK1,k9_relat_1(sK0,X0)) = k2_relat_1(k7_relat_1(k5_relat_1(sK0,sK1),X0)) ),
    inference(forward_demodulation,[],[f285,f79])).

fof(f79,plain,(
    ! [X0] : k9_relat_1(k5_relat_1(sK0,sK1),X0) = k9_relat_1(sK1,k9_relat_1(sK0,X0)) ),
    inference(resolution,[],[f70,f21])).

fof(f70,plain,(
    ! [X2,X3] :
      ( ~ v1_relat_1(X2)
      | k9_relat_1(k5_relat_1(X2,sK1),X3) = k9_relat_1(sK1,k9_relat_1(X2,X3)) ) ),
    inference(resolution,[],[f28,f22])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t159_relat_1)).

fof(f285,plain,(
    ! [X0] : k9_relat_1(k5_relat_1(sK0,sK1),X0) = k2_relat_1(k7_relat_1(k5_relat_1(sK0,sK1),X0)) ),
    inference(resolution,[],[f268,f21])).

fof(f268,plain,(
    ! [X2,X3] :
      ( ~ v1_relat_1(X2)
      | k9_relat_1(k5_relat_1(X2,sK1),X3) = k2_relat_1(k7_relat_1(k5_relat_1(X2,sK1),X3)) ) ),
    inference(resolution,[],[f35,f22])).

fof(f35,plain,(
    ! [X4,X2,X3] :
      ( ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2)
      | k2_relat_1(k7_relat_1(k5_relat_1(X2,X3),X4)) = k9_relat_1(k5_relat_1(X2,X3),X4) ) ),
    inference(resolution,[],[f26,f29])).

fof(f23,plain,(
    k2_relat_1(k5_relat_1(sK0,sK1)) != k9_relat_1(sK1,k2_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:16:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.38  % (19693)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.20/0.40  % (19690)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.20/0.41  % (19693)Refutation found. Thanks to Tanya!
% 0.20/0.41  % SZS status Theorem for theBenchmark
% 0.20/0.41  % SZS output start Proof for theBenchmark
% 0.20/0.41  fof(f293,plain,(
% 0.20/0.41    $false),
% 0.20/0.41    inference(global_subsumption,[],[f23,f292])).
% 0.20/0.41  fof(f292,plain,(
% 0.20/0.41    k2_relat_1(k5_relat_1(sK0,sK1)) = k9_relat_1(sK1,k2_relat_1(sK0))),
% 0.20/0.41    inference(forward_demodulation,[],[f290,f36])).
% 0.20/0.41  fof(f36,plain,(
% 0.20/0.41    k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0))),
% 0.20/0.41    inference(superposition,[],[f33,f30])).
% 0.20/0.41  fof(f30,plain,(
% 0.20/0.41    sK0 = k7_relat_1(sK0,k1_relat_1(sK0))),
% 0.20/0.41    inference(resolution,[],[f24,f21])).
% 0.20/0.41  fof(f21,plain,(
% 0.20/0.41    v1_relat_1(sK0)),
% 0.20/0.41    inference(cnf_transformation,[],[f20])).
% 0.20/0.41  fof(f20,plain,(
% 0.20/0.41    (k2_relat_1(k5_relat_1(sK0,sK1)) != k9_relat_1(sK1,k2_relat_1(sK0)) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.20/0.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f19,f18])).
% 0.20/0.41  fof(f18,plain,(
% 0.20/0.41    ? [X0] : (? [X1] : (k2_relat_1(k5_relat_1(X0,X1)) != k9_relat_1(X1,k2_relat_1(X0)) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (k2_relat_1(k5_relat_1(sK0,X1)) != k9_relat_1(X1,k2_relat_1(sK0)) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.20/0.41    introduced(choice_axiom,[])).
% 0.20/0.41  fof(f19,plain,(
% 0.20/0.41    ? [X1] : (k2_relat_1(k5_relat_1(sK0,X1)) != k9_relat_1(X1,k2_relat_1(sK0)) & v1_relat_1(X1)) => (k2_relat_1(k5_relat_1(sK0,sK1)) != k9_relat_1(sK1,k2_relat_1(sK0)) & v1_relat_1(sK1))),
% 0.20/0.41    introduced(choice_axiom,[])).
% 0.20/0.41  fof(f9,plain,(
% 0.20/0.41    ? [X0] : (? [X1] : (k2_relat_1(k5_relat_1(X0,X1)) != k9_relat_1(X1,k2_relat_1(X0)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.20/0.41    inference(ennf_transformation,[],[f8])).
% 0.20/0.41  fof(f8,negated_conjecture,(
% 0.20/0.41    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 0.20/0.41    inference(negated_conjecture,[],[f7])).
% 0.20/0.41  fof(f7,conjecture,(
% 0.20/0.41    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).
% 0.20/0.41  fof(f24,plain,(
% 0.20/0.41    ( ! [X0] : (~v1_relat_1(X0) | k7_relat_1(X0,k1_relat_1(X0)) = X0) )),
% 0.20/0.41    inference(cnf_transformation,[],[f10])).
% 0.20/0.41  fof(f10,plain,(
% 0.20/0.41    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 0.20/0.41    inference(ennf_transformation,[],[f6])).
% 0.20/0.41  fof(f6,axiom,(
% 0.20/0.41    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).
% 0.20/0.41  fof(f33,plain,(
% 0.20/0.41    ( ! [X0] : (k2_relat_1(k7_relat_1(sK0,X0)) = k9_relat_1(sK0,X0)) )),
% 0.20/0.41    inference(resolution,[],[f26,f21])).
% 0.20/0.41  fof(f26,plain,(
% 0.20/0.41    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f12])).
% 0.20/0.41  fof(f12,plain,(
% 0.20/0.41    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.41    inference(ennf_transformation,[],[f2])).
% 0.20/0.41  fof(f2,axiom,(
% 0.20/0.41    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.20/0.41  fof(f290,plain,(
% 0.20/0.41    k2_relat_1(k5_relat_1(sK0,sK1)) = k9_relat_1(sK1,k9_relat_1(sK0,k1_relat_1(sK0)))),
% 0.20/0.41    inference(superposition,[],[f288,f50])).
% 0.20/0.41  fof(f50,plain,(
% 0.20/0.41    k5_relat_1(sK0,sK1) = k7_relat_1(k5_relat_1(sK0,sK1),k1_relat_1(sK0))),
% 0.20/0.41    inference(resolution,[],[f41,f21])).
% 0.20/0.41  fof(f41,plain,(
% 0.20/0.41    ( ! [X1] : (~v1_relat_1(X1) | k5_relat_1(X1,sK1) = k7_relat_1(k5_relat_1(X1,sK1),k1_relat_1(X1))) )),
% 0.20/0.41    inference(resolution,[],[f39,f22])).
% 0.20/0.41  fof(f22,plain,(
% 0.20/0.41    v1_relat_1(sK1)),
% 0.20/0.41    inference(cnf_transformation,[],[f20])).
% 0.20/0.41  fof(f39,plain,(
% 0.20/0.41    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X0) | k5_relat_1(X0,X1) = k7_relat_1(k5_relat_1(X0,X1),k1_relat_1(X0))) )),
% 0.20/0.41    inference(global_subsumption,[],[f29,f38])).
% 0.20/0.41  fof(f38,plain,(
% 0.20/0.41    ( ! [X0,X1] : (k5_relat_1(X0,X1) = k7_relat_1(k5_relat_1(X0,X1),k1_relat_1(X0)) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.41    inference(resolution,[],[f27,f25])).
% 0.20/0.41  fof(f25,plain,(
% 0.20/0.41    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f11])).
% 0.20/0.41  fof(f11,plain,(
% 0.20/0.41    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.41    inference(ennf_transformation,[],[f4])).
% 0.20/0.41  fof(f4,axiom,(
% 0.20/0.41    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))))),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).
% 0.20/0.41  fof(f27,plain,(
% 0.20/0.41    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f14])).
% 0.20/0.41  fof(f14,plain,(
% 0.20/0.41    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.20/0.41    inference(flattening,[],[f13])).
% 0.20/0.41  fof(f13,plain,(
% 0.20/0.41    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.41    inference(ennf_transformation,[],[f5])).
% 0.20/0.41  fof(f5,axiom,(
% 0.20/0.41    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).
% 0.20/0.41  fof(f29,plain,(
% 0.20/0.41    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f17])).
% 0.20/0.41  fof(f17,plain,(
% 0.20/0.41    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.20/0.41    inference(flattening,[],[f16])).
% 0.20/0.41  fof(f16,plain,(
% 0.20/0.41    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 0.20/0.41    inference(ennf_transformation,[],[f1])).
% 0.20/0.41  fof(f1,axiom,(
% 0.20/0.41    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 0.20/0.41  fof(f288,plain,(
% 0.20/0.41    ( ! [X0] : (k9_relat_1(sK1,k9_relat_1(sK0,X0)) = k2_relat_1(k7_relat_1(k5_relat_1(sK0,sK1),X0))) )),
% 0.20/0.41    inference(forward_demodulation,[],[f285,f79])).
% 0.20/0.41  fof(f79,plain,(
% 0.20/0.41    ( ! [X0] : (k9_relat_1(k5_relat_1(sK0,sK1),X0) = k9_relat_1(sK1,k9_relat_1(sK0,X0))) )),
% 0.20/0.41    inference(resolution,[],[f70,f21])).
% 0.20/0.41  fof(f70,plain,(
% 0.20/0.41    ( ! [X2,X3] : (~v1_relat_1(X2) | k9_relat_1(k5_relat_1(X2,sK1),X3) = k9_relat_1(sK1,k9_relat_1(X2,X3))) )),
% 0.20/0.41    inference(resolution,[],[f28,f22])).
% 0.20/0.41  fof(f28,plain,(
% 0.20/0.41    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_relat_1(X1) | k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))) )),
% 0.20/0.41    inference(cnf_transformation,[],[f15])).
% 0.20/0.41  fof(f15,plain,(
% 0.20/0.41    ! [X0,X1] : (! [X2] : (k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.20/0.41    inference(ennf_transformation,[],[f3])).
% 0.20/0.41  fof(f3,axiom,(
% 0.20/0.41    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))))),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t159_relat_1)).
% 0.20/0.41  fof(f285,plain,(
% 0.20/0.41    ( ! [X0] : (k9_relat_1(k5_relat_1(sK0,sK1),X0) = k2_relat_1(k7_relat_1(k5_relat_1(sK0,sK1),X0))) )),
% 0.20/0.41    inference(resolution,[],[f268,f21])).
% 0.20/0.41  fof(f268,plain,(
% 0.20/0.41    ( ! [X2,X3] : (~v1_relat_1(X2) | k9_relat_1(k5_relat_1(X2,sK1),X3) = k2_relat_1(k7_relat_1(k5_relat_1(X2,sK1),X3))) )),
% 0.20/0.41    inference(resolution,[],[f35,f22])).
% 0.20/0.41  fof(f35,plain,(
% 0.20/0.41    ( ! [X4,X2,X3] : (~v1_relat_1(X3) | ~v1_relat_1(X2) | k2_relat_1(k7_relat_1(k5_relat_1(X2,X3),X4)) = k9_relat_1(k5_relat_1(X2,X3),X4)) )),
% 0.20/0.41    inference(resolution,[],[f26,f29])).
% 0.20/0.41  fof(f23,plain,(
% 0.20/0.41    k2_relat_1(k5_relat_1(sK0,sK1)) != k9_relat_1(sK1,k2_relat_1(sK0))),
% 0.20/0.41    inference(cnf_transformation,[],[f20])).
% 0.20/0.41  % SZS output end Proof for theBenchmark
% 0.20/0.41  % (19693)------------------------------
% 0.20/0.41  % (19693)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.41  % (19693)Termination reason: Refutation
% 0.20/0.41  
% 0.20/0.41  % (19693)Memory used [KB]: 6524
% 0.20/0.41  % (19693)Time elapsed: 0.033 s
% 0.20/0.41  % (19693)------------------------------
% 0.20/0.41  % (19693)------------------------------
% 0.20/0.41  % (19684)Success in time 0.063 s
%------------------------------------------------------------------------------
