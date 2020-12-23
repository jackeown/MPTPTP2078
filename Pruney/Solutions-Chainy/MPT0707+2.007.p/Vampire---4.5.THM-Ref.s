%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:27 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 149 expanded)
%              Number of leaves         :   15 (  46 expanded)
%              Depth                    :   14
%              Number of atoms          :  112 ( 221 expanded)
%              Number of equality atoms :   51 ( 127 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f275,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f268])).

fof(f268,plain,(
    sK1 != sK1 ),
    inference(superposition,[],[f27,f253])).

fof(f253,plain,(
    sK1 = k9_relat_1(k6_relat_1(sK0),sK1) ),
    inference(forward_demodulation,[],[f248,f33])).

fof(f33,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f248,plain,(
    k9_relat_1(k6_relat_1(sK0),sK1) = k1_relat_1(k6_relat_1(sK1)) ),
    inference(superposition,[],[f143,f231])).

fof(f231,plain,(
    k6_relat_1(sK1) = k7_relat_1(k6_relat_1(sK1),sK0) ),
    inference(resolution,[],[f228,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(k6_relat_1(X0),X1)
      | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1) ) ),
    inference(resolution,[],[f42,f28])).

fof(f28,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f228,plain,(
    v4_relat_1(k6_relat_1(sK1),sK0) ),
    inference(resolution,[],[f227,f31])).

fof(f31,plain,(
    ! [X0] : v4_relat_1(k6_relat_1(X0),X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v5_relat_1(k6_relat_1(X0),X0)
      & v4_relat_1(k6_relat_1(X0),X0)
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc24_relat_1)).

fof(f227,plain,(
    ! [X0] :
      ( ~ v4_relat_1(k6_relat_1(X0),sK1)
      | v4_relat_1(k6_relat_1(X0),sK0) ) ),
    inference(resolution,[],[f56,f50])).

fof(f50,plain,(
    r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f43,f26])).

fof(f26,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( sK1 != k9_relat_1(k6_relat_1(sK0),sK1)
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f23])).

fof(f23,plain,
    ( ? [X0,X1] :
        ( k9_relat_1(k6_relat_1(X0),X1) != X1
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( sK1 != k9_relat_1(k6_relat_1(sK0),sK1)
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1] :
      ( k9_relat_1(k6_relat_1(X0),X1) != X1
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_1)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | v4_relat_1(k6_relat_1(X0),X2)
      | ~ v4_relat_1(k6_relat_1(X0),X1) ) ),
    inference(resolution,[],[f41,f28])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v4_relat_1(X2,X0)
      | v4_relat_1(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v4_relat_1(X2,X1)
          | ~ v4_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v4_relat_1(X2,X1)
          | ~ v4_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( ( v4_relat_1(X2,X0)
            & v1_relat_1(X2) )
         => v4_relat_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t217_relat_1)).

fof(f143,plain,(
    ! [X10,X11] : k9_relat_1(k6_relat_1(X10),X11) = k1_relat_1(k7_relat_1(k6_relat_1(X11),X10)) ),
    inference(superposition,[],[f33,f77])).

fof(f77,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(k9_relat_1(k6_relat_1(X1),X0)) ),
    inference(backward_demodulation,[],[f72,f75])).

fof(f75,plain,(
    ! [X8,X9] : k1_relat_1(k7_relat_1(k6_relat_1(X8),X9)) = k9_relat_1(k6_relat_1(X8),X9) ),
    inference(backward_demodulation,[],[f64,f74])).

fof(f74,plain,(
    ! [X10,X11] : k1_setfam_1(k2_enumset1(X10,X10,X10,X11)) = k9_relat_1(k6_relat_1(X10),X11) ),
    inference(forward_demodulation,[],[f65,f54])).

fof(f54,plain,(
    ! [X0,X1] : k9_relat_1(k6_relat_1(X0),X1) = k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(resolution,[],[f40,f28])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f65,plain,(
    ! [X10,X11] : k1_setfam_1(k2_enumset1(X10,X10,X10,X11)) = k2_relat_1(k7_relat_1(k6_relat_1(X10),X11)) ),
    inference(superposition,[],[f34,f53])).

fof(f53,plain,(
    ! [X0,X1] : k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(backward_demodulation,[],[f49,f52])).

fof(f52,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(resolution,[],[f39,f28])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f49,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f38,f47])).

fof(f47,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f37,f46])).

fof(f46,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f36,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f36,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f37,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f38,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

fof(f34,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f64,plain,(
    ! [X8,X9] : k1_setfam_1(k2_enumset1(X8,X8,X8,X9)) = k1_relat_1(k7_relat_1(k6_relat_1(X8),X9)) ),
    inference(superposition,[],[f33,f53])).

fof(f72,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) ),
    inference(backward_demodulation,[],[f58,f64])).

fof(f58,plain,(
    ! [X0,X1] : k6_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(superposition,[],[f53,f48])).

fof(f48,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f35,f46,f46])).

fof(f35,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f27,plain,(
    sK1 != k9_relat_1(k6_relat_1(sK0),sK1) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:46:50 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.23/0.46  % (26860)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.23/0.47  % (26864)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.23/0.48  % (26861)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.23/0.48  % (26857)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.23/0.48  % (26871)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.23/0.49  % (26857)Refutation found. Thanks to Tanya!
% 0.23/0.49  % SZS status Theorem for theBenchmark
% 0.23/0.49  % SZS output start Proof for theBenchmark
% 0.23/0.49  fof(f275,plain,(
% 0.23/0.49    $false),
% 0.23/0.49    inference(trivial_inequality_removal,[],[f268])).
% 0.23/0.49  fof(f268,plain,(
% 0.23/0.49    sK1 != sK1),
% 0.23/0.49    inference(superposition,[],[f27,f253])).
% 0.23/0.49  fof(f253,plain,(
% 0.23/0.49    sK1 = k9_relat_1(k6_relat_1(sK0),sK1)),
% 0.23/0.49    inference(forward_demodulation,[],[f248,f33])).
% 0.23/0.49  fof(f33,plain,(
% 0.23/0.49    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.23/0.49    inference(cnf_transformation,[],[f9])).
% 0.23/0.49  fof(f9,axiom,(
% 0.23/0.49    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.23/0.49  fof(f248,plain,(
% 0.23/0.49    k9_relat_1(k6_relat_1(sK0),sK1) = k1_relat_1(k6_relat_1(sK1))),
% 0.23/0.49    inference(superposition,[],[f143,f231])).
% 0.23/0.49  fof(f231,plain,(
% 0.23/0.49    k6_relat_1(sK1) = k7_relat_1(k6_relat_1(sK1),sK0)),
% 0.23/0.49    inference(resolution,[],[f228,f55])).
% 0.23/0.49  fof(f55,plain,(
% 0.23/0.49    ( ! [X0,X1] : (~v4_relat_1(k6_relat_1(X0),X1) | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 0.23/0.49    inference(resolution,[],[f42,f28])).
% 0.23/0.49  fof(f28,plain,(
% 0.23/0.49    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.23/0.49    inference(cnf_transformation,[],[f12])).
% 0.23/0.49  fof(f12,axiom,(
% 0.23/0.49    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).
% 0.23/0.49  fof(f42,plain,(
% 0.23/0.49    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1) )),
% 0.23/0.49    inference(cnf_transformation,[],[f22])).
% 0.23/0.49  fof(f22,plain,(
% 0.23/0.49    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.23/0.49    inference(flattening,[],[f21])).
% 0.23/0.49  fof(f21,plain,(
% 0.23/0.49    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.23/0.49    inference(ennf_transformation,[],[f7])).
% 0.23/0.49  fof(f7,axiom,(
% 0.23/0.49    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 0.23/0.49  fof(f228,plain,(
% 0.23/0.49    v4_relat_1(k6_relat_1(sK1),sK0)),
% 0.23/0.49    inference(resolution,[],[f227,f31])).
% 0.23/0.49  fof(f31,plain,(
% 0.23/0.49    ( ! [X0] : (v4_relat_1(k6_relat_1(X0),X0)) )),
% 0.23/0.49    inference(cnf_transformation,[],[f11])).
% 0.23/0.49  fof(f11,axiom,(
% 0.23/0.49    ! [X0] : (v5_relat_1(k6_relat_1(X0),X0) & v4_relat_1(k6_relat_1(X0),X0) & v1_relat_1(k6_relat_1(X0)))),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc24_relat_1)).
% 0.23/0.49  fof(f227,plain,(
% 0.23/0.49    ( ! [X0] : (~v4_relat_1(k6_relat_1(X0),sK1) | v4_relat_1(k6_relat_1(X0),sK0)) )),
% 0.23/0.49    inference(resolution,[],[f56,f50])).
% 0.23/0.49  fof(f50,plain,(
% 0.23/0.49    r1_tarski(sK1,sK0)),
% 0.23/0.49    inference(resolution,[],[f43,f26])).
% 0.23/0.49  fof(f26,plain,(
% 0.23/0.49    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.23/0.49    inference(cnf_transformation,[],[f24])).
% 0.23/0.49  fof(f24,plain,(
% 0.23/0.49    sK1 != k9_relat_1(k6_relat_1(sK0),sK1) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.23/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f23])).
% 0.23/0.49  fof(f23,plain,(
% 0.23/0.49    ? [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) != X1 & m1_subset_1(X1,k1_zfmisc_1(X0))) => (sK1 != k9_relat_1(k6_relat_1(sK0),sK1) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.23/0.49    introduced(choice_axiom,[])).
% 0.23/0.49  fof(f16,plain,(
% 0.23/0.49    ? [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) != X1 & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.23/0.49    inference(ennf_transformation,[],[f15])).
% 0.23/0.49  fof(f15,negated_conjecture,(
% 0.23/0.49    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k9_relat_1(k6_relat_1(X0),X1) = X1)),
% 0.23/0.49    inference(negated_conjecture,[],[f14])).
% 0.23/0.49  fof(f14,conjecture,(
% 0.23/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k9_relat_1(k6_relat_1(X0),X1) = X1)),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_1)).
% 0.23/0.49  fof(f43,plain,(
% 0.23/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.23/0.49    inference(cnf_transformation,[],[f25])).
% 0.23/0.49  fof(f25,plain,(
% 0.23/0.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.23/0.49    inference(nnf_transformation,[],[f5])).
% 0.23/0.49  fof(f5,axiom,(
% 0.23/0.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.23/0.49  fof(f56,plain,(
% 0.23/0.49    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | v4_relat_1(k6_relat_1(X0),X2) | ~v4_relat_1(k6_relat_1(X0),X1)) )),
% 0.23/0.49    inference(resolution,[],[f41,f28])).
% 0.23/0.49  fof(f41,plain,(
% 0.23/0.49    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v4_relat_1(X2,X0) | v4_relat_1(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.23/0.49    inference(cnf_transformation,[],[f20])).
% 0.23/0.49  fof(f20,plain,(
% 0.23/0.49    ! [X0,X1] : (! [X2] : (v4_relat_1(X2,X1) | ~v4_relat_1(X2,X0) | ~v1_relat_1(X2)) | ~r1_tarski(X0,X1))),
% 0.23/0.49    inference(flattening,[],[f19])).
% 0.23/0.49  fof(f19,plain,(
% 0.23/0.49    ! [X0,X1] : (! [X2] : (v4_relat_1(X2,X1) | (~v4_relat_1(X2,X0) | ~v1_relat_1(X2))) | ~r1_tarski(X0,X1))),
% 0.23/0.49    inference(ennf_transformation,[],[f8])).
% 0.23/0.49  fof(f8,axiom,(
% 0.23/0.49    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : ((v4_relat_1(X2,X0) & v1_relat_1(X2)) => v4_relat_1(X2,X1)))),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t217_relat_1)).
% 0.23/0.49  fof(f143,plain,(
% 0.23/0.49    ( ! [X10,X11] : (k9_relat_1(k6_relat_1(X10),X11) = k1_relat_1(k7_relat_1(k6_relat_1(X11),X10))) )),
% 0.23/0.49    inference(superposition,[],[f33,f77])).
% 0.23/0.49  fof(f77,plain,(
% 0.23/0.49    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(k9_relat_1(k6_relat_1(X1),X0))) )),
% 0.23/0.49    inference(backward_demodulation,[],[f72,f75])).
% 0.23/0.49  fof(f75,plain,(
% 0.23/0.49    ( ! [X8,X9] : (k1_relat_1(k7_relat_1(k6_relat_1(X8),X9)) = k9_relat_1(k6_relat_1(X8),X9)) )),
% 0.23/0.49    inference(backward_demodulation,[],[f64,f74])).
% 0.23/0.49  fof(f74,plain,(
% 0.23/0.49    ( ! [X10,X11] : (k1_setfam_1(k2_enumset1(X10,X10,X10,X11)) = k9_relat_1(k6_relat_1(X10),X11)) )),
% 0.23/0.49    inference(forward_demodulation,[],[f65,f54])).
% 0.23/0.49  fof(f54,plain,(
% 0.23/0.49    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) = k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) )),
% 0.23/0.49    inference(resolution,[],[f40,f28])).
% 0.23/0.49  fof(f40,plain,(
% 0.23/0.49    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.23/0.49    inference(cnf_transformation,[],[f18])).
% 0.23/0.49  fof(f18,plain,(
% 0.23/0.49    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.23/0.49    inference(ennf_transformation,[],[f6])).
% 0.23/0.49  fof(f6,axiom,(
% 0.23/0.49    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.23/0.49  fof(f65,plain,(
% 0.23/0.49    ( ! [X10,X11] : (k1_setfam_1(k2_enumset1(X10,X10,X10,X11)) = k2_relat_1(k7_relat_1(k6_relat_1(X10),X11))) )),
% 0.23/0.49    inference(superposition,[],[f34,f53])).
% 0.23/0.49  fof(f53,plain,(
% 0.23/0.49    ( ! [X0,X1] : (k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 0.23/0.49    inference(backward_demodulation,[],[f49,f52])).
% 0.23/0.49  fof(f52,plain,(
% 0.23/0.49    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 0.23/0.49    inference(resolution,[],[f39,f28])).
% 0.23/0.49  fof(f39,plain,(
% 0.23/0.49    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 0.23/0.49    inference(cnf_transformation,[],[f17])).
% 0.23/0.49  fof(f17,plain,(
% 0.23/0.49    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.23/0.49    inference(ennf_transformation,[],[f10])).
% 0.23/0.49  fof(f10,axiom,(
% 0.23/0.49    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 0.23/0.49  fof(f49,plain,(
% 0.23/0.49    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) )),
% 0.23/0.49    inference(definition_unfolding,[],[f38,f47])).
% 0.23/0.49  fof(f47,plain,(
% 0.23/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 0.23/0.49    inference(definition_unfolding,[],[f37,f46])).
% 0.23/0.49  fof(f46,plain,(
% 0.23/0.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.23/0.49    inference(definition_unfolding,[],[f36,f45])).
% 0.23/0.49  fof(f45,plain,(
% 0.23/0.49    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.23/0.49    inference(cnf_transformation,[],[f3])).
% 0.23/0.49  fof(f3,axiom,(
% 0.23/0.49    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.23/0.49  fof(f36,plain,(
% 0.23/0.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.23/0.49    inference(cnf_transformation,[],[f2])).
% 0.23/0.49  fof(f2,axiom,(
% 0.23/0.49    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.23/0.49  fof(f37,plain,(
% 0.23/0.49    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.23/0.49    inference(cnf_transformation,[],[f4])).
% 0.23/0.49  fof(f4,axiom,(
% 0.23/0.49    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.23/0.49  fof(f38,plain,(
% 0.23/0.49    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) )),
% 0.23/0.49    inference(cnf_transformation,[],[f13])).
% 0.23/0.49  fof(f13,axiom,(
% 0.23/0.49    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
% 0.23/0.49  fof(f34,plain,(
% 0.23/0.49    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.23/0.49    inference(cnf_transformation,[],[f9])).
% 0.23/0.49  fof(f64,plain,(
% 0.23/0.49    ( ! [X8,X9] : (k1_setfam_1(k2_enumset1(X8,X8,X8,X9)) = k1_relat_1(k7_relat_1(k6_relat_1(X8),X9))) )),
% 0.23/0.49    inference(superposition,[],[f33,f53])).
% 0.23/0.49  fof(f72,plain,(
% 0.23/0.49    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X1),X0)))) )),
% 0.23/0.49    inference(backward_demodulation,[],[f58,f64])).
% 0.23/0.49  fof(f58,plain,(
% 0.23/0.49    ( ! [X0,X1] : (k6_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 0.23/0.49    inference(superposition,[],[f53,f48])).
% 0.23/0.49  fof(f48,plain,(
% 0.23/0.49    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)) )),
% 0.23/0.49    inference(definition_unfolding,[],[f35,f46,f46])).
% 0.23/0.49  fof(f35,plain,(
% 0.23/0.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.23/0.49    inference(cnf_transformation,[],[f1])).
% 0.23/0.49  fof(f1,axiom,(
% 0.23/0.49    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.23/0.49  fof(f27,plain,(
% 0.23/0.49    sK1 != k9_relat_1(k6_relat_1(sK0),sK1)),
% 0.23/0.49    inference(cnf_transformation,[],[f24])).
% 0.23/0.49  % SZS output end Proof for theBenchmark
% 0.23/0.49  % (26857)------------------------------
% 0.23/0.49  % (26857)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.49  % (26857)Termination reason: Refutation
% 0.23/0.49  
% 0.23/0.49  % (26857)Memory used [KB]: 1791
% 0.23/0.49  % (26857)Time elapsed: 0.067 s
% 0.23/0.49  % (26857)------------------------------
% 0.23/0.49  % (26857)------------------------------
% 0.23/0.49  % (26855)Success in time 0.123 s
%------------------------------------------------------------------------------
