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
% DateTime   : Thu Dec  3 12:56:12 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 152 expanded)
%              Number of leaves         :   13 (  48 expanded)
%              Depth                    :   13
%              Number of atoms          :   86 ( 223 expanded)
%              Number of equality atoms :   23 ( 108 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f110,plain,(
    $false ),
    inference(subsumption_resolution,[],[f106,f73])).

fof(f73,plain,(
    m1_subset_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
    inference(resolution,[],[f58,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f58,plain,(
    r1_tarski(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k2_zfmisc_1(sK1,sK3)) ),
    inference(resolution,[],[f52,f48])).

fof(f48,plain,(
    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) ),
    inference(resolution,[],[f45,f22])).

fof(f22,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ~ m1_subset_1(k1_tarski(k4_tarski(sK0,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    & r2_hidden(sK2,sK3)
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ m1_subset_1(k1_tarski(k4_tarski(X0,X2)),k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
        & r2_hidden(X2,X3)
        & r2_hidden(X0,X1) )
   => ( ~ m1_subset_1(k1_tarski(k4_tarski(sK0,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
      & r2_hidden(sK2,sK3)
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ m1_subset_1(k1_tarski(k4_tarski(X0,X2)),k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
      & r2_hidden(X2,X3)
      & r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ m1_subset_1(k1_tarski(k4_tarski(X0,X2)),k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
      & r2_hidden(X2,X3)
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r2_hidden(X2,X3)
          & r2_hidden(X0,X1) )
       => m1_subset_1(k1_tarski(k4_tarski(X0,X2)),k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(X2,X3)
        & r2_hidden(X0,X1) )
     => m1_subset_1(k1_tarski(k4_tarski(X0,X2)),k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_relset_1)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f30,f43])).

fof(f43,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f25,f42])).

fof(f42,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f26,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f31,f40])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f32,f39])).

fof(f39,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f35,f38])).

fof(f38,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f36,f37])).

fof(f37,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f36,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f35,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f32,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f31,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f26,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f25,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k2_zfmisc_1(X0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k2_zfmisc_1(X1,sK3)) ) ),
    inference(resolution,[],[f49,f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X2,X3)
      | r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_zfmisc_1)).

fof(f49,plain,(
    r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) ),
    inference(resolution,[],[f45,f23])).

fof(f23,plain,(
    r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f106,plain,(
    ~ m1_subset_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
    inference(backward_demodulation,[],[f44,f47])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)) = k6_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(definition_unfolding,[],[f33,f42,f42,f40])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_zfmisc_1)).

fof(f44,plain,(
    ~ m1_subset_1(k6_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
    inference(definition_unfolding,[],[f24,f43])).

fof(f24,plain,(
    ~ m1_subset_1(k1_tarski(k4_tarski(sK0,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 14:30:05 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.42  % (10501)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.42  % (10501)Refutation found. Thanks to Tanya!
% 0.22/0.42  % SZS status Theorem for theBenchmark
% 0.22/0.42  % SZS output start Proof for theBenchmark
% 0.22/0.42  fof(f110,plain,(
% 0.22/0.42    $false),
% 0.22/0.42    inference(subsumption_resolution,[],[f106,f73])).
% 0.22/0.42  fof(f73,plain,(
% 0.22/0.42    m1_subset_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))),
% 0.22/0.42    inference(resolution,[],[f58,f28])).
% 0.22/0.42  fof(f28,plain,(
% 0.22/0.42    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.22/0.42    inference(cnf_transformation,[],[f20])).
% 0.22/0.42  fof(f20,plain,(
% 0.22/0.42    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.42    inference(nnf_transformation,[],[f11])).
% 0.22/0.42  fof(f11,axiom,(
% 0.22/0.42    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.42  fof(f58,plain,(
% 0.22/0.42    r1_tarski(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k2_zfmisc_1(sK1,sK3))),
% 0.22/0.42    inference(resolution,[],[f52,f48])).
% 0.22/0.42  fof(f48,plain,(
% 0.22/0.42    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),
% 0.22/0.42    inference(resolution,[],[f45,f22])).
% 0.22/0.42  fof(f22,plain,(
% 0.22/0.42    r2_hidden(sK0,sK1)),
% 0.22/0.42    inference(cnf_transformation,[],[f19])).
% 0.22/0.42  fof(f19,plain,(
% 0.22/0.42    ~m1_subset_1(k1_tarski(k4_tarski(sK0,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) & r2_hidden(sK2,sK3) & r2_hidden(sK0,sK1)),
% 0.22/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f18])).
% 0.22/0.42  fof(f18,plain,(
% 0.22/0.42    ? [X0,X1,X2,X3] : (~m1_subset_1(k1_tarski(k4_tarski(X0,X2)),k1_zfmisc_1(k2_zfmisc_1(X1,X3))) & r2_hidden(X2,X3) & r2_hidden(X0,X1)) => (~m1_subset_1(k1_tarski(k4_tarski(sK0,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) & r2_hidden(sK2,sK3) & r2_hidden(sK0,sK1))),
% 0.22/0.42    introduced(choice_axiom,[])).
% 0.22/0.42  fof(f15,plain,(
% 0.22/0.42    ? [X0,X1,X2,X3] : (~m1_subset_1(k1_tarski(k4_tarski(X0,X2)),k1_zfmisc_1(k2_zfmisc_1(X1,X3))) & r2_hidden(X2,X3) & r2_hidden(X0,X1))),
% 0.22/0.42    inference(flattening,[],[f14])).
% 0.22/0.42  fof(f14,plain,(
% 0.22/0.42    ? [X0,X1,X2,X3] : (~m1_subset_1(k1_tarski(k4_tarski(X0,X2)),k1_zfmisc_1(k2_zfmisc_1(X1,X3))) & (r2_hidden(X2,X3) & r2_hidden(X0,X1)))),
% 0.22/0.42    inference(ennf_transformation,[],[f13])).
% 0.22/0.42  fof(f13,negated_conjecture,(
% 0.22/0.42    ~! [X0,X1,X2,X3] : ((r2_hidden(X2,X3) & r2_hidden(X0,X1)) => m1_subset_1(k1_tarski(k4_tarski(X0,X2)),k1_zfmisc_1(k2_zfmisc_1(X1,X3))))),
% 0.22/0.42    inference(negated_conjecture,[],[f12])).
% 0.22/0.42  fof(f12,conjecture,(
% 0.22/0.42    ! [X0,X1,X2,X3] : ((r2_hidden(X2,X3) & r2_hidden(X0,X1)) => m1_subset_1(k1_tarski(k4_tarski(X0,X2)),k1_zfmisc_1(k2_zfmisc_1(X1,X3))))),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_relset_1)).
% 0.22/0.42  fof(f45,plain,(
% 0.22/0.42    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)) )),
% 0.22/0.42    inference(definition_unfolding,[],[f30,f43])).
% 0.22/0.42  fof(f43,plain,(
% 0.22/0.42    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 0.22/0.42    inference(definition_unfolding,[],[f25,f42])).
% 0.22/0.42  fof(f42,plain,(
% 0.22/0.42    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.22/0.42    inference(definition_unfolding,[],[f26,f41])).
% 0.22/0.42  fof(f41,plain,(
% 0.22/0.42    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.22/0.42    inference(definition_unfolding,[],[f31,f40])).
% 0.22/0.42  fof(f40,plain,(
% 0.22/0.42    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.22/0.42    inference(definition_unfolding,[],[f32,f39])).
% 0.22/0.42  fof(f39,plain,(
% 0.22/0.42    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.22/0.42    inference(definition_unfolding,[],[f35,f38])).
% 0.22/0.42  fof(f38,plain,(
% 0.22/0.42    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.22/0.42    inference(definition_unfolding,[],[f36,f37])).
% 0.22/0.42  fof(f37,plain,(
% 0.22/0.42    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f7])).
% 0.22/0.42  fof(f7,axiom,(
% 0.22/0.42    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 0.22/0.42  fof(f36,plain,(
% 0.22/0.42    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f6])).
% 0.22/0.42  fof(f6,axiom,(
% 0.22/0.42    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 0.22/0.42  fof(f35,plain,(
% 0.22/0.42    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f5])).
% 0.22/0.42  fof(f5,axiom,(
% 0.22/0.42    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.22/0.42  fof(f32,plain,(
% 0.22/0.42    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f4])).
% 0.22/0.42  fof(f4,axiom,(
% 0.22/0.42    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.22/0.42  fof(f31,plain,(
% 0.22/0.42    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f3])).
% 0.22/0.42  fof(f3,axiom,(
% 0.22/0.42    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.42  fof(f26,plain,(
% 0.22/0.42    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f2])).
% 0.22/0.42  fof(f2,axiom,(
% 0.22/0.42    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.42  fof(f25,plain,(
% 0.22/0.42    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f1])).
% 0.22/0.42  fof(f1,axiom,(
% 0.22/0.42    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.42  fof(f30,plain,(
% 0.22/0.42    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f21])).
% 0.22/0.42  fof(f21,plain,(
% 0.22/0.42    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 0.22/0.42    inference(nnf_transformation,[],[f8])).
% 0.22/0.42  fof(f8,axiom,(
% 0.22/0.42    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.22/0.42  fof(f52,plain,(
% 0.22/0.42    ( ! [X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k2_zfmisc_1(X0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k2_zfmisc_1(X1,sK3))) )),
% 0.22/0.42    inference(resolution,[],[f49,f34])).
% 0.22/0.42  fof(f34,plain,(
% 0.22/0.42    ( ! [X2,X0,X3,X1] : (~r1_tarski(X2,X3) | r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f17])).
% 0.22/0.42  fof(f17,plain,(
% 0.22/0.42    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))),
% 0.22/0.42    inference(flattening,[],[f16])).
% 0.22/0.42  fof(f16,plain,(
% 0.22/0.42    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | (~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)))),
% 0.22/0.42    inference(ennf_transformation,[],[f9])).
% 0.22/0.42  fof(f9,axiom,(
% 0.22/0.42    ! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_zfmisc_1)).
% 0.22/0.42  fof(f49,plain,(
% 0.22/0.42    r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)),
% 0.22/0.42    inference(resolution,[],[f45,f23])).
% 0.22/0.42  fof(f23,plain,(
% 0.22/0.42    r2_hidden(sK2,sK3)),
% 0.22/0.42    inference(cnf_transformation,[],[f19])).
% 0.22/0.42  fof(f106,plain,(
% 0.22/0.42    ~m1_subset_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))),
% 0.22/0.42    inference(backward_demodulation,[],[f44,f47])).
% 0.22/0.42  fof(f47,plain,(
% 0.22/0.42    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)) = k6_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))) )),
% 0.22/0.42    inference(definition_unfolding,[],[f33,f42,f42,f40])).
% 0.22/0.42  fof(f33,plain,(
% 0.22/0.42    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))) )),
% 0.22/0.42    inference(cnf_transformation,[],[f10])).
% 0.22/0.42  fof(f10,axiom,(
% 0.22/0.42    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_zfmisc_1)).
% 0.22/0.42  fof(f44,plain,(
% 0.22/0.42    ~m1_subset_1(k6_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))),
% 0.22/0.42    inference(definition_unfolding,[],[f24,f43])).
% 0.22/0.42  fof(f24,plain,(
% 0.22/0.42    ~m1_subset_1(k1_tarski(k4_tarski(sK0,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))),
% 0.22/0.42    inference(cnf_transformation,[],[f19])).
% 0.22/0.42  % SZS output end Proof for theBenchmark
% 0.22/0.42  % (10501)------------------------------
% 0.22/0.42  % (10501)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.42  % (10501)Termination reason: Refutation
% 0.22/0.42  
% 0.22/0.42  % (10501)Memory used [KB]: 1663
% 0.22/0.42  % (10501)Time elapsed: 0.007 s
% 0.22/0.42  % (10501)------------------------------
% 0.22/0.42  % (10501)------------------------------
% 0.22/0.43  % (10488)Success in time 0.065 s
%------------------------------------------------------------------------------
