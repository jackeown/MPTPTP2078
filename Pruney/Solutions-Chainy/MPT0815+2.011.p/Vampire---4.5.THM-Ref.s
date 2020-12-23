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
% DateTime   : Thu Dec  3 12:56:13 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 146 expanded)
%              Number of leaves         :   12 (  44 expanded)
%              Depth                    :   12
%              Number of atoms          :   99 ( 270 expanded)
%              Number of equality atoms :   20 (  84 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f69,plain,(
    $false ),
    inference(resolution,[],[f67,f57])).

fof(f57,plain,(
    r1_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) ),
    inference(resolution,[],[f50,f23])).

fof(f23,plain,(
    r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ~ m1_subset_1(k1_tarski(k4_tarski(sK0,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    & r2_hidden(sK2,sK3)
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ m1_subset_1(k1_tarski(k4_tarski(X0,X2)),k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
        & r2_hidden(X2,X3)
        & r2_hidden(X0,X1) )
   => ( ~ m1_subset_1(k1_tarski(k4_tarski(sK0,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
      & r2_hidden(sK2,sK3)
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ m1_subset_1(k1_tarski(k4_tarski(X0,X2)),k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
      & r2_hidden(X2,X3)
      & r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ m1_subset_1(k1_tarski(k4_tarski(X0,X2)),k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
      & r2_hidden(X2,X3)
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r2_hidden(X2,X3)
          & r2_hidden(X0,X1) )
       => m1_subset_1(k1_tarski(k4_tarski(X0,X2)),k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(X2,X3)
        & r2_hidden(X0,X1) )
     => m1_subset_1(k1_tarski(k4_tarski(X0,X2)),k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_relset_1)).

fof(f50,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK3)
      | r1_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,X1),sK3) ) ),
    inference(resolution,[],[f44,f23])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X1,X2)
      | r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f32,f41])).

fof(f41,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f26,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f29,f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f33,f38])).

fof(f38,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f36,f37])).

fof(f37,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f36,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f33,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f29,plain,(
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

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f67,plain,(
    ~ r1_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) ),
    inference(resolution,[],[f64,f48])).

fof(f48,plain,(
    ~ m1_subset_1(k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
    inference(backward_demodulation,[],[f43,f47])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1),k5_enumset1(X2,X2,X2,X2,X2,X2,X3)) = k5_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(definition_unfolding,[],[f34,f41,f41,f39])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_zfmisc_1)).

fof(f43,plain,(
    ~ m1_subset_1(k5_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
    inference(definition_unfolding,[],[f24,f42])).

fof(f42,plain,(
    ! [X0] : k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f25,f41])).

fof(f25,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f24,plain,(
    ~ m1_subset_1(k1_tarski(k4_tarski(sK0,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
    inference(cnf_transformation,[],[f18])).

fof(f64,plain,(
    ! [X4,X5] :
      ( m1_subset_1(k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),X4),k1_zfmisc_1(k2_zfmisc_1(sK1,X5)))
      | ~ r1_tarski(X4,X5) ) ),
    inference(resolution,[],[f54,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0),k2_zfmisc_1(sK1,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f51,f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X2,X3)
      | r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_zfmisc_1)).

fof(f51,plain,(
    r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) ),
    inference(resolution,[],[f49,f22])).

fof(f22,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f49,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,X0),sK1) ) ),
    inference(resolution,[],[f44,f22])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 19:42:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.45  % (19801)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.45  % (19801)Refutation found. Thanks to Tanya!
% 0.21/0.45  % SZS status Theorem for theBenchmark
% 0.21/0.45  % SZS output start Proof for theBenchmark
% 0.21/0.45  fof(f69,plain,(
% 0.21/0.45    $false),
% 0.21/0.45    inference(resolution,[],[f67,f57])).
% 0.21/0.45  fof(f57,plain,(
% 0.21/0.45    r1_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)),
% 0.21/0.45    inference(resolution,[],[f50,f23])).
% 0.21/0.45  fof(f23,plain,(
% 0.21/0.45    r2_hidden(sK2,sK3)),
% 0.21/0.45    inference(cnf_transformation,[],[f18])).
% 0.21/0.45  fof(f18,plain,(
% 0.21/0.45    ~m1_subset_1(k1_tarski(k4_tarski(sK0,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) & r2_hidden(sK2,sK3) & r2_hidden(sK0,sK1)),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f17])).
% 0.21/0.45  fof(f17,plain,(
% 0.21/0.45    ? [X0,X1,X2,X3] : (~m1_subset_1(k1_tarski(k4_tarski(X0,X2)),k1_zfmisc_1(k2_zfmisc_1(X1,X3))) & r2_hidden(X2,X3) & r2_hidden(X0,X1)) => (~m1_subset_1(k1_tarski(k4_tarski(sK0,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) & r2_hidden(sK2,sK3) & r2_hidden(sK0,sK1))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f14,plain,(
% 0.21/0.45    ? [X0,X1,X2,X3] : (~m1_subset_1(k1_tarski(k4_tarski(X0,X2)),k1_zfmisc_1(k2_zfmisc_1(X1,X3))) & r2_hidden(X2,X3) & r2_hidden(X0,X1))),
% 0.21/0.45    inference(flattening,[],[f13])).
% 0.21/0.45  fof(f13,plain,(
% 0.21/0.45    ? [X0,X1,X2,X3] : (~m1_subset_1(k1_tarski(k4_tarski(X0,X2)),k1_zfmisc_1(k2_zfmisc_1(X1,X3))) & (r2_hidden(X2,X3) & r2_hidden(X0,X1)))),
% 0.21/0.45    inference(ennf_transformation,[],[f12])).
% 0.21/0.45  fof(f12,negated_conjecture,(
% 0.21/0.45    ~! [X0,X1,X2,X3] : ((r2_hidden(X2,X3) & r2_hidden(X0,X1)) => m1_subset_1(k1_tarski(k4_tarski(X0,X2)),k1_zfmisc_1(k2_zfmisc_1(X1,X3))))),
% 0.21/0.45    inference(negated_conjecture,[],[f11])).
% 0.21/0.45  fof(f11,conjecture,(
% 0.21/0.45    ! [X0,X1,X2,X3] : ((r2_hidden(X2,X3) & r2_hidden(X0,X1)) => m1_subset_1(k1_tarski(k4_tarski(X0,X2)),k1_zfmisc_1(k2_zfmisc_1(X1,X3))))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_relset_1)).
% 0.21/0.45  fof(f50,plain,(
% 0.21/0.45    ( ! [X1] : (~r2_hidden(X1,sK3) | r1_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,X1),sK3)) )),
% 0.21/0.45    inference(resolution,[],[f44,f23])).
% 0.21/0.45  fof(f44,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X1,X2) | r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1),X2)) )),
% 0.21/0.45    inference(definition_unfolding,[],[f32,f41])).
% 0.21/0.45  fof(f41,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 0.21/0.45    inference(definition_unfolding,[],[f26,f40])).
% 0.21/0.45  fof(f40,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 0.21/0.45    inference(definition_unfolding,[],[f29,f39])).
% 0.21/0.45  fof(f39,plain,(
% 0.21/0.45    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 0.21/0.45    inference(definition_unfolding,[],[f33,f38])).
% 0.21/0.45  fof(f38,plain,(
% 0.21/0.45    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 0.21/0.45    inference(definition_unfolding,[],[f36,f37])).
% 0.21/0.45  fof(f37,plain,(
% 0.21/0.45    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f6])).
% 0.21/0.45  fof(f6,axiom,(
% 0.21/0.45    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 0.21/0.45  fof(f36,plain,(
% 0.21/0.45    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f5])).
% 0.21/0.45  fof(f5,axiom,(
% 0.21/0.45    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.21/0.45  fof(f33,plain,(
% 0.21/0.45    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f4])).
% 0.21/0.45  fof(f4,axiom,(
% 0.21/0.45    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.45  fof(f29,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f3])).
% 0.21/0.45  fof(f3,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.45  fof(f26,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f2])).
% 0.21/0.45  fof(f2,axiom,(
% 0.21/0.45    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.45  fof(f32,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f21])).
% 0.21/0.45  fof(f21,plain,(
% 0.21/0.45    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.21/0.45    inference(flattening,[],[f20])).
% 0.21/0.45  fof(f20,plain,(
% 0.21/0.45    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.21/0.45    inference(nnf_transformation,[],[f9])).
% 0.21/0.45  fof(f9,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 0.21/0.45  fof(f67,plain,(
% 0.21/0.45    ~r1_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)),
% 0.21/0.45    inference(resolution,[],[f64,f48])).
% 0.21/0.45  fof(f48,plain,(
% 0.21/0.45    ~m1_subset_1(k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))),
% 0.21/0.45    inference(backward_demodulation,[],[f43,f47])).
% 0.21/0.45  fof(f47,plain,(
% 0.21/0.45    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1),k5_enumset1(X2,X2,X2,X2,X2,X2,X3)) = k5_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))) )),
% 0.21/0.45    inference(definition_unfolding,[],[f34,f41,f41,f39])).
% 0.21/0.45  fof(f34,plain,(
% 0.21/0.45    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f8])).
% 0.21/0.45  fof(f8,axiom,(
% 0.21/0.45    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_zfmisc_1)).
% 0.21/0.45  fof(f43,plain,(
% 0.21/0.45    ~m1_subset_1(k5_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))),
% 0.21/0.45    inference(definition_unfolding,[],[f24,f42])).
% 0.21/0.45  fof(f42,plain,(
% 0.21/0.45    ( ! [X0] : (k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) )),
% 0.21/0.45    inference(definition_unfolding,[],[f25,f41])).
% 0.21/0.45  fof(f25,plain,(
% 0.21/0.45    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f1])).
% 0.21/0.45  fof(f1,axiom,(
% 0.21/0.45    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.45  fof(f24,plain,(
% 0.21/0.45    ~m1_subset_1(k1_tarski(k4_tarski(sK0,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))),
% 0.21/0.45    inference(cnf_transformation,[],[f18])).
% 0.21/0.45  fof(f64,plain,(
% 0.21/0.45    ( ! [X4,X5] : (m1_subset_1(k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),X4),k1_zfmisc_1(k2_zfmisc_1(sK1,X5))) | ~r1_tarski(X4,X5)) )),
% 0.21/0.45    inference(resolution,[],[f54,f28])).
% 0.21/0.45  fof(f28,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f19])).
% 0.21/0.45  fof(f19,plain,(
% 0.21/0.45    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.45    inference(nnf_transformation,[],[f10])).
% 0.21/0.45  fof(f10,axiom,(
% 0.21/0.45    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.45  fof(f54,plain,(
% 0.21/0.45    ( ! [X0,X1] : (r1_tarski(k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0),k2_zfmisc_1(sK1,X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.45    inference(resolution,[],[f51,f35])).
% 0.21/0.45  fof(f35,plain,(
% 0.21/0.45    ( ! [X2,X0,X3,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X2,X3) | r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f16])).
% 0.21/0.45  fof(f16,plain,(
% 0.21/0.45    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))),
% 0.21/0.45    inference(flattening,[],[f15])).
% 0.21/0.45  fof(f15,plain,(
% 0.21/0.45    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | (~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)))),
% 0.21/0.45    inference(ennf_transformation,[],[f7])).
% 0.21/0.45  fof(f7,axiom,(
% 0.21/0.45    ! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_zfmisc_1)).
% 0.21/0.45  fof(f51,plain,(
% 0.21/0.45    r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),
% 0.21/0.45    inference(resolution,[],[f49,f22])).
% 0.21/0.45  fof(f22,plain,(
% 0.21/0.45    r2_hidden(sK0,sK1)),
% 0.21/0.45    inference(cnf_transformation,[],[f18])).
% 0.21/0.45  fof(f49,plain,(
% 0.21/0.45    ( ! [X0] : (~r2_hidden(X0,sK1) | r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,X0),sK1)) )),
% 0.21/0.45    inference(resolution,[],[f44,f22])).
% 0.21/0.45  % SZS output end Proof for theBenchmark
% 0.21/0.45  % (19801)------------------------------
% 0.21/0.45  % (19801)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (19801)Termination reason: Refutation
% 0.21/0.45  
% 0.21/0.45  % (19801)Memory used [KB]: 1663
% 0.21/0.45  % (19801)Time elapsed: 0.008 s
% 0.21/0.45  % (19801)------------------------------
% 0.21/0.45  % (19801)------------------------------
% 0.21/0.45  % (19799)Success in time 0.097 s
%------------------------------------------------------------------------------
