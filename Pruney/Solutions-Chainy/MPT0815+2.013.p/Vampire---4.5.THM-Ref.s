%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:13 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   42 ( 101 expanded)
%              Number of leaves         :    9 (  29 expanded)
%              Depth                    :   11
%              Number of atoms          :   91 ( 226 expanded)
%              Number of equality atoms :   12 (  40 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f83,plain,(
    $false ),
    inference(resolution,[],[f82,f49])).

fof(f49,plain,(
    r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),sK3) ),
    inference(resolution,[],[f42,f20])).

fof(f20,plain,(
    r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ~ m1_subset_1(k1_tarski(k4_tarski(sK0,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    & r2_hidden(sK2,sK3)
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ m1_subset_1(k1_tarski(k4_tarski(X0,X2)),k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
        & r2_hidden(X2,X3)
        & r2_hidden(X0,X1) )
   => ( ~ m1_subset_1(k1_tarski(k4_tarski(sK0,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
      & r2_hidden(sK2,sK3)
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ m1_subset_1(k1_tarski(k4_tarski(X0,X2)),k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
      & r2_hidden(X2,X3)
      & r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ m1_subset_1(k1_tarski(k4_tarski(X0,X2)),k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
      & r2_hidden(X2,X3)
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r2_hidden(X2,X3)
          & r2_hidden(X0,X1) )
       => m1_subset_1(k1_tarski(k4_tarski(X0,X2)),k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(X2,X3)
        & r2_hidden(X0,X1) )
     => m1_subset_1(k1_tarski(k4_tarski(X0,X2)),k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_relset_1)).

fof(f42,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK3)
      | r1_tarski(k2_enumset1(sK2,sK2,sK2,X1),sK3) ) ),
    inference(resolution,[],[f38,f20])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X1,X2)
      | r1_tarski(k2_enumset1(X0,X0,X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f31,f33])).

fof(f33,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f23,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f23,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f82,plain,(
    ~ r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),sK3) ),
    inference(resolution,[],[f79,f56])).

fof(f56,plain,(
    ! [X4,X5] :
      ( m1_subset_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),X4),k1_zfmisc_1(k2_zfmisc_1(sK1,X5)))
      | ~ r1_tarski(X4,X5) ) ),
    inference(resolution,[],[f46,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),X0),k2_zfmisc_1(sK1,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f43,f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X2,X3)
      | r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_zfmisc_1)).

fof(f43,plain,(
    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(resolution,[],[f41,f19])).

fof(f19,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f41,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | r1_tarski(k2_enumset1(sK0,sK0,sK0,X0),sK1) ) ),
    inference(resolution,[],[f38,f19])).

fof(f79,plain,(
    ~ m1_subset_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK2,sK2,sK2,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
    inference(backward_demodulation,[],[f35,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X2)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2)) ),
    inference(definition_unfolding,[],[f28,f33,f34,f33])).

fof(f34,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f22,f33])).

fof(f22,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f28,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))
      & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(f35,plain,(
    ~ m1_subset_1(k2_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
    inference(definition_unfolding,[],[f21,f34])).

fof(f21,plain,(
    ~ m1_subset_1(k1_tarski(k4_tarski(sK0,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:15:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.42  % (16677)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.43  % (16677)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.44  % (16686)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.44  % SZS output start Proof for theBenchmark
% 0.21/0.44  fof(f83,plain,(
% 0.21/0.44    $false),
% 0.21/0.44    inference(resolution,[],[f82,f49])).
% 0.21/0.44  fof(f49,plain,(
% 0.21/0.44    r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),sK3)),
% 0.21/0.44    inference(resolution,[],[f42,f20])).
% 0.21/0.44  fof(f20,plain,(
% 0.21/0.44    r2_hidden(sK2,sK3)),
% 0.21/0.44    inference(cnf_transformation,[],[f15])).
% 0.21/0.44  fof(f15,plain,(
% 0.21/0.44    ~m1_subset_1(k1_tarski(k4_tarski(sK0,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) & r2_hidden(sK2,sK3) & r2_hidden(sK0,sK1)),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f14])).
% 0.21/0.44  fof(f14,plain,(
% 0.21/0.44    ? [X0,X1,X2,X3] : (~m1_subset_1(k1_tarski(k4_tarski(X0,X2)),k1_zfmisc_1(k2_zfmisc_1(X1,X3))) & r2_hidden(X2,X3) & r2_hidden(X0,X1)) => (~m1_subset_1(k1_tarski(k4_tarski(sK0,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) & r2_hidden(sK2,sK3) & r2_hidden(sK0,sK1))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f11,plain,(
% 0.21/0.44    ? [X0,X1,X2,X3] : (~m1_subset_1(k1_tarski(k4_tarski(X0,X2)),k1_zfmisc_1(k2_zfmisc_1(X1,X3))) & r2_hidden(X2,X3) & r2_hidden(X0,X1))),
% 0.21/0.44    inference(flattening,[],[f10])).
% 0.21/0.44  fof(f10,plain,(
% 0.21/0.44    ? [X0,X1,X2,X3] : (~m1_subset_1(k1_tarski(k4_tarski(X0,X2)),k1_zfmisc_1(k2_zfmisc_1(X1,X3))) & (r2_hidden(X2,X3) & r2_hidden(X0,X1)))),
% 0.21/0.44    inference(ennf_transformation,[],[f9])).
% 0.21/0.44  fof(f9,negated_conjecture,(
% 0.21/0.44    ~! [X0,X1,X2,X3] : ((r2_hidden(X2,X3) & r2_hidden(X0,X1)) => m1_subset_1(k1_tarski(k4_tarski(X0,X2)),k1_zfmisc_1(k2_zfmisc_1(X1,X3))))),
% 0.21/0.44    inference(negated_conjecture,[],[f8])).
% 0.21/0.44  fof(f8,conjecture,(
% 0.21/0.44    ! [X0,X1,X2,X3] : ((r2_hidden(X2,X3) & r2_hidden(X0,X1)) => m1_subset_1(k1_tarski(k4_tarski(X0,X2)),k1_zfmisc_1(k2_zfmisc_1(X1,X3))))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_relset_1)).
% 0.21/0.44  fof(f42,plain,(
% 0.21/0.44    ( ! [X1] : (~r2_hidden(X1,sK3) | r1_tarski(k2_enumset1(sK2,sK2,sK2,X1),sK3)) )),
% 0.21/0.44    inference(resolution,[],[f38,f20])).
% 0.21/0.44  fof(f38,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X1,X2) | r1_tarski(k2_enumset1(X0,X0,X0,X1),X2)) )),
% 0.21/0.44    inference(definition_unfolding,[],[f31,f33])).
% 0.21/0.44  fof(f33,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.44    inference(definition_unfolding,[],[f23,f26])).
% 0.21/0.44  fof(f26,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f3])).
% 0.21/0.44  fof(f3,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.44  fof(f23,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f2])).
% 0.21/0.44  fof(f2,axiom,(
% 0.21/0.44    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.44  fof(f31,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f18])).
% 0.21/0.44  fof(f18,plain,(
% 0.21/0.44    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.21/0.44    inference(flattening,[],[f17])).
% 0.21/0.44  fof(f17,plain,(
% 0.21/0.44    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.21/0.44    inference(nnf_transformation,[],[f6])).
% 0.21/0.44  fof(f6,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 0.21/0.44  fof(f82,plain,(
% 0.21/0.44    ~r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),sK3)),
% 0.21/0.44    inference(resolution,[],[f79,f56])).
% 0.21/0.44  fof(f56,plain,(
% 0.21/0.44    ( ! [X4,X5] : (m1_subset_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),X4),k1_zfmisc_1(k2_zfmisc_1(sK1,X5))) | ~r1_tarski(X4,X5)) )),
% 0.21/0.44    inference(resolution,[],[f46,f25])).
% 0.21/0.44  fof(f25,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f16])).
% 0.21/0.44  fof(f16,plain,(
% 0.21/0.44    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.44    inference(nnf_transformation,[],[f7])).
% 0.21/0.44  fof(f7,axiom,(
% 0.21/0.44    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.44  fof(f46,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r1_tarski(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),X0),k2_zfmisc_1(sK1,X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.44    inference(resolution,[],[f43,f32])).
% 0.21/0.44  fof(f32,plain,(
% 0.21/0.44    ( ! [X2,X0,X3,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X2,X3) | r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f13])).
% 0.21/0.44  fof(f13,plain,(
% 0.21/0.44    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))),
% 0.21/0.44    inference(flattening,[],[f12])).
% 0.21/0.44  fof(f12,plain,(
% 0.21/0.44    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | (~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)))),
% 0.21/0.44    inference(ennf_transformation,[],[f4])).
% 0.21/0.44  fof(f4,axiom,(
% 0.21/0.44    ! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_zfmisc_1)).
% 0.21/0.44  fof(f43,plain,(
% 0.21/0.44    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 0.21/0.44    inference(resolution,[],[f41,f19])).
% 0.21/0.44  fof(f19,plain,(
% 0.21/0.44    r2_hidden(sK0,sK1)),
% 0.21/0.44    inference(cnf_transformation,[],[f15])).
% 0.21/0.44  fof(f41,plain,(
% 0.21/0.44    ( ! [X0] : (~r2_hidden(X0,sK1) | r1_tarski(k2_enumset1(sK0,sK0,sK0,X0),sK1)) )),
% 0.21/0.44    inference(resolution,[],[f38,f19])).
% 0.21/0.44  fof(f79,plain,(
% 0.21/0.44    ~m1_subset_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK2,sK2,sK2,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))),
% 0.21/0.44    inference(backward_demodulation,[],[f35,f36])).
% 0.21/0.44  fof(f36,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X2)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2))) )),
% 0.21/0.44    inference(definition_unfolding,[],[f28,f33,f34,f33])).
% 0.21/0.44  fof(f34,plain,(
% 0.21/0.44    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.21/0.44    inference(definition_unfolding,[],[f22,f33])).
% 0.21/0.44  fof(f22,plain,(
% 0.21/0.44    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f1])).
% 0.21/0.44  fof(f1,axiom,(
% 0.21/0.44    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.44  fof(f28,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f5])).
% 0.21/0.44  fof(f5,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).
% 0.21/0.44  fof(f35,plain,(
% 0.21/0.44    ~m1_subset_1(k2_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))),
% 0.21/0.44    inference(definition_unfolding,[],[f21,f34])).
% 0.21/0.44  fof(f21,plain,(
% 0.21/0.44    ~m1_subset_1(k1_tarski(k4_tarski(sK0,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))),
% 0.21/0.44    inference(cnf_transformation,[],[f15])).
% 0.21/0.44  % SZS output end Proof for theBenchmark
% 0.21/0.44  % (16677)------------------------------
% 0.21/0.44  % (16677)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (16677)Termination reason: Refutation
% 0.21/0.44  
% 0.21/0.44  % (16677)Memory used [KB]: 6140
% 0.21/0.44  % (16677)Time elapsed: 0.034 s
% 0.21/0.44  % (16677)------------------------------
% 0.21/0.44  % (16677)------------------------------
% 0.21/0.44  % (16672)Success in time 0.08 s
%------------------------------------------------------------------------------
