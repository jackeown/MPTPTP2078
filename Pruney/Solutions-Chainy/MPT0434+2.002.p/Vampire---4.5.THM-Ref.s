%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:54 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   42 (  73 expanded)
%              Number of leaves         :   11 (  25 expanded)
%              Depth                    :   11
%              Number of atoms          :   78 ( 179 expanded)
%              Number of equality atoms :   15 (  20 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f264,plain,(
    $false ),
    inference(resolution,[],[f263,f119])).

fof(f119,plain,(
    r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_xboole_0(sK0,sK1))) ),
    inference(superposition,[],[f23,f97])).

fof(f97,plain,(
    k1_relat_1(k2_xboole_0(sK0,sK1)) = k2_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) ),
    inference(resolution,[],[f93,f19])).

fof(f19,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ~ r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k6_subset_1(sK0,sK1)))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f16,f15])).

fof(f15,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(sK0,X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(sK0,X1)))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k6_subset_1(sK0,sK1)))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_relat_1)).

fof(f93,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(k2_xboole_0(sK0,X0)) = k2_xboole_0(k1_relat_1(sK0),k1_relat_1(X0)) ) ),
    inference(resolution,[],[f21,f18])).

fof(f18,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relat_1)).

fof(f23,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f263,plain,(
    ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f262,f26])).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f262,plain,(
    ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_xboole_0(sK1,sK0))) ),
    inference(forward_demodulation,[],[f241,f29])).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k6_subset_1(X1,X0)) ),
    inference(definition_unfolding,[],[f27,f25])).

fof(f25,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f241,plain,(
    ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,sK1)))) ),
    inference(backward_demodulation,[],[f56,f238])).

fof(f238,plain,(
    ! [X0] : k1_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,X0))) = k2_xboole_0(k1_relat_1(sK1),k1_relat_1(k6_subset_1(sK0,X0))) ),
    inference(resolution,[],[f141,f18])).

fof(f141,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(k2_xboole_0(sK1,k6_subset_1(X0,X1))) = k2_xboole_0(k1_relat_1(sK1),k1_relat_1(k6_subset_1(X0,X1))) ) ),
    inference(resolution,[],[f94,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k6_subset_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f22,f24])).

fof(f24,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
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

fof(f94,plain,(
    ! [X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k2_xboole_0(sK1,X1)) = k2_xboole_0(k1_relat_1(sK1),k1_relat_1(X1)) ) ),
    inference(resolution,[],[f21,f19])).

fof(f56,plain,(
    ~ r1_tarski(k1_relat_1(sK0),k2_xboole_0(k1_relat_1(sK1),k1_relat_1(k6_subset_1(sK0,sK1)))) ),
    inference(resolution,[],[f30,f20])).

fof(f20,plain,(
    ~ r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k6_subset_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f17])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k6_subset_1(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(definition_unfolding,[],[f28,f25])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:27:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.42  % (14929)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.43  % (14929)Refutation found. Thanks to Tanya!
% 0.20/0.43  % SZS status Theorem for theBenchmark
% 0.20/0.43  % SZS output start Proof for theBenchmark
% 0.20/0.43  fof(f264,plain,(
% 0.20/0.43    $false),
% 0.20/0.43    inference(resolution,[],[f263,f119])).
% 0.20/0.43  fof(f119,plain,(
% 0.20/0.43    r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_xboole_0(sK0,sK1)))),
% 0.20/0.43    inference(superposition,[],[f23,f97])).
% 0.20/0.43  fof(f97,plain,(
% 0.20/0.43    k1_relat_1(k2_xboole_0(sK0,sK1)) = k2_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))),
% 0.20/0.43    inference(resolution,[],[f93,f19])).
% 0.20/0.43  fof(f19,plain,(
% 0.20/0.43    v1_relat_1(sK1)),
% 0.20/0.43    inference(cnf_transformation,[],[f17])).
% 0.20/0.43  fof(f17,plain,(
% 0.20/0.43    (~r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k6_subset_1(sK0,sK1))) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.20/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f16,f15])).
% 0.20/0.43  fof(f15,plain,(
% 0.20/0.43    ? [X0] : (? [X1] : (~r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(sK0,X1))) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f16,plain,(
% 0.20/0.43    ? [X1] : (~r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(sK0,X1))) & v1_relat_1(X1)) => (~r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k6_subset_1(sK0,sK1))) & v1_relat_1(sK1))),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f11,plain,(
% 0.20/0.43    ? [X0] : (? [X1] : (~r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.20/0.43    inference(ennf_transformation,[],[f10])).
% 0.20/0.43  fof(f10,negated_conjecture,(
% 0.20/0.43    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))))),
% 0.20/0.43    inference(negated_conjecture,[],[f9])).
% 0.20/0.43  fof(f9,conjecture,(
% 0.20/0.43    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_relat_1)).
% 0.20/0.43  fof(f93,plain,(
% 0.20/0.43    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(k2_xboole_0(sK0,X0)) = k2_xboole_0(k1_relat_1(sK0),k1_relat_1(X0))) )),
% 0.20/0.43    inference(resolution,[],[f21,f18])).
% 0.20/0.43  fof(f18,plain,(
% 0.20/0.43    v1_relat_1(sK0)),
% 0.20/0.43    inference(cnf_transformation,[],[f17])).
% 0.20/0.43  fof(f21,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f12])).
% 0.20/0.43  fof(f12,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : (k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.43    inference(ennf_transformation,[],[f8])).
% 0.20/0.43  fof(f8,axiom,(
% 0.20/0.43    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1))))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relat_1)).
% 0.20/0.43  fof(f23,plain,(
% 0.20/0.43    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f4])).
% 0.20/0.43  fof(f4,axiom,(
% 0.20/0.43    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.20/0.43  fof(f263,plain,(
% 0.20/0.43    ~r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_xboole_0(sK0,sK1)))),
% 0.20/0.43    inference(forward_demodulation,[],[f262,f26])).
% 0.20/0.43  fof(f26,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f1])).
% 0.20/0.43  fof(f1,axiom,(
% 0.20/0.43    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.20/0.43  fof(f262,plain,(
% 0.20/0.43    ~r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_xboole_0(sK1,sK0)))),
% 0.20/0.43    inference(forward_demodulation,[],[f241,f29])).
% 0.20/0.43  fof(f29,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k6_subset_1(X1,X0))) )),
% 0.20/0.43    inference(definition_unfolding,[],[f27,f25])).
% 0.20/0.43  fof(f25,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f6])).
% 0.20/0.43  fof(f6,axiom,(
% 0.20/0.43    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.20/0.43  fof(f27,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f2])).
% 0.20/0.43  fof(f2,axiom,(
% 0.20/0.43    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.20/0.43  fof(f241,plain,(
% 0.20/0.43    ~r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,sK1))))),
% 0.20/0.43    inference(backward_demodulation,[],[f56,f238])).
% 0.20/0.43  fof(f238,plain,(
% 0.20/0.43    ( ! [X0] : (k1_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,X0))) = k2_xboole_0(k1_relat_1(sK1),k1_relat_1(k6_subset_1(sK0,X0)))) )),
% 0.20/0.43    inference(resolution,[],[f141,f18])).
% 0.20/0.43  fof(f141,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~v1_relat_1(X0) | k1_relat_1(k2_xboole_0(sK1,k6_subset_1(X0,X1))) = k2_xboole_0(k1_relat_1(sK1),k1_relat_1(k6_subset_1(X0,X1)))) )),
% 0.20/0.43    inference(resolution,[],[f94,f35])).
% 0.20/0.43  fof(f35,plain,(
% 0.20/0.43    ( ! [X0,X1] : (v1_relat_1(k6_subset_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.20/0.43    inference(resolution,[],[f22,f24])).
% 0.20/0.43  fof(f24,plain,(
% 0.20/0.43    ( ! [X0,X1] : (m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f5])).
% 0.20/0.43  fof(f5,axiom,(
% 0.20/0.43    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).
% 0.20/0.43  fof(f22,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f13])).
% 0.20/0.43  fof(f13,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.43    inference(ennf_transformation,[],[f7])).
% 0.20/0.43  fof(f7,axiom,(
% 0.20/0.43    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.43  fof(f94,plain,(
% 0.20/0.43    ( ! [X1] : (~v1_relat_1(X1) | k1_relat_1(k2_xboole_0(sK1,X1)) = k2_xboole_0(k1_relat_1(sK1),k1_relat_1(X1))) )),
% 0.20/0.43    inference(resolution,[],[f21,f19])).
% 0.20/0.43  fof(f56,plain,(
% 0.20/0.43    ~r1_tarski(k1_relat_1(sK0),k2_xboole_0(k1_relat_1(sK1),k1_relat_1(k6_subset_1(sK0,sK1))))),
% 0.20/0.43    inference(resolution,[],[f30,f20])).
% 0.20/0.43  fof(f20,plain,(
% 0.20/0.43    ~r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k6_subset_1(sK0,sK1)))),
% 0.20/0.43    inference(cnf_transformation,[],[f17])).
% 0.20/0.43  fof(f30,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 0.20/0.43    inference(definition_unfolding,[],[f28,f25])).
% 0.20/0.43  fof(f28,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f14])).
% 0.20/0.43  fof(f14,plain,(
% 0.20/0.43    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.20/0.43    inference(ennf_transformation,[],[f3])).
% 0.20/0.43  fof(f3,axiom,(
% 0.20/0.43    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).
% 0.20/0.43  % SZS output end Proof for theBenchmark
% 0.20/0.43  % (14929)------------------------------
% 0.20/0.43  % (14929)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.43  % (14929)Termination reason: Refutation
% 0.20/0.43  
% 0.20/0.43  % (14929)Memory used [KB]: 6268
% 0.20/0.43  % (14929)Time elapsed: 0.012 s
% 0.20/0.43  % (14929)------------------------------
% 0.20/0.43  % (14929)------------------------------
% 0.20/0.43  % (14925)Success in time 0.076 s
%------------------------------------------------------------------------------
