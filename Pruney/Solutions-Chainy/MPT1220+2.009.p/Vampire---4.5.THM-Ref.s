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
% DateTime   : Thu Dec  3 13:10:47 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   43 (  61 expanded)
%              Number of leaves         :    8 (  14 expanded)
%              Depth                    :   14
%              Number of atoms          :  115 ( 174 expanded)
%              Number of equality atoms :   24 (  41 expanded)
%              Maximal formula depth    :    7 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f101,plain,(
    $false ),
    inference(subsumption_resolution,[],[f100,f31])).

fof(f31,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f100,plain,(
    ~ r1_tarski(k2_struct_0(sK0),k2_struct_0(sK0)) ),
    inference(resolution,[],[f94,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f94,plain,(
    ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f93,f20])).

fof(f20,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( k2_struct_0(sK0) != k2_pre_topc(sK0,k2_struct_0(sK0))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f15])).

fof(f15,plain,
    ( ? [X0] :
        ( k2_struct_0(X0) != k2_pre_topc(X0,k2_struct_0(X0))
        & l1_pre_topc(X0) )
   => ( k2_struct_0(sK0) != k2_pre_topc(sK0,k2_struct_0(sK0))
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( k2_struct_0(X0) != k2_pre_topc(X0,k2_struct_0(X0))
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0)) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_tops_1)).

fof(f93,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(trivial_inequality_removal,[],[f77])).

fof(f77,plain,
    ( k2_struct_0(sK0) != k2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(superposition,[],[f21,f76])).

fof(f76,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(k2_struct_0(X0))) ) ),
    inference(subsumption_resolution,[],[f60,f23])).

fof(f23,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f60,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(k2_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(superposition,[],[f59,f22])).

fof(f22,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f59,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_pre_topc(X0,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(subsumption_resolution,[],[f58,f31])).

fof(f58,plain,(
    ! [X0] :
      ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X0))
      | u1_struct_0(X0) = k2_pre_topc(X0,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(duplicate_literal_removal,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X0))
      | u1_struct_0(X0) = k2_pre_topc(X0,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(resolution,[],[f39,f43])).

fof(f43,plain,(
    ! [X2,X3] :
      ( r1_tarski(k2_pre_topc(X3,X2),u1_struct_0(X3))
      | ~ l1_pre_topc(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3))) ) ),
    inference(resolution,[],[f25,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_pre_topc(X0,X1),X1)
      | ~ r1_tarski(X1,u1_struct_0(X0))
      | k2_pre_topc(X0,X1) = X1
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f36,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k2_pre_topc(X1,X0))
      | ~ l1_pre_topc(X1)
      | ~ r1_tarski(X0,u1_struct_0(X1)) ) ),
    inference(resolution,[],[f24,f30])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

fof(f21,plain,(
    k2_struct_0(sK0) != k2_pre_topc(sK0,k2_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 11:54:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.50  % (27464)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.50  % (27464)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f101,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(subsumption_resolution,[],[f100,f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.50    inference(equality_resolution,[],[f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.50    inference(flattening,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.50    inference(nnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.50  fof(f100,plain,(
% 0.21/0.50    ~r1_tarski(k2_struct_0(sK0),k2_struct_0(sK0))),
% 0.21/0.50    inference(resolution,[],[f94,f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.50    inference(nnf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.50  fof(f94,plain,(
% 0.21/0.50    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.21/0.50    inference(subsumption_resolution,[],[f93,f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    l1_pre_topc(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    k2_struct_0(sK0) != k2_pre_topc(sK0,k2_struct_0(sK0)) & l1_pre_topc(sK0)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ? [X0] : (k2_struct_0(X0) != k2_pre_topc(X0,k2_struct_0(X0)) & l1_pre_topc(X0)) => (k2_struct_0(sK0) != k2_pre_topc(sK0,k2_struct_0(sK0)) & l1_pre_topc(sK0))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f9,plain,(
% 0.21/0.50    ? [X0] : (k2_struct_0(X0) != k2_pre_topc(X0,k2_struct_0(X0)) & l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,negated_conjecture,(
% 0.21/0.50    ~! [X0] : (l1_pre_topc(X0) => k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0)))),
% 0.21/0.50    inference(negated_conjecture,[],[f7])).
% 0.21/0.50  fof(f7,conjecture,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_tops_1)).
% 0.21/0.50  fof(f93,plain,(
% 0.21/0.50    ~l1_pre_topc(sK0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.21/0.50    inference(trivial_inequality_removal,[],[f77])).
% 0.21/0.50  fof(f77,plain,(
% 0.21/0.50    k2_struct_0(sK0) != k2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.21/0.50    inference(superposition,[],[f21,f76])).
% 0.21/0.50  fof(f76,plain,(
% 0.21/0.50    ( ! [X0] : (k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0)) | ~l1_pre_topc(X0) | ~m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(k2_struct_0(X0)))) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f60,f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,plain,(
% 0.21/0.50    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    ( ! [X0] : (k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0)) | ~l1_pre_topc(X0) | ~m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(k2_struct_0(X0))) | ~l1_struct_0(X0)) )),
% 0.21/0.50    inference(superposition,[],[f59,f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,plain,(
% 0.21/0.50    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    ( ! [X0] : (u1_struct_0(X0) = k2_pre_topc(X0,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f58,f31])).
% 0.21/0.50  fof(f58,plain,(
% 0.21/0.50    ( ! [X0] : (~r1_tarski(u1_struct_0(X0),u1_struct_0(X0)) | u1_struct_0(X0) = k2_pre_topc(X0,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f55])).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    ( ! [X0] : (~r1_tarski(u1_struct_0(X0),u1_struct_0(X0)) | u1_struct_0(X0) = k2_pre_topc(X0,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.21/0.50    inference(resolution,[],[f39,f43])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    ( ! [X2,X3] : (r1_tarski(k2_pre_topc(X3,X2),u1_struct_0(X3)) | ~l1_pre_topc(X3) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))) )),
% 0.21/0.50    inference(resolution,[],[f25,f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(flattening,[],[f13])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_tarski(k2_pre_topc(X0,X1),X1) | ~r1_tarski(X1,u1_struct_0(X0)) | k2_pre_topc(X0,X1) = X1 | ~l1_pre_topc(X0)) )),
% 0.21/0.50    inference(resolution,[],[f36,f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_tarski(X0,k2_pre_topc(X1,X0)) | ~l1_pre_topc(X1) | ~r1_tarski(X0,u1_struct_0(X1))) )),
% 0.21/0.50    inference(resolution,[],[f24,f30])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(X1,k2_pre_topc(X0,X1)) | ~l1_pre_topc(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    k2_struct_0(sK0) != k2_pre_topc(sK0,k2_struct_0(sK0))),
% 0.21/0.50    inference(cnf_transformation,[],[f16])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (27464)------------------------------
% 0.21/0.50  % (27464)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (27464)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (27464)Memory used [KB]: 6140
% 0.21/0.50  % (27464)Time elapsed: 0.088 s
% 0.21/0.50  % (27464)------------------------------
% 0.21/0.50  % (27464)------------------------------
% 0.21/0.51  % (27453)Success in time 0.142 s
%------------------------------------------------------------------------------
