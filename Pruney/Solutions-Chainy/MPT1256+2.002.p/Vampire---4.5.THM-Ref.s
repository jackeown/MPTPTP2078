%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:27 EST 2020

% Result     : Theorem 6.41s
% Output     : Refutation 6.41s
% Verified   : 
% Statistics : Number of formulae       :   62 (  92 expanded)
%              Number of leaves         :   13 (  25 expanded)
%              Depth                    :   14
%              Number of atoms          :  185 ( 268 expanded)
%              Number of equality atoms :   20 (  26 expanded)
%              Maximal formula depth    :    8 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8038,plain,(
    $false ),
    inference(subsumption_resolution,[],[f8037,f47])).

fof(f47,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_tops_1(sK0,sK1))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f41,f40])).

fof(f40,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1))
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,X1)),k2_tops_1(sK0,X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,X1)),k2_tops_1(sK0,X1))
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_tops_1(sK0,sK1))
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_tops_1)).

fof(f8037,plain,(
    ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f8023,f46])).

fof(f46,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f8023,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f8019,f48])).

fof(f48,plain,(
    ~ r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_tops_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f42])).

fof(f8019,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(subsumption_resolution,[],[f8012,f525])).

fof(f525,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f524,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f524,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f523])).

fof(f523,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f515,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

fof(f515,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(subsumption_resolution,[],[f510,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f510,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f454,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f454,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,k3_subset_1(X0,X1),X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(subsumption_resolution,[],[f434,f326])).

fof(f326,plain,(
    ! [X4,X5,X3] :
      ( m1_subset_1(k7_subset_1(X3,X4,X5),k1_zfmisc_1(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(X3))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X3)) ) ),
    inference(subsumption_resolution,[],[f303,f53])).

fof(f303,plain,(
    ! [X4,X5,X3] :
      ( m1_subset_1(k7_subset_1(X3,X4,X5),k1_zfmisc_1(X3))
      | ~ m1_subset_1(k3_subset_1(X3,X5),k1_zfmisc_1(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(X3))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X3)) ) ),
    inference(superposition,[],[f66,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(f434,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,k3_subset_1(X0,X1),X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f53,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_subset_1)).

fof(f8012,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(duplicate_literal_removal,[],[f8005])).

fof(f8005,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f1624,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_1)).

fof(f1624,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1))),k2_tops_1(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(duplicate_literal_removal,[],[f1617])).

fof(f1617,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1))),k2_tops_1(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(superposition,[],[f164,f365])).

fof(f365,plain,(
    ! [X2,X3] :
      ( k1_tops_1(X2,k3_subset_1(u1_struct_0(X2),X3)) = k3_subset_1(u1_struct_0(X2),k2_pre_topc(X2,X3))
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(subsumption_resolution,[],[f349,f53])).

fof(f349,plain,(
    ! [X2,X3] :
      ( k1_tops_1(X2,k3_subset_1(u1_struct_0(X2),X3)) = k3_subset_1(u1_struct_0(X2),k2_pre_topc(X2,X3))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(X2),X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(superposition,[],[f52,f55])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

fof(f164,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tops_1(X0,k1_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))),k2_tops_1(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(subsumption_resolution,[],[f163,f53])).

fof(f163,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tops_1(X0,k1_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))),k2_tops_1(X0,X1))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(duplicate_literal_removal,[],[f158])).

fof(f158,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tops_1(X0,k1_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))),k2_tops_1(X0,X1))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f49,f50])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tops_1(X0,k1_tops_1(X0,X1)),k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,k1_tops_1(X0,X1)),k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k2_tops_1(X0,k1_tops_1(X0,X1)),k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_tops_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:47:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (22477)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.51  % (22492)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.51  % (22484)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.51  % (22476)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.51  % (22495)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.51  % (22482)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.53  % (22501)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.20/0.53  % (22487)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.54  % (22479)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.43/0.55  % (22478)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.43/0.55  % (22500)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.43/0.55  % (22474)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.43/0.56  % (22496)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.60/0.56  % (22488)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.60/0.56  % (22481)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.60/0.56  % (22480)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.60/0.56  % (22499)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.60/0.57  % (22491)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.60/0.57  % (22497)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.60/0.57  % (22485)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.60/0.58  % (22493)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.60/0.58  % (22490)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.60/0.58  % (22475)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.60/0.58  % (22498)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.60/0.61  % (22494)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.60/0.62  % (22483)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 3.09/0.79  % (22483)Refutation not found, incomplete strategy% (22483)------------------------------
% 3.09/0.79  % (22483)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.09/0.80  % (22483)Termination reason: Refutation not found, incomplete strategy
% 3.09/0.80  
% 3.09/0.80  % (22483)Memory used [KB]: 6140
% 3.09/0.80  % (22483)Time elapsed: 0.357 s
% 3.09/0.80  % (22483)------------------------------
% 3.09/0.80  % (22483)------------------------------
% 3.93/0.91  % (22474)Time limit reached!
% 3.93/0.91  % (22474)------------------------------
% 3.93/0.91  % (22474)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.93/0.91  % (22474)Termination reason: Time limit
% 3.93/0.91  % (22474)Termination phase: Saturation
% 3.93/0.91  
% 3.93/0.91  % (22474)Memory used [KB]: 13176
% 3.93/0.91  % (22474)Time elapsed: 0.500 s
% 3.93/0.91  % (22474)------------------------------
% 3.93/0.91  % (22474)------------------------------
% 3.93/0.92  % (22490)Time limit reached!
% 3.93/0.92  % (22490)------------------------------
% 3.93/0.92  % (22490)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.93/0.92  % (22490)Termination reason: Time limit
% 3.93/0.92  % (22490)Termination phase: Saturation
% 3.93/0.92  
% 3.93/0.92  % (22490)Memory used [KB]: 6908
% 3.93/0.92  % (22490)Time elapsed: 0.500 s
% 3.93/0.92  % (22490)------------------------------
% 3.93/0.92  % (22490)------------------------------
% 3.93/0.94  % (22488)Time limit reached!
% 3.93/0.94  % (22488)------------------------------
% 3.93/0.94  % (22488)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.93/0.94  % (22488)Termination reason: Time limit
% 3.93/0.94  
% 3.93/0.94  % (22488)Memory used [KB]: 11129
% 3.93/0.94  % (22488)Time elapsed: 0.531 s
% 3.93/0.94  % (22488)------------------------------
% 3.93/0.94  % (22488)------------------------------
% 4.91/1.03  % (22480)Time limit reached!
% 4.91/1.03  % (22480)------------------------------
% 4.91/1.03  % (22480)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.91/1.03  % (22480)Termination reason: Time limit
% 4.91/1.03  % (22480)Termination phase: Saturation
% 4.91/1.03  
% 4.91/1.03  % (22480)Memory used [KB]: 15735
% 4.91/1.03  % (22480)Time elapsed: 0.600 s
% 4.91/1.03  % (22480)------------------------------
% 4.91/1.03  % (22480)------------------------------
% 6.41/1.23  % (22478)Refutation found. Thanks to Tanya!
% 6.41/1.23  % SZS status Theorem for theBenchmark
% 6.41/1.23  % SZS output start Proof for theBenchmark
% 6.41/1.23  fof(f8038,plain,(
% 6.41/1.23    $false),
% 6.41/1.23    inference(subsumption_resolution,[],[f8037,f47])).
% 6.41/1.23  fof(f47,plain,(
% 6.41/1.23    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 6.41/1.23    inference(cnf_transformation,[],[f42])).
% 6.41/1.23  fof(f42,plain,(
% 6.41/1.23    (~r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_tops_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 6.41/1.23    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f41,f40])).
% 6.41/1.23  fof(f40,plain,(
% 6.41/1.23    ? [X0] : (? [X1] : (~r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (~r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,X1)),k2_tops_1(sK0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 6.41/1.23    introduced(choice_axiom,[])).
% 6.41/1.23  fof(f41,plain,(
% 6.41/1.23    ? [X1] : (~r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,X1)),k2_tops_1(sK0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (~r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_tops_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 6.41/1.23    introduced(choice_axiom,[])).
% 6.41/1.23  fof(f21,plain,(
% 6.41/1.23    ? [X0] : (? [X1] : (~r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 6.41/1.23    inference(ennf_transformation,[],[f20])).
% 6.41/1.23  fof(f20,negated_conjecture,(
% 6.41/1.23    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1))))),
% 6.41/1.23    inference(negated_conjecture,[],[f19])).
% 6.41/1.23  fof(f19,conjecture,(
% 6.41/1.23    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1))))),
% 6.41/1.23    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_tops_1)).
% 6.41/1.23  fof(f8037,plain,(
% 6.41/1.23    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 6.41/1.23    inference(subsumption_resolution,[],[f8023,f46])).
% 6.41/1.23  fof(f46,plain,(
% 6.41/1.23    l1_pre_topc(sK0)),
% 6.41/1.23    inference(cnf_transformation,[],[f42])).
% 6.41/1.23  fof(f8023,plain,(
% 6.41/1.23    ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 6.41/1.23    inference(resolution,[],[f8019,f48])).
% 6.41/1.23  fof(f48,plain,(
% 6.41/1.23    ~r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_tops_1(sK0,sK1))),
% 6.41/1.23    inference(cnf_transformation,[],[f42])).
% 6.41/1.23  fof(f8019,plain,(
% 6.41/1.23    ( ! [X0,X1] : (r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1)) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 6.41/1.23    inference(subsumption_resolution,[],[f8012,f525])).
% 6.41/1.23  fof(f525,plain,(
% 6.41/1.23    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 6.41/1.23    inference(subsumption_resolution,[],[f524,f60])).
% 6.41/1.23  fof(f60,plain,(
% 6.41/1.23    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 6.41/1.23    inference(cnf_transformation,[],[f35])).
% 6.41/1.23  fof(f35,plain,(
% 6.41/1.23    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 6.41/1.23    inference(flattening,[],[f34])).
% 6.41/1.23  fof(f34,plain,(
% 6.41/1.23    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 6.41/1.23    inference(ennf_transformation,[],[f15])).
% 6.41/1.23  fof(f15,axiom,(
% 6.41/1.23    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 6.41/1.23    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 6.41/1.23  fof(f524,plain,(
% 6.41/1.23    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 6.41/1.23    inference(duplicate_literal_removal,[],[f523])).
% 6.41/1.23  fof(f523,plain,(
% 6.41/1.23    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 6.41/1.23    inference(superposition,[],[f515,f51])).
% 6.41/1.23  fof(f51,plain,(
% 6.41/1.23    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 6.41/1.23    inference(cnf_transformation,[],[f24])).
% 6.41/1.23  fof(f24,plain,(
% 6.41/1.23    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 6.41/1.23    inference(ennf_transformation,[],[f17])).
% 6.41/1.23  fof(f17,axiom,(
% 6.41/1.23    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 6.41/1.23    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).
% 6.41/1.23  fof(f515,plain,(
% 6.41/1.23    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 6.41/1.23    inference(subsumption_resolution,[],[f510,f53])).
% 6.41/1.23  fof(f53,plain,(
% 6.41/1.23    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 6.41/1.23    inference(cnf_transformation,[],[f26])).
% 6.41/1.23  fof(f26,plain,(
% 6.41/1.23    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 6.41/1.23    inference(ennf_transformation,[],[f4])).
% 6.41/1.23  fof(f4,axiom,(
% 6.41/1.23    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 6.41/1.23    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 6.41/1.23  fof(f510,plain,(
% 6.41/1.23    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 6.41/1.23    inference(superposition,[],[f454,f55])).
% 6.41/1.23  fof(f55,plain,(
% 6.41/1.23    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 6.41/1.23    inference(cnf_transformation,[],[f28])).
% 6.41/1.23  fof(f28,plain,(
% 6.41/1.23    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 6.41/1.23    inference(ennf_transformation,[],[f6])).
% 6.41/1.23  fof(f6,axiom,(
% 6.41/1.23    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 6.41/1.23    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 6.41/1.23  fof(f454,plain,(
% 6.41/1.23    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,k3_subset_1(X0,X1),X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 6.41/1.23    inference(subsumption_resolution,[],[f434,f326])).
% 6.41/1.23  fof(f326,plain,(
% 6.41/1.23    ( ! [X4,X5,X3] : (m1_subset_1(k7_subset_1(X3,X4,X5),k1_zfmisc_1(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(X3)) | ~m1_subset_1(X4,k1_zfmisc_1(X3))) )),
% 6.41/1.23    inference(subsumption_resolution,[],[f303,f53])).
% 6.41/1.23  fof(f303,plain,(
% 6.41/1.23    ( ! [X4,X5,X3] : (m1_subset_1(k7_subset_1(X3,X4,X5),k1_zfmisc_1(X3)) | ~m1_subset_1(k3_subset_1(X3,X5),k1_zfmisc_1(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(X3)) | ~m1_subset_1(X4,k1_zfmisc_1(X3))) )),
% 6.41/1.23    inference(superposition,[],[f66,f57])).
% 6.41/1.23  fof(f57,plain,(
% 6.41/1.23    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 6.41/1.23    inference(cnf_transformation,[],[f30])).
% 6.41/1.23  fof(f30,plain,(
% 6.41/1.23    ! [X0,X1] : (! [X2] : (k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 6.41/1.23    inference(ennf_transformation,[],[f9])).
% 6.41/1.23  fof(f9,axiom,(
% 6.41/1.23    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))))),
% 6.41/1.23    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).
% 6.41/1.23  fof(f66,plain,(
% 6.41/1.23    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 6.41/1.23    inference(cnf_transformation,[],[f36])).
% 6.41/1.23  fof(f36,plain,(
% 6.41/1.23    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 6.41/1.23    inference(ennf_transformation,[],[f5])).
% 6.41/1.23  fof(f5,axiom,(
% 6.41/1.23    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 6.41/1.23    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).
% 6.41/1.23  fof(f434,plain,(
% 6.41/1.23    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,k3_subset_1(X0,X1),X2),k1_zfmisc_1(X0)) | ~m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 6.41/1.23    inference(superposition,[],[f53,f58])).
% 6.41/1.23  fof(f58,plain,(
% 6.41/1.23    ( ! [X2,X0,X1] : (k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 6.41/1.23    inference(cnf_transformation,[],[f31])).
% 6.41/1.23  fof(f31,plain,(
% 6.41/1.23    ! [X0,X1] : (! [X2] : (k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 6.41/1.23    inference(ennf_transformation,[],[f10])).
% 6.41/1.23  fof(f10,axiom,(
% 6.41/1.23    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)))),
% 6.41/1.23    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_subset_1)).
% 6.41/1.23  fof(f8012,plain,(
% 6.41/1.23    ( ! [X0,X1] : (r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1)) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 6.41/1.23    inference(duplicate_literal_removal,[],[f8005])).
% 6.41/1.23  fof(f8005,plain,(
% 6.41/1.23    ( ! [X0,X1] : (r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1)) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 6.41/1.23    inference(superposition,[],[f1624,f50])).
% 6.41/1.23  fof(f50,plain,(
% 6.41/1.23    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 6.41/1.23    inference(cnf_transformation,[],[f23])).
% 6.41/1.23  fof(f23,plain,(
% 6.41/1.23    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 6.41/1.23    inference(ennf_transformation,[],[f16])).
% 6.41/1.23  fof(f16,axiom,(
% 6.41/1.23    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))))),
% 6.41/1.23    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_1)).
% 6.41/1.23  fof(f1624,plain,(
% 6.41/1.23    ( ! [X0,X1] : (r1_tarski(k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1))),k2_tops_1(X0,X1)) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 6.41/1.23    inference(duplicate_literal_removal,[],[f1617])).
% 6.41/1.23  fof(f1617,plain,(
% 6.41/1.23    ( ! [X0,X1] : (r1_tarski(k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1))),k2_tops_1(X0,X1)) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 6.41/1.23    inference(superposition,[],[f164,f365])).
% 6.41/1.23  fof(f365,plain,(
% 6.41/1.23    ( ! [X2,X3] : (k1_tops_1(X2,k3_subset_1(u1_struct_0(X2),X3)) = k3_subset_1(u1_struct_0(X2),k2_pre_topc(X2,X3)) | ~l1_pre_topc(X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) )),
% 6.41/1.23    inference(subsumption_resolution,[],[f349,f53])).
% 6.41/1.23  fof(f349,plain,(
% 6.41/1.23    ( ! [X2,X3] : (k1_tops_1(X2,k3_subset_1(u1_struct_0(X2),X3)) = k3_subset_1(u1_struct_0(X2),k2_pre_topc(X2,X3)) | ~m1_subset_1(k3_subset_1(u1_struct_0(X2),X3),k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) )),
% 6.41/1.23    inference(superposition,[],[f52,f55])).
% 6.41/1.23  fof(f52,plain,(
% 6.41/1.23    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 6.41/1.23    inference(cnf_transformation,[],[f25])).
% 6.41/1.23  fof(f25,plain,(
% 6.41/1.23    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 6.41/1.23    inference(ennf_transformation,[],[f14])).
% 6.41/1.23  fof(f14,axiom,(
% 6.41/1.23    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))))),
% 6.41/1.23    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).
% 6.41/1.23  fof(f164,plain,(
% 6.41/1.23    ( ! [X0,X1] : (r1_tarski(k2_tops_1(X0,k1_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))),k2_tops_1(X0,X1)) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 6.41/1.23    inference(subsumption_resolution,[],[f163,f53])).
% 6.41/1.23  fof(f163,plain,(
% 6.41/1.23    ( ! [X0,X1] : (r1_tarski(k2_tops_1(X0,k1_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))),k2_tops_1(X0,X1)) | ~m1_subset_1(k3_subset_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 6.41/1.23    inference(duplicate_literal_removal,[],[f158])).
% 6.41/1.23  fof(f158,plain,(
% 6.41/1.23    ( ! [X0,X1] : (r1_tarski(k2_tops_1(X0,k1_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))),k2_tops_1(X0,X1)) | ~m1_subset_1(k3_subset_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 6.41/1.23    inference(superposition,[],[f49,f50])).
% 6.41/1.23  fof(f49,plain,(
% 6.41/1.23    ( ! [X0,X1] : (r1_tarski(k2_tops_1(X0,k1_tops_1(X0,X1)),k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 6.41/1.23    inference(cnf_transformation,[],[f22])).
% 6.41/1.23  fof(f22,plain,(
% 6.41/1.23    ! [X0] : (! [X1] : (r1_tarski(k2_tops_1(X0,k1_tops_1(X0,X1)),k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 6.41/1.23    inference(ennf_transformation,[],[f18])).
% 6.41/1.23  fof(f18,axiom,(
% 6.41/1.23    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k2_tops_1(X0,k1_tops_1(X0,X1)),k2_tops_1(X0,X1))))),
% 6.41/1.23    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_tops_1)).
% 6.41/1.23  % SZS output end Proof for theBenchmark
% 6.41/1.23  % (22478)------------------------------
% 6.41/1.23  % (22478)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.41/1.23  % (22478)Termination reason: Refutation
% 6.41/1.23  
% 6.41/1.23  % (22478)Memory used [KB]: 11513
% 6.41/1.23  % (22478)Time elapsed: 0.781 s
% 6.41/1.23  % (22478)------------------------------
% 6.41/1.23  % (22478)------------------------------
% 6.41/1.23  % (22471)Success in time 0.873 s
%------------------------------------------------------------------------------
