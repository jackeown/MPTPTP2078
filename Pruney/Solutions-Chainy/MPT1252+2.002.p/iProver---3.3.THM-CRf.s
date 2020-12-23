%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:14:06 EST 2020

% Result     : Theorem 31.45s
% Output     : CNFRefutation 31.45s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 585 expanded)
%              Number of clauses        :   80 ( 208 expanded)
%              Number of leaves         :   16 ( 145 expanded)
%              Depth                    :   18
%              Number of atoms          :  353 (1671 expanded)
%              Number of equality atoms :  130 ( 247 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

fof(f40,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f13,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k2_tops_1(X0,k2_tops_1(X0,X1)),k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => r1_tarski(k2_tops_1(X0,k2_tops_1(X0,X1)),k2_tops_1(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,k2_tops_1(X0,X1)),k2_tops_1(X0,X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,k2_tops_1(X0,X1)),k2_tops_1(X0,X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_tarski(k2_tops_1(X0,k2_tops_1(X0,sK1)),k2_tops_1(X0,sK1))
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k2_tops_1(X0,k2_tops_1(X0,X1)),k2_tops_1(X0,X1))
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,X1)),k2_tops_1(sK0,X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f31,f36,f35])).

fof(f54,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f37])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f53,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f15])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_tarski(X1,X2)
              | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
            & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | ~ r1_tarski(X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k2_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k2_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k2_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f55,plain,(
    ~ r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_411,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_43658,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(X2,sK1))
    | k2_tops_1(X2,sK1) != X1
    | k2_tops_1(sK0,k2_tops_1(sK0,sK1)) != X0 ),
    inference(instantiation,[status(thm)],[c_411])).

cnf(c_49263,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),X0)
    | r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(X1,sK1))
    | k2_tops_1(X1,sK1) != X0
    | k2_tops_1(sK0,k2_tops_1(sK0,sK1)) != k2_tops_1(sK0,k2_tops_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_43658])).

cnf(c_99711,plain,
    ( r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(X0,sK1))
    | ~ r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_pre_topc(sK0,k2_tops_1(sK0,sK1)))
    | k2_tops_1(X0,sK1) != k2_pre_topc(sK0,k2_tops_1(sK0,sK1))
    | k2_tops_1(sK0,k2_tops_1(sK0,sK1)) != k2_tops_1(sK0,k2_tops_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_49263])).

cnf(c_99716,plain,
    ( r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1))
    | ~ r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_pre_topc(sK0,k2_tops_1(sK0,sK1)))
    | k2_tops_1(sK0,k2_tops_1(sK0,sK1)) != k2_tops_1(sK0,k2_tops_1(sK0,sK1))
    | k2_tops_1(sK0,sK1) != k2_pre_topc(sK0,k2_tops_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_99711])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_833,plain,
    ( ~ r1_tarski(X0,k2_tops_1(sK0,sK1))
    | ~ r1_tarski(k2_tops_1(sK0,sK1),X0)
    | k2_tops_1(sK0,sK1) = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_29091,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k2_tops_1(sK0,sK1)))
    | ~ r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1))
    | k2_tops_1(sK0,sK1) = k2_pre_topc(sK0,k2_tops_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_833])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_689,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_17,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_212,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_17])).

cnf(c_213,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_212])).

cnf(c_687,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_213])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X0,X2) = k4_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_696,plain,
    ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2224,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,X0),X1) = k4_subset_1(u1_struct_0(sK0),X1,k2_tops_1(sK0,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_687,c_696])).

cnf(c_18855,plain,
    ( k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_689,c_2224])).

cnf(c_20606,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,X0)) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,X0),k2_tops_1(sK0,sK1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_687,c_18855])).

cnf(c_20935,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,X0)),k2_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,k2_tops_1(sK0,X0)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_687,c_20606])).

cnf(c_25798,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,k2_tops_1(sK0,sK1))) ),
    inference(superposition,[status(thm)],[c_689,c_20935])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_200,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_17])).

cnf(c_201,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_200])).

cnf(c_688,plain,
    ( k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_201])).

cnf(c_1122,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,X0),k2_tops_1(sK0,k2_tops_1(sK0,X0))) = k2_pre_topc(sK0,k2_tops_1(sK0,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_687,c_688])).

cnf(c_3142,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k2_pre_topc(sK0,k2_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_689,c_1122])).

cnf(c_25801,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k2_tops_1(sK0,sK1)) ),
    inference(light_normalisation,[status(thm)],[c_25798,c_3142])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | r1_tarski(k3_subset_1(X1,k4_subset_1(X1,X2,X0)),k3_subset_1(X1,X2)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_691,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(k3_subset_1(X1,k4_subset_1(X1,X2,X0)),k3_subset_1(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | r1_tarski(X2,X0)
    | ~ r1_tarski(k3_subset_1(X1,X0),k3_subset_1(X1,X2)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_693,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X2,X0) = iProver_top
    | r1_tarski(k3_subset_1(X1,X0),k3_subset_1(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2320,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k4_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X2,k4_subset_1(X1,X2,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_691,c_693])).

cnf(c_25812,plain,
    ( m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_25801,c_2320])).

cnf(c_25814,plain,
    ( m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_pre_topc(sK0,k2_tops_1(sK0,sK1))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_25812,c_25801])).

cnf(c_25817,plain,
    ( ~ m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_pre_topc(sK0,k2_tops_1(sK0,sK1))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_25814])).

cnf(c_23949,plain,
    ( m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_tops_1(sK0,sK1),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,k2_tops_1(sK0,sK1)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3142,c_2320])).

cnf(c_24060,plain,
    ( m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k2_tops_1(sK0,sK1))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_23949,c_3142])).

cnf(c_24114,plain,
    ( ~ m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k2_tops_1(sK0,sK1))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_24060])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1005,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_6109,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_1005])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_263,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_17])).

cnf(c_264,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_263])).

cnf(c_683,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_264])).

cnf(c_695,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k2_pre_topc(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_251,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,k2_pre_topc(X1,X0)) = k2_pre_topc(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_17])).

cnf(c_252,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k2_pre_topc(sK0,X0)) = k2_pre_topc(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_251])).

cnf(c_684,plain,
    ( k2_pre_topc(sK0,k2_pre_topc(sK0,X0)) = k2_pre_topc(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_252])).

cnf(c_1316,plain,
    ( k2_pre_topc(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_695,c_684])).

cnf(c_3027,plain,
    ( k2_pre_topc(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(superposition,[status(thm)],[c_689,c_1316])).

cnf(c_954,plain,
    ( k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_689,c_684])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X0,X2)),k9_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k2_pre_topc(X1,X2)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_236,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X0,X2)),k9_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k2_pre_topc(X1,X2)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_17])).

cnf(c_237,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k2_pre_topc(sK0,X1))) ),
    inference(unflattening,[status(thm)],[c_236])).

cnf(c_685,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k2_pre_topc(sK0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_237])).

cnf(c_1235,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_954,c_685])).

cnf(c_19,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_746,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_264])).

cnf(c_747,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_746])).

cnf(c_3347,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1235,c_19,c_747])).

cnf(c_3357,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3027,c_3347])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_224,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k9_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k2_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_17])).

cnf(c_225,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k2_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_224])).

cnf(c_686,plain,
    ( k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k2_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_225])).

cnf(c_1683,plain,
    ( k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_689,c_686])).

cnf(c_3359,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3357,c_1683])).

cnf(c_3417,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_683,c_3359])).

cnf(c_3418,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3417])).

cnf(c_409,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2135,plain,
    ( k2_tops_1(sK0,k2_tops_1(sK0,sK1)) = k2_tops_1(sK0,k2_tops_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_409])).

cnf(c_786,plain,
    ( ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_264])).

cnf(c_787,plain,
    ( m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_213])).

cnf(c_733,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_213])).

cnf(c_15,negated_conjecture,
    ( ~ r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f55])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_99716,c_29091,c_25817,c_24114,c_6109,c_3418,c_2135,c_786,c_787,c_733,c_15,c_16])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:14:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 31.45/4.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 31.45/4.50  
% 31.45/4.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 31.45/4.50  
% 31.45/4.50  ------  iProver source info
% 31.45/4.50  
% 31.45/4.50  git: date: 2020-06-30 10:37:57 +0100
% 31.45/4.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 31.45/4.50  git: non_committed_changes: false
% 31.45/4.50  git: last_make_outside_of_git: false
% 31.45/4.50  
% 31.45/4.50  ------ 
% 31.45/4.50  
% 31.45/4.50  ------ Input Options
% 31.45/4.50  
% 31.45/4.50  --out_options                           all
% 31.45/4.50  --tptp_safe_out                         true
% 31.45/4.50  --problem_path                          ""
% 31.45/4.50  --include_path                          ""
% 31.45/4.50  --clausifier                            res/vclausify_rel
% 31.45/4.50  --clausifier_options                    ""
% 31.45/4.50  --stdin                                 false
% 31.45/4.50  --stats_out                             all
% 31.45/4.50  
% 31.45/4.50  ------ General Options
% 31.45/4.50  
% 31.45/4.50  --fof                                   false
% 31.45/4.50  --time_out_real                         305.
% 31.45/4.50  --time_out_virtual                      -1.
% 31.45/4.50  --symbol_type_check                     false
% 31.45/4.50  --clausify_out                          false
% 31.45/4.50  --sig_cnt_out                           false
% 31.45/4.50  --trig_cnt_out                          false
% 31.45/4.50  --trig_cnt_out_tolerance                1.
% 31.45/4.50  --trig_cnt_out_sk_spl                   false
% 31.45/4.50  --abstr_cl_out                          false
% 31.45/4.50  
% 31.45/4.50  ------ Global Options
% 31.45/4.50  
% 31.45/4.50  --schedule                              default
% 31.45/4.50  --add_important_lit                     false
% 31.45/4.50  --prop_solver_per_cl                    1000
% 31.45/4.50  --min_unsat_core                        false
% 31.45/4.50  --soft_assumptions                      false
% 31.45/4.50  --soft_lemma_size                       3
% 31.45/4.50  --prop_impl_unit_size                   0
% 31.45/4.50  --prop_impl_unit                        []
% 31.45/4.50  --share_sel_clauses                     true
% 31.45/4.50  --reset_solvers                         false
% 31.45/4.50  --bc_imp_inh                            [conj_cone]
% 31.45/4.50  --conj_cone_tolerance                   3.
% 31.45/4.50  --extra_neg_conj                        none
% 31.45/4.50  --large_theory_mode                     true
% 31.45/4.50  --prolific_symb_bound                   200
% 31.45/4.50  --lt_threshold                          2000
% 31.45/4.50  --clause_weak_htbl                      true
% 31.45/4.50  --gc_record_bc_elim                     false
% 31.45/4.50  
% 31.45/4.50  ------ Preprocessing Options
% 31.45/4.50  
% 31.45/4.50  --preprocessing_flag                    true
% 31.45/4.50  --time_out_prep_mult                    0.1
% 31.45/4.50  --splitting_mode                        input
% 31.45/4.50  --splitting_grd                         true
% 31.45/4.50  --splitting_cvd                         false
% 31.45/4.50  --splitting_cvd_svl                     false
% 31.45/4.50  --splitting_nvd                         32
% 31.45/4.50  --sub_typing                            true
% 31.45/4.50  --prep_gs_sim                           true
% 31.45/4.50  --prep_unflatten                        true
% 31.45/4.50  --prep_res_sim                          true
% 31.45/4.50  --prep_upred                            true
% 31.45/4.50  --prep_sem_filter                       exhaustive
% 31.45/4.50  --prep_sem_filter_out                   false
% 31.45/4.50  --pred_elim                             true
% 31.45/4.50  --res_sim_input                         true
% 31.45/4.50  --eq_ax_congr_red                       true
% 31.45/4.50  --pure_diseq_elim                       true
% 31.45/4.50  --brand_transform                       false
% 31.45/4.50  --non_eq_to_eq                          false
% 31.45/4.50  --prep_def_merge                        true
% 31.45/4.50  --prep_def_merge_prop_impl              false
% 31.45/4.50  --prep_def_merge_mbd                    true
% 31.45/4.50  --prep_def_merge_tr_red                 false
% 31.45/4.50  --prep_def_merge_tr_cl                  false
% 31.45/4.50  --smt_preprocessing                     true
% 31.45/4.50  --smt_ac_axioms                         fast
% 31.45/4.50  --preprocessed_out                      false
% 31.45/4.50  --preprocessed_stats                    false
% 31.45/4.50  
% 31.45/4.50  ------ Abstraction refinement Options
% 31.45/4.50  
% 31.45/4.50  --abstr_ref                             []
% 31.45/4.50  --abstr_ref_prep                        false
% 31.45/4.50  --abstr_ref_until_sat                   false
% 31.45/4.50  --abstr_ref_sig_restrict                funpre
% 31.45/4.50  --abstr_ref_af_restrict_to_split_sk     false
% 31.45/4.50  --abstr_ref_under                       []
% 31.45/4.50  
% 31.45/4.50  ------ SAT Options
% 31.45/4.50  
% 31.45/4.50  --sat_mode                              false
% 31.45/4.50  --sat_fm_restart_options                ""
% 31.45/4.50  --sat_gr_def                            false
% 31.45/4.50  --sat_epr_types                         true
% 31.45/4.50  --sat_non_cyclic_types                  false
% 31.45/4.50  --sat_finite_models                     false
% 31.45/4.50  --sat_fm_lemmas                         false
% 31.45/4.50  --sat_fm_prep                           false
% 31.45/4.50  --sat_fm_uc_incr                        true
% 31.45/4.50  --sat_out_model                         small
% 31.45/4.50  --sat_out_clauses                       false
% 31.45/4.50  
% 31.45/4.50  ------ QBF Options
% 31.45/4.50  
% 31.45/4.50  --qbf_mode                              false
% 31.45/4.50  --qbf_elim_univ                         false
% 31.45/4.50  --qbf_dom_inst                          none
% 31.45/4.50  --qbf_dom_pre_inst                      false
% 31.45/4.50  --qbf_sk_in                             false
% 31.45/4.50  --qbf_pred_elim                         true
% 31.45/4.50  --qbf_split                             512
% 31.45/4.50  
% 31.45/4.50  ------ BMC1 Options
% 31.45/4.50  
% 31.45/4.50  --bmc1_incremental                      false
% 31.45/4.50  --bmc1_axioms                           reachable_all
% 31.45/4.50  --bmc1_min_bound                        0
% 31.45/4.50  --bmc1_max_bound                        -1
% 31.45/4.50  --bmc1_max_bound_default                -1
% 31.45/4.50  --bmc1_symbol_reachability              true
% 31.45/4.50  --bmc1_property_lemmas                  false
% 31.45/4.50  --bmc1_k_induction                      false
% 31.45/4.50  --bmc1_non_equiv_states                 false
% 31.45/4.50  --bmc1_deadlock                         false
% 31.45/4.50  --bmc1_ucm                              false
% 31.45/4.50  --bmc1_add_unsat_core                   none
% 31.45/4.50  --bmc1_unsat_core_children              false
% 31.45/4.50  --bmc1_unsat_core_extrapolate_axioms    false
% 31.45/4.50  --bmc1_out_stat                         full
% 31.45/4.50  --bmc1_ground_init                      false
% 31.45/4.50  --bmc1_pre_inst_next_state              false
% 31.45/4.50  --bmc1_pre_inst_state                   false
% 31.45/4.50  --bmc1_pre_inst_reach_state             false
% 31.45/4.50  --bmc1_out_unsat_core                   false
% 31.45/4.50  --bmc1_aig_witness_out                  false
% 31.45/4.50  --bmc1_verbose                          false
% 31.45/4.50  --bmc1_dump_clauses_tptp                false
% 31.45/4.50  --bmc1_dump_unsat_core_tptp             false
% 31.45/4.50  --bmc1_dump_file                        -
% 31.45/4.50  --bmc1_ucm_expand_uc_limit              128
% 31.45/4.50  --bmc1_ucm_n_expand_iterations          6
% 31.45/4.50  --bmc1_ucm_extend_mode                  1
% 31.45/4.50  --bmc1_ucm_init_mode                    2
% 31.45/4.50  --bmc1_ucm_cone_mode                    none
% 31.45/4.50  --bmc1_ucm_reduced_relation_type        0
% 31.45/4.50  --bmc1_ucm_relax_model                  4
% 31.45/4.50  --bmc1_ucm_full_tr_after_sat            true
% 31.45/4.50  --bmc1_ucm_expand_neg_assumptions       false
% 31.45/4.50  --bmc1_ucm_layered_model                none
% 31.45/4.50  --bmc1_ucm_max_lemma_size               10
% 31.45/4.50  
% 31.45/4.50  ------ AIG Options
% 31.45/4.50  
% 31.45/4.50  --aig_mode                              false
% 31.45/4.50  
% 31.45/4.50  ------ Instantiation Options
% 31.45/4.50  
% 31.45/4.50  --instantiation_flag                    true
% 31.45/4.50  --inst_sos_flag                         true
% 31.45/4.50  --inst_sos_phase                        true
% 31.45/4.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 31.45/4.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 31.45/4.50  --inst_lit_sel_side                     num_symb
% 31.45/4.50  --inst_solver_per_active                1400
% 31.45/4.50  --inst_solver_calls_frac                1.
% 31.45/4.50  --inst_passive_queue_type               priority_queues
% 31.45/4.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 31.45/4.50  --inst_passive_queues_freq              [25;2]
% 31.45/4.50  --inst_dismatching                      true
% 31.45/4.50  --inst_eager_unprocessed_to_passive     true
% 31.45/4.50  --inst_prop_sim_given                   true
% 31.45/4.50  --inst_prop_sim_new                     false
% 31.45/4.50  --inst_subs_new                         false
% 31.45/4.50  --inst_eq_res_simp                      false
% 31.45/4.50  --inst_subs_given                       false
% 31.45/4.50  --inst_orphan_elimination               true
% 31.45/4.50  --inst_learning_loop_flag               true
% 31.45/4.50  --inst_learning_start                   3000
% 31.45/4.50  --inst_learning_factor                  2
% 31.45/4.50  --inst_start_prop_sim_after_learn       3
% 31.45/4.50  --inst_sel_renew                        solver
% 31.45/4.50  --inst_lit_activity_flag                true
% 31.45/4.50  --inst_restr_to_given                   false
% 31.45/4.50  --inst_activity_threshold               500
% 31.45/4.50  --inst_out_proof                        true
% 31.45/4.50  
% 31.45/4.50  ------ Resolution Options
% 31.45/4.50  
% 31.45/4.50  --resolution_flag                       true
% 31.45/4.50  --res_lit_sel                           adaptive
% 31.45/4.50  --res_lit_sel_side                      none
% 31.45/4.50  --res_ordering                          kbo
% 31.45/4.50  --res_to_prop_solver                    active
% 31.45/4.50  --res_prop_simpl_new                    false
% 31.45/4.50  --res_prop_simpl_given                  true
% 31.45/4.50  --res_passive_queue_type                priority_queues
% 31.45/4.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 31.45/4.50  --res_passive_queues_freq               [15;5]
% 31.45/4.50  --res_forward_subs                      full
% 31.45/4.50  --res_backward_subs                     full
% 31.45/4.50  --res_forward_subs_resolution           true
% 31.45/4.50  --res_backward_subs_resolution          true
% 31.45/4.50  --res_orphan_elimination                true
% 31.45/4.50  --res_time_limit                        2.
% 31.45/4.50  --res_out_proof                         true
% 31.45/4.50  
% 31.45/4.50  ------ Superposition Options
% 31.45/4.50  
% 31.45/4.50  --superposition_flag                    true
% 31.45/4.50  --sup_passive_queue_type                priority_queues
% 31.45/4.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 31.45/4.50  --sup_passive_queues_freq               [8;1;4]
% 31.45/4.50  --demod_completeness_check              fast
% 31.45/4.50  --demod_use_ground                      true
% 31.45/4.50  --sup_to_prop_solver                    passive
% 31.45/4.50  --sup_prop_simpl_new                    true
% 31.45/4.50  --sup_prop_simpl_given                  true
% 31.45/4.50  --sup_fun_splitting                     true
% 31.45/4.50  --sup_smt_interval                      50000
% 31.45/4.50  
% 31.45/4.50  ------ Superposition Simplification Setup
% 31.45/4.50  
% 31.45/4.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 31.45/4.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 31.45/4.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 31.45/4.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 31.45/4.50  --sup_full_triv                         [TrivRules;PropSubs]
% 31.45/4.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 31.45/4.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 31.45/4.50  --sup_immed_triv                        [TrivRules]
% 31.45/4.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 31.45/4.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.45/4.50  --sup_immed_bw_main                     []
% 31.45/4.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 31.45/4.50  --sup_input_triv                        [Unflattening;TrivRules]
% 31.45/4.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.45/4.50  --sup_input_bw                          []
% 31.45/4.50  
% 31.45/4.50  ------ Combination Options
% 31.45/4.50  
% 31.45/4.50  --comb_res_mult                         3
% 31.45/4.50  --comb_sup_mult                         2
% 31.45/4.50  --comb_inst_mult                        10
% 31.45/4.50  
% 31.45/4.50  ------ Debug Options
% 31.45/4.50  
% 31.45/4.50  --dbg_backtrace                         false
% 31.45/4.50  --dbg_dump_prop_clauses                 false
% 31.45/4.50  --dbg_dump_prop_clauses_file            -
% 31.45/4.50  --dbg_out_stat                          false
% 31.45/4.50  ------ Parsing...
% 31.45/4.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 31.45/4.50  
% 31.45/4.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 31.45/4.50  
% 31.45/4.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 31.45/4.50  
% 31.45/4.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.45/4.50  ------ Proving...
% 31.45/4.50  ------ Problem Properties 
% 31.45/4.50  
% 31.45/4.50  
% 31.45/4.50  clauses                                 16
% 31.45/4.50  conjectures                             2
% 31.45/4.50  EPR                                     2
% 31.45/4.50  Horn                                    16
% 31.45/4.50  unary                                   3
% 31.45/4.50  binary                                  6
% 31.45/4.50  lits                                    38
% 31.45/4.50  lits eq                                 6
% 31.45/4.50  fd_pure                                 0
% 31.45/4.50  fd_pseudo                               0
% 31.45/4.50  fd_cond                                 0
% 31.45/4.50  fd_pseudo_cond                          1
% 31.45/4.50  AC symbols                              0
% 31.45/4.50  
% 31.45/4.50  ------ Schedule dynamic 5 is on 
% 31.45/4.50  
% 31.45/4.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 31.45/4.50  
% 31.45/4.50  
% 31.45/4.50  ------ 
% 31.45/4.50  Current options:
% 31.45/4.50  ------ 
% 31.45/4.50  
% 31.45/4.50  ------ Input Options
% 31.45/4.50  
% 31.45/4.50  --out_options                           all
% 31.45/4.50  --tptp_safe_out                         true
% 31.45/4.50  --problem_path                          ""
% 31.45/4.50  --include_path                          ""
% 31.45/4.50  --clausifier                            res/vclausify_rel
% 31.45/4.50  --clausifier_options                    ""
% 31.45/4.50  --stdin                                 false
% 31.45/4.50  --stats_out                             all
% 31.45/4.50  
% 31.45/4.50  ------ General Options
% 31.45/4.50  
% 31.45/4.50  --fof                                   false
% 31.45/4.50  --time_out_real                         305.
% 31.45/4.50  --time_out_virtual                      -1.
% 31.45/4.50  --symbol_type_check                     false
% 31.45/4.50  --clausify_out                          false
% 31.45/4.50  --sig_cnt_out                           false
% 31.45/4.50  --trig_cnt_out                          false
% 31.45/4.50  --trig_cnt_out_tolerance                1.
% 31.45/4.50  --trig_cnt_out_sk_spl                   false
% 31.45/4.50  --abstr_cl_out                          false
% 31.45/4.50  
% 31.45/4.50  ------ Global Options
% 31.45/4.50  
% 31.45/4.50  --schedule                              default
% 31.45/4.50  --add_important_lit                     false
% 31.45/4.50  --prop_solver_per_cl                    1000
% 31.45/4.50  --min_unsat_core                        false
% 31.45/4.50  --soft_assumptions                      false
% 31.45/4.50  --soft_lemma_size                       3
% 31.45/4.50  --prop_impl_unit_size                   0
% 31.45/4.50  --prop_impl_unit                        []
% 31.45/4.50  --share_sel_clauses                     true
% 31.45/4.50  --reset_solvers                         false
% 31.45/4.50  --bc_imp_inh                            [conj_cone]
% 31.45/4.50  --conj_cone_tolerance                   3.
% 31.45/4.50  --extra_neg_conj                        none
% 31.45/4.50  --large_theory_mode                     true
% 31.45/4.50  --prolific_symb_bound                   200
% 31.45/4.50  --lt_threshold                          2000
% 31.45/4.50  --clause_weak_htbl                      true
% 31.45/4.50  --gc_record_bc_elim                     false
% 31.45/4.50  
% 31.45/4.50  ------ Preprocessing Options
% 31.45/4.50  
% 31.45/4.50  --preprocessing_flag                    true
% 31.45/4.50  --time_out_prep_mult                    0.1
% 31.45/4.50  --splitting_mode                        input
% 31.45/4.50  --splitting_grd                         true
% 31.45/4.50  --splitting_cvd                         false
% 31.45/4.50  --splitting_cvd_svl                     false
% 31.45/4.50  --splitting_nvd                         32
% 31.45/4.50  --sub_typing                            true
% 31.45/4.50  --prep_gs_sim                           true
% 31.45/4.50  --prep_unflatten                        true
% 31.45/4.50  --prep_res_sim                          true
% 31.45/4.50  --prep_upred                            true
% 31.45/4.50  --prep_sem_filter                       exhaustive
% 31.45/4.50  --prep_sem_filter_out                   false
% 31.45/4.50  --pred_elim                             true
% 31.45/4.50  --res_sim_input                         true
% 31.45/4.50  --eq_ax_congr_red                       true
% 31.45/4.50  --pure_diseq_elim                       true
% 31.45/4.50  --brand_transform                       false
% 31.45/4.50  --non_eq_to_eq                          false
% 31.45/4.50  --prep_def_merge                        true
% 31.45/4.50  --prep_def_merge_prop_impl              false
% 31.45/4.50  --prep_def_merge_mbd                    true
% 31.45/4.50  --prep_def_merge_tr_red                 false
% 31.45/4.50  --prep_def_merge_tr_cl                  false
% 31.45/4.50  --smt_preprocessing                     true
% 31.45/4.50  --smt_ac_axioms                         fast
% 31.45/4.50  --preprocessed_out                      false
% 31.45/4.50  --preprocessed_stats                    false
% 31.45/4.50  
% 31.45/4.50  ------ Abstraction refinement Options
% 31.45/4.50  
% 31.45/4.50  --abstr_ref                             []
% 31.45/4.50  --abstr_ref_prep                        false
% 31.45/4.50  --abstr_ref_until_sat                   false
% 31.45/4.50  --abstr_ref_sig_restrict                funpre
% 31.45/4.50  --abstr_ref_af_restrict_to_split_sk     false
% 31.45/4.50  --abstr_ref_under                       []
% 31.45/4.50  
% 31.45/4.50  ------ SAT Options
% 31.45/4.50  
% 31.45/4.50  --sat_mode                              false
% 31.45/4.50  --sat_fm_restart_options                ""
% 31.45/4.50  --sat_gr_def                            false
% 31.45/4.50  --sat_epr_types                         true
% 31.45/4.50  --sat_non_cyclic_types                  false
% 31.45/4.50  --sat_finite_models                     false
% 31.45/4.50  --sat_fm_lemmas                         false
% 31.45/4.50  --sat_fm_prep                           false
% 31.45/4.50  --sat_fm_uc_incr                        true
% 31.45/4.50  --sat_out_model                         small
% 31.45/4.50  --sat_out_clauses                       false
% 31.45/4.50  
% 31.45/4.50  ------ QBF Options
% 31.45/4.50  
% 31.45/4.50  --qbf_mode                              false
% 31.45/4.50  --qbf_elim_univ                         false
% 31.45/4.50  --qbf_dom_inst                          none
% 31.45/4.50  --qbf_dom_pre_inst                      false
% 31.45/4.50  --qbf_sk_in                             false
% 31.45/4.50  --qbf_pred_elim                         true
% 31.45/4.50  --qbf_split                             512
% 31.45/4.50  
% 31.45/4.50  ------ BMC1 Options
% 31.45/4.50  
% 31.45/4.50  --bmc1_incremental                      false
% 31.45/4.50  --bmc1_axioms                           reachable_all
% 31.45/4.50  --bmc1_min_bound                        0
% 31.45/4.50  --bmc1_max_bound                        -1
% 31.45/4.50  --bmc1_max_bound_default                -1
% 31.45/4.50  --bmc1_symbol_reachability              true
% 31.45/4.50  --bmc1_property_lemmas                  false
% 31.45/4.50  --bmc1_k_induction                      false
% 31.45/4.50  --bmc1_non_equiv_states                 false
% 31.45/4.50  --bmc1_deadlock                         false
% 31.45/4.50  --bmc1_ucm                              false
% 31.45/4.50  --bmc1_add_unsat_core                   none
% 31.45/4.50  --bmc1_unsat_core_children              false
% 31.45/4.50  --bmc1_unsat_core_extrapolate_axioms    false
% 31.45/4.50  --bmc1_out_stat                         full
% 31.45/4.50  --bmc1_ground_init                      false
% 31.45/4.50  --bmc1_pre_inst_next_state              false
% 31.45/4.50  --bmc1_pre_inst_state                   false
% 31.45/4.50  --bmc1_pre_inst_reach_state             false
% 31.45/4.50  --bmc1_out_unsat_core                   false
% 31.45/4.50  --bmc1_aig_witness_out                  false
% 31.45/4.50  --bmc1_verbose                          false
% 31.45/4.50  --bmc1_dump_clauses_tptp                false
% 31.45/4.50  --bmc1_dump_unsat_core_tptp             false
% 31.45/4.50  --bmc1_dump_file                        -
% 31.45/4.50  --bmc1_ucm_expand_uc_limit              128
% 31.45/4.50  --bmc1_ucm_n_expand_iterations          6
% 31.45/4.50  --bmc1_ucm_extend_mode                  1
% 31.45/4.50  --bmc1_ucm_init_mode                    2
% 31.45/4.50  --bmc1_ucm_cone_mode                    none
% 31.45/4.50  --bmc1_ucm_reduced_relation_type        0
% 31.45/4.50  --bmc1_ucm_relax_model                  4
% 31.45/4.50  --bmc1_ucm_full_tr_after_sat            true
% 31.45/4.50  --bmc1_ucm_expand_neg_assumptions       false
% 31.45/4.50  --bmc1_ucm_layered_model                none
% 31.45/4.50  --bmc1_ucm_max_lemma_size               10
% 31.45/4.50  
% 31.45/4.50  ------ AIG Options
% 31.45/4.50  
% 31.45/4.50  --aig_mode                              false
% 31.45/4.50  
% 31.45/4.50  ------ Instantiation Options
% 31.45/4.50  
% 31.45/4.50  --instantiation_flag                    true
% 31.45/4.50  --inst_sos_flag                         true
% 31.45/4.50  --inst_sos_phase                        true
% 31.45/4.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 31.45/4.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 31.45/4.50  --inst_lit_sel_side                     none
% 31.45/4.50  --inst_solver_per_active                1400
% 31.45/4.50  --inst_solver_calls_frac                1.
% 31.45/4.50  --inst_passive_queue_type               priority_queues
% 31.45/4.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 31.45/4.50  --inst_passive_queues_freq              [25;2]
% 31.45/4.50  --inst_dismatching                      true
% 31.45/4.50  --inst_eager_unprocessed_to_passive     true
% 31.45/4.50  --inst_prop_sim_given                   true
% 31.45/4.50  --inst_prop_sim_new                     false
% 31.45/4.50  --inst_subs_new                         false
% 31.45/4.50  --inst_eq_res_simp                      false
% 31.45/4.50  --inst_subs_given                       false
% 31.45/4.50  --inst_orphan_elimination               true
% 31.45/4.50  --inst_learning_loop_flag               true
% 31.45/4.50  --inst_learning_start                   3000
% 31.45/4.50  --inst_learning_factor                  2
% 31.45/4.50  --inst_start_prop_sim_after_learn       3
% 31.45/4.50  --inst_sel_renew                        solver
% 31.45/4.50  --inst_lit_activity_flag                true
% 31.45/4.50  --inst_restr_to_given                   false
% 31.45/4.50  --inst_activity_threshold               500
% 31.45/4.50  --inst_out_proof                        true
% 31.45/4.50  
% 31.45/4.50  ------ Resolution Options
% 31.45/4.50  
% 31.45/4.50  --resolution_flag                       false
% 31.45/4.50  --res_lit_sel                           adaptive
% 31.45/4.50  --res_lit_sel_side                      none
% 31.45/4.50  --res_ordering                          kbo
% 31.45/4.50  --res_to_prop_solver                    active
% 31.45/4.50  --res_prop_simpl_new                    false
% 31.45/4.50  --res_prop_simpl_given                  true
% 31.45/4.50  --res_passive_queue_type                priority_queues
% 31.45/4.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 31.45/4.50  --res_passive_queues_freq               [15;5]
% 31.45/4.50  --res_forward_subs                      full
% 31.45/4.50  --res_backward_subs                     full
% 31.45/4.50  --res_forward_subs_resolution           true
% 31.45/4.50  --res_backward_subs_resolution          true
% 31.45/4.50  --res_orphan_elimination                true
% 31.45/4.50  --res_time_limit                        2.
% 31.45/4.50  --res_out_proof                         true
% 31.45/4.50  
% 31.45/4.50  ------ Superposition Options
% 31.45/4.50  
% 31.45/4.50  --superposition_flag                    true
% 31.45/4.50  --sup_passive_queue_type                priority_queues
% 31.45/4.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 31.45/4.50  --sup_passive_queues_freq               [8;1;4]
% 31.45/4.50  --demod_completeness_check              fast
% 31.45/4.50  --demod_use_ground                      true
% 31.45/4.50  --sup_to_prop_solver                    passive
% 31.45/4.50  --sup_prop_simpl_new                    true
% 31.45/4.50  --sup_prop_simpl_given                  true
% 31.45/4.50  --sup_fun_splitting                     true
% 31.45/4.50  --sup_smt_interval                      50000
% 31.45/4.50  
% 31.45/4.50  ------ Superposition Simplification Setup
% 31.45/4.50  
% 31.45/4.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 31.45/4.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 31.45/4.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 31.45/4.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 31.45/4.50  --sup_full_triv                         [TrivRules;PropSubs]
% 31.45/4.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 31.45/4.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 31.45/4.50  --sup_immed_triv                        [TrivRules]
% 31.45/4.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 31.45/4.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.45/4.50  --sup_immed_bw_main                     []
% 31.45/4.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 31.45/4.50  --sup_input_triv                        [Unflattening;TrivRules]
% 31.45/4.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.45/4.50  --sup_input_bw                          []
% 31.45/4.50  
% 31.45/4.50  ------ Combination Options
% 31.45/4.50  
% 31.45/4.50  --comb_res_mult                         3
% 31.45/4.50  --comb_sup_mult                         2
% 31.45/4.50  --comb_inst_mult                        10
% 31.45/4.50  
% 31.45/4.50  ------ Debug Options
% 31.45/4.50  
% 31.45/4.50  --dbg_backtrace                         false
% 31.45/4.50  --dbg_dump_prop_clauses                 false
% 31.45/4.50  --dbg_dump_prop_clauses_file            -
% 31.45/4.50  --dbg_out_stat                          false
% 31.45/4.50  
% 31.45/4.50  
% 31.45/4.50  
% 31.45/4.50  
% 31.45/4.50  ------ Proving...
% 31.45/4.50  
% 31.45/4.50  
% 31.45/4.50  % SZS status Theorem for theBenchmark.p
% 31.45/4.50  
% 31.45/4.50  % SZS output start CNFRefutation for theBenchmark.p
% 31.45/4.50  
% 31.45/4.50  fof(f1,axiom,(
% 31.45/4.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 31.45/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.45/4.50  
% 31.45/4.50  fof(f32,plain,(
% 31.45/4.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 31.45/4.50    inference(nnf_transformation,[],[f1])).
% 31.45/4.50  
% 31.45/4.50  fof(f33,plain,(
% 31.45/4.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 31.45/4.50    inference(flattening,[],[f32])).
% 31.45/4.50  
% 31.45/4.50  fof(f40,plain,(
% 31.45/4.50    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 31.45/4.50    inference(cnf_transformation,[],[f33])).
% 31.45/4.50  
% 31.45/4.50  fof(f13,conjecture,(
% 31.45/4.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k2_tops_1(X0,k2_tops_1(X0,X1)),k2_tops_1(X0,X1))))),
% 31.45/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.45/4.50  
% 31.45/4.50  fof(f14,negated_conjecture,(
% 31.45/4.50    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k2_tops_1(X0,k2_tops_1(X0,X1)),k2_tops_1(X0,X1))))),
% 31.45/4.50    inference(negated_conjecture,[],[f13])).
% 31.45/4.50  
% 31.45/4.50  fof(f31,plain,(
% 31.45/4.50    ? [X0] : (? [X1] : (~r1_tarski(k2_tops_1(X0,k2_tops_1(X0,X1)),k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 31.45/4.50    inference(ennf_transformation,[],[f14])).
% 31.45/4.50  
% 31.45/4.50  fof(f36,plain,(
% 31.45/4.50    ( ! [X0] : (? [X1] : (~r1_tarski(k2_tops_1(X0,k2_tops_1(X0,X1)),k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~r1_tarski(k2_tops_1(X0,k2_tops_1(X0,sK1)),k2_tops_1(X0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 31.45/4.50    introduced(choice_axiom,[])).
% 31.45/4.50  
% 31.45/4.50  fof(f35,plain,(
% 31.45/4.50    ? [X0] : (? [X1] : (~r1_tarski(k2_tops_1(X0,k2_tops_1(X0,X1)),k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (~r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,X1)),k2_tops_1(sK0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 31.45/4.50    introduced(choice_axiom,[])).
% 31.45/4.50  
% 31.45/4.50  fof(f37,plain,(
% 31.45/4.50    (~r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 31.45/4.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f31,f36,f35])).
% 31.45/4.50  
% 31.45/4.50  fof(f54,plain,(
% 31.45/4.50    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 31.45/4.50    inference(cnf_transformation,[],[f37])).
% 31.45/4.50  
% 31.45/4.50  fof(f11,axiom,(
% 31.45/4.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 31.45/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.45/4.50  
% 31.45/4.50  fof(f28,plain,(
% 31.45/4.50    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 31.45/4.50    inference(ennf_transformation,[],[f11])).
% 31.45/4.50  
% 31.45/4.50  fof(f29,plain,(
% 31.45/4.50    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 31.45/4.50    inference(flattening,[],[f28])).
% 31.45/4.50  
% 31.45/4.50  fof(f51,plain,(
% 31.45/4.50    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 31.45/4.50    inference(cnf_transformation,[],[f29])).
% 31.45/4.50  
% 31.45/4.50  fof(f53,plain,(
% 31.45/4.50    l1_pre_topc(sK0)),
% 31.45/4.50    inference(cnf_transformation,[],[f37])).
% 31.45/4.50  
% 31.45/4.50  fof(f2,axiom,(
% 31.45/4.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1))),
% 31.45/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.45/4.50  
% 31.45/4.50  fof(f15,plain,(
% 31.45/4.50    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 31.45/4.50    inference(ennf_transformation,[],[f2])).
% 31.45/4.50  
% 31.45/4.50  fof(f16,plain,(
% 31.45/4.50    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 31.45/4.50    inference(flattening,[],[f15])).
% 31.45/4.50  
% 31.45/4.50  fof(f41,plain,(
% 31.45/4.50    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 31.45/4.50    inference(cnf_transformation,[],[f16])).
% 31.45/4.50  
% 31.45/4.50  fof(f12,axiom,(
% 31.45/4.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)))),
% 31.45/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.45/4.50  
% 31.45/4.50  fof(f30,plain,(
% 31.45/4.50    ! [X0] : (! [X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 31.45/4.50    inference(ennf_transformation,[],[f12])).
% 31.45/4.50  
% 31.45/4.50  fof(f52,plain,(
% 31.45/4.50    ( ! [X0,X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 31.45/4.50    inference(cnf_transformation,[],[f30])).
% 31.45/4.50  
% 31.45/4.50  fof(f6,axiom,(
% 31.45/4.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))))),
% 31.45/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.45/4.50  
% 31.45/4.50  fof(f21,plain,(
% 31.45/4.50    ! [X0,X1] : (! [X2] : (r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 31.45/4.50    inference(ennf_transformation,[],[f6])).
% 31.45/4.50  
% 31.45/4.50  fof(f46,plain,(
% 31.45/4.50    ( ! [X2,X0,X1] : (r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 31.45/4.50    inference(cnf_transformation,[],[f21])).
% 31.45/4.50  
% 31.45/4.50  fof(f5,axiom,(
% 31.45/4.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 31.45/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.45/4.50  
% 31.45/4.50  fof(f20,plain,(
% 31.45/4.50    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 31.45/4.50    inference(ennf_transformation,[],[f5])).
% 31.45/4.50  
% 31.45/4.50  fof(f34,plain,(
% 31.45/4.50    ! [X0,X1] : (! [X2] : (((r1_tarski(X1,X2) | ~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 31.45/4.50    inference(nnf_transformation,[],[f20])).
% 31.45/4.50  
% 31.45/4.50  fof(f45,plain,(
% 31.45/4.50    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 31.45/4.50    inference(cnf_transformation,[],[f34])).
% 31.45/4.50  
% 31.45/4.50  fof(f3,axiom,(
% 31.45/4.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 31.45/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.45/4.50  
% 31.45/4.50  fof(f17,plain,(
% 31.45/4.50    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 31.45/4.50    inference(ennf_transformation,[],[f3])).
% 31.45/4.50  
% 31.45/4.50  fof(f42,plain,(
% 31.45/4.50    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 31.45/4.50    inference(cnf_transformation,[],[f17])).
% 31.45/4.50  
% 31.45/4.50  fof(f7,axiom,(
% 31.45/4.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 31.45/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.45/4.50  
% 31.45/4.50  fof(f22,plain,(
% 31.45/4.50    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 31.45/4.50    inference(ennf_transformation,[],[f7])).
% 31.45/4.50  
% 31.45/4.50  fof(f23,plain,(
% 31.45/4.50    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 31.45/4.50    inference(flattening,[],[f22])).
% 31.45/4.50  
% 31.45/4.50  fof(f47,plain,(
% 31.45/4.50    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 31.45/4.50    inference(cnf_transformation,[],[f23])).
% 31.45/4.50  
% 31.45/4.50  fof(f8,axiom,(
% 31.45/4.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)))),
% 31.45/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.45/4.50  
% 31.45/4.50  fof(f24,plain,(
% 31.45/4.50    ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 31.45/4.50    inference(ennf_transformation,[],[f8])).
% 31.45/4.50  
% 31.45/4.50  fof(f25,plain,(
% 31.45/4.50    ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 31.45/4.50    inference(flattening,[],[f24])).
% 31.45/4.50  
% 31.45/4.50  fof(f48,plain,(
% 31.45/4.50    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 31.45/4.50    inference(cnf_transformation,[],[f25])).
% 31.45/4.50  
% 31.45/4.50  fof(f9,axiom,(
% 31.45/4.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))))))),
% 31.45/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.45/4.50  
% 31.45/4.50  fof(f26,plain,(
% 31.45/4.50    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 31.45/4.50    inference(ennf_transformation,[],[f9])).
% 31.45/4.50  
% 31.45/4.50  fof(f49,plain,(
% 31.45/4.50    ( ! [X2,X0,X1] : (r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 31.45/4.50    inference(cnf_transformation,[],[f26])).
% 31.45/4.50  
% 31.45/4.50  fof(f10,axiom,(
% 31.45/4.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k2_tops_1(X0,X1)))),
% 31.45/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.45/4.50  
% 31.45/4.50  fof(f27,plain,(
% 31.45/4.50    ! [X0] : (! [X1] : (k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 31.45/4.50    inference(ennf_transformation,[],[f10])).
% 31.45/4.50  
% 31.45/4.50  fof(f50,plain,(
% 31.45/4.50    ( ! [X0,X1] : (k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 31.45/4.50    inference(cnf_transformation,[],[f27])).
% 31.45/4.50  
% 31.45/4.50  fof(f55,plain,(
% 31.45/4.50    ~r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1))),
% 31.45/4.50    inference(cnf_transformation,[],[f37])).
% 31.45/4.50  
% 31.45/4.50  cnf(c_411,plain,
% 31.45/4.50      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 31.45/4.50      theory(equality) ).
% 31.45/4.50  
% 31.45/4.50  cnf(c_43658,plain,
% 31.45/4.50      ( ~ r1_tarski(X0,X1)
% 31.45/4.50      | r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(X2,sK1))
% 31.45/4.50      | k2_tops_1(X2,sK1) != X1
% 31.45/4.50      | k2_tops_1(sK0,k2_tops_1(sK0,sK1)) != X0 ),
% 31.45/4.50      inference(instantiation,[status(thm)],[c_411]) ).
% 31.45/4.50  
% 31.45/4.50  cnf(c_49263,plain,
% 31.45/4.50      ( ~ r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),X0)
% 31.45/4.50      | r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(X1,sK1))
% 31.45/4.50      | k2_tops_1(X1,sK1) != X0
% 31.45/4.50      | k2_tops_1(sK0,k2_tops_1(sK0,sK1)) != k2_tops_1(sK0,k2_tops_1(sK0,sK1)) ),
% 31.45/4.50      inference(instantiation,[status(thm)],[c_43658]) ).
% 31.45/4.50  
% 31.45/4.50  cnf(c_99711,plain,
% 31.45/4.50      ( r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(X0,sK1))
% 31.45/4.50      | ~ r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_pre_topc(sK0,k2_tops_1(sK0,sK1)))
% 31.45/4.50      | k2_tops_1(X0,sK1) != k2_pre_topc(sK0,k2_tops_1(sK0,sK1))
% 31.45/4.50      | k2_tops_1(sK0,k2_tops_1(sK0,sK1)) != k2_tops_1(sK0,k2_tops_1(sK0,sK1)) ),
% 31.45/4.50      inference(instantiation,[status(thm)],[c_49263]) ).
% 31.45/4.50  
% 31.45/4.50  cnf(c_99716,plain,
% 31.45/4.50      ( r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1))
% 31.45/4.50      | ~ r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_pre_topc(sK0,k2_tops_1(sK0,sK1)))
% 31.45/4.50      | k2_tops_1(sK0,k2_tops_1(sK0,sK1)) != k2_tops_1(sK0,k2_tops_1(sK0,sK1))
% 31.45/4.50      | k2_tops_1(sK0,sK1) != k2_pre_topc(sK0,k2_tops_1(sK0,sK1)) ),
% 31.45/4.50      inference(instantiation,[status(thm)],[c_99711]) ).
% 31.45/4.50  
% 31.45/4.50  cnf(c_0,plain,
% 31.45/4.50      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 31.45/4.50      inference(cnf_transformation,[],[f40]) ).
% 31.45/4.50  
% 31.45/4.50  cnf(c_833,plain,
% 31.45/4.50      ( ~ r1_tarski(X0,k2_tops_1(sK0,sK1))
% 31.45/4.50      | ~ r1_tarski(k2_tops_1(sK0,sK1),X0)
% 31.45/4.50      | k2_tops_1(sK0,sK1) = X0 ),
% 31.45/4.50      inference(instantiation,[status(thm)],[c_0]) ).
% 31.45/4.50  
% 31.45/4.50  cnf(c_29091,plain,
% 31.45/4.50      ( ~ r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k2_tops_1(sK0,sK1)))
% 31.45/4.50      | ~ r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1))
% 31.45/4.50      | k2_tops_1(sK0,sK1) = k2_pre_topc(sK0,k2_tops_1(sK0,sK1)) ),
% 31.45/4.50      inference(instantiation,[status(thm)],[c_833]) ).
% 31.45/4.50  
% 31.45/4.50  cnf(c_16,negated_conjecture,
% 31.45/4.50      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 31.45/4.50      inference(cnf_transformation,[],[f54]) ).
% 31.45/4.50  
% 31.45/4.50  cnf(c_689,plain,
% 31.45/4.50      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 31.45/4.50      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 31.45/4.50  
% 31.45/4.50  cnf(c_13,plain,
% 31.45/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 31.45/4.50      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 31.45/4.50      | ~ l1_pre_topc(X1) ),
% 31.45/4.50      inference(cnf_transformation,[],[f51]) ).
% 31.45/4.50  
% 31.45/4.50  cnf(c_17,negated_conjecture,
% 31.45/4.50      ( l1_pre_topc(sK0) ),
% 31.45/4.50      inference(cnf_transformation,[],[f53]) ).
% 31.45/4.50  
% 31.45/4.50  cnf(c_212,plain,
% 31.45/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 31.45/4.50      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 31.45/4.50      | sK0 != X1 ),
% 31.45/4.50      inference(resolution_lifted,[status(thm)],[c_13,c_17]) ).
% 31.45/4.50  
% 31.45/4.50  cnf(c_213,plain,
% 31.45/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 31.45/4.50      | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 31.45/4.50      inference(unflattening,[status(thm)],[c_212]) ).
% 31.45/4.50  
% 31.45/4.50  cnf(c_687,plain,
% 31.45/4.50      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 31.45/4.50      | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 31.45/4.50      inference(predicate_to_equality,[status(thm)],[c_213]) ).
% 31.45/4.50  
% 31.45/4.50  cnf(c_3,plain,
% 31.45/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 31.45/4.50      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 31.45/4.50      | k4_subset_1(X1,X0,X2) = k4_subset_1(X1,X2,X0) ),
% 31.45/4.50      inference(cnf_transformation,[],[f41]) ).
% 31.45/4.50  
% 31.45/4.50  cnf(c_696,plain,
% 31.45/4.50      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
% 31.45/4.50      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 31.45/4.50      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 31.45/4.50      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 31.45/4.50  
% 31.45/4.50  cnf(c_2224,plain,
% 31.45/4.50      ( k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,X0),X1) = k4_subset_1(u1_struct_0(sK0),X1,k2_tops_1(sK0,X0))
% 31.45/4.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 31.45/4.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 31.45/4.50      inference(superposition,[status(thm)],[c_687,c_696]) ).
% 31.45/4.50  
% 31.45/4.50  cnf(c_18855,plain,
% 31.45/4.50      ( k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),X0)
% 31.45/4.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 31.45/4.50      inference(superposition,[status(thm)],[c_689,c_2224]) ).
% 31.45/4.50  
% 31.45/4.50  cnf(c_20606,plain,
% 31.45/4.50      ( k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,X0)) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,X0),k2_tops_1(sK0,sK1))
% 31.45/4.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 31.45/4.50      inference(superposition,[status(thm)],[c_687,c_18855]) ).
% 31.45/4.50  
% 31.45/4.50  cnf(c_20935,plain,
% 31.45/4.50      ( k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,X0)),k2_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,k2_tops_1(sK0,X0)))
% 31.45/4.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 31.45/4.50      inference(superposition,[status(thm)],[c_687,c_20606]) ).
% 31.45/4.50  
% 31.45/4.50  cnf(c_25798,plain,
% 31.45/4.50      ( k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,k2_tops_1(sK0,sK1))) ),
% 31.45/4.50      inference(superposition,[status(thm)],[c_689,c_20935]) ).
% 31.45/4.50  
% 31.45/4.50  cnf(c_14,plain,
% 31.45/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 31.45/4.50      | ~ l1_pre_topc(X1)
% 31.45/4.50      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
% 31.45/4.50      inference(cnf_transformation,[],[f52]) ).
% 31.45/4.50  
% 31.45/4.50  cnf(c_200,plain,
% 31.45/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 31.45/4.50      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0)
% 31.45/4.50      | sK0 != X1 ),
% 31.45/4.50      inference(resolution_lifted,[status(thm)],[c_14,c_17]) ).
% 31.45/4.50  
% 31.45/4.50  cnf(c_201,plain,
% 31.45/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 31.45/4.50      | k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0) ),
% 31.45/4.50      inference(unflattening,[status(thm)],[c_200]) ).
% 31.45/4.50  
% 31.45/4.50  cnf(c_688,plain,
% 31.45/4.50      ( k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0)
% 31.45/4.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 31.45/4.50      inference(predicate_to_equality,[status(thm)],[c_201]) ).
% 31.45/4.50  
% 31.45/4.50  cnf(c_1122,plain,
% 31.45/4.50      ( k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,X0),k2_tops_1(sK0,k2_tops_1(sK0,X0))) = k2_pre_topc(sK0,k2_tops_1(sK0,X0))
% 31.45/4.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 31.45/4.50      inference(superposition,[status(thm)],[c_687,c_688]) ).
% 31.45/4.50  
% 31.45/4.50  cnf(c_3142,plain,
% 31.45/4.50      ( k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k2_pre_topc(sK0,k2_tops_1(sK0,sK1)) ),
% 31.45/4.50      inference(superposition,[status(thm)],[c_689,c_1122]) ).
% 31.45/4.50  
% 31.45/4.50  cnf(c_25801,plain,
% 31.45/4.50      ( k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k2_tops_1(sK0,sK1)) ),
% 31.45/4.50      inference(light_normalisation,[status(thm)],[c_25798,c_3142]) ).
% 31.45/4.50  
% 31.45/4.50  cnf(c_8,plain,
% 31.45/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 31.45/4.50      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 31.45/4.50      | r1_tarski(k3_subset_1(X1,k4_subset_1(X1,X2,X0)),k3_subset_1(X1,X2)) ),
% 31.45/4.50      inference(cnf_transformation,[],[f46]) ).
% 31.45/4.50  
% 31.45/4.50  cnf(c_691,plain,
% 31.45/4.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 31.45/4.50      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 31.45/4.50      | r1_tarski(k3_subset_1(X1,k4_subset_1(X1,X2,X0)),k3_subset_1(X1,X2)) = iProver_top ),
% 31.45/4.50      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 31.45/4.50  
% 31.45/4.50  cnf(c_6,plain,
% 31.45/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 31.45/4.50      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 31.45/4.50      | r1_tarski(X2,X0)
% 31.45/4.50      | ~ r1_tarski(k3_subset_1(X1,X0),k3_subset_1(X1,X2)) ),
% 31.45/4.50      inference(cnf_transformation,[],[f45]) ).
% 31.45/4.50  
% 31.45/4.50  cnf(c_693,plain,
% 31.45/4.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 31.45/4.50      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 31.45/4.50      | r1_tarski(X2,X0) = iProver_top
% 31.45/4.50      | r1_tarski(k3_subset_1(X1,X0),k3_subset_1(X1,X2)) != iProver_top ),
% 31.45/4.50      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 31.45/4.50  
% 31.45/4.50  cnf(c_2320,plain,
% 31.45/4.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 31.45/4.50      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 31.45/4.50      | m1_subset_1(k4_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) != iProver_top
% 31.45/4.50      | r1_tarski(X2,k4_subset_1(X1,X2,X0)) = iProver_top ),
% 31.45/4.50      inference(superposition,[status(thm)],[c_691,c_693]) ).
% 31.45/4.50  
% 31.45/4.50  cnf(c_25812,plain,
% 31.45/4.50      ( m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 31.45/4.50      | m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 31.45/4.50      | m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 31.45/4.50      | r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1))) = iProver_top ),
% 31.45/4.50      inference(superposition,[status(thm)],[c_25801,c_2320]) ).
% 31.45/4.50  
% 31.45/4.50  cnf(c_25814,plain,
% 31.45/4.50      ( m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 31.45/4.50      | m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 31.45/4.50      | m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 31.45/4.50      | r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_pre_topc(sK0,k2_tops_1(sK0,sK1))) = iProver_top ),
% 31.45/4.50      inference(light_normalisation,[status(thm)],[c_25812,c_25801]) ).
% 31.45/4.50  
% 31.45/4.50  cnf(c_25817,plain,
% 31.45/4.50      ( ~ m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
% 31.45/4.50      | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 31.45/4.50      | ~ m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
% 31.45/4.50      | r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_pre_topc(sK0,k2_tops_1(sK0,sK1))) ),
% 31.45/4.50      inference(predicate_to_equality_rev,[status(thm)],[c_25814]) ).
% 31.45/4.50  
% 31.45/4.50  cnf(c_23949,plain,
% 31.45/4.50      ( m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 31.45/4.50      | m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 31.45/4.50      | m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 31.45/4.50      | r1_tarski(k2_tops_1(sK0,sK1),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,k2_tops_1(sK0,sK1)))) = iProver_top ),
% 31.45/4.50      inference(superposition,[status(thm)],[c_3142,c_2320]) ).
% 31.45/4.50  
% 31.45/4.50  cnf(c_24060,plain,
% 31.45/4.50      ( m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 31.45/4.50      | m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 31.45/4.50      | m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 31.45/4.50      | r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k2_tops_1(sK0,sK1))) = iProver_top ),
% 31.45/4.50      inference(light_normalisation,[status(thm)],[c_23949,c_3142]) ).
% 31.45/4.50  
% 31.45/4.50  cnf(c_24114,plain,
% 31.45/4.50      ( ~ m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
% 31.45/4.50      | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 31.45/4.50      | ~ m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
% 31.45/4.50      | r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k2_tops_1(sK0,sK1))) ),
% 31.45/4.50      inference(predicate_to_equality_rev,[status(thm)],[c_24060]) ).
% 31.45/4.50  
% 31.45/4.50  cnf(c_4,plain,
% 31.45/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 31.45/4.50      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 31.45/4.50      inference(cnf_transformation,[],[f42]) ).
% 31.45/4.50  
% 31.45/4.50  cnf(c_1005,plain,
% 31.45/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 31.45/4.50      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 31.45/4.50      inference(instantiation,[status(thm)],[c_4]) ).
% 31.45/4.50  
% 31.45/4.50  cnf(c_6109,plain,
% 31.45/4.50      ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 31.45/4.50      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 31.45/4.50      inference(instantiation,[status(thm)],[c_1005]) ).
% 31.45/4.50  
% 31.45/4.50  cnf(c_9,plain,
% 31.45/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 31.45/4.50      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 31.45/4.50      | ~ l1_pre_topc(X1) ),
% 31.45/4.50      inference(cnf_transformation,[],[f47]) ).
% 31.45/4.50  
% 31.45/4.50  cnf(c_263,plain,
% 31.45/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 31.45/4.50      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 31.45/4.50      | sK0 != X1 ),
% 31.45/4.50      inference(resolution_lifted,[status(thm)],[c_9,c_17]) ).
% 31.45/4.50  
% 31.45/4.50  cnf(c_264,plain,
% 31.45/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 31.45/4.50      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 31.45/4.50      inference(unflattening,[status(thm)],[c_263]) ).
% 31.45/4.50  
% 31.45/4.50  cnf(c_683,plain,
% 31.45/4.50      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 31.45/4.50      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 31.45/4.50      inference(predicate_to_equality,[status(thm)],[c_264]) ).
% 31.45/4.50  
% 31.45/4.50  cnf(c_695,plain,
% 31.45/4.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 31.45/4.50      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 31.45/4.50      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 31.45/4.50  
% 31.45/4.50  cnf(c_10,plain,
% 31.45/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 31.45/4.50      | ~ l1_pre_topc(X1)
% 31.45/4.50      | k2_pre_topc(X1,k2_pre_topc(X1,X0)) = k2_pre_topc(X1,X0) ),
% 31.45/4.50      inference(cnf_transformation,[],[f48]) ).
% 31.45/4.50  
% 31.45/4.50  cnf(c_251,plain,
% 31.45/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 31.45/4.50      | k2_pre_topc(X1,k2_pre_topc(X1,X0)) = k2_pre_topc(X1,X0)
% 31.45/4.50      | sK0 != X1 ),
% 31.45/4.50      inference(resolution_lifted,[status(thm)],[c_10,c_17]) ).
% 31.45/4.50  
% 31.45/4.50  cnf(c_252,plain,
% 31.45/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 31.45/4.50      | k2_pre_topc(sK0,k2_pre_topc(sK0,X0)) = k2_pre_topc(sK0,X0) ),
% 31.45/4.50      inference(unflattening,[status(thm)],[c_251]) ).
% 31.45/4.50  
% 31.45/4.50  cnf(c_684,plain,
% 31.45/4.50      ( k2_pre_topc(sK0,k2_pre_topc(sK0,X0)) = k2_pre_topc(sK0,X0)
% 31.45/4.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 31.45/4.50      inference(predicate_to_equality,[status(thm)],[c_252]) ).
% 31.45/4.50  
% 31.45/4.50  cnf(c_1316,plain,
% 31.45/4.50      ( k2_pre_topc(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))
% 31.45/4.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 31.45/4.50      inference(superposition,[status(thm)],[c_695,c_684]) ).
% 31.45/4.50  
% 31.45/4.50  cnf(c_3027,plain,
% 31.45/4.50      ( k2_pre_topc(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
% 31.45/4.50      inference(superposition,[status(thm)],[c_689,c_1316]) ).
% 31.45/4.50  
% 31.45/4.50  cnf(c_954,plain,
% 31.45/4.50      ( k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 31.45/4.50      inference(superposition,[status(thm)],[c_689,c_684]) ).
% 31.45/4.50  
% 31.45/4.50  cnf(c_11,plain,
% 31.45/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 31.45/4.50      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 31.45/4.50      | r1_tarski(k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X0,X2)),k9_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k2_pre_topc(X1,X2)))
% 31.45/4.50      | ~ l1_pre_topc(X1) ),
% 31.45/4.50      inference(cnf_transformation,[],[f49]) ).
% 31.45/4.50  
% 31.45/4.50  cnf(c_236,plain,
% 31.45/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 31.45/4.50      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 31.45/4.50      | r1_tarski(k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X0,X2)),k9_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k2_pre_topc(X1,X2)))
% 31.45/4.50      | sK0 != X1 ),
% 31.45/4.50      inference(resolution_lifted,[status(thm)],[c_11,c_17]) ).
% 31.45/4.50  
% 31.45/4.50  cnf(c_237,plain,
% 31.45/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 31.45/4.50      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 31.45/4.50      | r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k2_pre_topc(sK0,X1))) ),
% 31.45/4.50      inference(unflattening,[status(thm)],[c_236]) ).
% 31.45/4.50  
% 31.45/4.50  cnf(c_685,plain,
% 31.45/4.50      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 31.45/4.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 31.45/4.50      | r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k2_pre_topc(sK0,X1))) = iProver_top ),
% 31.45/4.50      inference(predicate_to_equality,[status(thm)],[c_237]) ).
% 31.45/4.50  
% 31.45/4.50  cnf(c_1235,plain,
% 31.45/4.50      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 31.45/4.50      | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 31.45/4.50      | r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X0))) = iProver_top ),
% 31.45/4.50      inference(superposition,[status(thm)],[c_954,c_685]) ).
% 31.45/4.50  
% 31.45/4.50  cnf(c_19,plain,
% 31.45/4.50      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 31.45/4.50      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 31.45/4.50  
% 31.45/4.50  cnf(c_746,plain,
% 31.45/4.50      ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 31.45/4.50      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 31.45/4.50      inference(instantiation,[status(thm)],[c_264]) ).
% 31.45/4.50  
% 31.45/4.50  cnf(c_747,plain,
% 31.45/4.50      ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 31.45/4.50      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 31.45/4.50      inference(predicate_to_equality,[status(thm)],[c_746]) ).
% 31.45/4.50  
% 31.45/4.50  cnf(c_3347,plain,
% 31.45/4.50      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 31.45/4.50      | r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X0))) = iProver_top ),
% 31.45/4.50      inference(global_propositional_subsumption,
% 31.45/4.50                [status(thm)],
% 31.45/4.50                [c_1235,c_19,c_747]) ).
% 31.45/4.50  
% 31.45/4.50  cnf(c_3357,plain,
% 31.45/4.50      ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 31.45/4.50      | r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))) = iProver_top ),
% 31.45/4.50      inference(superposition,[status(thm)],[c_3027,c_3347]) ).
% 31.45/4.50  
% 31.45/4.50  cnf(c_12,plain,
% 31.45/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 31.45/4.50      | ~ l1_pre_topc(X1)
% 31.45/4.50      | k9_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k2_tops_1(X1,X0) ),
% 31.45/4.50      inference(cnf_transformation,[],[f50]) ).
% 31.45/4.50  
% 31.45/4.50  cnf(c_224,plain,
% 31.45/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 31.45/4.50      | k9_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k2_tops_1(X1,X0)
% 31.45/4.50      | sK0 != X1 ),
% 31.45/4.50      inference(resolution_lifted,[status(thm)],[c_12,c_17]) ).
% 31.45/4.50  
% 31.45/4.50  cnf(c_225,plain,
% 31.45/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 31.45/4.50      | k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k2_tops_1(sK0,X0) ),
% 31.45/4.50      inference(unflattening,[status(thm)],[c_224]) ).
% 31.45/4.50  
% 31.45/4.50  cnf(c_686,plain,
% 31.45/4.50      ( k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k2_tops_1(sK0,X0)
% 31.45/4.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 31.45/4.50      inference(predicate_to_equality,[status(thm)],[c_225]) ).
% 31.45/4.50  
% 31.45/4.50  cnf(c_1683,plain,
% 31.45/4.50      ( k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k2_tops_1(sK0,sK1) ),
% 31.45/4.50      inference(superposition,[status(thm)],[c_689,c_686]) ).
% 31.45/4.50  
% 31.45/4.50  cnf(c_3359,plain,
% 31.45/4.50      ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 31.45/4.50      | r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) = iProver_top ),
% 31.45/4.50      inference(light_normalisation,[status(thm)],[c_3357,c_1683]) ).
% 31.45/4.50  
% 31.45/4.50  cnf(c_3417,plain,
% 31.45/4.50      ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 31.45/4.50      | r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) = iProver_top ),
% 31.45/4.50      inference(superposition,[status(thm)],[c_683,c_3359]) ).
% 31.45/4.50  
% 31.45/4.50  cnf(c_3418,plain,
% 31.45/4.50      ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 31.45/4.50      | r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) ),
% 31.45/4.50      inference(predicate_to_equality_rev,[status(thm)],[c_3417]) ).
% 31.45/4.50  
% 31.45/4.50  cnf(c_409,plain,( X0 = X0 ),theory(equality) ).
% 31.45/4.50  
% 31.45/4.50  cnf(c_2135,plain,
% 31.45/4.50      ( k2_tops_1(sK0,k2_tops_1(sK0,sK1)) = k2_tops_1(sK0,k2_tops_1(sK0,sK1)) ),
% 31.45/4.50      inference(instantiation,[status(thm)],[c_409]) ).
% 31.45/4.50  
% 31.45/4.50  cnf(c_786,plain,
% 31.45/4.50      ( ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 31.45/4.50      | m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 31.45/4.50      inference(instantiation,[status(thm)],[c_264]) ).
% 31.45/4.50  
% 31.45/4.50  cnf(c_787,plain,
% 31.45/4.50      ( m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
% 31.45/4.50      | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 31.45/4.50      inference(instantiation,[status(thm)],[c_213]) ).
% 31.45/4.50  
% 31.45/4.50  cnf(c_733,plain,
% 31.45/4.50      ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 31.45/4.50      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 31.45/4.50      inference(instantiation,[status(thm)],[c_213]) ).
% 31.45/4.50  
% 31.45/4.50  cnf(c_15,negated_conjecture,
% 31.45/4.50      ( ~ r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) ),
% 31.45/4.50      inference(cnf_transformation,[],[f55]) ).
% 31.45/4.50  
% 31.45/4.50  cnf(contradiction,plain,
% 31.45/4.50      ( $false ),
% 31.45/4.50      inference(minisat,
% 31.45/4.50                [status(thm)],
% 31.45/4.50                [c_99716,c_29091,c_25817,c_24114,c_6109,c_3418,c_2135,
% 31.45/4.50                 c_786,c_787,c_733,c_15,c_16]) ).
% 31.45/4.50  
% 31.45/4.50  
% 31.45/4.50  % SZS output end CNFRefutation for theBenchmark.p
% 31.45/4.50  
% 31.45/4.50  ------                               Statistics
% 31.45/4.50  
% 31.45/4.50  ------ General
% 31.45/4.50  
% 31.45/4.50  abstr_ref_over_cycles:                  0
% 31.45/4.50  abstr_ref_under_cycles:                 0
% 31.45/4.50  gc_basic_clause_elim:                   0
% 31.45/4.50  forced_gc_time:                         0
% 31.45/4.50  parsing_time:                           0.013
% 31.45/4.50  unif_index_cands_time:                  0.
% 31.45/4.50  unif_index_add_time:                    0.
% 31.45/4.50  orderings_time:                         0.
% 31.45/4.50  out_proof_time:                         0.018
% 31.45/4.50  total_time:                             3.989
% 31.45/4.50  num_of_symbols:                         44
% 31.45/4.50  num_of_terms:                           117216
% 31.45/4.50  
% 31.45/4.50  ------ Preprocessing
% 31.45/4.50  
% 31.45/4.50  num_of_splits:                          0
% 31.45/4.50  num_of_split_atoms:                     0
% 31.45/4.50  num_of_reused_defs:                     0
% 31.45/4.50  num_eq_ax_congr_red:                    10
% 31.45/4.50  num_of_sem_filtered_clauses:            1
% 31.45/4.50  num_of_subtypes:                        0
% 31.45/4.50  monotx_restored_types:                  0
% 31.45/4.50  sat_num_of_epr_types:                   0
% 31.45/4.50  sat_num_of_non_cyclic_types:            0
% 31.45/4.50  sat_guarded_non_collapsed_types:        0
% 31.45/4.50  num_pure_diseq_elim:                    0
% 31.45/4.50  simp_replaced_by:                       0
% 31.45/4.50  res_preprocessed:                       88
% 31.45/4.50  prep_upred:                             0
% 31.45/4.50  prep_unflattend:                        6
% 31.45/4.50  smt_new_axioms:                         0
% 31.45/4.50  pred_elim_cands:                        2
% 31.45/4.50  pred_elim:                              1
% 31.45/4.50  pred_elim_cl:                           1
% 31.45/4.50  pred_elim_cycles:                       3
% 31.45/4.50  merged_defs:                            0
% 31.45/4.50  merged_defs_ncl:                        0
% 31.45/4.50  bin_hyper_res:                          0
% 31.45/4.50  prep_cycles:                            4
% 31.45/4.50  pred_elim_time:                         0.002
% 31.45/4.50  splitting_time:                         0.
% 31.45/4.50  sem_filter_time:                        0.
% 31.45/4.50  monotx_time:                            0.
% 31.45/4.50  subtype_inf_time:                       0.
% 31.45/4.50  
% 31.45/4.50  ------ Problem properties
% 31.45/4.50  
% 31.45/4.50  clauses:                                16
% 31.45/4.50  conjectures:                            2
% 31.45/4.50  epr:                                    2
% 31.45/4.50  horn:                                   16
% 31.45/4.50  ground:                                 2
% 31.45/4.50  unary:                                  3
% 31.45/4.50  binary:                                 6
% 31.45/4.50  lits:                                   38
% 31.45/4.50  lits_eq:                                6
% 31.45/4.50  fd_pure:                                0
% 31.45/4.50  fd_pseudo:                              0
% 31.45/4.50  fd_cond:                                0
% 31.45/4.50  fd_pseudo_cond:                         1
% 31.45/4.50  ac_symbols:                             0
% 31.45/4.50  
% 31.45/4.50  ------ Propositional Solver
% 31.45/4.50  
% 31.45/4.50  prop_solver_calls:                      53
% 31.45/4.50  prop_fast_solver_calls:                 2626
% 31.45/4.50  smt_solver_calls:                       0
% 31.45/4.50  smt_fast_solver_calls:                  0
% 31.45/4.50  prop_num_of_clauses:                    39097
% 31.45/4.50  prop_preprocess_simplified:             74577
% 31.45/4.50  prop_fo_subsumed:                       118
% 31.45/4.50  prop_solver_time:                       0.
% 31.45/4.50  smt_solver_time:                        0.
% 31.45/4.50  smt_fast_solver_time:                   0.
% 31.45/4.50  prop_fast_solver_time:                  0.
% 31.45/4.50  prop_unsat_core_time:                   0.005
% 31.45/4.50  
% 31.45/4.50  ------ QBF
% 31.45/4.50  
% 31.45/4.50  qbf_q_res:                              0
% 31.45/4.50  qbf_num_tautologies:                    0
% 31.45/4.50  qbf_prep_cycles:                        0
% 31.45/4.50  
% 31.45/4.50  ------ BMC1
% 31.45/4.50  
% 31.45/4.50  bmc1_current_bound:                     -1
% 31.45/4.50  bmc1_last_solved_bound:                 -1
% 31.45/4.50  bmc1_unsat_core_size:                   -1
% 31.45/4.50  bmc1_unsat_core_parents_size:           -1
% 31.45/4.50  bmc1_merge_next_fun:                    0
% 31.45/4.50  bmc1_unsat_core_clauses_time:           0.
% 31.45/4.50  
% 31.45/4.50  ------ Instantiation
% 31.45/4.50  
% 31.45/4.50  inst_num_of_clauses:                    6939
% 31.45/4.50  inst_num_in_passive:                    3641
% 31.45/4.50  inst_num_in_active:                     5275
% 31.45/4.50  inst_num_in_unprocessed:                929
% 31.45/4.50  inst_num_of_loops:                      5614
% 31.45/4.50  inst_num_of_learning_restarts:          1
% 31.45/4.50  inst_num_moves_active_passive:          326
% 31.45/4.50  inst_lit_activity:                      0
% 31.45/4.50  inst_lit_activity_moves:                5
% 31.45/4.50  inst_num_tautologies:                   0
% 31.45/4.50  inst_num_prop_implied:                  0
% 31.45/4.50  inst_num_existing_simplified:           0
% 31.45/4.50  inst_num_eq_res_simplified:             0
% 31.45/4.50  inst_num_child_elim:                    0
% 31.45/4.50  inst_num_of_dismatching_blockings:      17922
% 31.45/4.50  inst_num_of_non_proper_insts:           17473
% 31.45/4.50  inst_num_of_duplicates:                 0
% 31.45/4.50  inst_inst_num_from_inst_to_res:         0
% 31.45/4.50  inst_dismatching_checking_time:         0.
% 31.45/4.50  
% 31.45/4.50  ------ Resolution
% 31.45/4.50  
% 31.45/4.50  res_num_of_clauses:                     27
% 31.45/4.50  res_num_in_passive:                     27
% 31.45/4.50  res_num_in_active:                      0
% 31.45/4.50  res_num_of_loops:                       92
% 31.45/4.50  res_forward_subset_subsumed:            723
% 31.45/4.50  res_backward_subset_subsumed:           0
% 31.45/4.50  res_forward_subsumed:                   0
% 31.45/4.50  res_backward_subsumed:                  0
% 31.45/4.50  res_forward_subsumption_resolution:     0
% 31.45/4.50  res_backward_subsumption_resolution:    0
% 31.45/4.50  res_clause_to_clause_subsumption:       25821
% 31.45/4.50  res_orphan_elimination:                 0
% 31.45/4.50  res_tautology_del:                      1359
% 31.45/4.50  res_num_eq_res_simplified:              0
% 31.45/4.50  res_num_sel_changes:                    0
% 31.45/4.50  res_moves_from_active_to_pass:          0
% 31.45/4.50  
% 31.45/4.50  ------ Superposition
% 31.45/4.50  
% 31.45/4.50  sup_time_total:                         0.
% 31.45/4.50  sup_time_generating:                    0.
% 31.45/4.50  sup_time_sim_full:                      0.
% 31.45/4.50  sup_time_sim_immed:                     0.
% 31.45/4.50  
% 31.45/4.50  sup_num_of_clauses:                     4834
% 31.45/4.50  sup_num_in_active:                      1048
% 31.45/4.50  sup_num_in_passive:                     3786
% 31.45/4.50  sup_num_of_loops:                       1122
% 31.45/4.50  sup_fw_superposition:                   3649
% 31.45/4.50  sup_bw_superposition:                   1772
% 31.45/4.50  sup_immediate_simplified:               1737
% 31.45/4.50  sup_given_eliminated:                   1
% 31.45/4.50  comparisons_done:                       0
% 31.45/4.50  comparisons_avoided:                    0
% 31.45/4.50  
% 31.45/4.50  ------ Simplifications
% 31.45/4.50  
% 31.45/4.50  
% 31.45/4.50  sim_fw_subset_subsumed:                 21
% 31.45/4.50  sim_bw_subset_subsumed:                 5
% 31.45/4.50  sim_fw_subsumed:                        25
% 31.45/4.50  sim_bw_subsumed:                        0
% 31.45/4.50  sim_fw_subsumption_res:                 0
% 31.45/4.50  sim_bw_subsumption_res:                 0
% 31.45/4.50  sim_tautology_del:                      49
% 31.45/4.50  sim_eq_tautology_del:                   310
% 31.45/4.50  sim_eq_res_simp:                        0
% 31.45/4.50  sim_fw_demodulated:                     48
% 31.45/4.50  sim_bw_demodulated:                     91
% 31.45/4.50  sim_light_normalised:                   1677
% 31.45/4.50  sim_joinable_taut:                      0
% 31.45/4.50  sim_joinable_simp:                      0
% 31.45/4.50  sim_ac_normalised:                      0
% 31.45/4.50  sim_smt_subsumption:                    0
% 31.45/4.50  
%------------------------------------------------------------------------------
