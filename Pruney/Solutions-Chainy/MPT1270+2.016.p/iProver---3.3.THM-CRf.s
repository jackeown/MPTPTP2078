%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:15:17 EST 2020

% Result     : Theorem 3.55s
% Output     : CNFRefutation 3.55s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 664 expanded)
%              Number of clauses        :   81 ( 216 expanded)
%              Number of leaves         :   18 ( 145 expanded)
%              Depth                    :   22
%              Number of atoms          :  416 (2777 expanded)
%              Number of equality atoms :  158 ( 346 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f15,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> r1_tarski(X1,k2_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tops_1(X1,X0)
            <=> r1_tarski(X1,k2_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> r1_tarski(X1,k2_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X1,k2_tops_1(X0,X1))
            | ~ v2_tops_1(X1,X0) )
          & ( r1_tarski(X1,k2_tops_1(X0,X1))
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X1,k2_tops_1(X0,X1))
            | ~ v2_tops_1(X1,X0) )
          & ( r1_tarski(X1,k2_tops_1(X0,X1))
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X1,k2_tops_1(X0,X1))
            | ~ v2_tops_1(X1,X0) )
          & ( r1_tarski(X1,k2_tops_1(X0,X1))
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ~ r1_tarski(sK2,k2_tops_1(X0,sK2))
          | ~ v2_tops_1(sK2,X0) )
        & ( r1_tarski(sK2,k2_tops_1(X0,sK2))
          | v2_tops_1(sK2,X0) )
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_tarski(X1,k2_tops_1(X0,X1))
              | ~ v2_tops_1(X1,X0) )
            & ( r1_tarski(X1,k2_tops_1(X0,X1))
              | v2_tops_1(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ r1_tarski(X1,k2_tops_1(sK1,X1))
            | ~ v2_tops_1(X1,sK1) )
          & ( r1_tarski(X1,k2_tops_1(sK1,X1))
            | v2_tops_1(X1,sK1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) )
      & l1_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ( ~ r1_tarski(sK2,k2_tops_1(sK1,sK2))
      | ~ v2_tops_1(sK2,sK1) )
    & ( r1_tarski(sK2,k2_tops_1(sK1,sK2))
      | v2_tops_1(sK2,sK1) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    & l1_pre_topc(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f37,f39,f38])).

fof(f59,plain,
    ( r1_tarski(sK2,k2_tops_1(sK1,sK2))
    | v2_tops_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f57,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f58,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f40])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | k1_xboole_0 != k1_tops_1(X0,X1) )
            & ( k1_xboole_0 = k1_tops_1(X0,X1)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | k1_xboole_0 != k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f19])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f8,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5,X6] :
                  ( ( r2_hidden(X6,X1)
                    & r2_hidden(X5,X6)
                    & r2_hidden(X4,X5)
                    & r2_hidden(X3,X4)
                    & r2_hidden(X2,X3) )
                 => r1_xboole_0(X2,X0) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5,X6] :
              ( r1_xboole_0(X2,X0)
              | ~ r2_hidden(X6,X1)
              | ~ r2_hidden(X5,X6)
              | ~ r2_hidden(X4,X5)
              | ~ r2_hidden(X3,X4)
              | ~ r2_hidden(X2,X3) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5,X6] :
              ( r1_xboole_0(X2,X0)
              | ~ r2_hidden(X6,X1)
              | ~ r2_hidden(X5,X6)
              | ~ r2_hidden(X4,X5)
              | ~ r2_hidden(X3,X4)
              | ~ r2_hidden(X2,X3) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(flattening,[],[f23])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5,X6] :
              ( r1_xboole_0(X2,X0)
              | ~ r2_hidden(X6,X1)
              | ~ r2_hidden(X5,X6)
              | ~ r2_hidden(X4,X5)
              | ~ r2_hidden(X3,X4)
              | ~ r2_hidden(X2,X3) )
          & r2_hidden(X1,X0) )
     => ( ! [X6,X5,X4,X3,X2] :
            ( r1_xboole_0(X2,X0)
            | ~ r2_hidden(X6,sK0(X0))
            | ~ r2_hidden(X5,X6)
            | ~ r2_hidden(X4,X5)
            | ~ r2_hidden(X3,X4)
            | ~ r2_hidden(X2,X3) )
        & r2_hidden(sK0(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4,X5,X6] :
            ( r1_xboole_0(X2,X0)
            | ~ r2_hidden(X6,sK0(X0))
            | ~ r2_hidden(X5,X6)
            | ~ r2_hidden(X4,X5)
            | ~ r2_hidden(X3,X4)
            | ~ r2_hidden(X2,X3) )
        & r2_hidden(sK0(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f33])).

fof(f48,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f4,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_tops_1(X0,X1)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f60,plain,
    ( ~ r1_tarski(sK2,k2_tops_1(sK1,sK2))
    | ~ v2_tops_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_702,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_699,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(k1_tops_1(X1,X0),X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2233,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),k2_pre_topc(X1,X0)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_702,c_699])).

cnf(c_17,negated_conjecture,
    ( v2_tops_1(sK2,sK1)
    | r1_tarski(sK2,k2_tops_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_694,plain,
    ( v2_tops_1(sK2,sK1) = iProver_top
    | r1_tarski(sK2,k2_tops_1(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_709,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1406,plain,
    ( v2_tops_1(sK2,sK1) = iProver_top
    | r1_tarski(X0,k2_tops_1(sK1,sK2)) = iProver_top
    | r1_tarski(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_694,c_709])).

cnf(c_1640,plain,
    ( v2_tops_1(sK2,sK1) = iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k2_tops_1(sK1,sK2)) = iProver_top
    | r1_tarski(X1,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1406,c_709])).

cnf(c_5072,plain,
    ( v2_tops_1(sK2,sK1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),k2_tops_1(sK1,sK2)) = iProver_top
    | r1_tarski(k2_pre_topc(X1,X0),sK2) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2233,c_1640])).

cnf(c_19,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_20,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_21,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_14,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1056,plain,
    ( v2_tops_1(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | k1_tops_1(sK1,X0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1057,plain,
    ( k1_tops_1(sK1,X0) != k1_xboole_0
    | v2_tops_1(X0,sK1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1056])).

cnf(c_1059,plain,
    ( k1_tops_1(sK1,sK2) != k1_xboole_0
    | v2_tops_1(sK2,sK1) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1057])).

cnf(c_693,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2054,plain,
    ( r1_tarski(k1_tops_1(sK1,sK2),sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_693,c_699])).

cnf(c_910,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(k1_tops_1(sK1,X0),X0)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_911,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(k1_tops_1(sK1,X0),X0) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_910])).

cnf(c_913,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(k1_tops_1(sK1,sK2),sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_911])).

cnf(c_2282,plain,
    ( r1_tarski(k1_tops_1(sK1,sK2),sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2054,c_20,c_21,c_913])).

cnf(c_2287,plain,
    ( v2_tops_1(sK2,sK1) = iProver_top
    | r1_tarski(k1_tops_1(sK1,sK2),k2_tops_1(sK1,sK2)) = iProver_top
    | r1_tarski(sK2,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2282,c_1640])).

cnf(c_22,plain,
    ( v2_tops_1(sK2,sK1) = iProver_top
    | r1_tarski(sK2,k2_tops_1(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1048,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(k1_tops_1(sK1,X0),X0)
    | r1_tarski(k1_tops_1(sK1,X0),X1) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1619,plain,
    ( r1_tarski(k1_tops_1(sK1,sK2),k2_tops_1(sK1,sK2))
    | ~ r1_tarski(k1_tops_1(sK1,sK2),sK2)
    | ~ r1_tarski(sK2,k2_tops_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_1048])).

cnf(c_1628,plain,
    ( r1_tarski(k1_tops_1(sK1,sK2),k2_tops_1(sK1,sK2)) = iProver_top
    | r1_tarski(k1_tops_1(sK1,sK2),sK2) != iProver_top
    | r1_tarski(sK2,k2_tops_1(sK1,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1619])).

cnf(c_2951,plain,
    ( r1_tarski(k1_tops_1(sK1,sK2),k2_tops_1(sK1,sK2)) = iProver_top
    | v2_tops_1(sK2,sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2287,c_20,c_21,c_22,c_913,c_1628])).

cnf(c_2952,plain,
    ( v2_tops_1(sK2,sK1) = iProver_top
    | r1_tarski(k1_tops_1(sK1,sK2),k2_tops_1(sK1,sK2)) = iProver_top ),
    inference(renaming,[status(thm)],[c_2951])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_xboole_0(k1_tops_1(X1,X0),k2_tops_1(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_698,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_xboole_0(k1_tops_1(X1,X0),k2_tops_1(X1,X0)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_tarski(X0,X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_708,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2134,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(k1_tops_1(X1,X0),k2_tops_1(X1,X0)) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_xboole_0(k1_tops_1(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_698,c_708])).

cnf(c_5240,plain,
    ( v2_tops_1(sK2,sK1) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_xboole_0(k1_tops_1(sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2952,c_2134])).

cnf(c_5885,plain,
    ( v2_tops_1(sK2,sK1) = iProver_top
    | v1_xboole_0(k1_tops_1(sK1,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5240,c_20,c_21])).

cnf(c_8,plain,
    ( r2_hidden(sK0(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_703,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_707,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_718,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_707,c_3])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_705,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
    | v1_xboole_0(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1809,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_718,c_705])).

cnf(c_3261,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_703,c_1809])).

cnf(c_5891,plain,
    ( k1_tops_1(sK1,sK2) = k1_xboole_0
    | v2_tops_1(sK2,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_5885,c_3261])).

cnf(c_6057,plain,
    ( v2_tops_1(sK2,sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5072,c_20,c_21,c_1059,c_5891])).

cnf(c_15,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_696,plain,
    ( k1_tops_1(X0,X1) = k1_xboole_0
    | v2_tops_1(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1068,plain,
    ( k1_tops_1(sK1,sK2) = k1_xboole_0
    | v2_tops_1(sK2,sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_693,c_696])).

cnf(c_1511,plain,
    ( v2_tops_1(sK2,sK1) != iProver_top
    | k1_tops_1(sK1,sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1068,c_20])).

cnf(c_1512,plain,
    ( k1_tops_1(sK1,sK2) = k1_xboole_0
    | v2_tops_1(sK2,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_1511])).

cnf(c_6062,plain,
    ( k1_tops_1(sK1,sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6057,c_1512])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_700,plain,
    ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3142,plain,
    ( k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),k1_tops_1(sK1,sK2)) = k2_tops_1(sK1,sK2)
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_693,c_700])).

cnf(c_976,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,X0),k1_tops_1(sK1,X0)) = k2_tops_1(sK1,X0) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_978,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),k1_tops_1(sK1,sK2)) = k2_tops_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_976])).

cnf(c_3579,plain,
    ( k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),k1_tops_1(sK1,sK2)) = k2_tops_1(sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3142,c_19,c_18,c_978])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_706,plain,
    ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2235,plain,
    ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X2) = k4_xboole_0(k2_pre_topc(X0,X1),X2)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_702,c_706])).

cnf(c_5255,plain,
    ( k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),X0) = k4_xboole_0(k2_pre_topc(sK1,sK2),X0)
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_693,c_2235])).

cnf(c_5430,plain,
    ( k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),X0) = k4_xboole_0(k2_pre_topc(sK1,sK2),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5255,c_20])).

cnf(c_5434,plain,
    ( k4_xboole_0(k2_pre_topc(sK1,sK2),k1_tops_1(sK1,sK2)) = k2_tops_1(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_3579,c_5430])).

cnf(c_6064,plain,
    ( k4_xboole_0(k2_pre_topc(sK1,sK2),k1_xboole_0) = k2_tops_1(sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_6062,c_5434])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_6085,plain,
    ( k2_tops_1(sK1,sK2) = k2_pre_topc(sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_6064,c_1])).

cnf(c_16,negated_conjecture,
    ( ~ v2_tops_1(sK2,sK1)
    | ~ r1_tarski(sK2,k2_tops_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_695,plain,
    ( v2_tops_1(sK2,sK1) != iProver_top
    | r1_tarski(sK2,k2_tops_1(sK1,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_6455,plain,
    ( v2_tops_1(sK2,sK1) != iProver_top
    | r1_tarski(sK2,k2_pre_topc(sK1,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6085,c_695])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_905,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(X0,k2_pre_topc(sK1,X0))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_906,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK1,X0)) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_905])).

cnf(c_908,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(sK2,k2_pre_topc(sK1,sK2)) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_906])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6455,c_6057,c_908,c_21,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.32  % Computer   : n022.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 15:35:26 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.55/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.55/0.97  
% 3.55/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.55/0.97  
% 3.55/0.97  ------  iProver source info
% 3.55/0.97  
% 3.55/0.97  git: date: 2020-06-30 10:37:57 +0100
% 3.55/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.55/0.97  git: non_committed_changes: false
% 3.55/0.97  git: last_make_outside_of_git: false
% 3.55/0.97  
% 3.55/0.97  ------ 
% 3.55/0.97  ------ Parsing...
% 3.55/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.55/0.97  
% 3.55/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.55/0.97  
% 3.55/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.55/0.97  
% 3.55/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.55/0.97  ------ Proving...
% 3.55/0.97  ------ Problem Properties 
% 3.55/0.97  
% 3.55/0.97  
% 3.55/0.97  clauses                                 20
% 3.55/0.97  conjectures                             4
% 3.55/0.97  EPR                                     3
% 3.55/0.97  Horn                                    17
% 3.55/0.97  unary                                   5
% 3.55/0.97  binary                                  4
% 3.55/0.97  lits                                    52
% 3.55/0.97  lits eq                                 8
% 3.55/0.97  fd_pure                                 0
% 3.55/0.97  fd_pseudo                               0
% 3.55/0.97  fd_cond                                 2
% 3.55/0.97  fd_pseudo_cond                          0
% 3.55/0.97  AC symbols                              0
% 3.55/0.97  
% 3.55/0.97  ------ Input Options Time Limit: Unbounded
% 3.55/0.97  
% 3.55/0.97  
% 3.55/0.97  ------ 
% 3.55/0.97  Current options:
% 3.55/0.97  ------ 
% 3.55/0.97  
% 3.55/0.97  
% 3.55/0.97  
% 3.55/0.97  
% 3.55/0.97  ------ Proving...
% 3.55/0.97  
% 3.55/0.97  
% 3.55/0.97  % SZS status Theorem for theBenchmark.p
% 3.55/0.97  
% 3.55/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 3.55/0.97  
% 3.55/0.97  fof(f9,axiom,(
% 3.55/0.97    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.55/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.55/0.97  
% 3.55/0.97  fof(f25,plain,(
% 3.55/0.97    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.55/0.97    inference(ennf_transformation,[],[f9])).
% 3.55/0.97  
% 3.55/0.97  fof(f26,plain,(
% 3.55/0.97    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.55/0.97    inference(flattening,[],[f25])).
% 3.55/0.97  
% 3.55/0.97  fof(f50,plain,(
% 3.55/0.97    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.55/0.97    inference(cnf_transformation,[],[f26])).
% 3.55/0.97  
% 3.55/0.97  fof(f12,axiom,(
% 3.55/0.97    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 3.55/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.55/0.97  
% 3.55/0.97  fof(f29,plain,(
% 3.55/0.97    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.55/0.97    inference(ennf_transformation,[],[f12])).
% 3.55/0.97  
% 3.55/0.97  fof(f53,plain,(
% 3.55/0.97    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.55/0.97    inference(cnf_transformation,[],[f29])).
% 3.55/0.97  
% 3.55/0.97  fof(f15,conjecture,(
% 3.55/0.97    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> r1_tarski(X1,k2_tops_1(X0,X1)))))),
% 3.55/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.55/0.97  
% 3.55/0.97  fof(f16,negated_conjecture,(
% 3.55/0.97    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> r1_tarski(X1,k2_tops_1(X0,X1)))))),
% 3.55/0.97    inference(negated_conjecture,[],[f15])).
% 3.55/0.97  
% 3.55/0.97  fof(f32,plain,(
% 3.55/0.97    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> r1_tarski(X1,k2_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.55/0.97    inference(ennf_transformation,[],[f16])).
% 3.55/0.97  
% 3.55/0.97  fof(f36,plain,(
% 3.55/0.97    ? [X0] : (? [X1] : (((~r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0)) & (r1_tarski(X1,k2_tops_1(X0,X1)) | v2_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.55/0.97    inference(nnf_transformation,[],[f32])).
% 3.55/0.97  
% 3.55/0.97  fof(f37,plain,(
% 3.55/0.97    ? [X0] : (? [X1] : ((~r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0)) & (r1_tarski(X1,k2_tops_1(X0,X1)) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.55/0.97    inference(flattening,[],[f36])).
% 3.55/0.97  
% 3.55/0.97  fof(f39,plain,(
% 3.55/0.97    ( ! [X0] : (? [X1] : ((~r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0)) & (r1_tarski(X1,k2_tops_1(X0,X1)) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((~r1_tarski(sK2,k2_tops_1(X0,sK2)) | ~v2_tops_1(sK2,X0)) & (r1_tarski(sK2,k2_tops_1(X0,sK2)) | v2_tops_1(sK2,X0)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.55/0.97    introduced(choice_axiom,[])).
% 3.55/0.97  
% 3.55/0.97  fof(f38,plain,(
% 3.55/0.97    ? [X0] : (? [X1] : ((~r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0)) & (r1_tarski(X1,k2_tops_1(X0,X1)) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((~r1_tarski(X1,k2_tops_1(sK1,X1)) | ~v2_tops_1(X1,sK1)) & (r1_tarski(X1,k2_tops_1(sK1,X1)) | v2_tops_1(X1,sK1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1))),
% 3.55/0.97    introduced(choice_axiom,[])).
% 3.55/0.97  
% 3.55/0.97  fof(f40,plain,(
% 3.55/0.97    ((~r1_tarski(sK2,k2_tops_1(sK1,sK2)) | ~v2_tops_1(sK2,sK1)) & (r1_tarski(sK2,k2_tops_1(sK1,sK2)) | v2_tops_1(sK2,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1)),
% 3.55/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f37,f39,f38])).
% 3.55/0.97  
% 3.55/0.97  fof(f59,plain,(
% 3.55/0.97    r1_tarski(sK2,k2_tops_1(sK1,sK2)) | v2_tops_1(sK2,sK1)),
% 3.55/0.97    inference(cnf_transformation,[],[f40])).
% 3.55/0.97  
% 3.55/0.97  fof(f1,axiom,(
% 3.55/0.97    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 3.55/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.55/0.97  
% 3.55/0.97  fof(f17,plain,(
% 3.55/0.97    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 3.55/0.97    inference(ennf_transformation,[],[f1])).
% 3.55/0.97  
% 3.55/0.97  fof(f18,plain,(
% 3.55/0.97    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 3.55/0.97    inference(flattening,[],[f17])).
% 3.55/0.97  
% 3.55/0.97  fof(f41,plain,(
% 3.55/0.97    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 3.55/0.97    inference(cnf_transformation,[],[f18])).
% 3.55/0.97  
% 3.55/0.97  fof(f57,plain,(
% 3.55/0.97    l1_pre_topc(sK1)),
% 3.55/0.97    inference(cnf_transformation,[],[f40])).
% 3.55/0.97  
% 3.55/0.97  fof(f58,plain,(
% 3.55/0.97    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))),
% 3.55/0.97    inference(cnf_transformation,[],[f40])).
% 3.55/0.97  
% 3.55/0.97  fof(f14,axiom,(
% 3.55/0.97    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 3.55/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.55/0.97  
% 3.55/0.97  fof(f31,plain,(
% 3.55/0.97    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.55/0.97    inference(ennf_transformation,[],[f14])).
% 3.55/0.97  
% 3.55/0.97  fof(f35,plain,(
% 3.55/0.97    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1)) & (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.55/0.97    inference(nnf_transformation,[],[f31])).
% 3.55/0.97  
% 3.55/0.97  fof(f56,plain,(
% 3.55/0.97    ( ! [X0,X1] : (v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.55/0.97    inference(cnf_transformation,[],[f35])).
% 3.55/0.97  
% 3.55/0.97  fof(f13,axiom,(
% 3.55/0.97    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1))))),
% 3.55/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.55/0.97  
% 3.55/0.97  fof(f30,plain,(
% 3.55/0.97    ! [X0] : (! [X1] : (r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.55/0.97    inference(ennf_transformation,[],[f13])).
% 3.55/0.97  
% 3.55/0.97  fof(f54,plain,(
% 3.55/0.97    ( ! [X0,X1] : (r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.55/0.97    inference(cnf_transformation,[],[f30])).
% 3.55/0.97  
% 3.55/0.97  fof(f3,axiom,(
% 3.55/0.97    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 3.55/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.55/0.97  
% 3.55/0.97  fof(f19,plain,(
% 3.55/0.97    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 3.55/0.97    inference(ennf_transformation,[],[f3])).
% 3.55/0.97  
% 3.55/0.97  fof(f20,plain,(
% 3.55/0.97    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 3.55/0.97    inference(flattening,[],[f19])).
% 3.55/0.97  
% 3.55/0.97  fof(f43,plain,(
% 3.55/0.97    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 3.55/0.97    inference(cnf_transformation,[],[f20])).
% 3.55/0.97  
% 3.55/0.97  fof(f8,axiom,(
% 3.55/0.97    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5,X6] : ((r2_hidden(X6,X1) & r2_hidden(X5,X6) & r2_hidden(X4,X5) & r2_hidden(X3,X4) & r2_hidden(X2,X3)) => r1_xboole_0(X2,X0)) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 3.55/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.55/0.97  
% 3.55/0.97  fof(f23,plain,(
% 3.55/0.97    ! [X0] : (? [X1] : (! [X2,X3,X4,X5,X6] : (r1_xboole_0(X2,X0) | (~r2_hidden(X6,X1) | ~r2_hidden(X5,X6) | ~r2_hidden(X4,X5) | ~r2_hidden(X3,X4) | ~r2_hidden(X2,X3))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 3.55/0.97    inference(ennf_transformation,[],[f8])).
% 3.55/0.97  
% 3.55/0.97  fof(f24,plain,(
% 3.55/0.97    ! [X0] : (? [X1] : (! [X2,X3,X4,X5,X6] : (r1_xboole_0(X2,X0) | ~r2_hidden(X6,X1) | ~r2_hidden(X5,X6) | ~r2_hidden(X4,X5) | ~r2_hidden(X3,X4) | ~r2_hidden(X2,X3)) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 3.55/0.97    inference(flattening,[],[f23])).
% 3.55/0.97  
% 3.55/0.97  fof(f33,plain,(
% 3.55/0.97    ! [X0] : (? [X1] : (! [X2,X3,X4,X5,X6] : (r1_xboole_0(X2,X0) | ~r2_hidden(X6,X1) | ~r2_hidden(X5,X6) | ~r2_hidden(X4,X5) | ~r2_hidden(X3,X4) | ~r2_hidden(X2,X3)) & r2_hidden(X1,X0)) => (! [X6,X5,X4,X3,X2] : (r1_xboole_0(X2,X0) | ~r2_hidden(X6,sK0(X0)) | ~r2_hidden(X5,X6) | ~r2_hidden(X4,X5) | ~r2_hidden(X3,X4) | ~r2_hidden(X2,X3)) & r2_hidden(sK0(X0),X0)))),
% 3.55/0.97    introduced(choice_axiom,[])).
% 3.55/0.97  
% 3.55/0.97  fof(f34,plain,(
% 3.55/0.97    ! [X0] : ((! [X2,X3,X4,X5,X6] : (r1_xboole_0(X2,X0) | ~r2_hidden(X6,sK0(X0)) | ~r2_hidden(X5,X6) | ~r2_hidden(X4,X5) | ~r2_hidden(X3,X4) | ~r2_hidden(X2,X3)) & r2_hidden(sK0(X0),X0)) | k1_xboole_0 = X0)),
% 3.55/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f33])).
% 3.55/0.97  
% 3.55/0.97  fof(f48,plain,(
% 3.55/0.97    ( ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0) )),
% 3.55/0.97    inference(cnf_transformation,[],[f34])).
% 3.55/0.97  
% 3.55/0.97  fof(f5,axiom,(
% 3.55/0.97    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 3.55/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.55/0.97  
% 3.55/0.97  fof(f45,plain,(
% 3.55/0.97    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 3.55/0.97    inference(cnf_transformation,[],[f5])).
% 3.55/0.97  
% 3.55/0.97  fof(f4,axiom,(
% 3.55/0.97    ! [X0] : k2_subset_1(X0) = X0),
% 3.55/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.55/0.97  
% 3.55/0.97  fof(f44,plain,(
% 3.55/0.97    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 3.55/0.97    inference(cnf_transformation,[],[f4])).
% 3.55/0.97  
% 3.55/0.97  fof(f7,axiom,(
% 3.55/0.97    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 3.55/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.55/0.97  
% 3.55/0.97  fof(f22,plain,(
% 3.55/0.97    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.55/0.97    inference(ennf_transformation,[],[f7])).
% 3.55/0.97  
% 3.55/0.97  fof(f47,plain,(
% 3.55/0.97    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.55/0.97    inference(cnf_transformation,[],[f22])).
% 3.55/0.97  
% 3.55/0.97  fof(f55,plain,(
% 3.55/0.97    ( ! [X0,X1] : (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.55/0.97    inference(cnf_transformation,[],[f35])).
% 3.55/0.97  
% 3.55/0.97  fof(f11,axiom,(
% 3.55/0.97    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)))),
% 3.55/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.55/0.97  
% 3.55/0.97  fof(f28,plain,(
% 3.55/0.97    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.55/0.97    inference(ennf_transformation,[],[f11])).
% 3.55/0.97  
% 3.55/0.97  fof(f52,plain,(
% 3.55/0.97    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.55/0.97    inference(cnf_transformation,[],[f28])).
% 3.55/0.97  
% 3.55/0.97  fof(f6,axiom,(
% 3.55/0.97    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 3.55/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.55/0.97  
% 3.55/0.97  fof(f21,plain,(
% 3.55/0.97    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.55/0.97    inference(ennf_transformation,[],[f6])).
% 3.55/0.97  
% 3.55/0.97  fof(f46,plain,(
% 3.55/0.97    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.55/0.97    inference(cnf_transformation,[],[f21])).
% 3.55/0.97  
% 3.55/0.97  fof(f2,axiom,(
% 3.55/0.97    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.55/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.55/0.97  
% 3.55/0.97  fof(f42,plain,(
% 3.55/0.97    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.55/0.97    inference(cnf_transformation,[],[f2])).
% 3.55/0.97  
% 3.55/0.97  fof(f60,plain,(
% 3.55/0.97    ~r1_tarski(sK2,k2_tops_1(sK1,sK2)) | ~v2_tops_1(sK2,sK1)),
% 3.55/0.97    inference(cnf_transformation,[],[f40])).
% 3.55/0.97  
% 3.55/0.97  fof(f10,axiom,(
% 3.55/0.97    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 3.55/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.55/0.97  
% 3.55/0.97  fof(f27,plain,(
% 3.55/0.97    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.55/0.97    inference(ennf_transformation,[],[f10])).
% 3.55/0.97  
% 3.55/0.97  fof(f51,plain,(
% 3.55/0.97    ( ! [X0,X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.55/0.97    inference(cnf_transformation,[],[f27])).
% 3.55/0.97  
% 3.55/0.97  cnf(c_9,plain,
% 3.55/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.55/0.97      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.55/0.97      | ~ l1_pre_topc(X1) ),
% 3.55/0.97      inference(cnf_transformation,[],[f50]) ).
% 3.55/0.97  
% 3.55/0.97  cnf(c_702,plain,
% 3.55/0.97      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.55/0.97      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 3.55/0.97      | l1_pre_topc(X1) != iProver_top ),
% 3.55/0.97      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.55/0.97  
% 3.55/0.97  cnf(c_12,plain,
% 3.55/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.55/0.97      | r1_tarski(k1_tops_1(X1,X0),X0)
% 3.55/0.97      | ~ l1_pre_topc(X1) ),
% 3.55/0.97      inference(cnf_transformation,[],[f53]) ).
% 3.55/0.97  
% 3.55/0.97  cnf(c_699,plain,
% 3.55/0.97      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.55/0.97      | r1_tarski(k1_tops_1(X1,X0),X0) = iProver_top
% 3.55/0.97      | l1_pre_topc(X1) != iProver_top ),
% 3.55/0.97      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.55/0.97  
% 3.55/0.97  cnf(c_2233,plain,
% 3.55/0.97      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.55/0.97      | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),k2_pre_topc(X1,X0)) = iProver_top
% 3.55/0.97      | l1_pre_topc(X1) != iProver_top ),
% 3.55/0.97      inference(superposition,[status(thm)],[c_702,c_699]) ).
% 3.55/0.97  
% 3.55/0.97  cnf(c_17,negated_conjecture,
% 3.55/0.97      ( v2_tops_1(sK2,sK1) | r1_tarski(sK2,k2_tops_1(sK1,sK2)) ),
% 3.55/0.97      inference(cnf_transformation,[],[f59]) ).
% 3.55/0.97  
% 3.55/0.97  cnf(c_694,plain,
% 3.55/0.97      ( v2_tops_1(sK2,sK1) = iProver_top
% 3.55/0.97      | r1_tarski(sK2,k2_tops_1(sK1,sK2)) = iProver_top ),
% 3.55/0.97      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.55/0.97  
% 3.55/0.97  cnf(c_0,plain,
% 3.55/0.97      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 3.55/0.97      inference(cnf_transformation,[],[f41]) ).
% 3.55/0.97  
% 3.55/0.97  cnf(c_709,plain,
% 3.55/0.97      ( r1_tarski(X0,X1) != iProver_top
% 3.55/0.97      | r1_tarski(X2,X0) != iProver_top
% 3.55/0.97      | r1_tarski(X2,X1) = iProver_top ),
% 3.55/0.97      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.55/0.97  
% 3.55/0.97  cnf(c_1406,plain,
% 3.55/0.97      ( v2_tops_1(sK2,sK1) = iProver_top
% 3.55/0.97      | r1_tarski(X0,k2_tops_1(sK1,sK2)) = iProver_top
% 3.55/0.97      | r1_tarski(X0,sK2) != iProver_top ),
% 3.55/0.97      inference(superposition,[status(thm)],[c_694,c_709]) ).
% 3.55/0.97  
% 3.55/0.97  cnf(c_1640,plain,
% 3.55/0.97      ( v2_tops_1(sK2,sK1) = iProver_top
% 3.55/0.97      | r1_tarski(X0,X1) != iProver_top
% 3.55/0.97      | r1_tarski(X0,k2_tops_1(sK1,sK2)) = iProver_top
% 3.55/0.97      | r1_tarski(X1,sK2) != iProver_top ),
% 3.55/0.97      inference(superposition,[status(thm)],[c_1406,c_709]) ).
% 3.55/0.97  
% 3.55/0.97  cnf(c_5072,plain,
% 3.55/0.97      ( v2_tops_1(sK2,sK1) = iProver_top
% 3.55/0.97      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.55/0.97      | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),k2_tops_1(sK1,sK2)) = iProver_top
% 3.55/0.97      | r1_tarski(k2_pre_topc(X1,X0),sK2) != iProver_top
% 3.55/0.97      | l1_pre_topc(X1) != iProver_top ),
% 3.55/0.97      inference(superposition,[status(thm)],[c_2233,c_1640]) ).
% 3.55/0.97  
% 3.55/0.97  cnf(c_19,negated_conjecture,
% 3.55/0.97      ( l1_pre_topc(sK1) ),
% 3.55/0.97      inference(cnf_transformation,[],[f57]) ).
% 3.55/0.97  
% 3.55/0.97  cnf(c_20,plain,
% 3.55/0.97      ( l1_pre_topc(sK1) = iProver_top ),
% 3.55/0.97      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.55/0.97  
% 3.55/0.97  cnf(c_18,negated_conjecture,
% 3.55/0.97      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 3.55/0.97      inference(cnf_transformation,[],[f58]) ).
% 3.55/0.97  
% 3.55/0.97  cnf(c_21,plain,
% 3.55/0.97      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 3.55/0.97      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.55/0.97  
% 3.55/0.97  cnf(c_14,plain,
% 3.55/0.97      ( v2_tops_1(X0,X1)
% 3.55/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.55/0.97      | ~ l1_pre_topc(X1)
% 3.55/0.97      | k1_tops_1(X1,X0) != k1_xboole_0 ),
% 3.55/0.97      inference(cnf_transformation,[],[f56]) ).
% 3.55/0.97  
% 3.55/0.97  cnf(c_1056,plain,
% 3.55/0.97      ( v2_tops_1(X0,sK1)
% 3.55/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.55/0.97      | ~ l1_pre_topc(sK1)
% 3.55/0.97      | k1_tops_1(sK1,X0) != k1_xboole_0 ),
% 3.55/0.97      inference(instantiation,[status(thm)],[c_14]) ).
% 3.55/0.97  
% 3.55/0.97  cnf(c_1057,plain,
% 3.55/0.97      ( k1_tops_1(sK1,X0) != k1_xboole_0
% 3.55/0.97      | v2_tops_1(X0,sK1) = iProver_top
% 3.55/0.97      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.55/0.97      | l1_pre_topc(sK1) != iProver_top ),
% 3.55/0.97      inference(predicate_to_equality,[status(thm)],[c_1056]) ).
% 3.55/0.97  
% 3.55/0.97  cnf(c_1059,plain,
% 3.55/0.97      ( k1_tops_1(sK1,sK2) != k1_xboole_0
% 3.55/0.97      | v2_tops_1(sK2,sK1) = iProver_top
% 3.55/0.97      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.55/0.97      | l1_pre_topc(sK1) != iProver_top ),
% 3.55/0.97      inference(instantiation,[status(thm)],[c_1057]) ).
% 3.55/0.97  
% 3.55/0.97  cnf(c_693,plain,
% 3.55/0.97      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 3.55/0.97      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.55/0.97  
% 3.55/0.97  cnf(c_2054,plain,
% 3.55/0.97      ( r1_tarski(k1_tops_1(sK1,sK2),sK2) = iProver_top
% 3.55/0.97      | l1_pre_topc(sK1) != iProver_top ),
% 3.55/0.97      inference(superposition,[status(thm)],[c_693,c_699]) ).
% 3.55/0.97  
% 3.55/0.97  cnf(c_910,plain,
% 3.55/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.55/0.97      | r1_tarski(k1_tops_1(sK1,X0),X0)
% 3.55/0.97      | ~ l1_pre_topc(sK1) ),
% 3.55/0.97      inference(instantiation,[status(thm)],[c_12]) ).
% 3.55/0.97  
% 3.55/0.97  cnf(c_911,plain,
% 3.55/0.97      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.55/0.97      | r1_tarski(k1_tops_1(sK1,X0),X0) = iProver_top
% 3.55/0.97      | l1_pre_topc(sK1) != iProver_top ),
% 3.55/0.97      inference(predicate_to_equality,[status(thm)],[c_910]) ).
% 3.55/0.97  
% 3.55/0.97  cnf(c_913,plain,
% 3.55/0.97      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.55/0.97      | r1_tarski(k1_tops_1(sK1,sK2),sK2) = iProver_top
% 3.55/0.97      | l1_pre_topc(sK1) != iProver_top ),
% 3.55/0.97      inference(instantiation,[status(thm)],[c_911]) ).
% 3.55/0.97  
% 3.55/0.97  cnf(c_2282,plain,
% 3.55/0.97      ( r1_tarski(k1_tops_1(sK1,sK2),sK2) = iProver_top ),
% 3.55/0.97      inference(global_propositional_subsumption,
% 3.55/0.97                [status(thm)],
% 3.55/0.97                [c_2054,c_20,c_21,c_913]) ).
% 3.55/0.97  
% 3.55/0.97  cnf(c_2287,plain,
% 3.55/0.97      ( v2_tops_1(sK2,sK1) = iProver_top
% 3.55/0.97      | r1_tarski(k1_tops_1(sK1,sK2),k2_tops_1(sK1,sK2)) = iProver_top
% 3.55/0.97      | r1_tarski(sK2,sK2) != iProver_top ),
% 3.55/0.97      inference(superposition,[status(thm)],[c_2282,c_1640]) ).
% 3.55/0.97  
% 3.55/0.97  cnf(c_22,plain,
% 3.55/0.97      ( v2_tops_1(sK2,sK1) = iProver_top
% 3.55/0.97      | r1_tarski(sK2,k2_tops_1(sK1,sK2)) = iProver_top ),
% 3.55/0.97      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.55/0.97  
% 3.55/0.97  cnf(c_1048,plain,
% 3.55/0.97      ( ~ r1_tarski(X0,X1)
% 3.55/0.97      | ~ r1_tarski(k1_tops_1(sK1,X0),X0)
% 3.55/0.97      | r1_tarski(k1_tops_1(sK1,X0),X1) ),
% 3.55/0.97      inference(instantiation,[status(thm)],[c_0]) ).
% 3.55/0.97  
% 3.55/0.97  cnf(c_1619,plain,
% 3.55/0.97      ( r1_tarski(k1_tops_1(sK1,sK2),k2_tops_1(sK1,sK2))
% 3.55/0.97      | ~ r1_tarski(k1_tops_1(sK1,sK2),sK2)
% 3.55/0.97      | ~ r1_tarski(sK2,k2_tops_1(sK1,sK2)) ),
% 3.55/0.97      inference(instantiation,[status(thm)],[c_1048]) ).
% 3.55/0.97  
% 3.55/0.97  cnf(c_1628,plain,
% 3.55/0.97      ( r1_tarski(k1_tops_1(sK1,sK2),k2_tops_1(sK1,sK2)) = iProver_top
% 3.55/0.97      | r1_tarski(k1_tops_1(sK1,sK2),sK2) != iProver_top
% 3.55/0.97      | r1_tarski(sK2,k2_tops_1(sK1,sK2)) != iProver_top ),
% 3.55/0.97      inference(predicate_to_equality,[status(thm)],[c_1619]) ).
% 3.55/0.97  
% 3.55/0.97  cnf(c_2951,plain,
% 3.55/0.97      ( r1_tarski(k1_tops_1(sK1,sK2),k2_tops_1(sK1,sK2)) = iProver_top
% 3.55/0.97      | v2_tops_1(sK2,sK1) = iProver_top ),
% 3.55/0.97      inference(global_propositional_subsumption,
% 3.55/0.97                [status(thm)],
% 3.55/0.97                [c_2287,c_20,c_21,c_22,c_913,c_1628]) ).
% 3.55/0.97  
% 3.55/0.97  cnf(c_2952,plain,
% 3.55/0.97      ( v2_tops_1(sK2,sK1) = iProver_top
% 3.55/0.97      | r1_tarski(k1_tops_1(sK1,sK2),k2_tops_1(sK1,sK2)) = iProver_top ),
% 3.55/0.97      inference(renaming,[status(thm)],[c_2951]) ).
% 3.55/0.97  
% 3.55/0.97  cnf(c_13,plain,
% 3.55/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.55/0.97      | r1_xboole_0(k1_tops_1(X1,X0),k2_tops_1(X1,X0))
% 3.55/0.97      | ~ l1_pre_topc(X1) ),
% 3.55/0.97      inference(cnf_transformation,[],[f54]) ).
% 3.55/0.97  
% 3.55/0.97  cnf(c_698,plain,
% 3.55/0.97      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.55/0.97      | r1_xboole_0(k1_tops_1(X1,X0),k2_tops_1(X1,X0)) = iProver_top
% 3.55/0.97      | l1_pre_topc(X1) != iProver_top ),
% 3.55/0.97      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.55/0.97  
% 3.55/0.97  cnf(c_2,plain,
% 3.55/0.97      ( ~ r1_xboole_0(X0,X1) | ~ r1_tarski(X0,X1) | v1_xboole_0(X0) ),
% 3.55/0.97      inference(cnf_transformation,[],[f43]) ).
% 3.55/0.97  
% 3.55/0.97  cnf(c_708,plain,
% 3.55/0.97      ( r1_xboole_0(X0,X1) != iProver_top
% 3.55/0.97      | r1_tarski(X0,X1) != iProver_top
% 3.55/0.97      | v1_xboole_0(X0) = iProver_top ),
% 3.55/0.97      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.55/0.97  
% 3.55/0.97  cnf(c_2134,plain,
% 3.55/0.97      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.55/0.97      | r1_tarski(k1_tops_1(X1,X0),k2_tops_1(X1,X0)) != iProver_top
% 3.55/0.97      | l1_pre_topc(X1) != iProver_top
% 3.55/0.97      | v1_xboole_0(k1_tops_1(X1,X0)) = iProver_top ),
% 3.55/0.97      inference(superposition,[status(thm)],[c_698,c_708]) ).
% 3.55/0.97  
% 3.55/0.97  cnf(c_5240,plain,
% 3.55/0.97      ( v2_tops_1(sK2,sK1) = iProver_top
% 3.55/0.97      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.55/0.97      | l1_pre_topc(sK1) != iProver_top
% 3.55/0.97      | v1_xboole_0(k1_tops_1(sK1,sK2)) = iProver_top ),
% 3.55/0.97      inference(superposition,[status(thm)],[c_2952,c_2134]) ).
% 3.55/0.97  
% 3.55/0.97  cnf(c_5885,plain,
% 3.55/0.97      ( v2_tops_1(sK2,sK1) = iProver_top
% 3.55/0.97      | v1_xboole_0(k1_tops_1(sK1,sK2)) = iProver_top ),
% 3.55/0.97      inference(global_propositional_subsumption,
% 3.55/0.97                [status(thm)],
% 3.55/0.97                [c_5240,c_20,c_21]) ).
% 3.55/0.97  
% 3.55/0.97  cnf(c_8,plain,
% 3.55/0.97      ( r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0 ),
% 3.55/0.97      inference(cnf_transformation,[],[f48]) ).
% 3.55/0.97  
% 3.55/0.97  cnf(c_703,plain,
% 3.55/0.97      ( k1_xboole_0 = X0 | r2_hidden(sK0(X0),X0) = iProver_top ),
% 3.55/0.97      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.55/0.97  
% 3.55/0.97  cnf(c_4,plain,
% 3.55/0.97      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 3.55/0.97      inference(cnf_transformation,[],[f45]) ).
% 3.55/0.97  
% 3.55/0.97  cnf(c_707,plain,
% 3.55/0.97      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 3.55/0.97      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.55/0.97  
% 3.55/0.97  cnf(c_3,plain,
% 3.55/0.97      ( k2_subset_1(X0) = X0 ),
% 3.55/0.97      inference(cnf_transformation,[],[f44]) ).
% 3.55/0.97  
% 3.55/0.97  cnf(c_718,plain,
% 3.55/0.97      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.55/0.97      inference(light_normalisation,[status(thm)],[c_707,c_3]) ).
% 3.55/0.97  
% 3.55/0.97  cnf(c_6,plain,
% 3.55/0.97      ( ~ r2_hidden(X0,X1)
% 3.55/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 3.55/0.97      | ~ v1_xboole_0(X2) ),
% 3.55/0.97      inference(cnf_transformation,[],[f47]) ).
% 3.55/0.97  
% 3.55/0.97  cnf(c_705,plain,
% 3.55/0.97      ( r2_hidden(X0,X1) != iProver_top
% 3.55/0.97      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
% 3.55/0.97      | v1_xboole_0(X2) != iProver_top ),
% 3.55/0.97      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.55/0.97  
% 3.55/0.97  cnf(c_1809,plain,
% 3.55/0.97      ( r2_hidden(X0,X1) != iProver_top
% 3.55/0.97      | v1_xboole_0(X1) != iProver_top ),
% 3.55/0.97      inference(superposition,[status(thm)],[c_718,c_705]) ).
% 3.55/0.97  
% 3.55/0.97  cnf(c_3261,plain,
% 3.55/0.97      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 3.55/0.97      inference(superposition,[status(thm)],[c_703,c_1809]) ).
% 3.55/0.97  
% 3.55/0.97  cnf(c_5891,plain,
% 3.55/0.97      ( k1_tops_1(sK1,sK2) = k1_xboole_0
% 3.55/0.97      | v2_tops_1(sK2,sK1) = iProver_top ),
% 3.55/0.97      inference(superposition,[status(thm)],[c_5885,c_3261]) ).
% 3.55/0.97  
% 3.55/0.97  cnf(c_6057,plain,
% 3.55/0.97      ( v2_tops_1(sK2,sK1) = iProver_top ),
% 3.55/0.97      inference(global_propositional_subsumption,
% 3.55/0.97                [status(thm)],
% 3.55/0.97                [c_5072,c_20,c_21,c_1059,c_5891]) ).
% 3.55/0.97  
% 3.55/0.97  cnf(c_15,plain,
% 3.55/0.97      ( ~ v2_tops_1(X0,X1)
% 3.55/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.55/0.97      | ~ l1_pre_topc(X1)
% 3.55/0.97      | k1_tops_1(X1,X0) = k1_xboole_0 ),
% 3.55/0.97      inference(cnf_transformation,[],[f55]) ).
% 3.55/0.97  
% 3.55/0.97  cnf(c_696,plain,
% 3.55/0.97      ( k1_tops_1(X0,X1) = k1_xboole_0
% 3.55/0.97      | v2_tops_1(X1,X0) != iProver_top
% 3.55/0.97      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.55/0.97      | l1_pre_topc(X0) != iProver_top ),
% 3.55/0.97      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.55/0.97  
% 3.55/0.97  cnf(c_1068,plain,
% 3.55/0.97      ( k1_tops_1(sK1,sK2) = k1_xboole_0
% 3.55/0.97      | v2_tops_1(sK2,sK1) != iProver_top
% 3.55/0.97      | l1_pre_topc(sK1) != iProver_top ),
% 3.55/0.97      inference(superposition,[status(thm)],[c_693,c_696]) ).
% 3.55/0.97  
% 3.55/0.97  cnf(c_1511,plain,
% 3.55/0.97      ( v2_tops_1(sK2,sK1) != iProver_top
% 3.55/0.97      | k1_tops_1(sK1,sK2) = k1_xboole_0 ),
% 3.55/0.97      inference(global_propositional_subsumption,
% 3.55/0.97                [status(thm)],
% 3.55/0.97                [c_1068,c_20]) ).
% 3.55/0.97  
% 3.55/0.97  cnf(c_1512,plain,
% 3.55/0.97      ( k1_tops_1(sK1,sK2) = k1_xboole_0
% 3.55/0.97      | v2_tops_1(sK2,sK1) != iProver_top ),
% 3.55/0.97      inference(renaming,[status(thm)],[c_1511]) ).
% 3.55/0.97  
% 3.55/0.97  cnf(c_6062,plain,
% 3.55/0.97      ( k1_tops_1(sK1,sK2) = k1_xboole_0 ),
% 3.55/0.97      inference(superposition,[status(thm)],[c_6057,c_1512]) ).
% 3.55/0.97  
% 3.55/0.97  cnf(c_11,plain,
% 3.55/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.55/0.97      | ~ l1_pre_topc(X1)
% 3.55/0.97      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
% 3.55/0.97      inference(cnf_transformation,[],[f52]) ).
% 3.55/0.97  
% 3.55/0.97  cnf(c_700,plain,
% 3.55/0.97      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
% 3.55/0.97      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.55/0.97      | l1_pre_topc(X0) != iProver_top ),
% 3.55/0.97      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.55/0.97  
% 3.55/0.97  cnf(c_3142,plain,
% 3.55/0.97      ( k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),k1_tops_1(sK1,sK2)) = k2_tops_1(sK1,sK2)
% 3.55/0.97      | l1_pre_topc(sK1) != iProver_top ),
% 3.55/0.97      inference(superposition,[status(thm)],[c_693,c_700]) ).
% 3.55/0.97  
% 3.55/0.97  cnf(c_976,plain,
% 3.55/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.55/0.97      | ~ l1_pre_topc(sK1)
% 3.55/0.97      | k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,X0),k1_tops_1(sK1,X0)) = k2_tops_1(sK1,X0) ),
% 3.55/0.97      inference(instantiation,[status(thm)],[c_11]) ).
% 3.55/0.97  
% 3.55/0.97  cnf(c_978,plain,
% 3.55/0.97      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.55/0.97      | ~ l1_pre_topc(sK1)
% 3.55/0.97      | k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),k1_tops_1(sK1,sK2)) = k2_tops_1(sK1,sK2) ),
% 3.55/0.97      inference(instantiation,[status(thm)],[c_976]) ).
% 3.55/0.97  
% 3.55/0.97  cnf(c_3579,plain,
% 3.55/0.97      ( k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),k1_tops_1(sK1,sK2)) = k2_tops_1(sK1,sK2) ),
% 3.55/0.97      inference(global_propositional_subsumption,
% 3.55/0.97                [status(thm)],
% 3.55/0.97                [c_3142,c_19,c_18,c_978]) ).
% 3.55/0.97  
% 3.55/0.97  cnf(c_5,plain,
% 3.55/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.55/0.97      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 3.55/0.97      inference(cnf_transformation,[],[f46]) ).
% 3.55/0.97  
% 3.55/0.97  cnf(c_706,plain,
% 3.55/0.97      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
% 3.55/0.97      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.55/0.97      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.55/0.97  
% 3.55/0.97  cnf(c_2235,plain,
% 3.55/0.97      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X2) = k4_xboole_0(k2_pre_topc(X0,X1),X2)
% 3.55/0.97      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.55/0.97      | l1_pre_topc(X0) != iProver_top ),
% 3.55/0.97      inference(superposition,[status(thm)],[c_702,c_706]) ).
% 3.55/0.97  
% 3.55/0.97  cnf(c_5255,plain,
% 3.55/0.97      ( k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),X0) = k4_xboole_0(k2_pre_topc(sK1,sK2),X0)
% 3.55/0.97      | l1_pre_topc(sK1) != iProver_top ),
% 3.55/0.97      inference(superposition,[status(thm)],[c_693,c_2235]) ).
% 3.55/0.97  
% 3.55/0.97  cnf(c_5430,plain,
% 3.55/0.97      ( k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),X0) = k4_xboole_0(k2_pre_topc(sK1,sK2),X0) ),
% 3.55/0.97      inference(global_propositional_subsumption,
% 3.55/0.97                [status(thm)],
% 3.55/0.97                [c_5255,c_20]) ).
% 3.55/0.97  
% 3.55/0.97  cnf(c_5434,plain,
% 3.55/0.97      ( k4_xboole_0(k2_pre_topc(sK1,sK2),k1_tops_1(sK1,sK2)) = k2_tops_1(sK1,sK2) ),
% 3.55/0.97      inference(superposition,[status(thm)],[c_3579,c_5430]) ).
% 3.55/0.97  
% 3.55/0.97  cnf(c_6064,plain,
% 3.55/0.97      ( k4_xboole_0(k2_pre_topc(sK1,sK2),k1_xboole_0) = k2_tops_1(sK1,sK2) ),
% 3.55/0.97      inference(demodulation,[status(thm)],[c_6062,c_5434]) ).
% 3.55/0.97  
% 3.55/0.97  cnf(c_1,plain,
% 3.55/0.97      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.55/0.97      inference(cnf_transformation,[],[f42]) ).
% 3.55/0.97  
% 3.55/0.97  cnf(c_6085,plain,
% 3.55/0.97      ( k2_tops_1(sK1,sK2) = k2_pre_topc(sK1,sK2) ),
% 3.55/0.97      inference(demodulation,[status(thm)],[c_6064,c_1]) ).
% 3.55/0.97  
% 3.55/0.97  cnf(c_16,negated_conjecture,
% 3.55/0.97      ( ~ v2_tops_1(sK2,sK1) | ~ r1_tarski(sK2,k2_tops_1(sK1,sK2)) ),
% 3.55/0.97      inference(cnf_transformation,[],[f60]) ).
% 3.55/0.97  
% 3.55/0.97  cnf(c_695,plain,
% 3.55/0.97      ( v2_tops_1(sK2,sK1) != iProver_top
% 3.55/0.97      | r1_tarski(sK2,k2_tops_1(sK1,sK2)) != iProver_top ),
% 3.55/0.97      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.55/0.97  
% 3.55/0.97  cnf(c_6455,plain,
% 3.55/0.97      ( v2_tops_1(sK2,sK1) != iProver_top
% 3.55/0.97      | r1_tarski(sK2,k2_pre_topc(sK1,sK2)) != iProver_top ),
% 3.55/0.97      inference(demodulation,[status(thm)],[c_6085,c_695]) ).
% 3.55/0.97  
% 3.55/0.97  cnf(c_10,plain,
% 3.55/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.55/0.97      | r1_tarski(X0,k2_pre_topc(X1,X0))
% 3.55/0.97      | ~ l1_pre_topc(X1) ),
% 3.55/0.97      inference(cnf_transformation,[],[f51]) ).
% 3.55/0.97  
% 3.55/0.97  cnf(c_905,plain,
% 3.55/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.55/0.97      | r1_tarski(X0,k2_pre_topc(sK1,X0))
% 3.55/0.97      | ~ l1_pre_topc(sK1) ),
% 3.55/0.97      inference(instantiation,[status(thm)],[c_10]) ).
% 3.55/0.97  
% 3.55/0.97  cnf(c_906,plain,
% 3.55/0.97      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.55/0.97      | r1_tarski(X0,k2_pre_topc(sK1,X0)) = iProver_top
% 3.55/0.97      | l1_pre_topc(sK1) != iProver_top ),
% 3.55/0.97      inference(predicate_to_equality,[status(thm)],[c_905]) ).
% 3.55/0.97  
% 3.55/0.97  cnf(c_908,plain,
% 3.55/0.97      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.55/0.97      | r1_tarski(sK2,k2_pre_topc(sK1,sK2)) = iProver_top
% 3.55/0.97      | l1_pre_topc(sK1) != iProver_top ),
% 3.55/0.97      inference(instantiation,[status(thm)],[c_906]) ).
% 3.55/0.97  
% 3.55/0.97  cnf(contradiction,plain,
% 3.55/0.97      ( $false ),
% 3.55/0.97      inference(minisat,[status(thm)],[c_6455,c_6057,c_908,c_21,c_20]) ).
% 3.55/0.97  
% 3.55/0.97  
% 3.55/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 3.55/0.97  
% 3.55/0.97  ------                               Statistics
% 3.55/0.97  
% 3.55/0.97  ------ Selected
% 3.55/0.97  
% 3.55/0.97  total_time:                             0.214
% 3.55/0.97  
%------------------------------------------------------------------------------
