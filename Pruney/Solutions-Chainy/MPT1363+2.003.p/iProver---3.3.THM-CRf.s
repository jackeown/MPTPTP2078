%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:17:56 EST 2020

% Result     : Theorem 2.08s
% Output     : CNFRefutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :  207 (3502 expanded)
%              Number of clauses        :  148 (1082 expanded)
%              Number of leaves         :   21 ( 934 expanded)
%              Depth                    :   22
%              Number of atoms          :  879 (22225 expanded)
%              Number of equality atoms :  317 (2005 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   16 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v4_pre_topc(X2,X0)
                  & r1_tarski(X2,X1)
                  & v2_compts_1(X1,X0) )
               => v2_compts_1(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v4_pre_topc(X2,X0)
                    & r1_tarski(X2,X1)
                    & v2_compts_1(X1,X0) )
                 => v2_compts_1(X2,X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_compts_1(X2,X0)
              & v4_pre_topc(X2,X0)
              & r1_tarski(X2,X1)
              & v2_compts_1(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_compts_1(X2,X0)
              & v4_pre_topc(X2,X0)
              & r1_tarski(X2,X1)
              & v2_compts_1(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ v2_compts_1(X2,X0)
          & v4_pre_topc(X2,X0)
          & r1_tarski(X2,X1)
          & v2_compts_1(X1,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v2_compts_1(sK3,X0)
        & v4_pre_topc(sK3,X0)
        & r1_tarski(sK3,X1)
        & v2_compts_1(X1,X0)
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_compts_1(X2,X0)
              & v4_pre_topc(X2,X0)
              & r1_tarski(X2,X1)
              & v2_compts_1(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ~ v2_compts_1(X2,X0)
            & v4_pre_topc(X2,X0)
            & r1_tarski(X2,sK2)
            & v2_compts_1(sK2,X0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v2_compts_1(X2,X0)
                & v4_pre_topc(X2,X0)
                & r1_tarski(X2,X1)
                & v2_compts_1(X1,X0)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_compts_1(X2,sK1)
              & v4_pre_topc(X2,sK1)
              & r1_tarski(X2,X1)
              & v2_compts_1(X1,sK1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ~ v2_compts_1(sK3,sK1)
    & v4_pre_topc(sK3,sK1)
    & r1_tarski(sK3,sK2)
    & v2_compts_1(sK2,sK1)
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f26,f35,f34,f33])).

fof(f55,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f36])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v2_pre_topc(X0)
             => ( ( v2_compts_1(X1,X0)
                <=> v1_compts_1(k1_pre_topc(X0,X1)) )
                | k1_xboole_0 = X1 ) )
            & ( k1_xboole_0 = X1
             => ( v2_compts_1(X1,X0)
              <=> v1_compts_1(k1_pre_topc(X0,X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( ( v2_compts_1(X1,X0)
              <=> v1_compts_1(k1_pre_topc(X0,X1)) )
              | k1_xboole_0 = X1
              | ~ v2_pre_topc(X0) )
            & ( ( v2_compts_1(X1,X0)
              <=> v1_compts_1(k1_pre_topc(X0,X1)) )
              | k1_xboole_0 != X1 ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( ( v2_compts_1(X1,X0)
              <=> v1_compts_1(k1_pre_topc(X0,X1)) )
              | k1_xboole_0 = X1
              | ~ v2_pre_topc(X0) )
            & ( ( v2_compts_1(X1,X0)
              <=> v1_compts_1(k1_pre_topc(X0,X1)) )
              | k1_xboole_0 != X1 ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( ( ( v2_compts_1(X1,X0)
                  | ~ v1_compts_1(k1_pre_topc(X0,X1)) )
                & ( v1_compts_1(k1_pre_topc(X0,X1))
                  | ~ v2_compts_1(X1,X0) ) )
              | k1_xboole_0 = X1
              | ~ v2_pre_topc(X0) )
            & ( ( ( v2_compts_1(X1,X0)
                  | ~ v1_compts_1(k1_pre_topc(X0,X1)) )
                & ( v1_compts_1(k1_pre_topc(X0,X1))
                  | ~ v2_compts_1(X1,X0) ) )
              | k1_xboole_0 != X1 ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v1_compts_1(k1_pre_topc(X0,X1))
      | ~ v2_compts_1(X1,X0)
      | k1_xboole_0 = X1
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f53,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f54,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f57,plain,(
    v2_compts_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f56,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f36])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( v4_pre_topc(X1,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( X1 = X3
                     => v4_pre_topc(X3,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v4_pre_topc(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v4_pre_topc(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( v4_pre_topc(X3,X2)
      | X1 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f63,plain,(
    ! [X2,X0,X3] :
      ( v4_pre_topc(X3,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v4_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f43])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f41,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f59,plain,(
    v4_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f60,plain,(
    ~ v2_compts_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_pre_topc(X2) )
             => ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k1_pre_topc(X0,X1) = X2
                  | k2_struct_0(X2) != X1 )
                & ( k2_struct_0(X2) = X1
                  | k1_pre_topc(X0,X1) != X2 ) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k2_struct_0(X2) = X1
      | k1_pre_topc(X0,X1) != X2
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_pre_topc(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k2_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ v1_pre_topc(k1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f37])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X2,k2_struct_0(X1))
               => ( v2_compts_1(X2,X0)
                <=> ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                     => ( X2 = X3
                       => v2_compts_1(X3,X1) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_compts_1(X2,X0)
              <=> ! [X3] :
                    ( v2_compts_1(X3,X1)
                    | X2 != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ r1_tarski(X2,k2_struct_0(X1))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_compts_1(X2,X0)
              <=> ! [X3] :
                    ( v2_compts_1(X3,X1)
                    | X2 != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ r1_tarski(X2,k2_struct_0(X1))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v2_compts_1(X2,X0)
                  | ? [X3] :
                      ( ~ v2_compts_1(X3,X1)
                      & X2 = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X3] :
                      ( v2_compts_1(X3,X1)
                      | X2 != X3
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v2_compts_1(X2,X0) ) )
              | ~ r1_tarski(X2,k2_struct_0(X1))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v2_compts_1(X2,X0)
                  | ? [X3] :
                      ( ~ v2_compts_1(X3,X1)
                      & X2 = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v2_compts_1(X4,X1)
                      | X2 != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v2_compts_1(X2,X0) ) )
              | ~ r1_tarski(X2,k2_struct_0(X1))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X2,X1] :
      ( ? [X3] :
          ( ~ v2_compts_1(X3,X1)
          & X2 = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v2_compts_1(sK0(X1,X2),X1)
        & sK0(X1,X2) = X2
        & m1_subset_1(sK0(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v2_compts_1(X2,X0)
                  | ( ~ v2_compts_1(sK0(X1,X2),X1)
                    & sK0(X1,X2) = X2
                    & m1_subset_1(sK0(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v2_compts_1(X4,X1)
                      | X2 != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v2_compts_1(X2,X0) ) )
              | ~ r1_tarski(X2,k2_struct_0(X1))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( v2_compts_1(X2,X0)
      | sK0(X1,X2) = X2
      | ~ r1_tarski(X2,k2_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f58,plain,(
    r1_tarski(sK3,sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( v2_compts_1(X2,X0)
      | m1_subset_1(sK0(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r1_tarski(X2,k2_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v4_pre_topc(X1,X0)
              & v1_compts_1(X0) )
           => v2_compts_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_compts_1(X1,X0)
          | ~ v4_pre_topc(X1,X0)
          | ~ v1_compts_1(X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_compts_1(X1,X0)
          | ~ v4_pre_topc(X1,X0)
          | ~ v1_compts_1(X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v2_compts_1(X1,X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ v1_compts_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( v2_compts_1(X2,X0)
      | ~ v2_compts_1(sK0(X1,X2),X1)
      | ~ r1_tarski(X2,k2_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v1_compts_1(k1_pre_topc(X0,X1))
      | ~ v2_compts_1(X1,X0)
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f66,plain,(
    ! [X0] :
      ( v1_compts_1(k1_pre_topc(X0,k1_xboole_0))
      | ~ v2_compts_1(k1_xboole_0,X0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f48])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1333,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1815,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1333])).

cnf(c_12,plain,
    ( ~ v2_compts_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v1_compts_1(k1_pre_topc(X1,X0))
    | ~ l1_pre_topc(X1)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_23,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_292,plain,
    ( ~ v2_compts_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_compts_1(k1_pre_topc(X1,X0))
    | ~ l1_pre_topc(X1)
    | sK1 != X1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_23])).

cnf(c_293,plain,
    ( ~ v2_compts_1(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_compts_1(k1_pre_topc(sK1,X0))
    | ~ l1_pre_topc(sK1)
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_292])).

cnf(c_22,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_297,plain,
    ( v1_compts_1(k1_pre_topc(sK1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_compts_1(X0,sK1)
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_293,c_22])).

cnf(c_298,plain,
    ( ~ v2_compts_1(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_compts_1(k1_pre_topc(sK1,X0))
    | k1_xboole_0 = X0 ),
    inference(renaming,[status(thm)],[c_297])).

cnf(c_1330,plain,
    ( ~ v2_compts_1(X0_46,sK1)
    | ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_compts_1(k1_pre_topc(sK1,X0_46))
    | k1_xboole_0 = X0_46 ),
    inference(subtyping,[status(esa)],[c_298])).

cnf(c_1818,plain,
    ( k1_xboole_0 = X0_46
    | v2_compts_1(X0_46,sK1) != iProver_top
    | m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v1_compts_1(k1_pre_topc(sK1,X0_46)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1330])).

cnf(c_2474,plain,
    ( sK2 = k1_xboole_0
    | v2_compts_1(sK2,sK1) != iProver_top
    | v1_compts_1(k1_pre_topc(sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1815,c_1818])).

cnf(c_19,negated_conjecture,
    ( v2_compts_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_28,plain,
    ( v2_compts_1(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2539,plain,
    ( sK2 = k1_xboole_0
    | v1_compts_1(k1_pre_topc(sK1,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2474,c_28])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_pre_topc(k1_pre_topc(X1,X0),X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1345,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(X0_47)))
    | m1_pre_topc(k1_pre_topc(X0_47,X0_46),X0_47)
    | ~ l1_pre_topc(X0_47) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1803,plain,
    ( m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(X0_47))) != iProver_top
    | m1_pre_topc(k1_pre_topc(X0_47,X0_46),X0_47) = iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1345])).

cnf(c_2287,plain,
    ( m1_pre_topc(k1_pre_topc(sK1,sK2),sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1815,c_1803])).

cnf(c_25,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_26,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2054,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_pre_topc(k1_pre_topc(sK1,sK2),sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_1345])).

cnf(c_2055,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_pre_topc(k1_pre_topc(sK1,sK2),sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2054])).

cnf(c_2461,plain,
    ( m1_pre_topc(k1_pre_topc(sK1,sK2),sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2287,c_25,c_26,c_2055])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1334,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1814,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1334])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1342,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(X0_47)))
    | m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(X1_47)))
    | ~ m1_pre_topc(X0_47,X1_47)
    | ~ l1_pre_topc(X1_47) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1806,plain,
    ( m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(X0_47))) != iProver_top
    | m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(X1_47))) = iProver_top
    | m1_pre_topc(X0_47,X1_47) != iProver_top
    | l1_pre_topc(X1_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1342])).

cnf(c_2632,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0_47))) = iProver_top
    | m1_pre_topc(sK1,X0_47) != iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(superposition,[status(thm)],[c_1814,c_1806])).

cnf(c_6,plain,
    ( ~ v4_pre_topc(X0,X1)
    | v4_pre_topc(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1341,plain,
    ( ~ v4_pre_topc(X0_46,X0_47)
    | v4_pre_topc(X0_46,X1_47)
    | ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(X1_47)))
    | ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(X0_47)))
    | ~ m1_pre_topc(X1_47,X0_47)
    | ~ l1_pre_topc(X0_47) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1807,plain,
    ( v4_pre_topc(X0_46,X0_47) != iProver_top
    | v4_pre_topc(X0_46,X1_47) = iProver_top
    | m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(X1_47))) != iProver_top
    | m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(X0_47))) != iProver_top
    | m1_pre_topc(X1_47,X0_47) != iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1341])).

cnf(c_1962,plain,
    ( v4_pre_topc(X0_46,X0_47) != iProver_top
    | v4_pre_topc(X0_46,X1_47) = iProver_top
    | m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(X1_47))) != iProver_top
    | m1_pre_topc(X1_47,X0_47) != iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1807,c_1806])).

cnf(c_4055,plain,
    ( v4_pre_topc(sK3,X0_47) != iProver_top
    | v4_pre_topc(sK3,X1_47) = iProver_top
    | m1_pre_topc(X1_47,X0_47) != iProver_top
    | m1_pre_topc(sK1,X1_47) != iProver_top
    | l1_pre_topc(X0_47) != iProver_top
    | l1_pre_topc(X1_47) != iProver_top ),
    inference(superposition,[status(thm)],[c_2632,c_1962])).

cnf(c_4,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1343,plain,
    ( ~ m1_pre_topc(X0_47,X1_47)
    | ~ l1_pre_topc(X1_47)
    | l1_pre_topc(X0_47) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1805,plain,
    ( m1_pre_topc(X0_47,X1_47) != iProver_top
    | l1_pre_topc(X1_47) != iProver_top
    | l1_pre_topc(X0_47) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1343])).

cnf(c_4162,plain,
    ( v4_pre_topc(sK3,X0_47) != iProver_top
    | v4_pre_topc(sK3,X1_47) = iProver_top
    | m1_pre_topc(X1_47,X0_47) != iProver_top
    | m1_pre_topc(sK1,X1_47) != iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4055,c_1805])).

cnf(c_4165,plain,
    ( v4_pre_topc(sK3,k1_pre_topc(sK1,sK2)) = iProver_top
    | v4_pre_topc(sK3,sK1) != iProver_top
    | m1_pre_topc(sK1,k1_pre_topc(sK1,sK2)) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2461,c_4162])).

cnf(c_27,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_17,negated_conjecture,
    ( v4_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_30,plain,
    ( v4_pre_topc(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_16,negated_conjecture,
    ( ~ v2_compts_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_31,plain,
    ( v2_compts_1(sK3,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(k1_pre_topc(X1,X0),X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_pre_topc(k1_pre_topc(X1,X0))
    | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | v1_pre_topc(k1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_143,plain,
    ( ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1,c_3,c_2])).

cnf(c_144,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
    inference(renaming,[status(thm)],[c_143])).

cnf(c_1331,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(X0_47)))
    | ~ l1_pre_topc(X0_47)
    | k2_struct_0(k1_pre_topc(X0_47,X0_46)) = X0_46 ),
    inference(subtyping,[status(esa)],[c_144])).

cnf(c_2044,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | k2_struct_0(k1_pre_topc(sK1,sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_1331])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,k2_struct_0(X1))
    | v2_compts_1(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | sK0(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_18,negated_conjecture,
    ( r1_tarski(sK3,sK2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_396,plain,
    ( v2_compts_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | sK0(X2,X0) = X0
    | k2_struct_0(X2) != sK2
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_18])).

cnf(c_397,plain,
    ( v2_compts_1(sK3,X0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0)
    | sK0(X1,sK3) = sK3
    | k2_struct_0(X1) != sK2 ),
    inference(unflattening,[status(thm)],[c_396])).

cnf(c_1326,plain,
    ( v2_compts_1(sK3,X0_47)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0_47)))
    | ~ m1_pre_topc(X1_47,X0_47)
    | ~ l1_pre_topc(X0_47)
    | sK0(X1_47,sK3) = sK3
    | k2_struct_0(X1_47) != sK2 ),
    inference(subtyping,[status(esa)],[c_397])).

cnf(c_2127,plain,
    ( v2_compts_1(sK3,X0_47)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0_47)))
    | ~ m1_pre_topc(k1_pre_topc(sK1,sK2),X0_47)
    | ~ l1_pre_topc(X0_47)
    | sK0(k1_pre_topc(sK1,sK2),sK3) = sK3
    | k2_struct_0(k1_pre_topc(sK1,sK2)) != sK2 ),
    inference(instantiation,[status(thm)],[c_1326])).

cnf(c_2129,plain,
    ( v2_compts_1(sK3,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_pre_topc(k1_pre_topc(sK1,sK2),sK1)
    | ~ l1_pre_topc(sK1)
    | sK0(k1_pre_topc(sK1,sK2),sK3) = sK3
    | k2_struct_0(k1_pre_topc(sK1,sK2)) != sK2 ),
    inference(instantiation,[status(thm)],[c_2127])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,k2_struct_0(X1))
    | v2_compts_1(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_372,plain,
    ( v2_compts_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK0(X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | k2_struct_0(X2) != sK2
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_18])).

cnf(c_373,plain,
    ( v2_compts_1(sK3,X0)
    | m1_subset_1(sK0(X1,sK3),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0)
    | k2_struct_0(X1) != sK2 ),
    inference(unflattening,[status(thm)],[c_372])).

cnf(c_1327,plain,
    ( v2_compts_1(sK3,X0_47)
    | m1_subset_1(sK0(X1_47,sK3),k1_zfmisc_1(u1_struct_0(X1_47)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0_47)))
    | ~ m1_pre_topc(X1_47,X0_47)
    | ~ l1_pre_topc(X0_47)
    | k2_struct_0(X1_47) != sK2 ),
    inference(subtyping,[status(esa)],[c_373])).

cnf(c_2126,plain,
    ( v2_compts_1(sK3,X0_47)
    | m1_subset_1(sK0(k1_pre_topc(sK1,sK2),sK3),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK1,sK2))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0_47)))
    | ~ m1_pre_topc(k1_pre_topc(sK1,sK2),X0_47)
    | ~ l1_pre_topc(X0_47)
    | k2_struct_0(k1_pre_topc(sK1,sK2)) != sK2 ),
    inference(instantiation,[status(thm)],[c_1327])).

cnf(c_2132,plain,
    ( k2_struct_0(k1_pre_topc(sK1,sK2)) != sK2
    | v2_compts_1(sK3,X0_47) = iProver_top
    | m1_subset_1(sK0(k1_pre_topc(sK1,sK2),sK3),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK1,sK2)))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0_47))) != iProver_top
    | m1_pre_topc(k1_pre_topc(sK1,sK2),X0_47) != iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2126])).

cnf(c_2134,plain,
    ( k2_struct_0(k1_pre_topc(sK1,sK2)) != sK2
    | v2_compts_1(sK3,sK1) = iProver_top
    | m1_subset_1(sK0(k1_pre_topc(sK1,sK2),sK3),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK1,sK2)))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_pre_topc(k1_pre_topc(sK1,sK2),sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2132])).

cnf(c_1348,plain,
    ( X0_46 = X0_46 ),
    theory(equality)).

cnf(c_2170,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1348])).

cnf(c_1350,plain,
    ( X0_48 = X0_48 ),
    theory(equality)).

cnf(c_2698,plain,
    ( k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK1,sK2))) = k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_1350])).

cnf(c_1352,plain,
    ( X0_46 != X1_46
    | X2_46 != X1_46
    | X2_46 = X0_46 ),
    theory(equality)).

cnf(c_2426,plain,
    ( X0_46 != X1_46
    | sK3 != X1_46
    | sK3 = X0_46 ),
    inference(instantiation,[status(thm)],[c_1352])).

cnf(c_2618,plain,
    ( X0_46 != sK3
    | sK3 = X0_46
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2426])).

cnf(c_3015,plain,
    ( sK0(k1_pre_topc(sK1,sK2),sK3) != sK3
    | sK3 = sK0(k1_pre_topc(sK1,sK2),sK3)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2618])).

cnf(c_2077,plain,
    ( v4_pre_topc(sK3,X0_47)
    | ~ v4_pre_topc(sK3,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0_47)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_pre_topc(X0_47,sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_1341])).

cnf(c_3090,plain,
    ( v4_pre_topc(sK3,k1_pre_topc(sK1,sK2))
    | ~ v4_pre_topc(sK3,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK1,sK2))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_pre_topc(k1_pre_topc(sK1,sK2),sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_2077])).

cnf(c_3093,plain,
    ( v4_pre_topc(sK3,k1_pre_topc(sK1,sK2)) = iProver_top
    | v4_pre_topc(sK3,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK1,sK2)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_pre_topc(k1_pre_topc(sK1,sK2),sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3090])).

cnf(c_1360,plain,
    ( ~ m1_subset_1(X0_46,X0_48)
    | m1_subset_1(X1_46,X1_48)
    | X1_48 != X0_48
    | X1_46 != X0_46 ),
    theory(equality)).

cnf(c_2380,plain,
    ( m1_subset_1(X0_46,X0_48)
    | ~ m1_subset_1(sK0(k1_pre_topc(sK1,sK2),sK3),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK1,sK2))))
    | X0_48 != k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK1,sK2)))
    | X0_46 != sK0(k1_pre_topc(sK1,sK2),sK3) ),
    inference(instantiation,[status(thm)],[c_1360])).

cnf(c_2697,plain,
    ( m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK1,sK2))))
    | ~ m1_subset_1(sK0(k1_pre_topc(sK1,sK2),sK3),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK1,sK2))))
    | k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK1,sK2))) != k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK1,sK2)))
    | X0_46 != sK0(k1_pre_topc(sK1,sK2),sK3) ),
    inference(instantiation,[status(thm)],[c_2380])).

cnf(c_3609,plain,
    ( ~ m1_subset_1(sK0(k1_pre_topc(sK1,sK2),sK3),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK1,sK2))))
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK1,sK2))))
    | k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK1,sK2))) != k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK1,sK2)))
    | sK3 != sK0(k1_pre_topc(sK1,sK2),sK3) ),
    inference(instantiation,[status(thm)],[c_2697])).

cnf(c_3613,plain,
    ( k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK1,sK2))) != k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK1,sK2)))
    | sK3 != sK0(k1_pre_topc(sK1,sK2),sK3)
    | m1_subset_1(sK0(k1_pre_topc(sK1,sK2),sK3),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK1,sK2)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK1,sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3609])).

cnf(c_4314,plain,
    ( v4_pre_topc(sK3,k1_pre_topc(sK1,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4165,c_22,c_25,c_21,c_26,c_20,c_27,c_30,c_16,c_31,c_2044,c_2054,c_2055,c_2129,c_2134,c_2170,c_2698,c_3015,c_3093,c_3613])).

cnf(c_15,plain,
    ( v2_compts_1(X0,X1)
    | ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_compts_1(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1338,plain,
    ( v2_compts_1(X0_46,X0_47)
    | ~ v4_pre_topc(X0_46,X0_47)
    | ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(X0_47)))
    | ~ v1_compts_1(X0_47)
    | ~ l1_pre_topc(X0_47) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1810,plain,
    ( v2_compts_1(X0_46,X0_47) = iProver_top
    | v4_pre_topc(X0_46,X0_47) != iProver_top
    | m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(X0_47))) != iProver_top
    | v1_compts_1(X0_47) != iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1338])).

cnf(c_2892,plain,
    ( v2_compts_1(sK3,X0_47) = iProver_top
    | v4_pre_topc(sK3,X0_47) != iProver_top
    | m1_pre_topc(sK1,X0_47) != iProver_top
    | v1_compts_1(X0_47) != iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(superposition,[status(thm)],[c_2632,c_1810])).

cnf(c_4319,plain,
    ( v2_compts_1(sK3,k1_pre_topc(sK1,sK2)) = iProver_top
    | m1_pre_topc(sK1,k1_pre_topc(sK1,sK2)) != iProver_top
    | v1_compts_1(k1_pre_topc(sK1,sK2)) != iProver_top
    | l1_pre_topc(k1_pre_topc(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4314,c_2892])).

cnf(c_2466,plain,
    ( l1_pre_topc(k1_pre_topc(sK1,sK2)) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2461,c_1805])).

cnf(c_2507,plain,
    ( v2_compts_1(X0_46,k1_pre_topc(sK1,sK2))
    | ~ v4_pre_topc(X0_46,k1_pre_topc(sK1,sK2))
    | ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK1,sK2))))
    | ~ v1_compts_1(k1_pre_topc(sK1,sK2))
    | ~ l1_pre_topc(k1_pre_topc(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_1338])).

cnf(c_3088,plain,
    ( v2_compts_1(sK3,k1_pre_topc(sK1,sK2))
    | ~ v4_pre_topc(sK3,k1_pre_topc(sK1,sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK1,sK2))))
    | ~ v1_compts_1(k1_pre_topc(sK1,sK2))
    | ~ l1_pre_topc(k1_pre_topc(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_2507])).

cnf(c_3091,plain,
    ( v2_compts_1(sK3,k1_pre_topc(sK1,sK2)) = iProver_top
    | v4_pre_topc(sK3,k1_pre_topc(sK1,sK2)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK1,sK2)))) != iProver_top
    | v1_compts_1(k1_pre_topc(sK1,sK2)) != iProver_top
    | l1_pre_topc(k1_pre_topc(sK1,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3088])).

cnf(c_4651,plain,
    ( v1_compts_1(k1_pre_topc(sK1,sK2)) != iProver_top
    | v2_compts_1(sK3,k1_pre_topc(sK1,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4319,c_22,c_25,c_21,c_26,c_20,c_27,c_30,c_16,c_31,c_2044,c_2054,c_2055,c_2129,c_2134,c_2170,c_2466,c_2698,c_3015,c_3091,c_3093,c_3613])).

cnf(c_4652,plain,
    ( v2_compts_1(sK3,k1_pre_topc(sK1,sK2)) = iProver_top
    | v1_compts_1(k1_pre_topc(sK1,sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4651])).

cnf(c_1817,plain,
    ( k2_struct_0(k1_pre_topc(X0_47,X0_46)) = X0_46
    | m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(X0_47))) != iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1331])).

cnf(c_3355,plain,
    ( k2_struct_0(k1_pre_topc(sK1,sK2)) = sK2
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1815,c_1817])).

cnf(c_3488,plain,
    ( k2_struct_0(k1_pre_topc(sK1,sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3355,c_22,c_21,c_2044])).

cnf(c_1822,plain,
    ( sK0(X0_47,sK3) = sK3
    | k2_struct_0(X0_47) != sK2
    | v2_compts_1(sK3,X1_47) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X1_47))) != iProver_top
    | m1_pre_topc(X0_47,X1_47) != iProver_top
    | l1_pre_topc(X1_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1326])).

cnf(c_3492,plain,
    ( sK0(k1_pre_topc(sK1,sK2),sK3) = sK3
    | v2_compts_1(sK3,X0_47) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0_47))) != iProver_top
    | m1_pre_topc(k1_pre_topc(sK1,sK2),X0_47) != iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(superposition,[status(thm)],[c_3488,c_1822])).

cnf(c_5054,plain,
    ( sK0(k1_pre_topc(sK1,sK2),sK3) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3492,c_22,c_21,c_20,c_16,c_2044,c_2054,c_2129])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,k2_struct_0(X1))
    | v2_compts_1(X0,X2)
    | ~ v2_compts_1(sK0(X1,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_420,plain,
    ( v2_compts_1(X0,X1)
    | ~ v2_compts_1(sK0(X2,X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | k2_struct_0(X2) != sK2
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_18])).

cnf(c_421,plain,
    ( ~ v2_compts_1(sK0(X0,sK3),X0)
    | v2_compts_1(sK3,X1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | k2_struct_0(X0) != sK2 ),
    inference(unflattening,[status(thm)],[c_420])).

cnf(c_1325,plain,
    ( ~ v2_compts_1(sK0(X0_47,sK3),X0_47)
    | v2_compts_1(sK3,X1_47)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X1_47)))
    | ~ m1_pre_topc(X0_47,X1_47)
    | ~ l1_pre_topc(X1_47)
    | k2_struct_0(X0_47) != sK2 ),
    inference(subtyping,[status(esa)],[c_421])).

cnf(c_1823,plain,
    ( k2_struct_0(X0_47) != sK2
    | v2_compts_1(sK0(X0_47,sK3),X0_47) != iProver_top
    | v2_compts_1(sK3,X1_47) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X1_47))) != iProver_top
    | m1_pre_topc(X0_47,X1_47) != iProver_top
    | l1_pre_topc(X1_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1325])).

cnf(c_3493,plain,
    ( v2_compts_1(sK0(k1_pre_topc(sK1,sK2),sK3),k1_pre_topc(sK1,sK2)) != iProver_top
    | v2_compts_1(sK3,X0_47) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0_47))) != iProver_top
    | m1_pre_topc(k1_pre_topc(sK1,sK2),X0_47) != iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(superposition,[status(thm)],[c_3488,c_1823])).

cnf(c_2121,plain,
    ( ~ v2_compts_1(sK0(k1_pre_topc(sK1,sK2),sK3),k1_pre_topc(sK1,sK2))
    | v2_compts_1(sK3,X0_47)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0_47)))
    | ~ m1_pre_topc(k1_pre_topc(sK1,sK2),X0_47)
    | ~ l1_pre_topc(X0_47)
    | k2_struct_0(k1_pre_topc(sK1,sK2)) != sK2 ),
    inference(instantiation,[status(thm)],[c_1325])).

cnf(c_2122,plain,
    ( k2_struct_0(k1_pre_topc(sK1,sK2)) != sK2
    | v2_compts_1(sK0(k1_pre_topc(sK1,sK2),sK3),k1_pre_topc(sK1,sK2)) != iProver_top
    | v2_compts_1(sK3,X0_47) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0_47))) != iProver_top
    | m1_pre_topc(k1_pre_topc(sK1,sK2),X0_47) != iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2121])).

cnf(c_2124,plain,
    ( k2_struct_0(k1_pre_topc(sK1,sK2)) != sK2
    | v2_compts_1(sK0(k1_pre_topc(sK1,sK2),sK3),k1_pre_topc(sK1,sK2)) != iProver_top
    | v2_compts_1(sK3,sK1) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_pre_topc(k1_pre_topc(sK1,sK2),sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2122])).

cnf(c_5048,plain,
    ( v2_compts_1(sK0(k1_pre_topc(sK1,sK2),sK3),k1_pre_topc(sK1,sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3493,c_22,c_25,c_21,c_26,c_27,c_31,c_2044,c_2055,c_2124])).

cnf(c_5057,plain,
    ( v2_compts_1(sK3,k1_pre_topc(sK1,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5054,c_5048])).

cnf(c_5233,plain,
    ( v1_compts_1(k1_pre_topc(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4652,c_5057])).

cnf(c_5834,plain,
    ( sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2539,c_5233])).

cnf(c_5843,plain,
    ( v2_compts_1(sK3,k1_pre_topc(sK1,k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5834,c_5057])).

cnf(c_5849,plain,
    ( v2_compts_1(sK3,k1_pre_topc(sK1,k1_xboole_0)) = iProver_top
    | v1_compts_1(k1_pre_topc(sK1,k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5834,c_4652])).

cnf(c_6071,plain,
    ( v1_compts_1(k1_pre_topc(sK1,k1_xboole_0)) != iProver_top ),
    inference(backward_subsumption_resolution,[status(thm)],[c_5843,c_5849])).

cnf(c_1362,plain,
    ( ~ v4_pre_topc(X0_46,X0_47)
    | v4_pre_topc(X1_46,X1_47)
    | X1_47 != X0_47
    | X1_46 != X0_46 ),
    theory(equality)).

cnf(c_2157,plain,
    ( v4_pre_topc(X0_46,X0_47)
    | ~ v4_pre_topc(sK3,X1_47)
    | X0_47 != X1_47
    | X0_46 != sK3 ),
    inference(instantiation,[status(thm)],[c_1362])).

cnf(c_2444,plain,
    ( v4_pre_topc(sK0(k1_pre_topc(sK1,sK2),sK3),X0_47)
    | ~ v4_pre_topc(sK3,X1_47)
    | X0_47 != X1_47
    | sK0(k1_pre_topc(sK1,sK2),sK3) != sK3 ),
    inference(instantiation,[status(thm)],[c_2157])).

cnf(c_3109,plain,
    ( v4_pre_topc(sK0(k1_pre_topc(sK1,sK2),sK3),k1_pre_topc(sK1,sK2))
    | ~ v4_pre_topc(sK3,X0_47)
    | k1_pre_topc(sK1,sK2) != X0_47
    | sK0(k1_pre_topc(sK1,sK2),sK3) != sK3 ),
    inference(instantiation,[status(thm)],[c_2444])).

cnf(c_4744,plain,
    ( v4_pre_topc(sK0(k1_pre_topc(sK1,sK2),sK3),k1_pre_topc(sK1,sK2))
    | ~ v4_pre_topc(sK3,k1_pre_topc(sK1,sK2))
    | k1_pre_topc(sK1,sK2) != k1_pre_topc(sK1,sK2)
    | sK0(k1_pre_topc(sK1,sK2),sK3) != sK3 ),
    inference(instantiation,[status(thm)],[c_3109])).

cnf(c_3108,plain,
    ( v2_compts_1(sK0(k1_pre_topc(sK1,sK2),sK3),k1_pre_topc(sK1,sK2))
    | ~ v4_pre_topc(sK0(k1_pre_topc(sK1,sK2),sK3),k1_pre_topc(sK1,sK2))
    | ~ m1_subset_1(sK0(k1_pre_topc(sK1,sK2),sK3),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK1,sK2))))
    | ~ v1_compts_1(k1_pre_topc(sK1,sK2))
    | ~ l1_pre_topc(k1_pre_topc(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_2507])).

cnf(c_1355,plain,
    ( X0_47 != X1_47
    | k1_pre_topc(X0_47,X0_46) = k1_pre_topc(X1_47,X1_46)
    | X0_46 != X1_46 ),
    theory(equality)).

cnf(c_2312,plain,
    ( X0_47 != sK1
    | k1_pre_topc(X0_47,X0_46) = k1_pre_topc(sK1,sK2)
    | X0_46 != sK2 ),
    inference(instantiation,[status(thm)],[c_1355])).

cnf(c_2695,plain,
    ( X0_47 != sK1
    | k1_pre_topc(X0_47,sK2) = k1_pre_topc(sK1,sK2)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_2312])).

cnf(c_2696,plain,
    ( k1_pre_topc(sK1,sK2) = k1_pre_topc(sK1,sK2)
    | sK1 != sK1
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_2695])).

cnf(c_2467,plain,
    ( l1_pre_topc(k1_pre_topc(sK1,sK2))
    | ~ l1_pre_topc(sK1) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2466])).

cnf(c_2248,plain,
    ( k1_zfmisc_1(u1_struct_0(sK1)) = k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_1350])).

cnf(c_2062,plain,
    ( m1_subset_1(X0_46,X0_48)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | X0_48 != k1_zfmisc_1(u1_struct_0(sK1))
    | X0_46 != sK2 ),
    inference(instantiation,[status(thm)],[c_1360])).

cnf(c_2247,plain,
    ( m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
    | X0_46 != sK2 ),
    inference(instantiation,[status(thm)],[c_2062])).

cnf(c_2249,plain,
    ( k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
    | X0_46 != sK2
    | m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2247])).

cnf(c_2251,plain,
    ( k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
    | k1_xboole_0 != sK2
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2249])).

cnf(c_2190,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_1348])).

cnf(c_2183,plain,
    ( ~ v2_compts_1(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_compts_1(k1_pre_topc(sK1,sK2))
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_1330])).

cnf(c_2133,plain,
    ( v2_compts_1(sK3,sK1)
    | m1_subset_1(sK0(k1_pre_topc(sK1,sK2),sK3),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK1,sK2))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_pre_topc(k1_pre_topc(sK1,sK2),sK1)
    | ~ l1_pre_topc(sK1)
    | k2_struct_0(k1_pre_topc(sK1,sK2)) != sK2 ),
    inference(instantiation,[status(thm)],[c_2126])).

cnf(c_2123,plain,
    ( ~ v2_compts_1(sK0(k1_pre_topc(sK1,sK2),sK3),k1_pre_topc(sK1,sK2))
    | v2_compts_1(sK3,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_pre_topc(k1_pre_topc(sK1,sK2),sK1)
    | ~ l1_pre_topc(sK1)
    | k2_struct_0(k1_pre_topc(sK1,sK2)) != sK2 ),
    inference(instantiation,[status(thm)],[c_2121])).

cnf(c_1363,plain,
    ( ~ v2_compts_1(X0_46,X0_47)
    | v2_compts_1(X1_46,X1_47)
    | X1_47 != X0_47
    | X1_46 != X0_46 ),
    theory(equality)).

cnf(c_2072,plain,
    ( v2_compts_1(X0_46,X0_47)
    | ~ v2_compts_1(sK2,sK1)
    | X0_47 != sK1
    | X0_46 != sK2 ),
    inference(instantiation,[status(thm)],[c_1363])).

cnf(c_2073,plain,
    ( X0_47 != sK1
    | X0_46 != sK2
    | v2_compts_1(X0_46,X0_47) = iProver_top
    | v2_compts_1(sK2,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2072])).

cnf(c_2075,plain,
    ( sK1 != sK1
    | k1_xboole_0 != sK2
    | v2_compts_1(sK2,sK1) != iProver_top
    | v2_compts_1(k1_xboole_0,sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2073])).

cnf(c_14,plain,
    ( ~ v2_compts_1(k1_xboole_0,X0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
    | v1_compts_1(k1_pre_topc(X0,k1_xboole_0))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1339,plain,
    ( ~ v2_compts_1(k1_xboole_0,X0_47)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0_47)))
    | v1_compts_1(k1_pre_topc(X0_47,k1_xboole_0))
    | ~ l1_pre_topc(X0_47) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1398,plain,
    ( v2_compts_1(k1_xboole_0,X0_47) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0_47))) != iProver_top
    | v1_compts_1(k1_pre_topc(X0_47,k1_xboole_0)) = iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1339])).

cnf(c_1400,plain,
    ( v2_compts_1(k1_xboole_0,sK1) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v1_compts_1(k1_pre_topc(sK1,k1_xboole_0)) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1398])).

cnf(c_1349,plain,
    ( X0_47 = X0_47 ),
    theory(equality)).

cnf(c_1380,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_1349])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6071,c_4744,c_3609,c_3108,c_3090,c_3015,c_2698,c_2696,c_2467,c_2248,c_2251,c_2190,c_2183,c_2170,c_2133,c_2129,c_2123,c_2075,c_2054,c_2044,c_1400,c_1380,c_16,c_17,c_28,c_19,c_20,c_26,c_21,c_25,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:20:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  % Running in FOF mode
% 2.08/1.06  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.06  
% 2.08/1.06  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.08/1.06  
% 2.08/1.06  ------  iProver source info
% 2.08/1.06  
% 2.08/1.06  git: date: 2020-06-30 10:37:57 +0100
% 2.08/1.06  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.08/1.06  git: non_committed_changes: false
% 2.08/1.06  git: last_make_outside_of_git: false
% 2.08/1.06  
% 2.08/1.06  ------ 
% 2.08/1.06  
% 2.08/1.06  ------ Input Options
% 2.08/1.06  
% 2.08/1.06  --out_options                           all
% 2.08/1.06  --tptp_safe_out                         true
% 2.08/1.06  --problem_path                          ""
% 2.08/1.06  --include_path                          ""
% 2.08/1.06  --clausifier                            res/vclausify_rel
% 2.08/1.06  --clausifier_options                    --mode clausify
% 2.08/1.06  --stdin                                 false
% 2.08/1.06  --stats_out                             all
% 2.08/1.06  
% 2.08/1.06  ------ General Options
% 2.08/1.06  
% 2.08/1.06  --fof                                   false
% 2.08/1.06  --time_out_real                         305.
% 2.08/1.06  --time_out_virtual                      -1.
% 2.08/1.06  --symbol_type_check                     false
% 2.08/1.06  --clausify_out                          false
% 2.08/1.06  --sig_cnt_out                           false
% 2.08/1.06  --trig_cnt_out                          false
% 2.08/1.06  --trig_cnt_out_tolerance                1.
% 2.08/1.06  --trig_cnt_out_sk_spl                   false
% 2.08/1.06  --abstr_cl_out                          false
% 2.08/1.06  
% 2.08/1.06  ------ Global Options
% 2.08/1.06  
% 2.08/1.06  --schedule                              default
% 2.08/1.06  --add_important_lit                     false
% 2.08/1.06  --prop_solver_per_cl                    1000
% 2.08/1.06  --min_unsat_core                        false
% 2.08/1.06  --soft_assumptions                      false
% 2.08/1.06  --soft_lemma_size                       3
% 2.08/1.06  --prop_impl_unit_size                   0
% 2.08/1.06  --prop_impl_unit                        []
% 2.08/1.06  --share_sel_clauses                     true
% 2.08/1.06  --reset_solvers                         false
% 2.08/1.06  --bc_imp_inh                            [conj_cone]
% 2.08/1.06  --conj_cone_tolerance                   3.
% 2.08/1.06  --extra_neg_conj                        none
% 2.08/1.06  --large_theory_mode                     true
% 2.08/1.06  --prolific_symb_bound                   200
% 2.08/1.06  --lt_threshold                          2000
% 2.08/1.06  --clause_weak_htbl                      true
% 2.08/1.06  --gc_record_bc_elim                     false
% 2.08/1.06  
% 2.08/1.06  ------ Preprocessing Options
% 2.08/1.06  
% 2.08/1.06  --preprocessing_flag                    true
% 2.08/1.06  --time_out_prep_mult                    0.1
% 2.08/1.06  --splitting_mode                        input
% 2.08/1.06  --splitting_grd                         true
% 2.08/1.06  --splitting_cvd                         false
% 2.08/1.06  --splitting_cvd_svl                     false
% 2.08/1.06  --splitting_nvd                         32
% 2.08/1.06  --sub_typing                            true
% 2.08/1.06  --prep_gs_sim                           true
% 2.08/1.06  --prep_unflatten                        true
% 2.08/1.06  --prep_res_sim                          true
% 2.08/1.06  --prep_upred                            true
% 2.08/1.06  --prep_sem_filter                       exhaustive
% 2.08/1.06  --prep_sem_filter_out                   false
% 2.08/1.06  --pred_elim                             true
% 2.08/1.06  --res_sim_input                         true
% 2.08/1.06  --eq_ax_congr_red                       true
% 2.08/1.06  --pure_diseq_elim                       true
% 2.08/1.06  --brand_transform                       false
% 2.08/1.06  --non_eq_to_eq                          false
% 2.08/1.06  --prep_def_merge                        true
% 2.08/1.06  --prep_def_merge_prop_impl              false
% 2.08/1.06  --prep_def_merge_mbd                    true
% 2.08/1.06  --prep_def_merge_tr_red                 false
% 2.08/1.06  --prep_def_merge_tr_cl                  false
% 2.08/1.06  --smt_preprocessing                     true
% 2.08/1.06  --smt_ac_axioms                         fast
% 2.08/1.06  --preprocessed_out                      false
% 2.08/1.06  --preprocessed_stats                    false
% 2.08/1.06  
% 2.08/1.06  ------ Abstraction refinement Options
% 2.08/1.06  
% 2.08/1.06  --abstr_ref                             []
% 2.08/1.06  --abstr_ref_prep                        false
% 2.08/1.06  --abstr_ref_until_sat                   false
% 2.08/1.06  --abstr_ref_sig_restrict                funpre
% 2.08/1.06  --abstr_ref_af_restrict_to_split_sk     false
% 2.08/1.06  --abstr_ref_under                       []
% 2.08/1.06  
% 2.08/1.06  ------ SAT Options
% 2.08/1.06  
% 2.08/1.06  --sat_mode                              false
% 2.08/1.06  --sat_fm_restart_options                ""
% 2.08/1.06  --sat_gr_def                            false
% 2.08/1.06  --sat_epr_types                         true
% 2.08/1.06  --sat_non_cyclic_types                  false
% 2.08/1.06  --sat_finite_models                     false
% 2.08/1.06  --sat_fm_lemmas                         false
% 2.08/1.06  --sat_fm_prep                           false
% 2.08/1.06  --sat_fm_uc_incr                        true
% 2.08/1.06  --sat_out_model                         small
% 2.08/1.06  --sat_out_clauses                       false
% 2.08/1.06  
% 2.08/1.06  ------ QBF Options
% 2.08/1.06  
% 2.08/1.06  --qbf_mode                              false
% 2.08/1.06  --qbf_elim_univ                         false
% 2.08/1.06  --qbf_dom_inst                          none
% 2.08/1.06  --qbf_dom_pre_inst                      false
% 2.08/1.06  --qbf_sk_in                             false
% 2.08/1.06  --qbf_pred_elim                         true
% 2.08/1.06  --qbf_split                             512
% 2.08/1.06  
% 2.08/1.06  ------ BMC1 Options
% 2.08/1.06  
% 2.08/1.06  --bmc1_incremental                      false
% 2.08/1.06  --bmc1_axioms                           reachable_all
% 2.08/1.06  --bmc1_min_bound                        0
% 2.08/1.06  --bmc1_max_bound                        -1
% 2.08/1.06  --bmc1_max_bound_default                -1
% 2.08/1.06  --bmc1_symbol_reachability              true
% 2.08/1.06  --bmc1_property_lemmas                  false
% 2.08/1.06  --bmc1_k_induction                      false
% 2.08/1.06  --bmc1_non_equiv_states                 false
% 2.08/1.06  --bmc1_deadlock                         false
% 2.08/1.06  --bmc1_ucm                              false
% 2.08/1.06  --bmc1_add_unsat_core                   none
% 2.08/1.06  --bmc1_unsat_core_children              false
% 2.08/1.06  --bmc1_unsat_core_extrapolate_axioms    false
% 2.08/1.06  --bmc1_out_stat                         full
% 2.08/1.06  --bmc1_ground_init                      false
% 2.08/1.06  --bmc1_pre_inst_next_state              false
% 2.08/1.06  --bmc1_pre_inst_state                   false
% 2.08/1.06  --bmc1_pre_inst_reach_state             false
% 2.08/1.06  --bmc1_out_unsat_core                   false
% 2.08/1.06  --bmc1_aig_witness_out                  false
% 2.08/1.06  --bmc1_verbose                          false
% 2.08/1.06  --bmc1_dump_clauses_tptp                false
% 2.08/1.06  --bmc1_dump_unsat_core_tptp             false
% 2.08/1.06  --bmc1_dump_file                        -
% 2.08/1.06  --bmc1_ucm_expand_uc_limit              128
% 2.08/1.06  --bmc1_ucm_n_expand_iterations          6
% 2.08/1.06  --bmc1_ucm_extend_mode                  1
% 2.08/1.06  --bmc1_ucm_init_mode                    2
% 2.08/1.06  --bmc1_ucm_cone_mode                    none
% 2.08/1.06  --bmc1_ucm_reduced_relation_type        0
% 2.08/1.06  --bmc1_ucm_relax_model                  4
% 2.08/1.06  --bmc1_ucm_full_tr_after_sat            true
% 2.08/1.06  --bmc1_ucm_expand_neg_assumptions       false
% 2.08/1.06  --bmc1_ucm_layered_model                none
% 2.08/1.06  --bmc1_ucm_max_lemma_size               10
% 2.08/1.06  
% 2.08/1.06  ------ AIG Options
% 2.08/1.06  
% 2.08/1.06  --aig_mode                              false
% 2.08/1.06  
% 2.08/1.06  ------ Instantiation Options
% 2.08/1.06  
% 2.08/1.06  --instantiation_flag                    true
% 2.08/1.06  --inst_sos_flag                         false
% 2.08/1.06  --inst_sos_phase                        true
% 2.08/1.06  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.08/1.06  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.08/1.06  --inst_lit_sel_side                     num_symb
% 2.08/1.06  --inst_solver_per_active                1400
% 2.08/1.06  --inst_solver_calls_frac                1.
% 2.08/1.06  --inst_passive_queue_type               priority_queues
% 2.08/1.06  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.08/1.06  --inst_passive_queues_freq              [25;2]
% 2.08/1.06  --inst_dismatching                      true
% 2.08/1.06  --inst_eager_unprocessed_to_passive     true
% 2.08/1.06  --inst_prop_sim_given                   true
% 2.08/1.06  --inst_prop_sim_new                     false
% 2.08/1.06  --inst_subs_new                         false
% 2.08/1.06  --inst_eq_res_simp                      false
% 2.08/1.06  --inst_subs_given                       false
% 2.08/1.06  --inst_orphan_elimination               true
% 2.08/1.06  --inst_learning_loop_flag               true
% 2.08/1.06  --inst_learning_start                   3000
% 2.08/1.06  --inst_learning_factor                  2
% 2.08/1.06  --inst_start_prop_sim_after_learn       3
% 2.08/1.06  --inst_sel_renew                        solver
% 2.08/1.06  --inst_lit_activity_flag                true
% 2.08/1.06  --inst_restr_to_given                   false
% 2.08/1.06  --inst_activity_threshold               500
% 2.08/1.06  --inst_out_proof                        true
% 2.08/1.06  
% 2.08/1.06  ------ Resolution Options
% 2.08/1.06  
% 2.08/1.06  --resolution_flag                       true
% 2.08/1.06  --res_lit_sel                           adaptive
% 2.08/1.06  --res_lit_sel_side                      none
% 2.08/1.06  --res_ordering                          kbo
% 2.08/1.06  --res_to_prop_solver                    active
% 2.08/1.06  --res_prop_simpl_new                    false
% 2.08/1.06  --res_prop_simpl_given                  true
% 2.08/1.06  --res_passive_queue_type                priority_queues
% 2.08/1.06  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.08/1.06  --res_passive_queues_freq               [15;5]
% 2.08/1.06  --res_forward_subs                      full
% 2.08/1.06  --res_backward_subs                     full
% 2.08/1.06  --res_forward_subs_resolution           true
% 2.08/1.06  --res_backward_subs_resolution          true
% 2.08/1.06  --res_orphan_elimination                true
% 2.08/1.06  --res_time_limit                        2.
% 2.08/1.06  --res_out_proof                         true
% 2.08/1.06  
% 2.08/1.06  ------ Superposition Options
% 2.08/1.06  
% 2.08/1.06  --superposition_flag                    true
% 2.08/1.06  --sup_passive_queue_type                priority_queues
% 2.08/1.06  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.08/1.06  --sup_passive_queues_freq               [8;1;4]
% 2.08/1.06  --demod_completeness_check              fast
% 2.08/1.06  --demod_use_ground                      true
% 2.08/1.06  --sup_to_prop_solver                    passive
% 2.08/1.06  --sup_prop_simpl_new                    true
% 2.08/1.06  --sup_prop_simpl_given                  true
% 2.08/1.06  --sup_fun_splitting                     false
% 2.08/1.06  --sup_smt_interval                      50000
% 2.08/1.06  
% 2.08/1.06  ------ Superposition Simplification Setup
% 2.08/1.06  
% 2.08/1.06  --sup_indices_passive                   []
% 2.08/1.06  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.08/1.06  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.08/1.06  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.08/1.06  --sup_full_triv                         [TrivRules;PropSubs]
% 2.08/1.06  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.08/1.06  --sup_full_bw                           [BwDemod]
% 2.08/1.06  --sup_immed_triv                        [TrivRules]
% 2.08/1.06  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.08/1.06  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.08/1.06  --sup_immed_bw_main                     []
% 2.08/1.06  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.08/1.06  --sup_input_triv                        [Unflattening;TrivRules]
% 2.08/1.06  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.08/1.06  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.08/1.06  
% 2.08/1.06  ------ Combination Options
% 2.08/1.06  
% 2.08/1.06  --comb_res_mult                         3
% 2.08/1.06  --comb_sup_mult                         2
% 2.08/1.06  --comb_inst_mult                        10
% 2.08/1.06  
% 2.08/1.06  ------ Debug Options
% 2.08/1.06  
% 2.08/1.06  --dbg_backtrace                         false
% 2.08/1.06  --dbg_dump_prop_clauses                 false
% 2.08/1.06  --dbg_dump_prop_clauses_file            -
% 2.08/1.06  --dbg_out_stat                          false
% 2.08/1.06  ------ Parsing...
% 2.08/1.06  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.08/1.06  
% 2.08/1.06  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.08/1.06  
% 2.08/1.06  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.08/1.06  
% 2.08/1.06  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.08/1.06  ------ Proving...
% 2.08/1.06  ------ Problem Properties 
% 2.08/1.06  
% 2.08/1.06  
% 2.08/1.06  clauses                                 22
% 2.08/1.06  conjectures                             6
% 2.08/1.06  EPR                                     5
% 2.08/1.06  Horn                                    18
% 2.08/1.06  unary                                   6
% 2.08/1.06  binary                                  0
% 2.08/1.06  lits                                    78
% 2.08/1.06  lits eq                                 9
% 2.08/1.06  fd_pure                                 0
% 2.08/1.06  fd_pseudo                               0
% 2.08/1.06  fd_cond                                 2
% 2.08/1.06  fd_pseudo_cond                          0
% 2.08/1.06  AC symbols                              0
% 2.08/1.06  
% 2.08/1.06  ------ Schedule dynamic 5 is on 
% 2.08/1.06  
% 2.08/1.06  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.08/1.06  
% 2.08/1.06  
% 2.08/1.06  ------ 
% 2.08/1.06  Current options:
% 2.08/1.06  ------ 
% 2.08/1.06  
% 2.08/1.06  ------ Input Options
% 2.08/1.06  
% 2.08/1.06  --out_options                           all
% 2.08/1.06  --tptp_safe_out                         true
% 2.08/1.06  --problem_path                          ""
% 2.08/1.06  --include_path                          ""
% 2.08/1.06  --clausifier                            res/vclausify_rel
% 2.08/1.06  --clausifier_options                    --mode clausify
% 2.08/1.06  --stdin                                 false
% 2.08/1.06  --stats_out                             all
% 2.08/1.06  
% 2.08/1.06  ------ General Options
% 2.08/1.06  
% 2.08/1.06  --fof                                   false
% 2.08/1.06  --time_out_real                         305.
% 2.08/1.06  --time_out_virtual                      -1.
% 2.08/1.06  --symbol_type_check                     false
% 2.08/1.06  --clausify_out                          false
% 2.08/1.06  --sig_cnt_out                           false
% 2.08/1.06  --trig_cnt_out                          false
% 2.08/1.06  --trig_cnt_out_tolerance                1.
% 2.08/1.06  --trig_cnt_out_sk_spl                   false
% 2.08/1.06  --abstr_cl_out                          false
% 2.08/1.06  
% 2.08/1.06  ------ Global Options
% 2.08/1.06  
% 2.08/1.06  --schedule                              default
% 2.08/1.06  --add_important_lit                     false
% 2.08/1.06  --prop_solver_per_cl                    1000
% 2.08/1.06  --min_unsat_core                        false
% 2.08/1.06  --soft_assumptions                      false
% 2.08/1.06  --soft_lemma_size                       3
% 2.08/1.06  --prop_impl_unit_size                   0
% 2.08/1.06  --prop_impl_unit                        []
% 2.08/1.06  --share_sel_clauses                     true
% 2.08/1.06  --reset_solvers                         false
% 2.08/1.06  --bc_imp_inh                            [conj_cone]
% 2.08/1.06  --conj_cone_tolerance                   3.
% 2.08/1.06  --extra_neg_conj                        none
% 2.08/1.06  --large_theory_mode                     true
% 2.08/1.06  --prolific_symb_bound                   200
% 2.08/1.06  --lt_threshold                          2000
% 2.08/1.06  --clause_weak_htbl                      true
% 2.08/1.06  --gc_record_bc_elim                     false
% 2.08/1.06  
% 2.08/1.06  ------ Preprocessing Options
% 2.08/1.06  
% 2.08/1.06  --preprocessing_flag                    true
% 2.08/1.06  --time_out_prep_mult                    0.1
% 2.08/1.06  --splitting_mode                        input
% 2.08/1.06  --splitting_grd                         true
% 2.08/1.06  --splitting_cvd                         false
% 2.08/1.06  --splitting_cvd_svl                     false
% 2.08/1.06  --splitting_nvd                         32
% 2.08/1.06  --sub_typing                            true
% 2.08/1.06  --prep_gs_sim                           true
% 2.08/1.06  --prep_unflatten                        true
% 2.08/1.06  --prep_res_sim                          true
% 2.08/1.06  --prep_upred                            true
% 2.08/1.06  --prep_sem_filter                       exhaustive
% 2.08/1.06  --prep_sem_filter_out                   false
% 2.08/1.06  --pred_elim                             true
% 2.08/1.06  --res_sim_input                         true
% 2.08/1.06  --eq_ax_congr_red                       true
% 2.08/1.06  --pure_diseq_elim                       true
% 2.08/1.06  --brand_transform                       false
% 2.08/1.06  --non_eq_to_eq                          false
% 2.08/1.06  --prep_def_merge                        true
% 2.08/1.06  --prep_def_merge_prop_impl              false
% 2.08/1.06  --prep_def_merge_mbd                    true
% 2.08/1.06  --prep_def_merge_tr_red                 false
% 2.08/1.06  --prep_def_merge_tr_cl                  false
% 2.08/1.06  --smt_preprocessing                     true
% 2.08/1.06  --smt_ac_axioms                         fast
% 2.08/1.06  --preprocessed_out                      false
% 2.08/1.06  --preprocessed_stats                    false
% 2.08/1.06  
% 2.08/1.06  ------ Abstraction refinement Options
% 2.08/1.06  
% 2.08/1.06  --abstr_ref                             []
% 2.08/1.06  --abstr_ref_prep                        false
% 2.08/1.06  --abstr_ref_until_sat                   false
% 2.08/1.06  --abstr_ref_sig_restrict                funpre
% 2.08/1.06  --abstr_ref_af_restrict_to_split_sk     false
% 2.08/1.06  --abstr_ref_under                       []
% 2.08/1.06  
% 2.08/1.06  ------ SAT Options
% 2.08/1.06  
% 2.08/1.06  --sat_mode                              false
% 2.08/1.06  --sat_fm_restart_options                ""
% 2.08/1.06  --sat_gr_def                            false
% 2.08/1.06  --sat_epr_types                         true
% 2.08/1.06  --sat_non_cyclic_types                  false
% 2.08/1.06  --sat_finite_models                     false
% 2.08/1.06  --sat_fm_lemmas                         false
% 2.08/1.06  --sat_fm_prep                           false
% 2.08/1.06  --sat_fm_uc_incr                        true
% 2.08/1.06  --sat_out_model                         small
% 2.08/1.06  --sat_out_clauses                       false
% 2.08/1.06  
% 2.08/1.06  ------ QBF Options
% 2.08/1.06  
% 2.08/1.06  --qbf_mode                              false
% 2.08/1.06  --qbf_elim_univ                         false
% 2.08/1.06  --qbf_dom_inst                          none
% 2.08/1.06  --qbf_dom_pre_inst                      false
% 2.08/1.06  --qbf_sk_in                             false
% 2.08/1.06  --qbf_pred_elim                         true
% 2.08/1.06  --qbf_split                             512
% 2.08/1.06  
% 2.08/1.06  ------ BMC1 Options
% 2.08/1.06  
% 2.08/1.06  --bmc1_incremental                      false
% 2.08/1.06  --bmc1_axioms                           reachable_all
% 2.08/1.06  --bmc1_min_bound                        0
% 2.08/1.06  --bmc1_max_bound                        -1
% 2.08/1.06  --bmc1_max_bound_default                -1
% 2.08/1.06  --bmc1_symbol_reachability              true
% 2.08/1.06  --bmc1_property_lemmas                  false
% 2.08/1.06  --bmc1_k_induction                      false
% 2.08/1.06  --bmc1_non_equiv_states                 false
% 2.08/1.06  --bmc1_deadlock                         false
% 2.08/1.06  --bmc1_ucm                              false
% 2.08/1.06  --bmc1_add_unsat_core                   none
% 2.08/1.06  --bmc1_unsat_core_children              false
% 2.08/1.06  --bmc1_unsat_core_extrapolate_axioms    false
% 2.08/1.06  --bmc1_out_stat                         full
% 2.08/1.06  --bmc1_ground_init                      false
% 2.08/1.06  --bmc1_pre_inst_next_state              false
% 2.08/1.06  --bmc1_pre_inst_state                   false
% 2.08/1.06  --bmc1_pre_inst_reach_state             false
% 2.08/1.06  --bmc1_out_unsat_core                   false
% 2.08/1.06  --bmc1_aig_witness_out                  false
% 2.08/1.06  --bmc1_verbose                          false
% 2.08/1.06  --bmc1_dump_clauses_tptp                false
% 2.08/1.06  --bmc1_dump_unsat_core_tptp             false
% 2.08/1.06  --bmc1_dump_file                        -
% 2.08/1.06  --bmc1_ucm_expand_uc_limit              128
% 2.08/1.06  --bmc1_ucm_n_expand_iterations          6
% 2.08/1.06  --bmc1_ucm_extend_mode                  1
% 2.08/1.06  --bmc1_ucm_init_mode                    2
% 2.08/1.06  --bmc1_ucm_cone_mode                    none
% 2.08/1.06  --bmc1_ucm_reduced_relation_type        0
% 2.08/1.06  --bmc1_ucm_relax_model                  4
% 2.08/1.06  --bmc1_ucm_full_tr_after_sat            true
% 2.08/1.06  --bmc1_ucm_expand_neg_assumptions       false
% 2.08/1.06  --bmc1_ucm_layered_model                none
% 2.08/1.06  --bmc1_ucm_max_lemma_size               10
% 2.08/1.06  
% 2.08/1.06  ------ AIG Options
% 2.08/1.06  
% 2.08/1.06  --aig_mode                              false
% 2.08/1.06  
% 2.08/1.06  ------ Instantiation Options
% 2.08/1.06  
% 2.08/1.06  --instantiation_flag                    true
% 2.08/1.06  --inst_sos_flag                         false
% 2.08/1.06  --inst_sos_phase                        true
% 2.08/1.06  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.08/1.06  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.08/1.06  --inst_lit_sel_side                     none
% 2.08/1.06  --inst_solver_per_active                1400
% 2.08/1.06  --inst_solver_calls_frac                1.
% 2.08/1.06  --inst_passive_queue_type               priority_queues
% 2.08/1.06  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.08/1.06  --inst_passive_queues_freq              [25;2]
% 2.08/1.06  --inst_dismatching                      true
% 2.08/1.06  --inst_eager_unprocessed_to_passive     true
% 2.08/1.06  --inst_prop_sim_given                   true
% 2.08/1.06  --inst_prop_sim_new                     false
% 2.08/1.06  --inst_subs_new                         false
% 2.08/1.06  --inst_eq_res_simp                      false
% 2.08/1.06  --inst_subs_given                       false
% 2.08/1.06  --inst_orphan_elimination               true
% 2.08/1.06  --inst_learning_loop_flag               true
% 2.08/1.06  --inst_learning_start                   3000
% 2.08/1.06  --inst_learning_factor                  2
% 2.08/1.06  --inst_start_prop_sim_after_learn       3
% 2.08/1.06  --inst_sel_renew                        solver
% 2.08/1.06  --inst_lit_activity_flag                true
% 2.08/1.06  --inst_restr_to_given                   false
% 2.08/1.06  --inst_activity_threshold               500
% 2.08/1.06  --inst_out_proof                        true
% 2.08/1.06  
% 2.08/1.06  ------ Resolution Options
% 2.08/1.06  
% 2.08/1.06  --resolution_flag                       false
% 2.08/1.06  --res_lit_sel                           adaptive
% 2.08/1.06  --res_lit_sel_side                      none
% 2.08/1.06  --res_ordering                          kbo
% 2.08/1.06  --res_to_prop_solver                    active
% 2.08/1.06  --res_prop_simpl_new                    false
% 2.08/1.06  --res_prop_simpl_given                  true
% 2.08/1.06  --res_passive_queue_type                priority_queues
% 2.08/1.06  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.08/1.06  --res_passive_queues_freq               [15;5]
% 2.08/1.06  --res_forward_subs                      full
% 2.08/1.06  --res_backward_subs                     full
% 2.08/1.06  --res_forward_subs_resolution           true
% 2.08/1.06  --res_backward_subs_resolution          true
% 2.08/1.06  --res_orphan_elimination                true
% 2.08/1.06  --res_time_limit                        2.
% 2.08/1.06  --res_out_proof                         true
% 2.08/1.06  
% 2.08/1.06  ------ Superposition Options
% 2.08/1.06  
% 2.08/1.06  --superposition_flag                    true
% 2.08/1.06  --sup_passive_queue_type                priority_queues
% 2.08/1.06  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.08/1.06  --sup_passive_queues_freq               [8;1;4]
% 2.08/1.06  --demod_completeness_check              fast
% 2.08/1.06  --demod_use_ground                      true
% 2.08/1.06  --sup_to_prop_solver                    passive
% 2.08/1.06  --sup_prop_simpl_new                    true
% 2.08/1.06  --sup_prop_simpl_given                  true
% 2.08/1.06  --sup_fun_splitting                     false
% 2.08/1.06  --sup_smt_interval                      50000
% 2.08/1.06  
% 2.08/1.06  ------ Superposition Simplification Setup
% 2.08/1.06  
% 2.08/1.06  --sup_indices_passive                   []
% 2.08/1.06  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.08/1.06  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.08/1.06  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.08/1.06  --sup_full_triv                         [TrivRules;PropSubs]
% 2.08/1.06  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.08/1.06  --sup_full_bw                           [BwDemod]
% 2.08/1.06  --sup_immed_triv                        [TrivRules]
% 2.08/1.06  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.08/1.06  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.08/1.06  --sup_immed_bw_main                     []
% 2.08/1.06  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.08/1.06  --sup_input_triv                        [Unflattening;TrivRules]
% 2.08/1.06  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.08/1.06  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.08/1.06  
% 2.08/1.06  ------ Combination Options
% 2.08/1.06  
% 2.08/1.06  --comb_res_mult                         3
% 2.08/1.06  --comb_sup_mult                         2
% 2.08/1.06  --comb_inst_mult                        10
% 2.08/1.06  
% 2.08/1.06  ------ Debug Options
% 2.08/1.06  
% 2.08/1.06  --dbg_backtrace                         false
% 2.08/1.06  --dbg_dump_prop_clauses                 false
% 2.08/1.06  --dbg_dump_prop_clauses_file            -
% 2.08/1.06  --dbg_out_stat                          false
% 2.08/1.06  
% 2.08/1.06  
% 2.08/1.06  
% 2.08/1.06  
% 2.08/1.06  ------ Proving...
% 2.08/1.06  
% 2.08/1.06  
% 2.08/1.06  % SZS status Theorem for theBenchmark.p
% 2.08/1.06  
% 2.08/1.06  % SZS output start CNFRefutation for theBenchmark.p
% 2.08/1.06  
% 2.08/1.06  fof(f9,conjecture,(
% 2.08/1.06    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X2,X0) & r1_tarski(X2,X1) & v2_compts_1(X1,X0)) => v2_compts_1(X2,X0)))))),
% 2.08/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.08/1.06  
% 2.08/1.06  fof(f10,negated_conjecture,(
% 2.08/1.06    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X2,X0) & r1_tarski(X2,X1) & v2_compts_1(X1,X0)) => v2_compts_1(X2,X0)))))),
% 2.08/1.06    inference(negated_conjecture,[],[f9])).
% 2.08/1.06  
% 2.08/1.06  fof(f25,plain,(
% 2.08/1.06    ? [X0] : (? [X1] : (? [X2] : ((~v2_compts_1(X2,X0) & (v4_pre_topc(X2,X0) & r1_tarski(X2,X1) & v2_compts_1(X1,X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.08/1.06    inference(ennf_transformation,[],[f10])).
% 2.08/1.06  
% 2.08/1.06  fof(f26,plain,(
% 2.08/1.06    ? [X0] : (? [X1] : (? [X2] : (~v2_compts_1(X2,X0) & v4_pre_topc(X2,X0) & r1_tarski(X2,X1) & v2_compts_1(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.08/1.06    inference(flattening,[],[f25])).
% 2.08/1.06  
% 2.08/1.06  fof(f35,plain,(
% 2.08/1.06    ( ! [X0,X1] : (? [X2] : (~v2_compts_1(X2,X0) & v4_pre_topc(X2,X0) & r1_tarski(X2,X1) & v2_compts_1(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v2_compts_1(sK3,X0) & v4_pre_topc(sK3,X0) & r1_tarski(sK3,X1) & v2_compts_1(X1,X0) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.08/1.06    introduced(choice_axiom,[])).
% 2.08/1.06  
% 2.08/1.06  fof(f34,plain,(
% 2.08/1.06    ( ! [X0] : (? [X1] : (? [X2] : (~v2_compts_1(X2,X0) & v4_pre_topc(X2,X0) & r1_tarski(X2,X1) & v2_compts_1(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (~v2_compts_1(X2,X0) & v4_pre_topc(X2,X0) & r1_tarski(X2,sK2) & v2_compts_1(sK2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.08/1.06    introduced(choice_axiom,[])).
% 2.08/1.06  
% 2.08/1.06  fof(f33,plain,(
% 2.08/1.06    ? [X0] : (? [X1] : (? [X2] : (~v2_compts_1(X2,X0) & v4_pre_topc(X2,X0) & r1_tarski(X2,X1) & v2_compts_1(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (~v2_compts_1(X2,sK1) & v4_pre_topc(X2,sK1) & r1_tarski(X2,X1) & v2_compts_1(X1,sK1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & v2_pre_topc(sK1))),
% 2.08/1.06    introduced(choice_axiom,[])).
% 2.08/1.06  
% 2.08/1.06  fof(f36,plain,(
% 2.08/1.06    ((~v2_compts_1(sK3,sK1) & v4_pre_topc(sK3,sK1) & r1_tarski(sK3,sK2) & v2_compts_1(sK2,sK1) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & v2_pre_topc(sK1)),
% 2.08/1.06    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f26,f35,f34,f33])).
% 2.08/1.06  
% 2.08/1.06  fof(f55,plain,(
% 2.08/1.06    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))),
% 2.08/1.06    inference(cnf_transformation,[],[f36])).
% 2.08/1.06  
% 2.08/1.06  fof(f7,axiom,(
% 2.08/1.06    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_pre_topc(X0) => ((v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1))) | k1_xboole_0 = X1)) & (k1_xboole_0 = X1 => (v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1)))))))),
% 2.08/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.08/1.06  
% 2.08/1.06  fof(f21,plain,(
% 2.08/1.06    ! [X0] : (! [X1] : (((((v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1))) | k1_xboole_0 = X1) | ~v2_pre_topc(X0)) & ((v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1))) | k1_xboole_0 != X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.08/1.06    inference(ennf_transformation,[],[f7])).
% 2.08/1.06  
% 2.08/1.06  fof(f22,plain,(
% 2.08/1.06    ! [X0] : (! [X1] : ((((v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1))) | k1_xboole_0 = X1 | ~v2_pre_topc(X0)) & ((v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1))) | k1_xboole_0 != X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.08/1.06    inference(flattening,[],[f21])).
% 2.08/1.06  
% 2.08/1.06  fof(f32,plain,(
% 2.08/1.06    ! [X0] : (! [X1] : (((((v2_compts_1(X1,X0) | ~v1_compts_1(k1_pre_topc(X0,X1))) & (v1_compts_1(k1_pre_topc(X0,X1)) | ~v2_compts_1(X1,X0))) | k1_xboole_0 = X1 | ~v2_pre_topc(X0)) & (((v2_compts_1(X1,X0) | ~v1_compts_1(k1_pre_topc(X0,X1))) & (v1_compts_1(k1_pre_topc(X0,X1)) | ~v2_compts_1(X1,X0))) | k1_xboole_0 != X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.08/1.06    inference(nnf_transformation,[],[f22])).
% 2.08/1.06  
% 2.08/1.06  fof(f50,plain,(
% 2.08/1.06    ( ! [X0,X1] : (v1_compts_1(k1_pre_topc(X0,X1)) | ~v2_compts_1(X1,X0) | k1_xboole_0 = X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.08/1.06    inference(cnf_transformation,[],[f32])).
% 2.08/1.06  
% 2.08/1.06  fof(f53,plain,(
% 2.08/1.06    v2_pre_topc(sK1)),
% 2.08/1.06    inference(cnf_transformation,[],[f36])).
% 2.08/1.06  
% 2.08/1.06  fof(f54,plain,(
% 2.08/1.06    l1_pre_topc(sK1)),
% 2.08/1.06    inference(cnf_transformation,[],[f36])).
% 2.08/1.06  
% 2.08/1.06  fof(f57,plain,(
% 2.08/1.06    v2_compts_1(sK2,sK1)),
% 2.08/1.06    inference(cnf_transformation,[],[f36])).
% 2.08/1.06  
% 2.08/1.06  fof(f2,axiom,(
% 2.08/1.06    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => (m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))))),
% 2.08/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.08/1.06  
% 2.08/1.06  fof(f13,plain,(
% 2.08/1.06    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.08/1.06    inference(ennf_transformation,[],[f2])).
% 2.08/1.06  
% 2.08/1.06  fof(f14,plain,(
% 2.08/1.06    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.08/1.06    inference(flattening,[],[f13])).
% 2.08/1.06  
% 2.08/1.06  fof(f40,plain,(
% 2.08/1.06    ( ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.08/1.06    inference(cnf_transformation,[],[f14])).
% 2.08/1.06  
% 2.08/1.06  fof(f56,plain,(
% 2.08/1.06    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))),
% 2.08/1.06    inference(cnf_transformation,[],[f36])).
% 2.08/1.06  
% 2.08/1.06  fof(f4,axiom,(
% 2.08/1.06    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))))),
% 2.08/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.08/1.06  
% 2.08/1.06  fof(f16,plain,(
% 2.08/1.06    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.08/1.06    inference(ennf_transformation,[],[f4])).
% 2.08/1.06  
% 2.08/1.06  fof(f42,plain,(
% 2.08/1.06    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.08/1.06    inference(cnf_transformation,[],[f16])).
% 2.08/1.06  
% 2.08/1.06  fof(f5,axiom,(
% 2.08/1.06    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v4_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v4_pre_topc(X3,X2)))))))),
% 2.08/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.08/1.06  
% 2.08/1.06  fof(f17,plain,(
% 2.08/1.06    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((v4_pre_topc(X3,X2) | X1 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v4_pre_topc(X1,X0)) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.08/1.06    inference(ennf_transformation,[],[f5])).
% 2.08/1.06  
% 2.08/1.06  fof(f18,plain,(
% 2.08/1.06    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (v4_pre_topc(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v4_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.08/1.06    inference(flattening,[],[f17])).
% 2.08/1.06  
% 2.08/1.06  fof(f43,plain,(
% 2.08/1.06    ( ! [X2,X0,X3,X1] : (v4_pre_topc(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~v4_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.08/1.06    inference(cnf_transformation,[],[f18])).
% 2.08/1.06  
% 2.08/1.06  fof(f63,plain,(
% 2.08/1.06    ( ! [X2,X0,X3] : (v4_pre_topc(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~v4_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.08/1.06    inference(equality_resolution,[],[f43])).
% 2.08/1.06  
% 2.08/1.06  fof(f3,axiom,(
% 2.08/1.06    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.08/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.08/1.06  
% 2.08/1.06  fof(f15,plain,(
% 2.08/1.06    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.08/1.06    inference(ennf_transformation,[],[f3])).
% 2.08/1.06  
% 2.08/1.06  fof(f41,plain,(
% 2.08/1.06    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.08/1.06    inference(cnf_transformation,[],[f15])).
% 2.08/1.06  
% 2.08/1.06  fof(f59,plain,(
% 2.08/1.06    v4_pre_topc(sK3,sK1)),
% 2.08/1.06    inference(cnf_transformation,[],[f36])).
% 2.08/1.06  
% 2.08/1.06  fof(f60,plain,(
% 2.08/1.06    ~v2_compts_1(sK3,sK1)),
% 2.08/1.06    inference(cnf_transformation,[],[f36])).
% 2.08/1.06  
% 2.08/1.06  fof(f1,axiom,(
% 2.08/1.06    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_pre_topc(X2)) => (k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1))))),
% 2.08/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.08/1.06  
% 2.08/1.06  fof(f11,plain,(
% 2.08/1.06    ! [X0] : (! [X1] : (! [X2] : ((k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1) | (~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.08/1.06    inference(ennf_transformation,[],[f1])).
% 2.08/1.06  
% 2.08/1.06  fof(f12,plain,(
% 2.08/1.06    ! [X0] : (! [X1] : (! [X2] : ((k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.08/1.06    inference(flattening,[],[f11])).
% 2.08/1.06  
% 2.08/1.06  fof(f27,plain,(
% 2.08/1.06    ! [X0] : (! [X1] : (! [X2] : (((k1_pre_topc(X0,X1) = X2 | k2_struct_0(X2) != X1) & (k2_struct_0(X2) = X1 | k1_pre_topc(X0,X1) != X2)) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.08/1.06    inference(nnf_transformation,[],[f12])).
% 2.08/1.06  
% 2.08/1.06  fof(f37,plain,(
% 2.08/1.06    ( ! [X2,X0,X1] : (k2_struct_0(X2) = X1 | k1_pre_topc(X0,X1) != X2 | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.08/1.06    inference(cnf_transformation,[],[f27])).
% 2.08/1.06  
% 2.08/1.06  fof(f62,plain,(
% 2.08/1.06    ( ! [X0,X1] : (k2_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~v1_pre_topc(k1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.08/1.06    inference(equality_resolution,[],[f37])).
% 2.08/1.06  
% 2.08/1.06  fof(f39,plain,(
% 2.08/1.06    ( ! [X0,X1] : (v1_pre_topc(k1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.08/1.06    inference(cnf_transformation,[],[f14])).
% 2.08/1.06  
% 2.08/1.06  fof(f6,axiom,(
% 2.08/1.06    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X2,k2_struct_0(X1)) => (v2_compts_1(X2,X0) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (X2 = X3 => v2_compts_1(X3,X1))))))))),
% 2.08/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.08/1.06  
% 2.08/1.06  fof(f19,plain,(
% 2.08/1.06    ! [X0] : (! [X1] : (! [X2] : (((v2_compts_1(X2,X0) <=> ! [X3] : ((v2_compts_1(X3,X1) | X2 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | ~r1_tarski(X2,k2_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.08/1.06    inference(ennf_transformation,[],[f6])).
% 2.08/1.06  
% 2.08/1.06  fof(f20,plain,(
% 2.08/1.06    ! [X0] : (! [X1] : (! [X2] : ((v2_compts_1(X2,X0) <=> ! [X3] : (v2_compts_1(X3,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.08/1.06    inference(flattening,[],[f19])).
% 2.08/1.06  
% 2.08/1.06  fof(f28,plain,(
% 2.08/1.06    ! [X0] : (! [X1] : (! [X2] : (((v2_compts_1(X2,X0) | ? [X3] : (~v2_compts_1(X3,X1) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (v2_compts_1(X3,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v2_compts_1(X2,X0))) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.08/1.06    inference(nnf_transformation,[],[f20])).
% 2.08/1.06  
% 2.08/1.06  fof(f29,plain,(
% 2.08/1.06    ! [X0] : (! [X1] : (! [X2] : (((v2_compts_1(X2,X0) | ? [X3] : (~v2_compts_1(X3,X1) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v2_compts_1(X4,X1) | X2 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v2_compts_1(X2,X0))) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.08/1.06    inference(rectify,[],[f28])).
% 2.08/1.06  
% 2.08/1.06  fof(f30,plain,(
% 2.08/1.06    ! [X2,X1] : (? [X3] : (~v2_compts_1(X3,X1) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) => (~v2_compts_1(sK0(X1,X2),X1) & sK0(X1,X2) = X2 & m1_subset_1(sK0(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))))),
% 2.08/1.06    introduced(choice_axiom,[])).
% 2.08/1.06  
% 2.08/1.06  fof(f31,plain,(
% 2.08/1.06    ! [X0] : (! [X1] : (! [X2] : (((v2_compts_1(X2,X0) | (~v2_compts_1(sK0(X1,X2),X1) & sK0(X1,X2) = X2 & m1_subset_1(sK0(X1,X2),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v2_compts_1(X4,X1) | X2 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v2_compts_1(X2,X0))) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.08/1.06    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).
% 2.08/1.06  
% 2.08/1.06  fof(f46,plain,(
% 2.08/1.06    ( ! [X2,X0,X1] : (v2_compts_1(X2,X0) | sK0(X1,X2) = X2 | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.08/1.06    inference(cnf_transformation,[],[f31])).
% 2.08/1.06  
% 2.08/1.06  fof(f58,plain,(
% 2.08/1.06    r1_tarski(sK3,sK2)),
% 2.08/1.06    inference(cnf_transformation,[],[f36])).
% 2.08/1.06  
% 2.08/1.06  fof(f45,plain,(
% 2.08/1.06    ( ! [X2,X0,X1] : (v2_compts_1(X2,X0) | m1_subset_1(sK0(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.08/1.06    inference(cnf_transformation,[],[f31])).
% 2.08/1.06  
% 2.08/1.06  fof(f8,axiom,(
% 2.08/1.06    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X1,X0) & v1_compts_1(X0)) => v2_compts_1(X1,X0))))),
% 2.08/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.08/1.06  
% 2.08/1.06  fof(f23,plain,(
% 2.08/1.06    ! [X0] : (! [X1] : ((v2_compts_1(X1,X0) | (~v4_pre_topc(X1,X0) | ~v1_compts_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.08/1.06    inference(ennf_transformation,[],[f8])).
% 2.08/1.06  
% 2.08/1.06  fof(f24,plain,(
% 2.08/1.06    ! [X0] : (! [X1] : (v2_compts_1(X1,X0) | ~v4_pre_topc(X1,X0) | ~v1_compts_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.08/1.06    inference(flattening,[],[f23])).
% 2.08/1.06  
% 2.08/1.06  fof(f52,plain,(
% 2.08/1.06    ( ! [X0,X1] : (v2_compts_1(X1,X0) | ~v4_pre_topc(X1,X0) | ~v1_compts_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.08/1.06    inference(cnf_transformation,[],[f24])).
% 2.08/1.06  
% 2.08/1.06  fof(f47,plain,(
% 2.08/1.06    ( ! [X2,X0,X1] : (v2_compts_1(X2,X0) | ~v2_compts_1(sK0(X1,X2),X1) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.08/1.06    inference(cnf_transformation,[],[f31])).
% 2.08/1.06  
% 2.08/1.06  fof(f48,plain,(
% 2.08/1.06    ( ! [X0,X1] : (v1_compts_1(k1_pre_topc(X0,X1)) | ~v2_compts_1(X1,X0) | k1_xboole_0 != X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.08/1.06    inference(cnf_transformation,[],[f32])).
% 2.08/1.06  
% 2.08/1.06  fof(f66,plain,(
% 2.08/1.06    ( ! [X0] : (v1_compts_1(k1_pre_topc(X0,k1_xboole_0)) | ~v2_compts_1(k1_xboole_0,X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.08/1.06    inference(equality_resolution,[],[f48])).
% 2.08/1.06  
% 2.08/1.06  cnf(c_21,negated_conjecture,
% 2.08/1.06      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.08/1.06      inference(cnf_transformation,[],[f55]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_1333,negated_conjecture,
% 2.08/1.06      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.08/1.06      inference(subtyping,[status(esa)],[c_21]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_1815,plain,
% 2.08/1.06      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.08/1.06      inference(predicate_to_equality,[status(thm)],[c_1333]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_12,plain,
% 2.08/1.06      ( ~ v2_compts_1(X0,X1)
% 2.08/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.08/1.06      | ~ v2_pre_topc(X1)
% 2.08/1.06      | v1_compts_1(k1_pre_topc(X1,X0))
% 2.08/1.06      | ~ l1_pre_topc(X1)
% 2.08/1.06      | k1_xboole_0 = X0 ),
% 2.08/1.06      inference(cnf_transformation,[],[f50]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_23,negated_conjecture,
% 2.08/1.06      ( v2_pre_topc(sK1) ),
% 2.08/1.06      inference(cnf_transformation,[],[f53]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_292,plain,
% 2.08/1.06      ( ~ v2_compts_1(X0,X1)
% 2.08/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.08/1.06      | v1_compts_1(k1_pre_topc(X1,X0))
% 2.08/1.06      | ~ l1_pre_topc(X1)
% 2.08/1.06      | sK1 != X1
% 2.08/1.06      | k1_xboole_0 = X0 ),
% 2.08/1.06      inference(resolution_lifted,[status(thm)],[c_12,c_23]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_293,plain,
% 2.08/1.06      ( ~ v2_compts_1(X0,sK1)
% 2.08/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.08/1.06      | v1_compts_1(k1_pre_topc(sK1,X0))
% 2.08/1.06      | ~ l1_pre_topc(sK1)
% 2.08/1.06      | k1_xboole_0 = X0 ),
% 2.08/1.06      inference(unflattening,[status(thm)],[c_292]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_22,negated_conjecture,
% 2.08/1.06      ( l1_pre_topc(sK1) ),
% 2.08/1.06      inference(cnf_transformation,[],[f54]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_297,plain,
% 2.08/1.06      ( v1_compts_1(k1_pre_topc(sK1,X0))
% 2.08/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.08/1.06      | ~ v2_compts_1(X0,sK1)
% 2.08/1.06      | k1_xboole_0 = X0 ),
% 2.08/1.06      inference(global_propositional_subsumption,
% 2.08/1.06                [status(thm)],
% 2.08/1.06                [c_293,c_22]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_298,plain,
% 2.08/1.06      ( ~ v2_compts_1(X0,sK1)
% 2.08/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.08/1.06      | v1_compts_1(k1_pre_topc(sK1,X0))
% 2.08/1.06      | k1_xboole_0 = X0 ),
% 2.08/1.06      inference(renaming,[status(thm)],[c_297]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_1330,plain,
% 2.08/1.06      ( ~ v2_compts_1(X0_46,sK1)
% 2.08/1.06      | ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.08/1.06      | v1_compts_1(k1_pre_topc(sK1,X0_46))
% 2.08/1.06      | k1_xboole_0 = X0_46 ),
% 2.08/1.06      inference(subtyping,[status(esa)],[c_298]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_1818,plain,
% 2.08/1.06      ( k1_xboole_0 = X0_46
% 2.08/1.06      | v2_compts_1(X0_46,sK1) != iProver_top
% 2.08/1.06      | m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.08/1.06      | v1_compts_1(k1_pre_topc(sK1,X0_46)) = iProver_top ),
% 2.08/1.06      inference(predicate_to_equality,[status(thm)],[c_1330]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_2474,plain,
% 2.08/1.06      ( sK2 = k1_xboole_0
% 2.08/1.06      | v2_compts_1(sK2,sK1) != iProver_top
% 2.08/1.06      | v1_compts_1(k1_pre_topc(sK1,sK2)) = iProver_top ),
% 2.08/1.06      inference(superposition,[status(thm)],[c_1815,c_1818]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_19,negated_conjecture,
% 2.08/1.06      ( v2_compts_1(sK2,sK1) ),
% 2.08/1.06      inference(cnf_transformation,[],[f57]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_28,plain,
% 2.08/1.06      ( v2_compts_1(sK2,sK1) = iProver_top ),
% 2.08/1.06      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_2539,plain,
% 2.08/1.06      ( sK2 = k1_xboole_0
% 2.08/1.06      | v1_compts_1(k1_pre_topc(sK1,sK2)) = iProver_top ),
% 2.08/1.06      inference(global_propositional_subsumption,
% 2.08/1.06                [status(thm)],
% 2.08/1.06                [c_2474,c_28]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_2,plain,
% 2.08/1.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.08/1.06      | m1_pre_topc(k1_pre_topc(X1,X0),X1)
% 2.08/1.06      | ~ l1_pre_topc(X1) ),
% 2.08/1.06      inference(cnf_transformation,[],[f40]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_1345,plain,
% 2.08/1.06      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(X0_47)))
% 2.08/1.06      | m1_pre_topc(k1_pre_topc(X0_47,X0_46),X0_47)
% 2.08/1.06      | ~ l1_pre_topc(X0_47) ),
% 2.08/1.06      inference(subtyping,[status(esa)],[c_2]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_1803,plain,
% 2.08/1.06      ( m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(X0_47))) != iProver_top
% 2.08/1.06      | m1_pre_topc(k1_pre_topc(X0_47,X0_46),X0_47) = iProver_top
% 2.08/1.06      | l1_pre_topc(X0_47) != iProver_top ),
% 2.08/1.06      inference(predicate_to_equality,[status(thm)],[c_1345]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_2287,plain,
% 2.08/1.06      ( m1_pre_topc(k1_pre_topc(sK1,sK2),sK1) = iProver_top
% 2.08/1.06      | l1_pre_topc(sK1) != iProver_top ),
% 2.08/1.06      inference(superposition,[status(thm)],[c_1815,c_1803]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_25,plain,
% 2.08/1.06      ( l1_pre_topc(sK1) = iProver_top ),
% 2.08/1.06      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_26,plain,
% 2.08/1.06      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.08/1.06      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_2054,plain,
% 2.08/1.06      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.08/1.06      | m1_pre_topc(k1_pre_topc(sK1,sK2),sK1)
% 2.08/1.06      | ~ l1_pre_topc(sK1) ),
% 2.08/1.06      inference(instantiation,[status(thm)],[c_1345]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_2055,plain,
% 2.08/1.06      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.08/1.06      | m1_pre_topc(k1_pre_topc(sK1,sK2),sK1) = iProver_top
% 2.08/1.06      | l1_pre_topc(sK1) != iProver_top ),
% 2.08/1.06      inference(predicate_to_equality,[status(thm)],[c_2054]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_2461,plain,
% 2.08/1.06      ( m1_pre_topc(k1_pre_topc(sK1,sK2),sK1) = iProver_top ),
% 2.08/1.06      inference(global_propositional_subsumption,
% 2.08/1.06                [status(thm)],
% 2.08/1.06                [c_2287,c_25,c_26,c_2055]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_20,negated_conjecture,
% 2.08/1.06      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.08/1.06      inference(cnf_transformation,[],[f56]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_1334,negated_conjecture,
% 2.08/1.06      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.08/1.06      inference(subtyping,[status(esa)],[c_20]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_1814,plain,
% 2.08/1.06      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.08/1.06      inference(predicate_to_equality,[status(thm)],[c_1334]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_5,plain,
% 2.08/1.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.08/1.06      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
% 2.08/1.06      | ~ m1_pre_topc(X1,X2)
% 2.08/1.06      | ~ l1_pre_topc(X2) ),
% 2.08/1.06      inference(cnf_transformation,[],[f42]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_1342,plain,
% 2.08/1.06      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(X0_47)))
% 2.08/1.06      | m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(X1_47)))
% 2.08/1.06      | ~ m1_pre_topc(X0_47,X1_47)
% 2.08/1.06      | ~ l1_pre_topc(X1_47) ),
% 2.08/1.06      inference(subtyping,[status(esa)],[c_5]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_1806,plain,
% 2.08/1.06      ( m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(X0_47))) != iProver_top
% 2.08/1.06      | m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(X1_47))) = iProver_top
% 2.08/1.06      | m1_pre_topc(X0_47,X1_47) != iProver_top
% 2.08/1.06      | l1_pre_topc(X1_47) != iProver_top ),
% 2.08/1.06      inference(predicate_to_equality,[status(thm)],[c_1342]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_2632,plain,
% 2.08/1.06      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0_47))) = iProver_top
% 2.08/1.06      | m1_pre_topc(sK1,X0_47) != iProver_top
% 2.08/1.06      | l1_pre_topc(X0_47) != iProver_top ),
% 2.08/1.06      inference(superposition,[status(thm)],[c_1814,c_1806]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_6,plain,
% 2.08/1.06      ( ~ v4_pre_topc(X0,X1)
% 2.08/1.06      | v4_pre_topc(X0,X2)
% 2.08/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
% 2.08/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.08/1.06      | ~ m1_pre_topc(X2,X1)
% 2.08/1.06      | ~ l1_pre_topc(X1) ),
% 2.08/1.06      inference(cnf_transformation,[],[f63]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_1341,plain,
% 2.08/1.06      ( ~ v4_pre_topc(X0_46,X0_47)
% 2.08/1.06      | v4_pre_topc(X0_46,X1_47)
% 2.08/1.06      | ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(X1_47)))
% 2.08/1.06      | ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(X0_47)))
% 2.08/1.06      | ~ m1_pre_topc(X1_47,X0_47)
% 2.08/1.06      | ~ l1_pre_topc(X0_47) ),
% 2.08/1.06      inference(subtyping,[status(esa)],[c_6]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_1807,plain,
% 2.08/1.06      ( v4_pre_topc(X0_46,X0_47) != iProver_top
% 2.08/1.06      | v4_pre_topc(X0_46,X1_47) = iProver_top
% 2.08/1.06      | m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(X1_47))) != iProver_top
% 2.08/1.06      | m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(X0_47))) != iProver_top
% 2.08/1.06      | m1_pre_topc(X1_47,X0_47) != iProver_top
% 2.08/1.06      | l1_pre_topc(X0_47) != iProver_top ),
% 2.08/1.06      inference(predicate_to_equality,[status(thm)],[c_1341]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_1962,plain,
% 2.08/1.06      ( v4_pre_topc(X0_46,X0_47) != iProver_top
% 2.08/1.06      | v4_pre_topc(X0_46,X1_47) = iProver_top
% 2.08/1.06      | m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(X1_47))) != iProver_top
% 2.08/1.06      | m1_pre_topc(X1_47,X0_47) != iProver_top
% 2.08/1.06      | l1_pre_topc(X0_47) != iProver_top ),
% 2.08/1.06      inference(forward_subsumption_resolution,
% 2.08/1.06                [status(thm)],
% 2.08/1.06                [c_1807,c_1806]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_4055,plain,
% 2.08/1.06      ( v4_pre_topc(sK3,X0_47) != iProver_top
% 2.08/1.06      | v4_pre_topc(sK3,X1_47) = iProver_top
% 2.08/1.06      | m1_pre_topc(X1_47,X0_47) != iProver_top
% 2.08/1.06      | m1_pre_topc(sK1,X1_47) != iProver_top
% 2.08/1.06      | l1_pre_topc(X0_47) != iProver_top
% 2.08/1.06      | l1_pre_topc(X1_47) != iProver_top ),
% 2.08/1.06      inference(superposition,[status(thm)],[c_2632,c_1962]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_4,plain,
% 2.08/1.06      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 2.08/1.06      inference(cnf_transformation,[],[f41]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_1343,plain,
% 2.08/1.06      ( ~ m1_pre_topc(X0_47,X1_47)
% 2.08/1.06      | ~ l1_pre_topc(X1_47)
% 2.08/1.06      | l1_pre_topc(X0_47) ),
% 2.08/1.06      inference(subtyping,[status(esa)],[c_4]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_1805,plain,
% 2.08/1.06      ( m1_pre_topc(X0_47,X1_47) != iProver_top
% 2.08/1.06      | l1_pre_topc(X1_47) != iProver_top
% 2.08/1.06      | l1_pre_topc(X0_47) = iProver_top ),
% 2.08/1.06      inference(predicate_to_equality,[status(thm)],[c_1343]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_4162,plain,
% 2.08/1.06      ( v4_pre_topc(sK3,X0_47) != iProver_top
% 2.08/1.06      | v4_pre_topc(sK3,X1_47) = iProver_top
% 2.08/1.06      | m1_pre_topc(X1_47,X0_47) != iProver_top
% 2.08/1.06      | m1_pre_topc(sK1,X1_47) != iProver_top
% 2.08/1.06      | l1_pre_topc(X0_47) != iProver_top ),
% 2.08/1.06      inference(forward_subsumption_resolution,
% 2.08/1.06                [status(thm)],
% 2.08/1.06                [c_4055,c_1805]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_4165,plain,
% 2.08/1.06      ( v4_pre_topc(sK3,k1_pre_topc(sK1,sK2)) = iProver_top
% 2.08/1.06      | v4_pre_topc(sK3,sK1) != iProver_top
% 2.08/1.06      | m1_pre_topc(sK1,k1_pre_topc(sK1,sK2)) != iProver_top
% 2.08/1.06      | l1_pre_topc(sK1) != iProver_top ),
% 2.08/1.06      inference(superposition,[status(thm)],[c_2461,c_4162]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_27,plain,
% 2.08/1.06      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.08/1.06      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_17,negated_conjecture,
% 2.08/1.06      ( v4_pre_topc(sK3,sK1) ),
% 2.08/1.06      inference(cnf_transformation,[],[f59]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_30,plain,
% 2.08/1.06      ( v4_pre_topc(sK3,sK1) = iProver_top ),
% 2.08/1.06      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_16,negated_conjecture,
% 2.08/1.06      ( ~ v2_compts_1(sK3,sK1) ),
% 2.08/1.06      inference(cnf_transformation,[],[f60]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_31,plain,
% 2.08/1.06      ( v2_compts_1(sK3,sK1) != iProver_top ),
% 2.08/1.06      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_1,plain,
% 2.08/1.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.08/1.06      | ~ m1_pre_topc(k1_pre_topc(X1,X0),X1)
% 2.08/1.06      | ~ l1_pre_topc(X1)
% 2.08/1.06      | ~ v1_pre_topc(k1_pre_topc(X1,X0))
% 2.08/1.06      | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
% 2.08/1.06      inference(cnf_transformation,[],[f62]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_3,plain,
% 2.08/1.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.08/1.06      | ~ l1_pre_topc(X1)
% 2.08/1.06      | v1_pre_topc(k1_pre_topc(X1,X0)) ),
% 2.08/1.06      inference(cnf_transformation,[],[f39]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_143,plain,
% 2.08/1.06      ( ~ l1_pre_topc(X1)
% 2.08/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.08/1.06      | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
% 2.08/1.06      inference(global_propositional_subsumption,
% 2.08/1.06                [status(thm)],
% 2.08/1.06                [c_1,c_3,c_2]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_144,plain,
% 2.08/1.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.08/1.06      | ~ l1_pre_topc(X1)
% 2.08/1.06      | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
% 2.08/1.06      inference(renaming,[status(thm)],[c_143]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_1331,plain,
% 2.08/1.06      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(X0_47)))
% 2.08/1.06      | ~ l1_pre_topc(X0_47)
% 2.08/1.06      | k2_struct_0(k1_pre_topc(X0_47,X0_46)) = X0_46 ),
% 2.08/1.06      inference(subtyping,[status(esa)],[c_144]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_2044,plain,
% 2.08/1.06      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.08/1.06      | ~ l1_pre_topc(sK1)
% 2.08/1.06      | k2_struct_0(k1_pre_topc(sK1,sK2)) = sK2 ),
% 2.08/1.06      inference(instantiation,[status(thm)],[c_1331]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_8,plain,
% 2.08/1.06      ( ~ r1_tarski(X0,k2_struct_0(X1))
% 2.08/1.06      | v2_compts_1(X0,X2)
% 2.08/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
% 2.08/1.06      | ~ m1_pre_topc(X1,X2)
% 2.08/1.06      | ~ l1_pre_topc(X2)
% 2.08/1.06      | sK0(X1,X0) = X0 ),
% 2.08/1.06      inference(cnf_transformation,[],[f46]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_18,negated_conjecture,
% 2.08/1.06      ( r1_tarski(sK3,sK2) ),
% 2.08/1.06      inference(cnf_transformation,[],[f58]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_396,plain,
% 2.08/1.06      ( v2_compts_1(X0,X1)
% 2.08/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.08/1.06      | ~ m1_pre_topc(X2,X1)
% 2.08/1.06      | ~ l1_pre_topc(X1)
% 2.08/1.06      | sK0(X2,X0) = X0
% 2.08/1.06      | k2_struct_0(X2) != sK2
% 2.08/1.06      | sK3 != X0 ),
% 2.08/1.06      inference(resolution_lifted,[status(thm)],[c_8,c_18]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_397,plain,
% 2.08/1.06      ( v2_compts_1(sK3,X0)
% 2.08/1.06      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0)))
% 2.08/1.06      | ~ m1_pre_topc(X1,X0)
% 2.08/1.06      | ~ l1_pre_topc(X0)
% 2.08/1.06      | sK0(X1,sK3) = sK3
% 2.08/1.06      | k2_struct_0(X1) != sK2 ),
% 2.08/1.06      inference(unflattening,[status(thm)],[c_396]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_1326,plain,
% 2.08/1.06      ( v2_compts_1(sK3,X0_47)
% 2.08/1.06      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0_47)))
% 2.08/1.06      | ~ m1_pre_topc(X1_47,X0_47)
% 2.08/1.06      | ~ l1_pre_topc(X0_47)
% 2.08/1.06      | sK0(X1_47,sK3) = sK3
% 2.08/1.06      | k2_struct_0(X1_47) != sK2 ),
% 2.08/1.06      inference(subtyping,[status(esa)],[c_397]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_2127,plain,
% 2.08/1.06      ( v2_compts_1(sK3,X0_47)
% 2.08/1.06      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0_47)))
% 2.08/1.06      | ~ m1_pre_topc(k1_pre_topc(sK1,sK2),X0_47)
% 2.08/1.06      | ~ l1_pre_topc(X0_47)
% 2.08/1.06      | sK0(k1_pre_topc(sK1,sK2),sK3) = sK3
% 2.08/1.06      | k2_struct_0(k1_pre_topc(sK1,sK2)) != sK2 ),
% 2.08/1.06      inference(instantiation,[status(thm)],[c_1326]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_2129,plain,
% 2.08/1.06      ( v2_compts_1(sK3,sK1)
% 2.08/1.06      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.08/1.06      | ~ m1_pre_topc(k1_pre_topc(sK1,sK2),sK1)
% 2.08/1.06      | ~ l1_pre_topc(sK1)
% 2.08/1.06      | sK0(k1_pre_topc(sK1,sK2),sK3) = sK3
% 2.08/1.06      | k2_struct_0(k1_pre_topc(sK1,sK2)) != sK2 ),
% 2.08/1.06      inference(instantiation,[status(thm)],[c_2127]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_9,plain,
% 2.08/1.06      ( ~ r1_tarski(X0,k2_struct_0(X1))
% 2.08/1.06      | v2_compts_1(X0,X2)
% 2.08/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
% 2.08/1.06      | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.08/1.06      | ~ m1_pre_topc(X1,X2)
% 2.08/1.06      | ~ l1_pre_topc(X2) ),
% 2.08/1.06      inference(cnf_transformation,[],[f45]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_372,plain,
% 2.08/1.06      ( v2_compts_1(X0,X1)
% 2.08/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.08/1.06      | m1_subset_1(sK0(X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
% 2.08/1.06      | ~ m1_pre_topc(X2,X1)
% 2.08/1.06      | ~ l1_pre_topc(X1)
% 2.08/1.06      | k2_struct_0(X2) != sK2
% 2.08/1.06      | sK3 != X0 ),
% 2.08/1.06      inference(resolution_lifted,[status(thm)],[c_9,c_18]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_373,plain,
% 2.08/1.06      ( v2_compts_1(sK3,X0)
% 2.08/1.06      | m1_subset_1(sK0(X1,sK3),k1_zfmisc_1(u1_struct_0(X1)))
% 2.08/1.06      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0)))
% 2.08/1.06      | ~ m1_pre_topc(X1,X0)
% 2.08/1.06      | ~ l1_pre_topc(X0)
% 2.08/1.06      | k2_struct_0(X1) != sK2 ),
% 2.08/1.06      inference(unflattening,[status(thm)],[c_372]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_1327,plain,
% 2.08/1.06      ( v2_compts_1(sK3,X0_47)
% 2.08/1.06      | m1_subset_1(sK0(X1_47,sK3),k1_zfmisc_1(u1_struct_0(X1_47)))
% 2.08/1.06      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0_47)))
% 2.08/1.06      | ~ m1_pre_topc(X1_47,X0_47)
% 2.08/1.06      | ~ l1_pre_topc(X0_47)
% 2.08/1.06      | k2_struct_0(X1_47) != sK2 ),
% 2.08/1.06      inference(subtyping,[status(esa)],[c_373]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_2126,plain,
% 2.08/1.06      ( v2_compts_1(sK3,X0_47)
% 2.08/1.06      | m1_subset_1(sK0(k1_pre_topc(sK1,sK2),sK3),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK1,sK2))))
% 2.08/1.06      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0_47)))
% 2.08/1.06      | ~ m1_pre_topc(k1_pre_topc(sK1,sK2),X0_47)
% 2.08/1.06      | ~ l1_pre_topc(X0_47)
% 2.08/1.06      | k2_struct_0(k1_pre_topc(sK1,sK2)) != sK2 ),
% 2.08/1.06      inference(instantiation,[status(thm)],[c_1327]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_2132,plain,
% 2.08/1.06      ( k2_struct_0(k1_pre_topc(sK1,sK2)) != sK2
% 2.08/1.06      | v2_compts_1(sK3,X0_47) = iProver_top
% 2.08/1.06      | m1_subset_1(sK0(k1_pre_topc(sK1,sK2),sK3),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK1,sK2)))) = iProver_top
% 2.08/1.06      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0_47))) != iProver_top
% 2.08/1.06      | m1_pre_topc(k1_pre_topc(sK1,sK2),X0_47) != iProver_top
% 2.08/1.06      | l1_pre_topc(X0_47) != iProver_top ),
% 2.08/1.06      inference(predicate_to_equality,[status(thm)],[c_2126]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_2134,plain,
% 2.08/1.06      ( k2_struct_0(k1_pre_topc(sK1,sK2)) != sK2
% 2.08/1.06      | v2_compts_1(sK3,sK1) = iProver_top
% 2.08/1.06      | m1_subset_1(sK0(k1_pre_topc(sK1,sK2),sK3),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK1,sK2)))) = iProver_top
% 2.08/1.06      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.08/1.06      | m1_pre_topc(k1_pre_topc(sK1,sK2),sK1) != iProver_top
% 2.08/1.06      | l1_pre_topc(sK1) != iProver_top ),
% 2.08/1.06      inference(instantiation,[status(thm)],[c_2132]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_1348,plain,( X0_46 = X0_46 ),theory(equality) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_2170,plain,
% 2.08/1.06      ( sK3 = sK3 ),
% 2.08/1.06      inference(instantiation,[status(thm)],[c_1348]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_1350,plain,( X0_48 = X0_48 ),theory(equality) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_2698,plain,
% 2.08/1.06      ( k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK1,sK2))) = k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK1,sK2))) ),
% 2.08/1.06      inference(instantiation,[status(thm)],[c_1350]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_1352,plain,
% 2.08/1.06      ( X0_46 != X1_46 | X2_46 != X1_46 | X2_46 = X0_46 ),
% 2.08/1.06      theory(equality) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_2426,plain,
% 2.08/1.06      ( X0_46 != X1_46 | sK3 != X1_46 | sK3 = X0_46 ),
% 2.08/1.06      inference(instantiation,[status(thm)],[c_1352]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_2618,plain,
% 2.08/1.06      ( X0_46 != sK3 | sK3 = X0_46 | sK3 != sK3 ),
% 2.08/1.06      inference(instantiation,[status(thm)],[c_2426]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_3015,plain,
% 2.08/1.06      ( sK0(k1_pre_topc(sK1,sK2),sK3) != sK3
% 2.08/1.06      | sK3 = sK0(k1_pre_topc(sK1,sK2),sK3)
% 2.08/1.06      | sK3 != sK3 ),
% 2.08/1.06      inference(instantiation,[status(thm)],[c_2618]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_2077,plain,
% 2.08/1.06      ( v4_pre_topc(sK3,X0_47)
% 2.08/1.06      | ~ v4_pre_topc(sK3,sK1)
% 2.08/1.06      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0_47)))
% 2.08/1.06      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.08/1.06      | ~ m1_pre_topc(X0_47,sK1)
% 2.08/1.06      | ~ l1_pre_topc(sK1) ),
% 2.08/1.06      inference(instantiation,[status(thm)],[c_1341]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_3090,plain,
% 2.08/1.06      ( v4_pre_topc(sK3,k1_pre_topc(sK1,sK2))
% 2.08/1.06      | ~ v4_pre_topc(sK3,sK1)
% 2.08/1.06      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK1,sK2))))
% 2.08/1.06      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.08/1.06      | ~ m1_pre_topc(k1_pre_topc(sK1,sK2),sK1)
% 2.08/1.06      | ~ l1_pre_topc(sK1) ),
% 2.08/1.06      inference(instantiation,[status(thm)],[c_2077]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_3093,plain,
% 2.08/1.06      ( v4_pre_topc(sK3,k1_pre_topc(sK1,sK2)) = iProver_top
% 2.08/1.06      | v4_pre_topc(sK3,sK1) != iProver_top
% 2.08/1.06      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK1,sK2)))) != iProver_top
% 2.08/1.06      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.08/1.06      | m1_pre_topc(k1_pre_topc(sK1,sK2),sK1) != iProver_top
% 2.08/1.06      | l1_pre_topc(sK1) != iProver_top ),
% 2.08/1.06      inference(predicate_to_equality,[status(thm)],[c_3090]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_1360,plain,
% 2.08/1.06      ( ~ m1_subset_1(X0_46,X0_48)
% 2.08/1.06      | m1_subset_1(X1_46,X1_48)
% 2.08/1.06      | X1_48 != X0_48
% 2.08/1.06      | X1_46 != X0_46 ),
% 2.08/1.06      theory(equality) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_2380,plain,
% 2.08/1.06      ( m1_subset_1(X0_46,X0_48)
% 2.08/1.06      | ~ m1_subset_1(sK0(k1_pre_topc(sK1,sK2),sK3),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK1,sK2))))
% 2.08/1.06      | X0_48 != k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK1,sK2)))
% 2.08/1.06      | X0_46 != sK0(k1_pre_topc(sK1,sK2),sK3) ),
% 2.08/1.06      inference(instantiation,[status(thm)],[c_1360]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_2697,plain,
% 2.08/1.06      ( m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK1,sK2))))
% 2.08/1.06      | ~ m1_subset_1(sK0(k1_pre_topc(sK1,sK2),sK3),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK1,sK2))))
% 2.08/1.06      | k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK1,sK2))) != k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK1,sK2)))
% 2.08/1.06      | X0_46 != sK0(k1_pre_topc(sK1,sK2),sK3) ),
% 2.08/1.06      inference(instantiation,[status(thm)],[c_2380]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_3609,plain,
% 2.08/1.06      ( ~ m1_subset_1(sK0(k1_pre_topc(sK1,sK2),sK3),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK1,sK2))))
% 2.08/1.06      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK1,sK2))))
% 2.08/1.06      | k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK1,sK2))) != k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK1,sK2)))
% 2.08/1.06      | sK3 != sK0(k1_pre_topc(sK1,sK2),sK3) ),
% 2.08/1.06      inference(instantiation,[status(thm)],[c_2697]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_3613,plain,
% 2.08/1.06      ( k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK1,sK2))) != k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK1,sK2)))
% 2.08/1.06      | sK3 != sK0(k1_pre_topc(sK1,sK2),sK3)
% 2.08/1.06      | m1_subset_1(sK0(k1_pre_topc(sK1,sK2),sK3),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK1,sK2)))) != iProver_top
% 2.08/1.06      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK1,sK2)))) = iProver_top ),
% 2.08/1.06      inference(predicate_to_equality,[status(thm)],[c_3609]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_4314,plain,
% 2.08/1.06      ( v4_pre_topc(sK3,k1_pre_topc(sK1,sK2)) = iProver_top ),
% 2.08/1.06      inference(global_propositional_subsumption,
% 2.08/1.06                [status(thm)],
% 2.08/1.06                [c_4165,c_22,c_25,c_21,c_26,c_20,c_27,c_30,c_16,c_31,
% 2.08/1.06                 c_2044,c_2054,c_2055,c_2129,c_2134,c_2170,c_2698,c_3015,
% 2.08/1.06                 c_3093,c_3613]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_15,plain,
% 2.08/1.06      ( v2_compts_1(X0,X1)
% 2.08/1.06      | ~ v4_pre_topc(X0,X1)
% 2.08/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.08/1.06      | ~ v1_compts_1(X1)
% 2.08/1.06      | ~ l1_pre_topc(X1) ),
% 2.08/1.06      inference(cnf_transformation,[],[f52]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_1338,plain,
% 2.08/1.06      ( v2_compts_1(X0_46,X0_47)
% 2.08/1.06      | ~ v4_pre_topc(X0_46,X0_47)
% 2.08/1.06      | ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(X0_47)))
% 2.08/1.06      | ~ v1_compts_1(X0_47)
% 2.08/1.06      | ~ l1_pre_topc(X0_47) ),
% 2.08/1.06      inference(subtyping,[status(esa)],[c_15]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_1810,plain,
% 2.08/1.06      ( v2_compts_1(X0_46,X0_47) = iProver_top
% 2.08/1.06      | v4_pre_topc(X0_46,X0_47) != iProver_top
% 2.08/1.06      | m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(X0_47))) != iProver_top
% 2.08/1.06      | v1_compts_1(X0_47) != iProver_top
% 2.08/1.06      | l1_pre_topc(X0_47) != iProver_top ),
% 2.08/1.06      inference(predicate_to_equality,[status(thm)],[c_1338]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_2892,plain,
% 2.08/1.06      ( v2_compts_1(sK3,X0_47) = iProver_top
% 2.08/1.06      | v4_pre_topc(sK3,X0_47) != iProver_top
% 2.08/1.06      | m1_pre_topc(sK1,X0_47) != iProver_top
% 2.08/1.06      | v1_compts_1(X0_47) != iProver_top
% 2.08/1.06      | l1_pre_topc(X0_47) != iProver_top ),
% 2.08/1.06      inference(superposition,[status(thm)],[c_2632,c_1810]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_4319,plain,
% 2.08/1.06      ( v2_compts_1(sK3,k1_pre_topc(sK1,sK2)) = iProver_top
% 2.08/1.06      | m1_pre_topc(sK1,k1_pre_topc(sK1,sK2)) != iProver_top
% 2.08/1.06      | v1_compts_1(k1_pre_topc(sK1,sK2)) != iProver_top
% 2.08/1.06      | l1_pre_topc(k1_pre_topc(sK1,sK2)) != iProver_top ),
% 2.08/1.06      inference(superposition,[status(thm)],[c_4314,c_2892]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_2466,plain,
% 2.08/1.06      ( l1_pre_topc(k1_pre_topc(sK1,sK2)) = iProver_top
% 2.08/1.06      | l1_pre_topc(sK1) != iProver_top ),
% 2.08/1.06      inference(superposition,[status(thm)],[c_2461,c_1805]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_2507,plain,
% 2.08/1.06      ( v2_compts_1(X0_46,k1_pre_topc(sK1,sK2))
% 2.08/1.06      | ~ v4_pre_topc(X0_46,k1_pre_topc(sK1,sK2))
% 2.08/1.06      | ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK1,sK2))))
% 2.08/1.06      | ~ v1_compts_1(k1_pre_topc(sK1,sK2))
% 2.08/1.06      | ~ l1_pre_topc(k1_pre_topc(sK1,sK2)) ),
% 2.08/1.06      inference(instantiation,[status(thm)],[c_1338]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_3088,plain,
% 2.08/1.06      ( v2_compts_1(sK3,k1_pre_topc(sK1,sK2))
% 2.08/1.06      | ~ v4_pre_topc(sK3,k1_pre_topc(sK1,sK2))
% 2.08/1.06      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK1,sK2))))
% 2.08/1.06      | ~ v1_compts_1(k1_pre_topc(sK1,sK2))
% 2.08/1.06      | ~ l1_pre_topc(k1_pre_topc(sK1,sK2)) ),
% 2.08/1.06      inference(instantiation,[status(thm)],[c_2507]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_3091,plain,
% 2.08/1.06      ( v2_compts_1(sK3,k1_pre_topc(sK1,sK2)) = iProver_top
% 2.08/1.06      | v4_pre_topc(sK3,k1_pre_topc(sK1,sK2)) != iProver_top
% 2.08/1.06      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK1,sK2)))) != iProver_top
% 2.08/1.06      | v1_compts_1(k1_pre_topc(sK1,sK2)) != iProver_top
% 2.08/1.06      | l1_pre_topc(k1_pre_topc(sK1,sK2)) != iProver_top ),
% 2.08/1.06      inference(predicate_to_equality,[status(thm)],[c_3088]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_4651,plain,
% 2.08/1.06      ( v1_compts_1(k1_pre_topc(sK1,sK2)) != iProver_top
% 2.08/1.06      | v2_compts_1(sK3,k1_pre_topc(sK1,sK2)) = iProver_top ),
% 2.08/1.06      inference(global_propositional_subsumption,
% 2.08/1.06                [status(thm)],
% 2.08/1.06                [c_4319,c_22,c_25,c_21,c_26,c_20,c_27,c_30,c_16,c_31,
% 2.08/1.06                 c_2044,c_2054,c_2055,c_2129,c_2134,c_2170,c_2466,c_2698,
% 2.08/1.06                 c_3015,c_3091,c_3093,c_3613]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_4652,plain,
% 2.08/1.06      ( v2_compts_1(sK3,k1_pre_topc(sK1,sK2)) = iProver_top
% 2.08/1.06      | v1_compts_1(k1_pre_topc(sK1,sK2)) != iProver_top ),
% 2.08/1.06      inference(renaming,[status(thm)],[c_4651]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_1817,plain,
% 2.08/1.06      ( k2_struct_0(k1_pre_topc(X0_47,X0_46)) = X0_46
% 2.08/1.06      | m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(X0_47))) != iProver_top
% 2.08/1.06      | l1_pre_topc(X0_47) != iProver_top ),
% 2.08/1.06      inference(predicate_to_equality,[status(thm)],[c_1331]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_3355,plain,
% 2.08/1.06      ( k2_struct_0(k1_pre_topc(sK1,sK2)) = sK2
% 2.08/1.06      | l1_pre_topc(sK1) != iProver_top ),
% 2.08/1.06      inference(superposition,[status(thm)],[c_1815,c_1817]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_3488,plain,
% 2.08/1.06      ( k2_struct_0(k1_pre_topc(sK1,sK2)) = sK2 ),
% 2.08/1.06      inference(global_propositional_subsumption,
% 2.08/1.06                [status(thm)],
% 2.08/1.06                [c_3355,c_22,c_21,c_2044]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_1822,plain,
% 2.08/1.06      ( sK0(X0_47,sK3) = sK3
% 2.08/1.06      | k2_struct_0(X0_47) != sK2
% 2.08/1.06      | v2_compts_1(sK3,X1_47) = iProver_top
% 2.08/1.06      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X1_47))) != iProver_top
% 2.08/1.06      | m1_pre_topc(X0_47,X1_47) != iProver_top
% 2.08/1.06      | l1_pre_topc(X1_47) != iProver_top ),
% 2.08/1.06      inference(predicate_to_equality,[status(thm)],[c_1326]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_3492,plain,
% 2.08/1.06      ( sK0(k1_pre_topc(sK1,sK2),sK3) = sK3
% 2.08/1.06      | v2_compts_1(sK3,X0_47) = iProver_top
% 2.08/1.06      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0_47))) != iProver_top
% 2.08/1.06      | m1_pre_topc(k1_pre_topc(sK1,sK2),X0_47) != iProver_top
% 2.08/1.06      | l1_pre_topc(X0_47) != iProver_top ),
% 2.08/1.06      inference(superposition,[status(thm)],[c_3488,c_1822]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_5054,plain,
% 2.08/1.06      ( sK0(k1_pre_topc(sK1,sK2),sK3) = sK3 ),
% 2.08/1.06      inference(global_propositional_subsumption,
% 2.08/1.06                [status(thm)],
% 2.08/1.06                [c_3492,c_22,c_21,c_20,c_16,c_2044,c_2054,c_2129]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_7,plain,
% 2.08/1.06      ( ~ r1_tarski(X0,k2_struct_0(X1))
% 2.08/1.06      | v2_compts_1(X0,X2)
% 2.08/1.06      | ~ v2_compts_1(sK0(X1,X0),X1)
% 2.08/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
% 2.08/1.06      | ~ m1_pre_topc(X1,X2)
% 2.08/1.06      | ~ l1_pre_topc(X2) ),
% 2.08/1.06      inference(cnf_transformation,[],[f47]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_420,plain,
% 2.08/1.06      ( v2_compts_1(X0,X1)
% 2.08/1.06      | ~ v2_compts_1(sK0(X2,X0),X2)
% 2.08/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.08/1.06      | ~ m1_pre_topc(X2,X1)
% 2.08/1.06      | ~ l1_pre_topc(X1)
% 2.08/1.06      | k2_struct_0(X2) != sK2
% 2.08/1.06      | sK3 != X0 ),
% 2.08/1.06      inference(resolution_lifted,[status(thm)],[c_7,c_18]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_421,plain,
% 2.08/1.06      ( ~ v2_compts_1(sK0(X0,sK3),X0)
% 2.08/1.06      | v2_compts_1(sK3,X1)
% 2.08/1.06      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X1)))
% 2.08/1.06      | ~ m1_pre_topc(X0,X1)
% 2.08/1.06      | ~ l1_pre_topc(X1)
% 2.08/1.06      | k2_struct_0(X0) != sK2 ),
% 2.08/1.06      inference(unflattening,[status(thm)],[c_420]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_1325,plain,
% 2.08/1.06      ( ~ v2_compts_1(sK0(X0_47,sK3),X0_47)
% 2.08/1.06      | v2_compts_1(sK3,X1_47)
% 2.08/1.06      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X1_47)))
% 2.08/1.06      | ~ m1_pre_topc(X0_47,X1_47)
% 2.08/1.06      | ~ l1_pre_topc(X1_47)
% 2.08/1.06      | k2_struct_0(X0_47) != sK2 ),
% 2.08/1.06      inference(subtyping,[status(esa)],[c_421]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_1823,plain,
% 2.08/1.06      ( k2_struct_0(X0_47) != sK2
% 2.08/1.06      | v2_compts_1(sK0(X0_47,sK3),X0_47) != iProver_top
% 2.08/1.06      | v2_compts_1(sK3,X1_47) = iProver_top
% 2.08/1.06      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X1_47))) != iProver_top
% 2.08/1.06      | m1_pre_topc(X0_47,X1_47) != iProver_top
% 2.08/1.06      | l1_pre_topc(X1_47) != iProver_top ),
% 2.08/1.06      inference(predicate_to_equality,[status(thm)],[c_1325]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_3493,plain,
% 2.08/1.06      ( v2_compts_1(sK0(k1_pre_topc(sK1,sK2),sK3),k1_pre_topc(sK1,sK2)) != iProver_top
% 2.08/1.06      | v2_compts_1(sK3,X0_47) = iProver_top
% 2.08/1.06      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0_47))) != iProver_top
% 2.08/1.06      | m1_pre_topc(k1_pre_topc(sK1,sK2),X0_47) != iProver_top
% 2.08/1.06      | l1_pre_topc(X0_47) != iProver_top ),
% 2.08/1.06      inference(superposition,[status(thm)],[c_3488,c_1823]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_2121,plain,
% 2.08/1.06      ( ~ v2_compts_1(sK0(k1_pre_topc(sK1,sK2),sK3),k1_pre_topc(sK1,sK2))
% 2.08/1.06      | v2_compts_1(sK3,X0_47)
% 2.08/1.06      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0_47)))
% 2.08/1.06      | ~ m1_pre_topc(k1_pre_topc(sK1,sK2),X0_47)
% 2.08/1.06      | ~ l1_pre_topc(X0_47)
% 2.08/1.06      | k2_struct_0(k1_pre_topc(sK1,sK2)) != sK2 ),
% 2.08/1.06      inference(instantiation,[status(thm)],[c_1325]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_2122,plain,
% 2.08/1.06      ( k2_struct_0(k1_pre_topc(sK1,sK2)) != sK2
% 2.08/1.06      | v2_compts_1(sK0(k1_pre_topc(sK1,sK2),sK3),k1_pre_topc(sK1,sK2)) != iProver_top
% 2.08/1.06      | v2_compts_1(sK3,X0_47) = iProver_top
% 2.08/1.06      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0_47))) != iProver_top
% 2.08/1.06      | m1_pre_topc(k1_pre_topc(sK1,sK2),X0_47) != iProver_top
% 2.08/1.06      | l1_pre_topc(X0_47) != iProver_top ),
% 2.08/1.06      inference(predicate_to_equality,[status(thm)],[c_2121]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_2124,plain,
% 2.08/1.06      ( k2_struct_0(k1_pre_topc(sK1,sK2)) != sK2
% 2.08/1.06      | v2_compts_1(sK0(k1_pre_topc(sK1,sK2),sK3),k1_pre_topc(sK1,sK2)) != iProver_top
% 2.08/1.06      | v2_compts_1(sK3,sK1) = iProver_top
% 2.08/1.06      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.08/1.06      | m1_pre_topc(k1_pre_topc(sK1,sK2),sK1) != iProver_top
% 2.08/1.06      | l1_pre_topc(sK1) != iProver_top ),
% 2.08/1.06      inference(instantiation,[status(thm)],[c_2122]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_5048,plain,
% 2.08/1.06      ( v2_compts_1(sK0(k1_pre_topc(sK1,sK2),sK3),k1_pre_topc(sK1,sK2)) != iProver_top ),
% 2.08/1.06      inference(global_propositional_subsumption,
% 2.08/1.06                [status(thm)],
% 2.08/1.06                [c_3493,c_22,c_25,c_21,c_26,c_27,c_31,c_2044,c_2055,
% 2.08/1.06                 c_2124]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_5057,plain,
% 2.08/1.06      ( v2_compts_1(sK3,k1_pre_topc(sK1,sK2)) != iProver_top ),
% 2.08/1.06      inference(demodulation,[status(thm)],[c_5054,c_5048]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_5233,plain,
% 2.08/1.06      ( v1_compts_1(k1_pre_topc(sK1,sK2)) != iProver_top ),
% 2.08/1.06      inference(superposition,[status(thm)],[c_4652,c_5057]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_5834,plain,
% 2.08/1.06      ( sK2 = k1_xboole_0 ),
% 2.08/1.06      inference(superposition,[status(thm)],[c_2539,c_5233]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_5843,plain,
% 2.08/1.06      ( v2_compts_1(sK3,k1_pre_topc(sK1,k1_xboole_0)) != iProver_top ),
% 2.08/1.06      inference(demodulation,[status(thm)],[c_5834,c_5057]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_5849,plain,
% 2.08/1.06      ( v2_compts_1(sK3,k1_pre_topc(sK1,k1_xboole_0)) = iProver_top
% 2.08/1.06      | v1_compts_1(k1_pre_topc(sK1,k1_xboole_0)) != iProver_top ),
% 2.08/1.06      inference(demodulation,[status(thm)],[c_5834,c_4652]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_6071,plain,
% 2.08/1.06      ( v1_compts_1(k1_pre_topc(sK1,k1_xboole_0)) != iProver_top ),
% 2.08/1.06      inference(backward_subsumption_resolution,
% 2.08/1.06                [status(thm)],
% 2.08/1.06                [c_5843,c_5849]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_1362,plain,
% 2.08/1.06      ( ~ v4_pre_topc(X0_46,X0_47)
% 2.08/1.06      | v4_pre_topc(X1_46,X1_47)
% 2.08/1.06      | X1_47 != X0_47
% 2.08/1.06      | X1_46 != X0_46 ),
% 2.08/1.06      theory(equality) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_2157,plain,
% 2.08/1.06      ( v4_pre_topc(X0_46,X0_47)
% 2.08/1.06      | ~ v4_pre_topc(sK3,X1_47)
% 2.08/1.06      | X0_47 != X1_47
% 2.08/1.06      | X0_46 != sK3 ),
% 2.08/1.06      inference(instantiation,[status(thm)],[c_1362]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_2444,plain,
% 2.08/1.06      ( v4_pre_topc(sK0(k1_pre_topc(sK1,sK2),sK3),X0_47)
% 2.08/1.06      | ~ v4_pre_topc(sK3,X1_47)
% 2.08/1.06      | X0_47 != X1_47
% 2.08/1.06      | sK0(k1_pre_topc(sK1,sK2),sK3) != sK3 ),
% 2.08/1.06      inference(instantiation,[status(thm)],[c_2157]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_3109,plain,
% 2.08/1.06      ( v4_pre_topc(sK0(k1_pre_topc(sK1,sK2),sK3),k1_pre_topc(sK1,sK2))
% 2.08/1.06      | ~ v4_pre_topc(sK3,X0_47)
% 2.08/1.06      | k1_pre_topc(sK1,sK2) != X0_47
% 2.08/1.06      | sK0(k1_pre_topc(sK1,sK2),sK3) != sK3 ),
% 2.08/1.06      inference(instantiation,[status(thm)],[c_2444]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_4744,plain,
% 2.08/1.06      ( v4_pre_topc(sK0(k1_pre_topc(sK1,sK2),sK3),k1_pre_topc(sK1,sK2))
% 2.08/1.06      | ~ v4_pre_topc(sK3,k1_pre_topc(sK1,sK2))
% 2.08/1.06      | k1_pre_topc(sK1,sK2) != k1_pre_topc(sK1,sK2)
% 2.08/1.06      | sK0(k1_pre_topc(sK1,sK2),sK3) != sK3 ),
% 2.08/1.06      inference(instantiation,[status(thm)],[c_3109]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_3108,plain,
% 2.08/1.06      ( v2_compts_1(sK0(k1_pre_topc(sK1,sK2),sK3),k1_pre_topc(sK1,sK2))
% 2.08/1.06      | ~ v4_pre_topc(sK0(k1_pre_topc(sK1,sK2),sK3),k1_pre_topc(sK1,sK2))
% 2.08/1.06      | ~ m1_subset_1(sK0(k1_pre_topc(sK1,sK2),sK3),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK1,sK2))))
% 2.08/1.06      | ~ v1_compts_1(k1_pre_topc(sK1,sK2))
% 2.08/1.06      | ~ l1_pre_topc(k1_pre_topc(sK1,sK2)) ),
% 2.08/1.06      inference(instantiation,[status(thm)],[c_2507]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_1355,plain,
% 2.08/1.06      ( X0_47 != X1_47
% 2.08/1.06      | k1_pre_topc(X0_47,X0_46) = k1_pre_topc(X1_47,X1_46)
% 2.08/1.06      | X0_46 != X1_46 ),
% 2.08/1.06      theory(equality) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_2312,plain,
% 2.08/1.06      ( X0_47 != sK1
% 2.08/1.06      | k1_pre_topc(X0_47,X0_46) = k1_pre_topc(sK1,sK2)
% 2.08/1.06      | X0_46 != sK2 ),
% 2.08/1.06      inference(instantiation,[status(thm)],[c_1355]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_2695,plain,
% 2.08/1.06      ( X0_47 != sK1
% 2.08/1.06      | k1_pre_topc(X0_47,sK2) = k1_pre_topc(sK1,sK2)
% 2.08/1.06      | sK2 != sK2 ),
% 2.08/1.06      inference(instantiation,[status(thm)],[c_2312]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_2696,plain,
% 2.08/1.06      ( k1_pre_topc(sK1,sK2) = k1_pre_topc(sK1,sK2)
% 2.08/1.06      | sK1 != sK1
% 2.08/1.06      | sK2 != sK2 ),
% 2.08/1.06      inference(instantiation,[status(thm)],[c_2695]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_2467,plain,
% 2.08/1.06      ( l1_pre_topc(k1_pre_topc(sK1,sK2)) | ~ l1_pre_topc(sK1) ),
% 2.08/1.06      inference(predicate_to_equality_rev,[status(thm)],[c_2466]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_2248,plain,
% 2.08/1.06      ( k1_zfmisc_1(u1_struct_0(sK1)) = k1_zfmisc_1(u1_struct_0(sK1)) ),
% 2.08/1.06      inference(instantiation,[status(thm)],[c_1350]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_2062,plain,
% 2.08/1.06      ( m1_subset_1(X0_46,X0_48)
% 2.08/1.06      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.08/1.06      | X0_48 != k1_zfmisc_1(u1_struct_0(sK1))
% 2.08/1.06      | X0_46 != sK2 ),
% 2.08/1.06      inference(instantiation,[status(thm)],[c_1360]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_2247,plain,
% 2.08/1.06      ( m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.08/1.06      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.08/1.06      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
% 2.08/1.06      | X0_46 != sK2 ),
% 2.08/1.06      inference(instantiation,[status(thm)],[c_2062]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_2249,plain,
% 2.08/1.06      ( k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
% 2.08/1.06      | X0_46 != sK2
% 2.08/1.06      | m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 2.08/1.06      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.08/1.06      inference(predicate_to_equality,[status(thm)],[c_2247]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_2251,plain,
% 2.08/1.06      ( k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
% 2.08/1.06      | k1_xboole_0 != sK2
% 2.08/1.06      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.08/1.06      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.08/1.06      inference(instantiation,[status(thm)],[c_2249]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_2190,plain,
% 2.08/1.06      ( sK2 = sK2 ),
% 2.08/1.06      inference(instantiation,[status(thm)],[c_1348]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_2183,plain,
% 2.08/1.06      ( ~ v2_compts_1(sK2,sK1)
% 2.08/1.06      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.08/1.06      | v1_compts_1(k1_pre_topc(sK1,sK2))
% 2.08/1.06      | k1_xboole_0 = sK2 ),
% 2.08/1.06      inference(instantiation,[status(thm)],[c_1330]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_2133,plain,
% 2.08/1.06      ( v2_compts_1(sK3,sK1)
% 2.08/1.06      | m1_subset_1(sK0(k1_pre_topc(sK1,sK2),sK3),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK1,sK2))))
% 2.08/1.06      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.08/1.06      | ~ m1_pre_topc(k1_pre_topc(sK1,sK2),sK1)
% 2.08/1.06      | ~ l1_pre_topc(sK1)
% 2.08/1.06      | k2_struct_0(k1_pre_topc(sK1,sK2)) != sK2 ),
% 2.08/1.06      inference(instantiation,[status(thm)],[c_2126]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_2123,plain,
% 2.08/1.06      ( ~ v2_compts_1(sK0(k1_pre_topc(sK1,sK2),sK3),k1_pre_topc(sK1,sK2))
% 2.08/1.06      | v2_compts_1(sK3,sK1)
% 2.08/1.06      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.08/1.06      | ~ m1_pre_topc(k1_pre_topc(sK1,sK2),sK1)
% 2.08/1.06      | ~ l1_pre_topc(sK1)
% 2.08/1.06      | k2_struct_0(k1_pre_topc(sK1,sK2)) != sK2 ),
% 2.08/1.06      inference(instantiation,[status(thm)],[c_2121]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_1363,plain,
% 2.08/1.06      ( ~ v2_compts_1(X0_46,X0_47)
% 2.08/1.06      | v2_compts_1(X1_46,X1_47)
% 2.08/1.06      | X1_47 != X0_47
% 2.08/1.06      | X1_46 != X0_46 ),
% 2.08/1.06      theory(equality) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_2072,plain,
% 2.08/1.06      ( v2_compts_1(X0_46,X0_47)
% 2.08/1.06      | ~ v2_compts_1(sK2,sK1)
% 2.08/1.06      | X0_47 != sK1
% 2.08/1.06      | X0_46 != sK2 ),
% 2.08/1.06      inference(instantiation,[status(thm)],[c_1363]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_2073,plain,
% 2.08/1.06      ( X0_47 != sK1
% 2.08/1.06      | X0_46 != sK2
% 2.08/1.06      | v2_compts_1(X0_46,X0_47) = iProver_top
% 2.08/1.06      | v2_compts_1(sK2,sK1) != iProver_top ),
% 2.08/1.06      inference(predicate_to_equality,[status(thm)],[c_2072]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_2075,plain,
% 2.08/1.06      ( sK1 != sK1
% 2.08/1.06      | k1_xboole_0 != sK2
% 2.08/1.06      | v2_compts_1(sK2,sK1) != iProver_top
% 2.08/1.06      | v2_compts_1(k1_xboole_0,sK1) = iProver_top ),
% 2.08/1.06      inference(instantiation,[status(thm)],[c_2073]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_14,plain,
% 2.08/1.06      ( ~ v2_compts_1(k1_xboole_0,X0)
% 2.08/1.06      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
% 2.08/1.06      | v1_compts_1(k1_pre_topc(X0,k1_xboole_0))
% 2.08/1.06      | ~ l1_pre_topc(X0) ),
% 2.08/1.06      inference(cnf_transformation,[],[f66]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_1339,plain,
% 2.08/1.06      ( ~ v2_compts_1(k1_xboole_0,X0_47)
% 2.08/1.06      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0_47)))
% 2.08/1.06      | v1_compts_1(k1_pre_topc(X0_47,k1_xboole_0))
% 2.08/1.06      | ~ l1_pre_topc(X0_47) ),
% 2.08/1.06      inference(subtyping,[status(esa)],[c_14]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_1398,plain,
% 2.08/1.06      ( v2_compts_1(k1_xboole_0,X0_47) != iProver_top
% 2.08/1.06      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0_47))) != iProver_top
% 2.08/1.06      | v1_compts_1(k1_pre_topc(X0_47,k1_xboole_0)) = iProver_top
% 2.08/1.06      | l1_pre_topc(X0_47) != iProver_top ),
% 2.08/1.06      inference(predicate_to_equality,[status(thm)],[c_1339]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_1400,plain,
% 2.08/1.06      ( v2_compts_1(k1_xboole_0,sK1) != iProver_top
% 2.08/1.06      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.08/1.06      | v1_compts_1(k1_pre_topc(sK1,k1_xboole_0)) = iProver_top
% 2.08/1.06      | l1_pre_topc(sK1) != iProver_top ),
% 2.08/1.06      inference(instantiation,[status(thm)],[c_1398]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_1349,plain,( X0_47 = X0_47 ),theory(equality) ).
% 2.08/1.06  
% 2.08/1.06  cnf(c_1380,plain,
% 2.08/1.06      ( sK1 = sK1 ),
% 2.08/1.06      inference(instantiation,[status(thm)],[c_1349]) ).
% 2.08/1.06  
% 2.08/1.06  cnf(contradiction,plain,
% 2.08/1.06      ( $false ),
% 2.08/1.06      inference(minisat,
% 2.08/1.06                [status(thm)],
% 2.08/1.06                [c_6071,c_4744,c_3609,c_3108,c_3090,c_3015,c_2698,c_2696,
% 2.08/1.06                 c_2467,c_2248,c_2251,c_2190,c_2183,c_2170,c_2133,c_2129,
% 2.08/1.06                 c_2123,c_2075,c_2054,c_2044,c_1400,c_1380,c_16,c_17,
% 2.08/1.06                 c_28,c_19,c_20,c_26,c_21,c_25,c_22]) ).
% 2.08/1.06  
% 2.08/1.06  
% 2.08/1.06  % SZS output end CNFRefutation for theBenchmark.p
% 2.08/1.06  
% 2.08/1.06  ------                               Statistics
% 2.08/1.06  
% 2.08/1.06  ------ General
% 2.08/1.06  
% 2.08/1.06  abstr_ref_over_cycles:                  0
% 2.08/1.06  abstr_ref_under_cycles:                 0
% 2.08/1.06  gc_basic_clause_elim:                   0
% 2.08/1.06  forced_gc_time:                         0
% 2.08/1.06  parsing_time:                           0.035
% 2.08/1.06  unif_index_cands_time:                  0.
% 2.08/1.06  unif_index_add_time:                    0.
% 2.08/1.06  orderings_time:                         0.
% 2.08/1.06  out_proof_time:                         0.012
% 2.08/1.06  total_time:                             0.218
% 2.08/1.06  num_of_symbols:                         50
% 2.08/1.06  num_of_terms:                           3613
% 2.08/1.06  
% 2.08/1.06  ------ Preprocessing
% 2.08/1.06  
% 2.08/1.06  num_of_splits:                          0
% 2.08/1.06  num_of_split_atoms:                     0
% 2.08/1.06  num_of_reused_defs:                     0
% 2.08/1.06  num_eq_ax_congr_red:                    8
% 2.08/1.06  num_of_sem_filtered_clauses:            1
% 2.08/1.06  num_of_subtypes:                        4
% 2.08/1.06  monotx_restored_types:                  1
% 2.08/1.06  sat_num_of_epr_types:                   0
% 2.08/1.06  sat_num_of_non_cyclic_types:            0
% 2.08/1.06  sat_guarded_non_collapsed_types:        1
% 2.08/1.06  num_pure_diseq_elim:                    0
% 2.08/1.06  simp_replaced_by:                       0
% 2.08/1.06  res_preprocessed:                       127
% 2.08/1.06  prep_upred:                             0
% 2.08/1.06  prep_unflattend:                        44
% 2.08/1.06  smt_new_axioms:                         0
% 2.08/1.06  pred_elim_cands:                        7
% 2.08/1.06  pred_elim:                              2
% 2.08/1.06  pred_elim_cl:                           2
% 2.08/1.06  pred_elim_cycles:                       8
% 2.08/1.06  merged_defs:                            0
% 2.08/1.06  merged_defs_ncl:                        0
% 2.08/1.06  bin_hyper_res:                          0
% 2.08/1.06  prep_cycles:                            4
% 2.08/1.06  pred_elim_time:                         0.02
% 2.08/1.06  splitting_time:                         0.
% 2.08/1.06  sem_filter_time:                        0.
% 2.08/1.06  monotx_time:                            0.
% 2.08/1.06  subtype_inf_time:                       0.001
% 2.08/1.06  
% 2.08/1.06  ------ Problem properties
% 2.08/1.06  
% 2.08/1.06  clauses:                                22
% 2.08/1.06  conjectures:                            6
% 2.08/1.06  epr:                                    5
% 2.08/1.06  horn:                                   18
% 2.08/1.06  ground:                                 6
% 2.08/1.06  unary:                                  6
% 2.08/1.06  binary:                                 0
% 2.08/1.06  lits:                                   78
% 2.08/1.06  lits_eq:                                9
% 2.08/1.06  fd_pure:                                0
% 2.08/1.06  fd_pseudo:                              0
% 2.08/1.06  fd_cond:                                2
% 2.08/1.06  fd_pseudo_cond:                         0
% 2.08/1.06  ac_symbols:                             0
% 2.08/1.06  
% 2.08/1.06  ------ Propositional Solver
% 2.08/1.06  
% 2.08/1.06  prop_solver_calls:                      29
% 2.08/1.06  prop_fast_solver_calls:                 1376
% 2.08/1.06  smt_solver_calls:                       0
% 2.08/1.06  smt_fast_solver_calls:                  0
% 2.08/1.06  prop_num_of_clauses:                    1774
% 2.08/1.06  prop_preprocess_simplified:             5666
% 2.08/1.06  prop_fo_subsumed:                       59
% 2.08/1.06  prop_solver_time:                       0.
% 2.08/1.06  smt_solver_time:                        0.
% 2.08/1.06  smt_fast_solver_time:                   0.
% 2.08/1.06  prop_fast_solver_time:                  0.
% 2.08/1.06  prop_unsat_core_time:                   0.
% 2.08/1.06  
% 2.08/1.06  ------ QBF
% 2.08/1.06  
% 2.08/1.06  qbf_q_res:                              0
% 2.08/1.06  qbf_num_tautologies:                    0
% 2.08/1.06  qbf_prep_cycles:                        0
% 2.08/1.06  
% 2.08/1.06  ------ BMC1
% 2.08/1.06  
% 2.08/1.06  bmc1_current_bound:                     -1
% 2.08/1.06  bmc1_last_solved_bound:                 -1
% 2.08/1.06  bmc1_unsat_core_size:                   -1
% 2.08/1.06  bmc1_unsat_core_parents_size:           -1
% 2.08/1.06  bmc1_merge_next_fun:                    0
% 2.08/1.06  bmc1_unsat_core_clauses_time:           0.
% 2.08/1.06  
% 2.08/1.06  ------ Instantiation
% 2.08/1.06  
% 2.08/1.06  inst_num_of_clauses:                    612
% 2.08/1.06  inst_num_in_passive:                    241
% 2.08/1.06  inst_num_in_active:                     341
% 2.08/1.06  inst_num_in_unprocessed:                30
% 2.08/1.06  inst_num_of_loops:                      380
% 2.08/1.06  inst_num_of_learning_restarts:          0
% 2.08/1.06  inst_num_moves_active_passive:          33
% 2.08/1.06  inst_lit_activity:                      0
% 2.08/1.06  inst_lit_activity_moves:                0
% 2.08/1.06  inst_num_tautologies:                   0
% 2.08/1.06  inst_num_prop_implied:                  0
% 2.08/1.06  inst_num_existing_simplified:           0
% 2.08/1.06  inst_num_eq_res_simplified:             0
% 2.08/1.06  inst_num_child_elim:                    0
% 2.08/1.06  inst_num_of_dismatching_blockings:      168
% 2.08/1.06  inst_num_of_non_proper_insts:           549
% 2.08/1.06  inst_num_of_duplicates:                 0
% 2.08/1.06  inst_inst_num_from_inst_to_res:         0
% 2.08/1.06  inst_dismatching_checking_time:         0.
% 2.08/1.06  
% 2.08/1.06  ------ Resolution
% 2.08/1.06  
% 2.08/1.06  res_num_of_clauses:                     0
% 2.08/1.06  res_num_in_passive:                     0
% 2.08/1.06  res_num_in_active:                      0
% 2.08/1.06  res_num_of_loops:                       131
% 2.08/1.06  res_forward_subset_subsumed:            82
% 2.08/1.06  res_backward_subset_subsumed:           0
% 2.08/1.06  res_forward_subsumed:                   0
% 2.08/1.06  res_backward_subsumed:                  0
% 2.08/1.06  res_forward_subsumption_resolution:     1
% 2.08/1.06  res_backward_subsumption_resolution:    0
% 2.08/1.06  res_clause_to_clause_subsumption:       286
% 2.08/1.06  res_orphan_elimination:                 0
% 2.08/1.06  res_tautology_del:                      80
% 2.08/1.06  res_num_eq_res_simplified:              0
% 2.08/1.06  res_num_sel_changes:                    0
% 2.08/1.06  res_moves_from_active_to_pass:          0
% 2.08/1.06  
% 2.08/1.06  ------ Superposition
% 2.08/1.06  
% 2.08/1.06  sup_time_total:                         0.
% 2.08/1.06  sup_time_generating:                    0.
% 2.08/1.06  sup_time_sim_full:                      0.
% 2.08/1.06  sup_time_sim_immed:                     0.
% 2.08/1.06  
% 2.08/1.06  sup_num_of_clauses:                     42
% 2.08/1.06  sup_num_in_active:                      34
% 2.08/1.06  sup_num_in_passive:                     8
% 2.08/1.06  sup_num_of_loops:                       75
% 2.08/1.06  sup_fw_superposition:                   51
% 2.08/1.06  sup_bw_superposition:                   39
% 2.08/1.06  sup_immediate_simplified:               26
% 2.08/1.06  sup_given_eliminated:                   0
% 2.08/1.06  comparisons_done:                       0
% 2.08/1.06  comparisons_avoided:                    0
% 2.08/1.06  
% 2.08/1.06  ------ Simplifications
% 2.08/1.06  
% 2.08/1.06  
% 2.08/1.06  sim_fw_subset_subsumed:                 17
% 2.08/1.06  sim_bw_subset_subsumed:                 3
% 2.08/1.06  sim_fw_subsumed:                        7
% 2.08/1.06  sim_bw_subsumed:                        0
% 2.08/1.06  sim_fw_subsumption_res:                 5
% 2.08/1.06  sim_bw_subsumption_res:                 2
% 2.08/1.06  sim_tautology_del:                      0
% 2.08/1.06  sim_eq_tautology_del:                   4
% 2.08/1.06  sim_eq_res_simp:                        0
% 2.08/1.06  sim_fw_demodulated:                     0
% 2.08/1.06  sim_bw_demodulated:                     40
% 2.08/1.06  sim_light_normalised:                   3
% 2.08/1.06  sim_joinable_taut:                      0
% 2.08/1.06  sim_joinable_simp:                      0
% 2.08/1.06  sim_ac_normalised:                      0
% 2.08/1.06  sim_smt_subsumption:                    0
% 2.08/1.06  
%------------------------------------------------------------------------------
