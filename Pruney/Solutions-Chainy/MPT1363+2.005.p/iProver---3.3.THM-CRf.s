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
% DateTime   : Thu Dec  3 12:17:56 EST 2020

% Result     : Theorem 4.09s
% Output     : CNFRefutation 4.09s
% Verified   : 
% Statistics : Number of formulae       :  186 (1025 expanded)
%              Number of clauses        :  127 ( 413 expanded)
%              Number of leaves         :   20 ( 277 expanded)
%              Depth                    :   16
%              Number of atoms          :  763 (6089 expanded)
%              Number of equality atoms :  257 ( 800 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f40,plain,(
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

fof(f39,plain,(
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

fof(f38,plain,
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

fof(f41,plain,
    ( ~ v2_compts_1(sK3,sK1)
    & v4_pre_topc(sK3,sK1)
    & r1_tarski(sK3,sK2)
    & v2_compts_1(sK2,sK1)
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f31,f40,f39,f38])).

fof(f62,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f41])).

fof(f10,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v1_compts_1(k1_pre_topc(X0,X1))
      | ~ v2_compts_1(X1,X0)
      | k1_xboole_0 = X1
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f60,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f61,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f64,plain,(
    v2_compts_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => u1_struct_0(k1_pre_topc(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f48,plain,(
    ! [X0,X1] :
      ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v4_pre_topc(X1,X0)
              & v1_compts_1(X0) )
           => v2_compts_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_compts_1(X1,X0)
          | ~ v4_pre_topc(X1,X0)
          | ~ v1_compts_1(X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_compts_1(X1,X0)
          | ~ v4_pre_topc(X1,X0)
          | ~ v1_compts_1(X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v2_compts_1(X1,X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ v1_compts_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f63,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f41])).

fof(f65,plain,(
    r1_tarski(sK3,sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f66,plain,(
    v4_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f67,plain,(
    ~ v2_compts_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_pre_topc(k1_pre_topc(X0,X1),X0) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f47,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f46,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f44,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f9,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f34,plain,(
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
    inference(rectify,[],[f33])).

fof(f35,plain,(
    ! [X2,X1] :
      ( ? [X3] :
          ( ~ v2_compts_1(X3,X1)
          & X2 = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v2_compts_1(sK0(X1,X2),X1)
        & sK0(X1,X2) = X2
        & m1_subset_1(sK0(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( v2_compts_1(X2,X0)
      | m1_subset_1(sK0(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r1_tarski(X2,k2_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v2_compts_1(X2,X0)
      | ~ v2_compts_1(sK0(X1,X2),X1)
      | ~ r1_tarski(X2,k2_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v2_compts_1(X2,X0)
      | sK0(X1,X2) = X2
      | ~ r1_tarski(X2,k2_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f8,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( v4_pre_topc(X3,X2)
      | X1 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f68,plain,(
    ! [X2,X0,X3] :
      ( v4_pre_topc(X3,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v4_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f50])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v1_compts_1(k1_pre_topc(X0,X1))
      | ~ v2_compts_1(X1,X0)
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f71,plain,(
    ! [X0] :
      ( v1_compts_1(k1_pre_topc(X0,k1_xboole_0))
      | ~ v2_compts_1(k1_xboole_0,X0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f55])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2371,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_14,plain,
    ( ~ v2_compts_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v1_compts_1(k1_pre_topc(X1,X0))
    | ~ l1_pre_topc(X1)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_25,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_342,plain,
    ( ~ v2_compts_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_compts_1(k1_pre_topc(X1,X0))
    | ~ l1_pre_topc(X1)
    | sK1 != X1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_25])).

cnf(c_343,plain,
    ( ~ v2_compts_1(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_compts_1(k1_pre_topc(sK1,X0))
    | ~ l1_pre_topc(sK1)
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_342])).

cnf(c_24,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_347,plain,
    ( v1_compts_1(k1_pre_topc(sK1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_compts_1(X0,sK1)
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_343,c_24])).

cnf(c_348,plain,
    ( ~ v2_compts_1(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_compts_1(k1_pre_topc(sK1,X0))
    | k1_xboole_0 = X0 ),
    inference(renaming,[status(thm)],[c_347])).

cnf(c_2368,plain,
    ( k1_xboole_0 = X0
    | v2_compts_1(X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v1_compts_1(k1_pre_topc(sK1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_348])).

cnf(c_2878,plain,
    ( sK2 = k1_xboole_0
    | v2_compts_1(sK2,sK1) != iProver_top
    | v1_compts_1(k1_pre_topc(sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2371,c_2368])).

cnf(c_21,negated_conjecture,
    ( v2_compts_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_30,plain,
    ( v2_compts_1(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3519,plain,
    ( sK2 = k1_xboole_0
    | v1_compts_1(k1_pre_topc(sK1,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2878,c_30])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k1_pre_topc(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_2386,plain,
    ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3235,plain,
    ( u1_struct_0(k1_pre_topc(sK1,sK2)) = sK2
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2371,c_2386])).

cnf(c_2652,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | u1_struct_0(k1_pre_topc(sK1,X0)) = X0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2819,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | u1_struct_0(k1_pre_topc(sK1,sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_2652])).

cnf(c_3426,plain,
    ( u1_struct_0(k1_pre_topc(sK1,sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3235,c_24,c_23,c_2819])).

cnf(c_17,plain,
    ( v2_compts_1(X0,X1)
    | ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_compts_1(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2377,plain,
    ( v2_compts_1(X0,X1) = iProver_top
    | v4_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v1_compts_1(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4640,plain,
    ( v2_compts_1(X0,k1_pre_topc(sK1,sK2)) = iProver_top
    | v4_pre_topc(X0,k1_pre_topc(sK1,sK2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
    | v1_compts_1(k1_pre_topc(sK1,sK2)) != iProver_top
    | l1_pre_topc(k1_pre_topc(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3426,c_2377])).

cnf(c_27,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_28,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_29,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_20,negated_conjecture,
    ( r1_tarski(sK3,sK2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_31,plain,
    ( r1_tarski(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_19,negated_conjecture,
    ( v4_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_32,plain,
    ( v4_pre_topc(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_18,negated_conjecture,
    ( ~ v2_compts_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_33,plain,
    ( v2_compts_1(sK3,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3,plain,
    ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_2647,plain,
    ( m1_pre_topc(k1_pre_topc(sK1,X0),sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2813,plain,
    ( m1_pre_topc(k1_pre_topc(sK1,sK2),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_2647])).

cnf(c_2814,plain,
    ( m1_pre_topc(k1_pre_topc(sK1,sK2),sK1) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2813])).

cnf(c_2816,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | u1_struct_0(k1_pre_topc(sK1,sK3)) = sK3 ),
    inference(instantiation,[status(thm)],[c_2652])).

cnf(c_1736,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2825,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1736])).

cnf(c_2839,plain,
    ( k1_zfmisc_1(u1_struct_0(sK1)) = k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_1736])).

cnf(c_2866,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_1736])).

cnf(c_5,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_2966,plain,
    ( ~ m1_pre_topc(k1_pre_topc(sK1,sK2),sK1)
    | l1_pre_topc(k1_pre_topc(sK1,sK2))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2967,plain,
    ( m1_pre_topc(k1_pre_topc(sK1,sK2),sK1) != iProver_top
    | l1_pre_topc(k1_pre_topc(sK1,sK2)) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2966])).

cnf(c_1745,plain,
    ( ~ v4_pre_topc(X0,X1)
    | v4_pre_topc(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2704,plain,
    ( v4_pre_topc(X0,X1)
    | ~ v4_pre_topc(sK3,sK1)
    | X1 != sK1
    | X0 != sK3 ),
    inference(instantiation,[status(thm)],[c_1745])).

cnf(c_3002,plain,
    ( v4_pre_topc(u1_struct_0(k1_pre_topc(sK1,sK3)),X0)
    | ~ v4_pre_topc(sK3,sK1)
    | X0 != sK1
    | u1_struct_0(k1_pre_topc(sK1,sK3)) != sK3 ),
    inference(instantiation,[status(thm)],[c_2704])).

cnf(c_3596,plain,
    ( v4_pre_topc(u1_struct_0(k1_pre_topc(sK1,sK3)),sK1)
    | ~ v4_pre_topc(sK3,sK1)
    | u1_struct_0(k1_pre_topc(sK1,sK3)) != sK3
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_3002])).

cnf(c_3597,plain,
    ( u1_struct_0(k1_pre_topc(sK1,sK3)) != sK3
    | sK1 != sK1
    | v4_pre_topc(u1_struct_0(k1_pre_topc(sK1,sK3)),sK1) = iProver_top
    | v4_pre_topc(sK3,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3596])).

cnf(c_1739,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2689,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | X1 != k1_zfmisc_1(u1_struct_0(sK1))
    | X0 != sK3 ),
    inference(instantiation,[status(thm)],[c_1739])).

cnf(c_3004,plain,
    ( m1_subset_1(u1_struct_0(k1_pre_topc(sK1,sK3)),X0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | X0 != k1_zfmisc_1(u1_struct_0(sK1))
    | u1_struct_0(k1_pre_topc(sK1,sK3)) != sK3 ),
    inference(instantiation,[status(thm)],[c_2689])).

cnf(c_3680,plain,
    ( m1_subset_1(u1_struct_0(k1_pre_topc(sK1,sK3)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | u1_struct_0(k1_pre_topc(sK1,sK3)) != sK3
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_3004])).

cnf(c_3681,plain,
    ( u1_struct_0(k1_pre_topc(sK1,sK3)) != sK3
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
    | m1_subset_1(u1_struct_0(k1_pre_topc(sK1,sK3)),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3680])).

cnf(c_1740,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2699,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(sK3,sK2)
    | X1 != sK2
    | X0 != sK3 ),
    inference(instantiation,[status(thm)],[c_1740])).

cnf(c_3018,plain,
    ( r1_tarski(sK3,X0)
    | ~ r1_tarski(sK3,sK2)
    | X0 != sK2
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2699])).

cnf(c_3696,plain,
    ( r1_tarski(sK3,u1_struct_0(k1_pre_topc(sK1,sK2)))
    | ~ r1_tarski(sK3,sK2)
    | u1_struct_0(k1_pre_topc(sK1,sK2)) != sK2
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_3018])).

cnf(c_3697,plain,
    ( u1_struct_0(k1_pre_topc(sK1,sK2)) != sK2
    | sK3 != sK3
    | r1_tarski(sK3,u1_struct_0(k1_pre_topc(sK1,sK2))) = iProver_top
    | r1_tarski(sK3,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3696])).

cnf(c_4,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_2,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_328,plain,
    ( ~ l1_pre_topc(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_4,c_2])).

cnf(c_3400,plain,
    ( ~ l1_pre_topc(k1_pre_topc(sK1,X0))
    | u1_struct_0(k1_pre_topc(sK1,X0)) = k2_struct_0(k1_pre_topc(sK1,X0)) ),
    inference(instantiation,[status(thm)],[c_328])).

cnf(c_4151,plain,
    ( ~ l1_pre_topc(k1_pre_topc(sK1,sK2))
    | u1_struct_0(k1_pre_topc(sK1,sK2)) = k2_struct_0(k1_pre_topc(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_3400])).

cnf(c_1737,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3351,plain,
    ( X0 != X1
    | sK3 != X1
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_1737])).

cnf(c_4277,plain,
    ( X0 != sK3
    | sK3 = X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_3351])).

cnf(c_4963,plain,
    ( u1_struct_0(k1_pre_topc(sK1,sK3)) != sK3
    | sK3 = u1_struct_0(k1_pre_topc(sK1,sK3))
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_4277])).

cnf(c_1746,plain,
    ( ~ v2_compts_1(X0,X1)
    | v2_compts_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3190,plain,
    ( v2_compts_1(X0,X1)
    | ~ v2_compts_1(X2,sK1)
    | X0 != X2
    | X1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1746])).

cnf(c_4414,plain,
    ( ~ v2_compts_1(X0,sK1)
    | v2_compts_1(X1,sK1)
    | X1 != X0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_3190])).

cnf(c_5294,plain,
    ( ~ v2_compts_1(X0,sK1)
    | v2_compts_1(sK3,sK1)
    | sK1 != sK1
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_4414])).

cnf(c_5542,plain,
    ( ~ v2_compts_1(u1_struct_0(k1_pre_topc(sK1,sK3)),sK1)
    | v2_compts_1(sK3,sK1)
    | sK1 != sK1
    | sK3 != u1_struct_0(k1_pre_topc(sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_5294])).

cnf(c_5543,plain,
    ( sK1 != sK1
    | sK3 != u1_struct_0(k1_pre_topc(sK1,sK3))
    | v2_compts_1(u1_struct_0(k1_pre_topc(sK1,sK3)),sK1) != iProver_top
    | v2_compts_1(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5542])).

cnf(c_4563,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(sK3,u1_struct_0(k1_pre_topc(sK1,sK2)))
    | X1 != u1_struct_0(k1_pre_topc(sK1,sK2))
    | X0 != sK3 ),
    inference(instantiation,[status(thm)],[c_1740])).

cnf(c_5853,plain,
    ( r1_tarski(u1_struct_0(k1_pre_topc(sK1,sK3)),X0)
    | ~ r1_tarski(sK3,u1_struct_0(k1_pre_topc(sK1,sK2)))
    | X0 != u1_struct_0(k1_pre_topc(sK1,sK2))
    | u1_struct_0(k1_pre_topc(sK1,sK3)) != sK3 ),
    inference(instantiation,[status(thm)],[c_4563])).

cnf(c_6287,plain,
    ( r1_tarski(u1_struct_0(k1_pre_topc(sK1,sK3)),k2_struct_0(k1_pre_topc(sK1,sK2)))
    | ~ r1_tarski(sK3,u1_struct_0(k1_pre_topc(sK1,sK2)))
    | u1_struct_0(k1_pre_topc(sK1,sK3)) != sK3
    | k2_struct_0(k1_pre_topc(sK1,sK2)) != u1_struct_0(k1_pre_topc(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_5853])).

cnf(c_6292,plain,
    ( u1_struct_0(k1_pre_topc(sK1,sK3)) != sK3
    | k2_struct_0(k1_pre_topc(sK1,sK2)) != u1_struct_0(k1_pre_topc(sK1,sK2))
    | r1_tarski(u1_struct_0(k1_pre_topc(sK1,sK3)),k2_struct_0(k1_pre_topc(sK1,sK2))) = iProver_top
    | r1_tarski(sK3,u1_struct_0(k1_pre_topc(sK1,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6287])).

cnf(c_11,plain,
    ( v2_compts_1(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ r1_tarski(X0,k2_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK0(X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2978,plain,
    ( v2_compts_1(X0,sK1)
    | ~ m1_pre_topc(k1_pre_topc(sK1,sK2),sK1)
    | ~ r1_tarski(X0,k2_struct_0(k1_pre_topc(sK1,sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(sK0(k1_pre_topc(sK1,sK2),X0),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK1,sK2))))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_6291,plain,
    ( v2_compts_1(u1_struct_0(k1_pre_topc(sK1,sK3)),sK1)
    | ~ m1_pre_topc(k1_pre_topc(sK1,sK2),sK1)
    | ~ r1_tarski(u1_struct_0(k1_pre_topc(sK1,sK3)),k2_struct_0(k1_pre_topc(sK1,sK2)))
    | m1_subset_1(sK0(k1_pre_topc(sK1,sK2),u1_struct_0(k1_pre_topc(sK1,sK3))),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK1,sK2))))
    | ~ m1_subset_1(u1_struct_0(k1_pre_topc(sK1,sK3)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_2978])).

cnf(c_6294,plain,
    ( v2_compts_1(u1_struct_0(k1_pre_topc(sK1,sK3)),sK1) = iProver_top
    | m1_pre_topc(k1_pre_topc(sK1,sK2),sK1) != iProver_top
    | r1_tarski(u1_struct_0(k1_pre_topc(sK1,sK3)),k2_struct_0(k1_pre_topc(sK1,sK2))) != iProver_top
    | m1_subset_1(sK0(k1_pre_topc(sK1,sK2),u1_struct_0(k1_pre_topc(sK1,sK3))),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK1,sK2)))) = iProver_top
    | m1_subset_1(u1_struct_0(k1_pre_topc(sK1,sK3)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6291])).

cnf(c_9,plain,
    ( v2_compts_1(X0,X1)
    | ~ v2_compts_1(sK0(X2,X0),X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ r1_tarski(X0,k2_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2980,plain,
    ( v2_compts_1(X0,sK1)
    | ~ v2_compts_1(sK0(k1_pre_topc(sK1,sK2),X0),k1_pre_topc(sK1,sK2))
    | ~ m1_pre_topc(k1_pre_topc(sK1,sK2),sK1)
    | ~ r1_tarski(X0,k2_struct_0(k1_pre_topc(sK1,sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_6290,plain,
    ( ~ v2_compts_1(sK0(k1_pre_topc(sK1,sK2),u1_struct_0(k1_pre_topc(sK1,sK3))),k1_pre_topc(sK1,sK2))
    | v2_compts_1(u1_struct_0(k1_pre_topc(sK1,sK3)),sK1)
    | ~ m1_pre_topc(k1_pre_topc(sK1,sK2),sK1)
    | ~ r1_tarski(u1_struct_0(k1_pre_topc(sK1,sK3)),k2_struct_0(k1_pre_topc(sK1,sK2)))
    | ~ m1_subset_1(u1_struct_0(k1_pre_topc(sK1,sK3)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_2980])).

cnf(c_6296,plain,
    ( v2_compts_1(sK0(k1_pre_topc(sK1,sK2),u1_struct_0(k1_pre_topc(sK1,sK3))),k1_pre_topc(sK1,sK2)) != iProver_top
    | v2_compts_1(u1_struct_0(k1_pre_topc(sK1,sK3)),sK1) = iProver_top
    | m1_pre_topc(k1_pre_topc(sK1,sK2),sK1) != iProver_top
    | r1_tarski(u1_struct_0(k1_pre_topc(sK1,sK3)),k2_struct_0(k1_pre_topc(sK1,sK2))) != iProver_top
    | m1_subset_1(u1_struct_0(k1_pre_topc(sK1,sK3)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6290])).

cnf(c_10,plain,
    ( v2_compts_1(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ r1_tarski(X0,k2_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK0(X2,X0) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2979,plain,
    ( v2_compts_1(X0,sK1)
    | ~ m1_pre_topc(k1_pre_topc(sK1,sK2),sK1)
    | ~ r1_tarski(X0,k2_struct_0(k1_pre_topc(sK1,sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | sK0(k1_pre_topc(sK1,sK2),X0) = X0 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_6288,plain,
    ( v2_compts_1(u1_struct_0(k1_pre_topc(sK1,sK3)),sK1)
    | ~ m1_pre_topc(k1_pre_topc(sK1,sK2),sK1)
    | ~ r1_tarski(u1_struct_0(k1_pre_topc(sK1,sK3)),k2_struct_0(k1_pre_topc(sK1,sK2)))
    | ~ m1_subset_1(u1_struct_0(k1_pre_topc(sK1,sK3)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | sK0(k1_pre_topc(sK1,sK2),u1_struct_0(k1_pre_topc(sK1,sK3))) = u1_struct_0(k1_pre_topc(sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_2979])).

cnf(c_6300,plain,
    ( sK0(k1_pre_topc(sK1,sK2),u1_struct_0(k1_pre_topc(sK1,sK3))) = u1_struct_0(k1_pre_topc(sK1,sK3))
    | v2_compts_1(u1_struct_0(k1_pre_topc(sK1,sK3)),sK1) = iProver_top
    | m1_pre_topc(k1_pre_topc(sK1,sK2),sK1) != iProver_top
    | r1_tarski(u1_struct_0(k1_pre_topc(sK1,sK3)),k2_struct_0(k1_pre_topc(sK1,sK2))) != iProver_top
    | m1_subset_1(u1_struct_0(k1_pre_topc(sK1,sK3)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6288])).

cnf(c_5316,plain,
    ( X0 != X1
    | X0 = u1_struct_0(k1_pre_topc(sK1,sK2))
    | u1_struct_0(k1_pre_topc(sK1,sK2)) != X1 ),
    inference(instantiation,[status(thm)],[c_1737])).

cnf(c_7742,plain,
    ( X0 = u1_struct_0(k1_pre_topc(sK1,sK2))
    | X0 != k2_struct_0(k1_pre_topc(sK1,sK2))
    | u1_struct_0(k1_pre_topc(sK1,sK2)) != k2_struct_0(k1_pre_topc(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_5316])).

cnf(c_9661,plain,
    ( u1_struct_0(k1_pre_topc(sK1,sK2)) != k2_struct_0(k1_pre_topc(sK1,sK2))
    | k2_struct_0(k1_pre_topc(sK1,sK2)) = u1_struct_0(k1_pre_topc(sK1,sK2))
    | k2_struct_0(k1_pre_topc(sK1,sK2)) != k2_struct_0(k1_pre_topc(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_7742])).

cnf(c_9662,plain,
    ( k2_struct_0(k1_pre_topc(sK1,sK2)) = k2_struct_0(k1_pre_topc(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_1736])).

cnf(c_4611,plain,
    ( v4_pre_topc(X0,X1)
    | ~ v4_pre_topc(u1_struct_0(k1_pre_topc(sK1,sK3)),sK1)
    | X0 != u1_struct_0(k1_pre_topc(sK1,sK3))
    | X1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1745])).

cnf(c_7552,plain,
    ( v4_pre_topc(X0,sK1)
    | ~ v4_pre_topc(u1_struct_0(k1_pre_topc(sK1,sK3)),sK1)
    | X0 != u1_struct_0(k1_pre_topc(sK1,sK3))
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_4611])).

cnf(c_13655,plain,
    ( v4_pre_topc(sK0(k1_pre_topc(sK1,sK2),u1_struct_0(k1_pre_topc(sK1,sK3))),sK1)
    | ~ v4_pre_topc(u1_struct_0(k1_pre_topc(sK1,sK3)),sK1)
    | sK0(k1_pre_topc(sK1,sK2),u1_struct_0(k1_pre_topc(sK1,sK3))) != u1_struct_0(k1_pre_topc(sK1,sK3))
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_7552])).

cnf(c_13682,plain,
    ( sK0(k1_pre_topc(sK1,sK2),u1_struct_0(k1_pre_topc(sK1,sK3))) != u1_struct_0(k1_pre_topc(sK1,sK3))
    | sK1 != sK1
    | v4_pre_topc(sK0(k1_pre_topc(sK1,sK2),u1_struct_0(k1_pre_topc(sK1,sK3))),sK1) = iProver_top
    | v4_pre_topc(u1_struct_0(k1_pre_topc(sK1,sK3)),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13655])).

cnf(c_3111,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
    | X0 != X2
    | X1 != k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_1739])).

cnf(c_4910,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(u1_struct_0(k1_pre_topc(sK1,sK3)),k1_zfmisc_1(u1_struct_0(sK1)))
    | X0 != u1_struct_0(k1_pre_topc(sK1,sK3))
    | X1 != k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_3111])).

cnf(c_7703,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(u1_struct_0(k1_pre_topc(sK1,sK3)),k1_zfmisc_1(u1_struct_0(sK1)))
    | X0 != u1_struct_0(k1_pre_topc(sK1,sK3))
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_4910])).

cnf(c_13654,plain,
    ( m1_subset_1(sK0(k1_pre_topc(sK1,sK2),u1_struct_0(k1_pre_topc(sK1,sK3))),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(u1_struct_0(k1_pre_topc(sK1,sK3)),k1_zfmisc_1(u1_struct_0(sK1)))
    | sK0(k1_pre_topc(sK1,sK2),u1_struct_0(k1_pre_topc(sK1,sK3))) != u1_struct_0(k1_pre_topc(sK1,sK3))
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_7703])).

cnf(c_13684,plain,
    ( sK0(k1_pre_topc(sK1,sK2),u1_struct_0(k1_pre_topc(sK1,sK3))) != u1_struct_0(k1_pre_topc(sK1,sK3))
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
    | m1_subset_1(sK0(k1_pre_topc(sK1,sK2),u1_struct_0(k1_pre_topc(sK1,sK3))),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m1_subset_1(u1_struct_0(k1_pre_topc(sK1,sK3)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13654])).

cnf(c_8,plain,
    ( ~ v4_pre_topc(X0,X1)
    | v4_pre_topc(X0,X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_3138,plain,
    ( v4_pre_topc(X0,k1_pre_topc(sK1,X1))
    | ~ v4_pre_topc(X0,sK1)
    | ~ m1_pre_topc(k1_pre_topc(sK1,X1),sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK1,X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_13704,plain,
    ( v4_pre_topc(sK0(k1_pre_topc(sK1,sK2),u1_struct_0(k1_pre_topc(sK1,sK3))),k1_pre_topc(sK1,sK2))
    | ~ v4_pre_topc(sK0(k1_pre_topc(sK1,sK2),u1_struct_0(k1_pre_topc(sK1,sK3))),sK1)
    | ~ m1_pre_topc(k1_pre_topc(sK1,sK2),sK1)
    | ~ m1_subset_1(sK0(k1_pre_topc(sK1,sK2),u1_struct_0(k1_pre_topc(sK1,sK3))),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK1,sK2))))
    | ~ m1_subset_1(sK0(k1_pre_topc(sK1,sK2),u1_struct_0(k1_pre_topc(sK1,sK3))),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_3138])).

cnf(c_13705,plain,
    ( v4_pre_topc(sK0(k1_pre_topc(sK1,sK2),u1_struct_0(k1_pre_topc(sK1,sK3))),k1_pre_topc(sK1,sK2)) = iProver_top
    | v4_pre_topc(sK0(k1_pre_topc(sK1,sK2),u1_struct_0(k1_pre_topc(sK1,sK3))),sK1) != iProver_top
    | m1_pre_topc(k1_pre_topc(sK1,sK2),sK1) != iProver_top
    | m1_subset_1(sK0(k1_pre_topc(sK1,sK2),u1_struct_0(k1_pre_topc(sK1,sK3))),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK1,sK2)))) != iProver_top
    | m1_subset_1(sK0(k1_pre_topc(sK1,sK2),u1_struct_0(k1_pre_topc(sK1,sK3))),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13704])).

cnf(c_3577,plain,
    ( v2_compts_1(X0,k1_pre_topc(sK1,sK2))
    | ~ v4_pre_topc(X0,k1_pre_topc(sK1,sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK1,sK2))))
    | ~ v1_compts_1(k1_pre_topc(sK1,sK2))
    | ~ l1_pre_topc(k1_pre_topc(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_16728,plain,
    ( v2_compts_1(sK0(k1_pre_topc(sK1,sK2),u1_struct_0(k1_pre_topc(sK1,sK3))),k1_pre_topc(sK1,sK2))
    | ~ v4_pre_topc(sK0(k1_pre_topc(sK1,sK2),u1_struct_0(k1_pre_topc(sK1,sK3))),k1_pre_topc(sK1,sK2))
    | ~ m1_subset_1(sK0(k1_pre_topc(sK1,sK2),u1_struct_0(k1_pre_topc(sK1,sK3))),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK1,sK2))))
    | ~ v1_compts_1(k1_pre_topc(sK1,sK2))
    | ~ l1_pre_topc(k1_pre_topc(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_3577])).

cnf(c_16729,plain,
    ( v2_compts_1(sK0(k1_pre_topc(sK1,sK2),u1_struct_0(k1_pre_topc(sK1,sK3))),k1_pre_topc(sK1,sK2)) = iProver_top
    | v4_pre_topc(sK0(k1_pre_topc(sK1,sK2),u1_struct_0(k1_pre_topc(sK1,sK3))),k1_pre_topc(sK1,sK2)) != iProver_top
    | m1_subset_1(sK0(k1_pre_topc(sK1,sK2),u1_struct_0(k1_pre_topc(sK1,sK3))),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK1,sK2)))) != iProver_top
    | v1_compts_1(k1_pre_topc(sK1,sK2)) != iProver_top
    | l1_pre_topc(k1_pre_topc(sK1,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16728])).

cnf(c_17929,plain,
    ( v1_compts_1(k1_pre_topc(sK1,sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4640,c_24,c_27,c_23,c_28,c_22,c_29,c_31,c_32,c_33,c_2813,c_2814,c_2816,c_2819,c_2825,c_2839,c_2866,c_2966,c_2967,c_3597,c_3681,c_3697,c_4151,c_4963,c_5543,c_6292,c_6294,c_6296,c_6300,c_9661,c_9662,c_13682,c_13684,c_13705,c_16729])).

cnf(c_17934,plain,
    ( sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3519,c_17929])).

cnf(c_18177,plain,
    ( v1_compts_1(k1_pre_topc(sK1,k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_17934,c_17929])).

cnf(c_16,plain,
    ( ~ v2_compts_1(k1_xboole_0,X0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
    | v1_compts_1(k1_pre_topc(X0,k1_xboole_0))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_3196,plain,
    ( ~ v2_compts_1(k1_xboole_0,sK1)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_compts_1(k1_pre_topc(sK1,k1_xboole_0))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_3199,plain,
    ( v2_compts_1(k1_xboole_0,sK1) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v1_compts_1(k1_pre_topc(sK1,k1_xboole_0)) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3196])).

cnf(c_2709,plain,
    ( v2_compts_1(X0,X1)
    | ~ v2_compts_1(sK2,sK1)
    | X0 != sK2
    | X1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1746])).

cnf(c_2865,plain,
    ( v2_compts_1(X0,sK1)
    | ~ v2_compts_1(sK2,sK1)
    | X0 != sK2
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_2709])).

cnf(c_2867,plain,
    ( X0 != sK2
    | sK1 != sK1
    | v2_compts_1(X0,sK1) = iProver_top
    | v2_compts_1(sK2,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2865])).

cnf(c_2869,plain,
    ( sK1 != sK1
    | k1_xboole_0 != sK2
    | v2_compts_1(sK2,sK1) != iProver_top
    | v2_compts_1(k1_xboole_0,sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2867])).

cnf(c_2694,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | X1 != k1_zfmisc_1(u1_struct_0(sK1))
    | X0 != sK2 ),
    inference(instantiation,[status(thm)],[c_1739])).

cnf(c_2838,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | X0 != sK2
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_2694])).

cnf(c_2840,plain,
    ( X0 != sK2
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2838])).

cnf(c_2842,plain,
    ( k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
    | k1_xboole_0 != sK2
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2840])).

cnf(c_2676,plain,
    ( ~ v2_compts_1(sK2,sK1)
    | v1_compts_1(k1_pre_topc(sK1,sK2))
    | k1_xboole_0 = sK2 ),
    inference(resolution,[status(thm)],[c_348,c_23])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_18177,c_16728,c_13704,c_13654,c_13655,c_9662,c_9661,c_6300,c_6290,c_6291,c_6292,c_6287,c_5543,c_5542,c_4963,c_4151,c_3697,c_3696,c_3681,c_3680,c_3596,c_3199,c_2966,c_2866,c_2869,c_2839,c_2842,c_2825,c_2819,c_2816,c_2814,c_2813,c_2676,c_33,c_18,c_19,c_31,c_20,c_30,c_21,c_29,c_22,c_28,c_23,c_27,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 20:36:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 4.09/1.03  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.09/1.03  
% 4.09/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.09/1.03  
% 4.09/1.03  ------  iProver source info
% 4.09/1.03  
% 4.09/1.03  git: date: 2020-06-30 10:37:57 +0100
% 4.09/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.09/1.03  git: non_committed_changes: false
% 4.09/1.03  git: last_make_outside_of_git: false
% 4.09/1.03  
% 4.09/1.03  ------ 
% 4.09/1.03  ------ Parsing...
% 4.09/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.09/1.03  
% 4.09/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 4.09/1.03  
% 4.09/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.09/1.03  
% 4.09/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.09/1.03  ------ Proving...
% 4.09/1.03  ------ Problem Properties 
% 4.09/1.03  
% 4.09/1.03  
% 4.09/1.03  clauses                                 24
% 4.09/1.03  conjectures                             7
% 4.09/1.03  EPR                                     6
% 4.09/1.03  Horn                                    20
% 4.09/1.03  unary                                   7
% 4.09/1.03  binary                                  3
% 4.09/1.03  lits                                    78
% 4.09/1.03  lits eq                                 5
% 4.09/1.03  fd_pure                                 0
% 4.09/1.03  fd_pseudo                               0
% 4.09/1.03  fd_cond                                 2
% 4.09/1.03  fd_pseudo_cond                          0
% 4.09/1.03  AC symbols                              0
% 4.09/1.03  
% 4.09/1.03  ------ Input Options Time Limit: Unbounded
% 4.09/1.03  
% 4.09/1.03  
% 4.09/1.03  ------ 
% 4.09/1.03  Current options:
% 4.09/1.03  ------ 
% 4.09/1.03  
% 4.09/1.03  
% 4.09/1.03  
% 4.09/1.03  
% 4.09/1.03  ------ Proving...
% 4.09/1.03  
% 4.09/1.03  
% 4.09/1.03  % SZS status Theorem for theBenchmark.p
% 4.09/1.03  
% 4.09/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 4.09/1.03  
% 4.09/1.03  fof(f12,conjecture,(
% 4.09/1.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X2,X0) & r1_tarski(X2,X1) & v2_compts_1(X1,X0)) => v2_compts_1(X2,X0)))))),
% 4.09/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.09/1.03  
% 4.09/1.03  fof(f13,negated_conjecture,(
% 4.09/1.03    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X2,X0) & r1_tarski(X2,X1) & v2_compts_1(X1,X0)) => v2_compts_1(X2,X0)))))),
% 4.09/1.03    inference(negated_conjecture,[],[f12])).
% 4.09/1.03  
% 4.09/1.03  fof(f30,plain,(
% 4.09/1.03    ? [X0] : (? [X1] : (? [X2] : ((~v2_compts_1(X2,X0) & (v4_pre_topc(X2,X0) & r1_tarski(X2,X1) & v2_compts_1(X1,X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 4.09/1.03    inference(ennf_transformation,[],[f13])).
% 4.09/1.03  
% 4.09/1.03  fof(f31,plain,(
% 4.09/1.03    ? [X0] : (? [X1] : (? [X2] : (~v2_compts_1(X2,X0) & v4_pre_topc(X2,X0) & r1_tarski(X2,X1) & v2_compts_1(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 4.09/1.03    inference(flattening,[],[f30])).
% 4.09/1.03  
% 4.09/1.03  fof(f40,plain,(
% 4.09/1.03    ( ! [X0,X1] : (? [X2] : (~v2_compts_1(X2,X0) & v4_pre_topc(X2,X0) & r1_tarski(X2,X1) & v2_compts_1(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v2_compts_1(sK3,X0) & v4_pre_topc(sK3,X0) & r1_tarski(sK3,X1) & v2_compts_1(X1,X0) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 4.09/1.03    introduced(choice_axiom,[])).
% 4.09/1.03  
% 4.09/1.03  fof(f39,plain,(
% 4.09/1.03    ( ! [X0] : (? [X1] : (? [X2] : (~v2_compts_1(X2,X0) & v4_pre_topc(X2,X0) & r1_tarski(X2,X1) & v2_compts_1(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (~v2_compts_1(X2,X0) & v4_pre_topc(X2,X0) & r1_tarski(X2,sK2) & v2_compts_1(sK2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 4.09/1.03    introduced(choice_axiom,[])).
% 4.09/1.03  
% 4.09/1.03  fof(f38,plain,(
% 4.09/1.03    ? [X0] : (? [X1] : (? [X2] : (~v2_compts_1(X2,X0) & v4_pre_topc(X2,X0) & r1_tarski(X2,X1) & v2_compts_1(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (~v2_compts_1(X2,sK1) & v4_pre_topc(X2,sK1) & r1_tarski(X2,X1) & v2_compts_1(X1,sK1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & v2_pre_topc(sK1))),
% 4.09/1.03    introduced(choice_axiom,[])).
% 4.09/1.03  
% 4.09/1.03  fof(f41,plain,(
% 4.09/1.03    ((~v2_compts_1(sK3,sK1) & v4_pre_topc(sK3,sK1) & r1_tarski(sK3,sK2) & v2_compts_1(sK2,sK1) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & v2_pre_topc(sK1)),
% 4.09/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f31,f40,f39,f38])).
% 4.09/1.03  
% 4.09/1.03  fof(f62,plain,(
% 4.09/1.03    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))),
% 4.09/1.03    inference(cnf_transformation,[],[f41])).
% 4.09/1.03  
% 4.09/1.03  fof(f10,axiom,(
% 4.09/1.03    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_pre_topc(X0) => ((v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1))) | k1_xboole_0 = X1)) & (k1_xboole_0 = X1 => (v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1)))))))),
% 4.09/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.09/1.03  
% 4.09/1.03  fof(f26,plain,(
% 4.09/1.03    ! [X0] : (! [X1] : (((((v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1))) | k1_xboole_0 = X1) | ~v2_pre_topc(X0)) & ((v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1))) | k1_xboole_0 != X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.09/1.03    inference(ennf_transformation,[],[f10])).
% 4.09/1.03  
% 4.09/1.03  fof(f27,plain,(
% 4.09/1.03    ! [X0] : (! [X1] : ((((v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1))) | k1_xboole_0 = X1 | ~v2_pre_topc(X0)) & ((v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1))) | k1_xboole_0 != X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.09/1.03    inference(flattening,[],[f26])).
% 4.09/1.03  
% 4.09/1.03  fof(f37,plain,(
% 4.09/1.03    ! [X0] : (! [X1] : (((((v2_compts_1(X1,X0) | ~v1_compts_1(k1_pre_topc(X0,X1))) & (v1_compts_1(k1_pre_topc(X0,X1)) | ~v2_compts_1(X1,X0))) | k1_xboole_0 = X1 | ~v2_pre_topc(X0)) & (((v2_compts_1(X1,X0) | ~v1_compts_1(k1_pre_topc(X0,X1))) & (v1_compts_1(k1_pre_topc(X0,X1)) | ~v2_compts_1(X1,X0))) | k1_xboole_0 != X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.09/1.03    inference(nnf_transformation,[],[f27])).
% 4.09/1.03  
% 4.09/1.03  fof(f57,plain,(
% 4.09/1.03    ( ! [X0,X1] : (v1_compts_1(k1_pre_topc(X0,X1)) | ~v2_compts_1(X1,X0) | k1_xboole_0 = X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 4.09/1.03    inference(cnf_transformation,[],[f37])).
% 4.09/1.03  
% 4.09/1.03  fof(f60,plain,(
% 4.09/1.03    v2_pre_topc(sK1)),
% 4.09/1.03    inference(cnf_transformation,[],[f41])).
% 4.09/1.03  
% 4.09/1.03  fof(f61,plain,(
% 4.09/1.03    l1_pre_topc(sK1)),
% 4.09/1.03    inference(cnf_transformation,[],[f41])).
% 4.09/1.03  
% 4.09/1.03  fof(f64,plain,(
% 4.09/1.03    v2_compts_1(sK2,sK1)),
% 4.09/1.03    inference(cnf_transformation,[],[f41])).
% 4.09/1.03  
% 4.09/1.03  fof(f6,axiom,(
% 4.09/1.03    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => u1_struct_0(k1_pre_topc(X0,X1)) = X1))),
% 4.09/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.09/1.03  
% 4.09/1.03  fof(f20,plain,(
% 4.09/1.03    ! [X0] : (! [X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.09/1.03    inference(ennf_transformation,[],[f6])).
% 4.09/1.03  
% 4.09/1.03  fof(f48,plain,(
% 4.09/1.03    ( ! [X0,X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 4.09/1.03    inference(cnf_transformation,[],[f20])).
% 4.09/1.03  
% 4.09/1.03  fof(f11,axiom,(
% 4.09/1.03    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X1,X0) & v1_compts_1(X0)) => v2_compts_1(X1,X0))))),
% 4.09/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.09/1.03  
% 4.09/1.03  fof(f28,plain,(
% 4.09/1.03    ! [X0] : (! [X1] : ((v2_compts_1(X1,X0) | (~v4_pre_topc(X1,X0) | ~v1_compts_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.09/1.03    inference(ennf_transformation,[],[f11])).
% 4.09/1.03  
% 4.09/1.03  fof(f29,plain,(
% 4.09/1.03    ! [X0] : (! [X1] : (v2_compts_1(X1,X0) | ~v4_pre_topc(X1,X0) | ~v1_compts_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.09/1.03    inference(flattening,[],[f28])).
% 4.09/1.03  
% 4.09/1.03  fof(f59,plain,(
% 4.09/1.03    ( ! [X0,X1] : (v2_compts_1(X1,X0) | ~v4_pre_topc(X1,X0) | ~v1_compts_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 4.09/1.03    inference(cnf_transformation,[],[f29])).
% 4.09/1.03  
% 4.09/1.03  fof(f63,plain,(
% 4.09/1.03    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))),
% 4.09/1.03    inference(cnf_transformation,[],[f41])).
% 4.09/1.03  
% 4.09/1.03  fof(f65,plain,(
% 4.09/1.03    r1_tarski(sK3,sK2)),
% 4.09/1.03    inference(cnf_transformation,[],[f41])).
% 4.09/1.03  
% 4.09/1.03  fof(f66,plain,(
% 4.09/1.03    v4_pre_topc(sK3,sK1)),
% 4.09/1.03    inference(cnf_transformation,[],[f41])).
% 4.09/1.03  
% 4.09/1.03  fof(f67,plain,(
% 4.09/1.03    ~v2_compts_1(sK3,sK1)),
% 4.09/1.03    inference(cnf_transformation,[],[f41])).
% 4.09/1.03  
% 4.09/1.03  fof(f3,axiom,(
% 4.09/1.03    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => (m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))))),
% 4.09/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.09/1.03  
% 4.09/1.03  fof(f14,plain,(
% 4.09/1.03    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_pre_topc(k1_pre_topc(X0,X1),X0))),
% 4.09/1.03    inference(pure_predicate_removal,[],[f3])).
% 4.09/1.03  
% 4.09/1.03  fof(f16,plain,(
% 4.09/1.03    ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 4.09/1.03    inference(ennf_transformation,[],[f14])).
% 4.09/1.03  
% 4.09/1.03  fof(f17,plain,(
% 4.09/1.03    ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 4.09/1.03    inference(flattening,[],[f16])).
% 4.09/1.03  
% 4.09/1.03  fof(f45,plain,(
% 4.09/1.03    ( ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 4.09/1.03    inference(cnf_transformation,[],[f17])).
% 4.09/1.03  
% 4.09/1.03  fof(f5,axiom,(
% 4.09/1.03    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 4.09/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.09/1.03  
% 4.09/1.03  fof(f19,plain,(
% 4.09/1.03    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 4.09/1.03    inference(ennf_transformation,[],[f5])).
% 4.09/1.03  
% 4.09/1.03  fof(f47,plain,(
% 4.09/1.03    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 4.09/1.03    inference(cnf_transformation,[],[f19])).
% 4.09/1.03  
% 4.09/1.03  fof(f4,axiom,(
% 4.09/1.03    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 4.09/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.09/1.03  
% 4.09/1.03  fof(f18,plain,(
% 4.09/1.03    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 4.09/1.03    inference(ennf_transformation,[],[f4])).
% 4.09/1.03  
% 4.09/1.03  fof(f46,plain,(
% 4.09/1.03    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 4.09/1.03    inference(cnf_transformation,[],[f18])).
% 4.09/1.03  
% 4.09/1.03  fof(f2,axiom,(
% 4.09/1.03    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 4.09/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.09/1.03  
% 4.09/1.03  fof(f15,plain,(
% 4.09/1.03    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 4.09/1.03    inference(ennf_transformation,[],[f2])).
% 4.09/1.03  
% 4.09/1.03  fof(f44,plain,(
% 4.09/1.03    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 4.09/1.03    inference(cnf_transformation,[],[f15])).
% 4.09/1.03  
% 4.09/1.03  fof(f9,axiom,(
% 4.09/1.03    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X2,k2_struct_0(X1)) => (v2_compts_1(X2,X0) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (X2 = X3 => v2_compts_1(X3,X1))))))))),
% 4.09/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.09/1.03  
% 4.09/1.03  fof(f24,plain,(
% 4.09/1.03    ! [X0] : (! [X1] : (! [X2] : (((v2_compts_1(X2,X0) <=> ! [X3] : ((v2_compts_1(X3,X1) | X2 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | ~r1_tarski(X2,k2_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 4.09/1.03    inference(ennf_transformation,[],[f9])).
% 4.09/1.03  
% 4.09/1.03  fof(f25,plain,(
% 4.09/1.03    ! [X0] : (! [X1] : (! [X2] : ((v2_compts_1(X2,X0) <=> ! [X3] : (v2_compts_1(X3,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 4.09/1.03    inference(flattening,[],[f24])).
% 4.09/1.03  
% 4.09/1.03  fof(f33,plain,(
% 4.09/1.03    ! [X0] : (! [X1] : (! [X2] : (((v2_compts_1(X2,X0) | ? [X3] : (~v2_compts_1(X3,X1) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (v2_compts_1(X3,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v2_compts_1(X2,X0))) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 4.09/1.03    inference(nnf_transformation,[],[f25])).
% 4.09/1.03  
% 4.09/1.03  fof(f34,plain,(
% 4.09/1.03    ! [X0] : (! [X1] : (! [X2] : (((v2_compts_1(X2,X0) | ? [X3] : (~v2_compts_1(X3,X1) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v2_compts_1(X4,X1) | X2 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v2_compts_1(X2,X0))) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 4.09/1.03    inference(rectify,[],[f33])).
% 4.09/1.03  
% 4.09/1.03  fof(f35,plain,(
% 4.09/1.03    ! [X2,X1] : (? [X3] : (~v2_compts_1(X3,X1) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) => (~v2_compts_1(sK0(X1,X2),X1) & sK0(X1,X2) = X2 & m1_subset_1(sK0(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))))),
% 4.09/1.03    introduced(choice_axiom,[])).
% 4.09/1.03  
% 4.09/1.03  fof(f36,plain,(
% 4.09/1.03    ! [X0] : (! [X1] : (! [X2] : (((v2_compts_1(X2,X0) | (~v2_compts_1(sK0(X1,X2),X1) & sK0(X1,X2) = X2 & m1_subset_1(sK0(X1,X2),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v2_compts_1(X4,X1) | X2 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v2_compts_1(X2,X0))) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 4.09/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).
% 4.09/1.03  
% 4.09/1.03  fof(f52,plain,(
% 4.09/1.03    ( ! [X2,X0,X1] : (v2_compts_1(X2,X0) | m1_subset_1(sK0(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 4.09/1.03    inference(cnf_transformation,[],[f36])).
% 4.09/1.03  
% 4.09/1.03  fof(f54,plain,(
% 4.09/1.03    ( ! [X2,X0,X1] : (v2_compts_1(X2,X0) | ~v2_compts_1(sK0(X1,X2),X1) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 4.09/1.03    inference(cnf_transformation,[],[f36])).
% 4.09/1.03  
% 4.09/1.03  fof(f53,plain,(
% 4.09/1.03    ( ! [X2,X0,X1] : (v2_compts_1(X2,X0) | sK0(X1,X2) = X2 | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 4.09/1.03    inference(cnf_transformation,[],[f36])).
% 4.09/1.03  
% 4.09/1.03  fof(f8,axiom,(
% 4.09/1.03    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v4_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v4_pre_topc(X3,X2)))))))),
% 4.09/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.09/1.03  
% 4.09/1.03  fof(f22,plain,(
% 4.09/1.03    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((v4_pre_topc(X3,X2) | X1 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v4_pre_topc(X1,X0)) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.09/1.03    inference(ennf_transformation,[],[f8])).
% 4.09/1.03  
% 4.09/1.03  fof(f23,plain,(
% 4.09/1.03    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (v4_pre_topc(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v4_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.09/1.03    inference(flattening,[],[f22])).
% 4.09/1.03  
% 4.09/1.03  fof(f50,plain,(
% 4.09/1.03    ( ! [X2,X0,X3,X1] : (v4_pre_topc(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~v4_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 4.09/1.03    inference(cnf_transformation,[],[f23])).
% 4.09/1.03  
% 4.09/1.03  fof(f68,plain,(
% 4.09/1.03    ( ! [X2,X0,X3] : (v4_pre_topc(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~v4_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 4.09/1.03    inference(equality_resolution,[],[f50])).
% 4.09/1.03  
% 4.09/1.03  fof(f55,plain,(
% 4.09/1.03    ( ! [X0,X1] : (v1_compts_1(k1_pre_topc(X0,X1)) | ~v2_compts_1(X1,X0) | k1_xboole_0 != X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 4.09/1.03    inference(cnf_transformation,[],[f37])).
% 4.09/1.03  
% 4.09/1.03  fof(f71,plain,(
% 4.09/1.03    ( ! [X0] : (v1_compts_1(k1_pre_topc(X0,k1_xboole_0)) | ~v2_compts_1(k1_xboole_0,X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 4.09/1.03    inference(equality_resolution,[],[f55])).
% 4.09/1.03  
% 4.09/1.03  cnf(c_23,negated_conjecture,
% 4.09/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 4.09/1.03      inference(cnf_transformation,[],[f62]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_2371,plain,
% 4.09/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 4.09/1.03      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_14,plain,
% 4.09/1.03      ( ~ v2_compts_1(X0,X1)
% 4.09/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.09/1.03      | ~ v2_pre_topc(X1)
% 4.09/1.03      | v1_compts_1(k1_pre_topc(X1,X0))
% 4.09/1.03      | ~ l1_pre_topc(X1)
% 4.09/1.03      | k1_xboole_0 = X0 ),
% 4.09/1.03      inference(cnf_transformation,[],[f57]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_25,negated_conjecture,
% 4.09/1.03      ( v2_pre_topc(sK1) ),
% 4.09/1.03      inference(cnf_transformation,[],[f60]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_342,plain,
% 4.09/1.03      ( ~ v2_compts_1(X0,X1)
% 4.09/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.09/1.03      | v1_compts_1(k1_pre_topc(X1,X0))
% 4.09/1.03      | ~ l1_pre_topc(X1)
% 4.09/1.03      | sK1 != X1
% 4.09/1.03      | k1_xboole_0 = X0 ),
% 4.09/1.03      inference(resolution_lifted,[status(thm)],[c_14,c_25]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_343,plain,
% 4.09/1.03      ( ~ v2_compts_1(X0,sK1)
% 4.09/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 4.09/1.03      | v1_compts_1(k1_pre_topc(sK1,X0))
% 4.09/1.03      | ~ l1_pre_topc(sK1)
% 4.09/1.03      | k1_xboole_0 = X0 ),
% 4.09/1.03      inference(unflattening,[status(thm)],[c_342]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_24,negated_conjecture,
% 4.09/1.03      ( l1_pre_topc(sK1) ),
% 4.09/1.03      inference(cnf_transformation,[],[f61]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_347,plain,
% 4.09/1.03      ( v1_compts_1(k1_pre_topc(sK1,X0))
% 4.09/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 4.09/1.03      | ~ v2_compts_1(X0,sK1)
% 4.09/1.03      | k1_xboole_0 = X0 ),
% 4.09/1.03      inference(global_propositional_subsumption,
% 4.09/1.03                [status(thm)],
% 4.09/1.03                [c_343,c_24]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_348,plain,
% 4.09/1.03      ( ~ v2_compts_1(X0,sK1)
% 4.09/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 4.09/1.03      | v1_compts_1(k1_pre_topc(sK1,X0))
% 4.09/1.03      | k1_xboole_0 = X0 ),
% 4.09/1.03      inference(renaming,[status(thm)],[c_347]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_2368,plain,
% 4.09/1.03      ( k1_xboole_0 = X0
% 4.09/1.03      | v2_compts_1(X0,sK1) != iProver_top
% 4.09/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 4.09/1.03      | v1_compts_1(k1_pre_topc(sK1,X0)) = iProver_top ),
% 4.09/1.03      inference(predicate_to_equality,[status(thm)],[c_348]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_2878,plain,
% 4.09/1.03      ( sK2 = k1_xboole_0
% 4.09/1.03      | v2_compts_1(sK2,sK1) != iProver_top
% 4.09/1.03      | v1_compts_1(k1_pre_topc(sK1,sK2)) = iProver_top ),
% 4.09/1.03      inference(superposition,[status(thm)],[c_2371,c_2368]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_21,negated_conjecture,
% 4.09/1.03      ( v2_compts_1(sK2,sK1) ),
% 4.09/1.03      inference(cnf_transformation,[],[f64]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_30,plain,
% 4.09/1.03      ( v2_compts_1(sK2,sK1) = iProver_top ),
% 4.09/1.03      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_3519,plain,
% 4.09/1.03      ( sK2 = k1_xboole_0
% 4.09/1.03      | v1_compts_1(k1_pre_topc(sK1,sK2)) = iProver_top ),
% 4.09/1.03      inference(global_propositional_subsumption,
% 4.09/1.03                [status(thm)],
% 4.09/1.03                [c_2878,c_30]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_6,plain,
% 4.09/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.09/1.03      | ~ l1_pre_topc(X1)
% 4.09/1.03      | u1_struct_0(k1_pre_topc(X1,X0)) = X0 ),
% 4.09/1.03      inference(cnf_transformation,[],[f48]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_2386,plain,
% 4.09/1.03      ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
% 4.09/1.03      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 4.09/1.03      | l1_pre_topc(X0) != iProver_top ),
% 4.09/1.03      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_3235,plain,
% 4.09/1.03      ( u1_struct_0(k1_pre_topc(sK1,sK2)) = sK2
% 4.09/1.03      | l1_pre_topc(sK1) != iProver_top ),
% 4.09/1.03      inference(superposition,[status(thm)],[c_2371,c_2386]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_2652,plain,
% 4.09/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 4.09/1.03      | ~ l1_pre_topc(sK1)
% 4.09/1.03      | u1_struct_0(k1_pre_topc(sK1,X0)) = X0 ),
% 4.09/1.03      inference(instantiation,[status(thm)],[c_6]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_2819,plain,
% 4.09/1.03      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 4.09/1.03      | ~ l1_pre_topc(sK1)
% 4.09/1.03      | u1_struct_0(k1_pre_topc(sK1,sK2)) = sK2 ),
% 4.09/1.03      inference(instantiation,[status(thm)],[c_2652]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_3426,plain,
% 4.09/1.03      ( u1_struct_0(k1_pre_topc(sK1,sK2)) = sK2 ),
% 4.09/1.03      inference(global_propositional_subsumption,
% 4.09/1.03                [status(thm)],
% 4.09/1.03                [c_3235,c_24,c_23,c_2819]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_17,plain,
% 4.09/1.03      ( v2_compts_1(X0,X1)
% 4.09/1.03      | ~ v4_pre_topc(X0,X1)
% 4.09/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.09/1.03      | ~ v1_compts_1(X1)
% 4.09/1.03      | ~ l1_pre_topc(X1) ),
% 4.09/1.03      inference(cnf_transformation,[],[f59]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_2377,plain,
% 4.09/1.03      ( v2_compts_1(X0,X1) = iProver_top
% 4.09/1.03      | v4_pre_topc(X0,X1) != iProver_top
% 4.09/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 4.09/1.03      | v1_compts_1(X1) != iProver_top
% 4.09/1.03      | l1_pre_topc(X1) != iProver_top ),
% 4.09/1.03      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_4640,plain,
% 4.09/1.03      ( v2_compts_1(X0,k1_pre_topc(sK1,sK2)) = iProver_top
% 4.09/1.03      | v4_pre_topc(X0,k1_pre_topc(sK1,sK2)) != iProver_top
% 4.09/1.03      | m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
% 4.09/1.03      | v1_compts_1(k1_pre_topc(sK1,sK2)) != iProver_top
% 4.09/1.03      | l1_pre_topc(k1_pre_topc(sK1,sK2)) != iProver_top ),
% 4.09/1.03      inference(superposition,[status(thm)],[c_3426,c_2377]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_27,plain,
% 4.09/1.03      ( l1_pre_topc(sK1) = iProver_top ),
% 4.09/1.03      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_28,plain,
% 4.09/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 4.09/1.03      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_22,negated_conjecture,
% 4.09/1.03      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 4.09/1.03      inference(cnf_transformation,[],[f63]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_29,plain,
% 4.09/1.03      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 4.09/1.03      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_20,negated_conjecture,
% 4.09/1.03      ( r1_tarski(sK3,sK2) ),
% 4.09/1.03      inference(cnf_transformation,[],[f65]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_31,plain,
% 4.09/1.03      ( r1_tarski(sK3,sK2) = iProver_top ),
% 4.09/1.03      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_19,negated_conjecture,
% 4.09/1.03      ( v4_pre_topc(sK3,sK1) ),
% 4.09/1.03      inference(cnf_transformation,[],[f66]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_32,plain,
% 4.09/1.03      ( v4_pre_topc(sK3,sK1) = iProver_top ),
% 4.09/1.03      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_18,negated_conjecture,
% 4.09/1.03      ( ~ v2_compts_1(sK3,sK1) ),
% 4.09/1.03      inference(cnf_transformation,[],[f67]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_33,plain,
% 4.09/1.03      ( v2_compts_1(sK3,sK1) != iProver_top ),
% 4.09/1.03      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_3,plain,
% 4.09/1.03      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
% 4.09/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 4.09/1.03      | ~ l1_pre_topc(X0) ),
% 4.09/1.03      inference(cnf_transformation,[],[f45]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_2647,plain,
% 4.09/1.03      ( m1_pre_topc(k1_pre_topc(sK1,X0),sK1)
% 4.09/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 4.09/1.03      | ~ l1_pre_topc(sK1) ),
% 4.09/1.03      inference(instantiation,[status(thm)],[c_3]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_2813,plain,
% 4.09/1.03      ( m1_pre_topc(k1_pre_topc(sK1,sK2),sK1)
% 4.09/1.03      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 4.09/1.03      | ~ l1_pre_topc(sK1) ),
% 4.09/1.03      inference(instantiation,[status(thm)],[c_2647]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_2814,plain,
% 4.09/1.03      ( m1_pre_topc(k1_pre_topc(sK1,sK2),sK1) = iProver_top
% 4.09/1.03      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 4.09/1.03      | l1_pre_topc(sK1) != iProver_top ),
% 4.09/1.03      inference(predicate_to_equality,[status(thm)],[c_2813]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_2816,plain,
% 4.09/1.03      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 4.09/1.03      | ~ l1_pre_topc(sK1)
% 4.09/1.03      | u1_struct_0(k1_pre_topc(sK1,sK3)) = sK3 ),
% 4.09/1.03      inference(instantiation,[status(thm)],[c_2652]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_1736,plain,( X0 = X0 ),theory(equality) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_2825,plain,
% 4.09/1.03      ( sK3 = sK3 ),
% 4.09/1.03      inference(instantiation,[status(thm)],[c_1736]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_2839,plain,
% 4.09/1.03      ( k1_zfmisc_1(u1_struct_0(sK1)) = k1_zfmisc_1(u1_struct_0(sK1)) ),
% 4.09/1.03      inference(instantiation,[status(thm)],[c_1736]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_2866,plain,
% 4.09/1.03      ( sK1 = sK1 ),
% 4.09/1.03      inference(instantiation,[status(thm)],[c_1736]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_5,plain,
% 4.09/1.03      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 4.09/1.03      inference(cnf_transformation,[],[f47]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_2966,plain,
% 4.09/1.03      ( ~ m1_pre_topc(k1_pre_topc(sK1,sK2),sK1)
% 4.09/1.03      | l1_pre_topc(k1_pre_topc(sK1,sK2))
% 4.09/1.03      | ~ l1_pre_topc(sK1) ),
% 4.09/1.03      inference(instantiation,[status(thm)],[c_5]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_2967,plain,
% 4.09/1.03      ( m1_pre_topc(k1_pre_topc(sK1,sK2),sK1) != iProver_top
% 4.09/1.03      | l1_pre_topc(k1_pre_topc(sK1,sK2)) = iProver_top
% 4.09/1.03      | l1_pre_topc(sK1) != iProver_top ),
% 4.09/1.03      inference(predicate_to_equality,[status(thm)],[c_2966]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_1745,plain,
% 4.09/1.03      ( ~ v4_pre_topc(X0,X1) | v4_pre_topc(X2,X3) | X2 != X0 | X3 != X1 ),
% 4.09/1.03      theory(equality) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_2704,plain,
% 4.09/1.03      ( v4_pre_topc(X0,X1)
% 4.09/1.03      | ~ v4_pre_topc(sK3,sK1)
% 4.09/1.03      | X1 != sK1
% 4.09/1.03      | X0 != sK3 ),
% 4.09/1.03      inference(instantiation,[status(thm)],[c_1745]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_3002,plain,
% 4.09/1.03      ( v4_pre_topc(u1_struct_0(k1_pre_topc(sK1,sK3)),X0)
% 4.09/1.03      | ~ v4_pre_topc(sK3,sK1)
% 4.09/1.03      | X0 != sK1
% 4.09/1.03      | u1_struct_0(k1_pre_topc(sK1,sK3)) != sK3 ),
% 4.09/1.03      inference(instantiation,[status(thm)],[c_2704]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_3596,plain,
% 4.09/1.03      ( v4_pre_topc(u1_struct_0(k1_pre_topc(sK1,sK3)),sK1)
% 4.09/1.03      | ~ v4_pre_topc(sK3,sK1)
% 4.09/1.03      | u1_struct_0(k1_pre_topc(sK1,sK3)) != sK3
% 4.09/1.03      | sK1 != sK1 ),
% 4.09/1.03      inference(instantiation,[status(thm)],[c_3002]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_3597,plain,
% 4.09/1.03      ( u1_struct_0(k1_pre_topc(sK1,sK3)) != sK3
% 4.09/1.03      | sK1 != sK1
% 4.09/1.03      | v4_pre_topc(u1_struct_0(k1_pre_topc(sK1,sK3)),sK1) = iProver_top
% 4.09/1.03      | v4_pre_topc(sK3,sK1) != iProver_top ),
% 4.09/1.03      inference(predicate_to_equality,[status(thm)],[c_3596]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_1739,plain,
% 4.09/1.03      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 4.09/1.03      theory(equality) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_2689,plain,
% 4.09/1.03      ( m1_subset_1(X0,X1)
% 4.09/1.03      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 4.09/1.03      | X1 != k1_zfmisc_1(u1_struct_0(sK1))
% 4.09/1.03      | X0 != sK3 ),
% 4.09/1.03      inference(instantiation,[status(thm)],[c_1739]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_3004,plain,
% 4.09/1.03      ( m1_subset_1(u1_struct_0(k1_pre_topc(sK1,sK3)),X0)
% 4.09/1.03      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 4.09/1.03      | X0 != k1_zfmisc_1(u1_struct_0(sK1))
% 4.09/1.03      | u1_struct_0(k1_pre_topc(sK1,sK3)) != sK3 ),
% 4.09/1.03      inference(instantiation,[status(thm)],[c_2689]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_3680,plain,
% 4.09/1.03      ( m1_subset_1(u1_struct_0(k1_pre_topc(sK1,sK3)),k1_zfmisc_1(u1_struct_0(sK1)))
% 4.09/1.03      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 4.09/1.03      | u1_struct_0(k1_pre_topc(sK1,sK3)) != sK3
% 4.09/1.03      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
% 4.09/1.03      inference(instantiation,[status(thm)],[c_3004]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_3681,plain,
% 4.09/1.03      ( u1_struct_0(k1_pre_topc(sK1,sK3)) != sK3
% 4.09/1.03      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
% 4.09/1.03      | m1_subset_1(u1_struct_0(k1_pre_topc(sK1,sK3)),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 4.09/1.03      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 4.09/1.03      inference(predicate_to_equality,[status(thm)],[c_3680]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_1740,plain,
% 4.09/1.03      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 4.09/1.03      theory(equality) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_2699,plain,
% 4.09/1.03      ( r1_tarski(X0,X1) | ~ r1_tarski(sK3,sK2) | X1 != sK2 | X0 != sK3 ),
% 4.09/1.03      inference(instantiation,[status(thm)],[c_1740]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_3018,plain,
% 4.09/1.03      ( r1_tarski(sK3,X0)
% 4.09/1.03      | ~ r1_tarski(sK3,sK2)
% 4.09/1.03      | X0 != sK2
% 4.09/1.03      | sK3 != sK3 ),
% 4.09/1.03      inference(instantiation,[status(thm)],[c_2699]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_3696,plain,
% 4.09/1.03      ( r1_tarski(sK3,u1_struct_0(k1_pre_topc(sK1,sK2)))
% 4.09/1.03      | ~ r1_tarski(sK3,sK2)
% 4.09/1.03      | u1_struct_0(k1_pre_topc(sK1,sK2)) != sK2
% 4.09/1.03      | sK3 != sK3 ),
% 4.09/1.03      inference(instantiation,[status(thm)],[c_3018]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_3697,plain,
% 4.09/1.03      ( u1_struct_0(k1_pre_topc(sK1,sK2)) != sK2
% 4.09/1.03      | sK3 != sK3
% 4.09/1.03      | r1_tarski(sK3,u1_struct_0(k1_pre_topc(sK1,sK2))) = iProver_top
% 4.09/1.03      | r1_tarski(sK3,sK2) != iProver_top ),
% 4.09/1.03      inference(predicate_to_equality,[status(thm)],[c_3696]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_4,plain,
% 4.09/1.03      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 4.09/1.03      inference(cnf_transformation,[],[f46]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_2,plain,
% 4.09/1.03      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 4.09/1.03      inference(cnf_transformation,[],[f44]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_328,plain,
% 4.09/1.03      ( ~ l1_pre_topc(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 4.09/1.03      inference(resolution,[status(thm)],[c_4,c_2]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_3400,plain,
% 4.09/1.03      ( ~ l1_pre_topc(k1_pre_topc(sK1,X0))
% 4.09/1.03      | u1_struct_0(k1_pre_topc(sK1,X0)) = k2_struct_0(k1_pre_topc(sK1,X0)) ),
% 4.09/1.03      inference(instantiation,[status(thm)],[c_328]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_4151,plain,
% 4.09/1.03      ( ~ l1_pre_topc(k1_pre_topc(sK1,sK2))
% 4.09/1.03      | u1_struct_0(k1_pre_topc(sK1,sK2)) = k2_struct_0(k1_pre_topc(sK1,sK2)) ),
% 4.09/1.03      inference(instantiation,[status(thm)],[c_3400]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_1737,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_3351,plain,
% 4.09/1.03      ( X0 != X1 | sK3 != X1 | sK3 = X0 ),
% 4.09/1.03      inference(instantiation,[status(thm)],[c_1737]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_4277,plain,
% 4.09/1.03      ( X0 != sK3 | sK3 = X0 | sK3 != sK3 ),
% 4.09/1.03      inference(instantiation,[status(thm)],[c_3351]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_4963,plain,
% 4.09/1.03      ( u1_struct_0(k1_pre_topc(sK1,sK3)) != sK3
% 4.09/1.03      | sK3 = u1_struct_0(k1_pre_topc(sK1,sK3))
% 4.09/1.03      | sK3 != sK3 ),
% 4.09/1.03      inference(instantiation,[status(thm)],[c_4277]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_1746,plain,
% 4.09/1.03      ( ~ v2_compts_1(X0,X1) | v2_compts_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 4.09/1.03      theory(equality) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_3190,plain,
% 4.09/1.03      ( v2_compts_1(X0,X1)
% 4.09/1.03      | ~ v2_compts_1(X2,sK1)
% 4.09/1.03      | X0 != X2
% 4.09/1.03      | X1 != sK1 ),
% 4.09/1.03      inference(instantiation,[status(thm)],[c_1746]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_4414,plain,
% 4.09/1.03      ( ~ v2_compts_1(X0,sK1)
% 4.09/1.03      | v2_compts_1(X1,sK1)
% 4.09/1.03      | X1 != X0
% 4.09/1.03      | sK1 != sK1 ),
% 4.09/1.03      inference(instantiation,[status(thm)],[c_3190]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_5294,plain,
% 4.09/1.03      ( ~ v2_compts_1(X0,sK1)
% 4.09/1.03      | v2_compts_1(sK3,sK1)
% 4.09/1.03      | sK1 != sK1
% 4.09/1.03      | sK3 != X0 ),
% 4.09/1.03      inference(instantiation,[status(thm)],[c_4414]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_5542,plain,
% 4.09/1.03      ( ~ v2_compts_1(u1_struct_0(k1_pre_topc(sK1,sK3)),sK1)
% 4.09/1.03      | v2_compts_1(sK3,sK1)
% 4.09/1.03      | sK1 != sK1
% 4.09/1.03      | sK3 != u1_struct_0(k1_pre_topc(sK1,sK3)) ),
% 4.09/1.03      inference(instantiation,[status(thm)],[c_5294]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_5543,plain,
% 4.09/1.03      ( sK1 != sK1
% 4.09/1.03      | sK3 != u1_struct_0(k1_pre_topc(sK1,sK3))
% 4.09/1.03      | v2_compts_1(u1_struct_0(k1_pre_topc(sK1,sK3)),sK1) != iProver_top
% 4.09/1.03      | v2_compts_1(sK3,sK1) = iProver_top ),
% 4.09/1.03      inference(predicate_to_equality,[status(thm)],[c_5542]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_4563,plain,
% 4.09/1.03      ( r1_tarski(X0,X1)
% 4.09/1.03      | ~ r1_tarski(sK3,u1_struct_0(k1_pre_topc(sK1,sK2)))
% 4.09/1.03      | X1 != u1_struct_0(k1_pre_topc(sK1,sK2))
% 4.09/1.03      | X0 != sK3 ),
% 4.09/1.03      inference(instantiation,[status(thm)],[c_1740]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_5853,plain,
% 4.09/1.03      ( r1_tarski(u1_struct_0(k1_pre_topc(sK1,sK3)),X0)
% 4.09/1.03      | ~ r1_tarski(sK3,u1_struct_0(k1_pre_topc(sK1,sK2)))
% 4.09/1.03      | X0 != u1_struct_0(k1_pre_topc(sK1,sK2))
% 4.09/1.03      | u1_struct_0(k1_pre_topc(sK1,sK3)) != sK3 ),
% 4.09/1.03      inference(instantiation,[status(thm)],[c_4563]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_6287,plain,
% 4.09/1.03      ( r1_tarski(u1_struct_0(k1_pre_topc(sK1,sK3)),k2_struct_0(k1_pre_topc(sK1,sK2)))
% 4.09/1.03      | ~ r1_tarski(sK3,u1_struct_0(k1_pre_topc(sK1,sK2)))
% 4.09/1.03      | u1_struct_0(k1_pre_topc(sK1,sK3)) != sK3
% 4.09/1.03      | k2_struct_0(k1_pre_topc(sK1,sK2)) != u1_struct_0(k1_pre_topc(sK1,sK2)) ),
% 4.09/1.03      inference(instantiation,[status(thm)],[c_5853]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_6292,plain,
% 4.09/1.03      ( u1_struct_0(k1_pre_topc(sK1,sK3)) != sK3
% 4.09/1.03      | k2_struct_0(k1_pre_topc(sK1,sK2)) != u1_struct_0(k1_pre_topc(sK1,sK2))
% 4.09/1.03      | r1_tarski(u1_struct_0(k1_pre_topc(sK1,sK3)),k2_struct_0(k1_pre_topc(sK1,sK2))) = iProver_top
% 4.09/1.03      | r1_tarski(sK3,u1_struct_0(k1_pre_topc(sK1,sK2))) != iProver_top ),
% 4.09/1.03      inference(predicate_to_equality,[status(thm)],[c_6287]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_11,plain,
% 4.09/1.03      ( v2_compts_1(X0,X1)
% 4.09/1.03      | ~ m1_pre_topc(X2,X1)
% 4.09/1.03      | ~ r1_tarski(X0,k2_struct_0(X2))
% 4.09/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.09/1.03      | m1_subset_1(sK0(X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
% 4.09/1.03      | ~ l1_pre_topc(X1) ),
% 4.09/1.03      inference(cnf_transformation,[],[f52]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_2978,plain,
% 4.09/1.03      ( v2_compts_1(X0,sK1)
% 4.09/1.03      | ~ m1_pre_topc(k1_pre_topc(sK1,sK2),sK1)
% 4.09/1.03      | ~ r1_tarski(X0,k2_struct_0(k1_pre_topc(sK1,sK2)))
% 4.09/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 4.09/1.03      | m1_subset_1(sK0(k1_pre_topc(sK1,sK2),X0),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK1,sK2))))
% 4.09/1.03      | ~ l1_pre_topc(sK1) ),
% 4.09/1.03      inference(instantiation,[status(thm)],[c_11]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_6291,plain,
% 4.09/1.03      ( v2_compts_1(u1_struct_0(k1_pre_topc(sK1,sK3)),sK1)
% 4.09/1.03      | ~ m1_pre_topc(k1_pre_topc(sK1,sK2),sK1)
% 4.09/1.03      | ~ r1_tarski(u1_struct_0(k1_pre_topc(sK1,sK3)),k2_struct_0(k1_pre_topc(sK1,sK2)))
% 4.09/1.03      | m1_subset_1(sK0(k1_pre_topc(sK1,sK2),u1_struct_0(k1_pre_topc(sK1,sK3))),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK1,sK2))))
% 4.09/1.03      | ~ m1_subset_1(u1_struct_0(k1_pre_topc(sK1,sK3)),k1_zfmisc_1(u1_struct_0(sK1)))
% 4.09/1.03      | ~ l1_pre_topc(sK1) ),
% 4.09/1.03      inference(instantiation,[status(thm)],[c_2978]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_6294,plain,
% 4.09/1.03      ( v2_compts_1(u1_struct_0(k1_pre_topc(sK1,sK3)),sK1) = iProver_top
% 4.09/1.03      | m1_pre_topc(k1_pre_topc(sK1,sK2),sK1) != iProver_top
% 4.09/1.03      | r1_tarski(u1_struct_0(k1_pre_topc(sK1,sK3)),k2_struct_0(k1_pre_topc(sK1,sK2))) != iProver_top
% 4.09/1.03      | m1_subset_1(sK0(k1_pre_topc(sK1,sK2),u1_struct_0(k1_pre_topc(sK1,sK3))),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK1,sK2)))) = iProver_top
% 4.09/1.03      | m1_subset_1(u1_struct_0(k1_pre_topc(sK1,sK3)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 4.09/1.03      | l1_pre_topc(sK1) != iProver_top ),
% 4.09/1.03      inference(predicate_to_equality,[status(thm)],[c_6291]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_9,plain,
% 4.09/1.03      ( v2_compts_1(X0,X1)
% 4.09/1.03      | ~ v2_compts_1(sK0(X2,X0),X2)
% 4.09/1.03      | ~ m1_pre_topc(X2,X1)
% 4.09/1.03      | ~ r1_tarski(X0,k2_struct_0(X2))
% 4.09/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.09/1.03      | ~ l1_pre_topc(X1) ),
% 4.09/1.03      inference(cnf_transformation,[],[f54]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_2980,plain,
% 4.09/1.03      ( v2_compts_1(X0,sK1)
% 4.09/1.03      | ~ v2_compts_1(sK0(k1_pre_topc(sK1,sK2),X0),k1_pre_topc(sK1,sK2))
% 4.09/1.03      | ~ m1_pre_topc(k1_pre_topc(sK1,sK2),sK1)
% 4.09/1.03      | ~ r1_tarski(X0,k2_struct_0(k1_pre_topc(sK1,sK2)))
% 4.09/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 4.09/1.03      | ~ l1_pre_topc(sK1) ),
% 4.09/1.03      inference(instantiation,[status(thm)],[c_9]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_6290,plain,
% 4.09/1.03      ( ~ v2_compts_1(sK0(k1_pre_topc(sK1,sK2),u1_struct_0(k1_pre_topc(sK1,sK3))),k1_pre_topc(sK1,sK2))
% 4.09/1.03      | v2_compts_1(u1_struct_0(k1_pre_topc(sK1,sK3)),sK1)
% 4.09/1.03      | ~ m1_pre_topc(k1_pre_topc(sK1,sK2),sK1)
% 4.09/1.03      | ~ r1_tarski(u1_struct_0(k1_pre_topc(sK1,sK3)),k2_struct_0(k1_pre_topc(sK1,sK2)))
% 4.09/1.03      | ~ m1_subset_1(u1_struct_0(k1_pre_topc(sK1,sK3)),k1_zfmisc_1(u1_struct_0(sK1)))
% 4.09/1.03      | ~ l1_pre_topc(sK1) ),
% 4.09/1.03      inference(instantiation,[status(thm)],[c_2980]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_6296,plain,
% 4.09/1.03      ( v2_compts_1(sK0(k1_pre_topc(sK1,sK2),u1_struct_0(k1_pre_topc(sK1,sK3))),k1_pre_topc(sK1,sK2)) != iProver_top
% 4.09/1.03      | v2_compts_1(u1_struct_0(k1_pre_topc(sK1,sK3)),sK1) = iProver_top
% 4.09/1.03      | m1_pre_topc(k1_pre_topc(sK1,sK2),sK1) != iProver_top
% 4.09/1.03      | r1_tarski(u1_struct_0(k1_pre_topc(sK1,sK3)),k2_struct_0(k1_pre_topc(sK1,sK2))) != iProver_top
% 4.09/1.03      | m1_subset_1(u1_struct_0(k1_pre_topc(sK1,sK3)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 4.09/1.03      | l1_pre_topc(sK1) != iProver_top ),
% 4.09/1.03      inference(predicate_to_equality,[status(thm)],[c_6290]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_10,plain,
% 4.09/1.03      ( v2_compts_1(X0,X1)
% 4.09/1.03      | ~ m1_pre_topc(X2,X1)
% 4.09/1.03      | ~ r1_tarski(X0,k2_struct_0(X2))
% 4.09/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.09/1.03      | ~ l1_pre_topc(X1)
% 4.09/1.03      | sK0(X2,X0) = X0 ),
% 4.09/1.03      inference(cnf_transformation,[],[f53]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_2979,plain,
% 4.09/1.03      ( v2_compts_1(X0,sK1)
% 4.09/1.03      | ~ m1_pre_topc(k1_pre_topc(sK1,sK2),sK1)
% 4.09/1.03      | ~ r1_tarski(X0,k2_struct_0(k1_pre_topc(sK1,sK2)))
% 4.09/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 4.09/1.03      | ~ l1_pre_topc(sK1)
% 4.09/1.03      | sK0(k1_pre_topc(sK1,sK2),X0) = X0 ),
% 4.09/1.03      inference(instantiation,[status(thm)],[c_10]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_6288,plain,
% 4.09/1.03      ( v2_compts_1(u1_struct_0(k1_pre_topc(sK1,sK3)),sK1)
% 4.09/1.03      | ~ m1_pre_topc(k1_pre_topc(sK1,sK2),sK1)
% 4.09/1.03      | ~ r1_tarski(u1_struct_0(k1_pre_topc(sK1,sK3)),k2_struct_0(k1_pre_topc(sK1,sK2)))
% 4.09/1.03      | ~ m1_subset_1(u1_struct_0(k1_pre_topc(sK1,sK3)),k1_zfmisc_1(u1_struct_0(sK1)))
% 4.09/1.03      | ~ l1_pre_topc(sK1)
% 4.09/1.03      | sK0(k1_pre_topc(sK1,sK2),u1_struct_0(k1_pre_topc(sK1,sK3))) = u1_struct_0(k1_pre_topc(sK1,sK3)) ),
% 4.09/1.03      inference(instantiation,[status(thm)],[c_2979]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_6300,plain,
% 4.09/1.03      ( sK0(k1_pre_topc(sK1,sK2),u1_struct_0(k1_pre_topc(sK1,sK3))) = u1_struct_0(k1_pre_topc(sK1,sK3))
% 4.09/1.03      | v2_compts_1(u1_struct_0(k1_pre_topc(sK1,sK3)),sK1) = iProver_top
% 4.09/1.03      | m1_pre_topc(k1_pre_topc(sK1,sK2),sK1) != iProver_top
% 4.09/1.03      | r1_tarski(u1_struct_0(k1_pre_topc(sK1,sK3)),k2_struct_0(k1_pre_topc(sK1,sK2))) != iProver_top
% 4.09/1.03      | m1_subset_1(u1_struct_0(k1_pre_topc(sK1,sK3)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 4.09/1.03      | l1_pre_topc(sK1) != iProver_top ),
% 4.09/1.03      inference(predicate_to_equality,[status(thm)],[c_6288]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_5316,plain,
% 4.09/1.03      ( X0 != X1
% 4.09/1.03      | X0 = u1_struct_0(k1_pre_topc(sK1,sK2))
% 4.09/1.03      | u1_struct_0(k1_pre_topc(sK1,sK2)) != X1 ),
% 4.09/1.03      inference(instantiation,[status(thm)],[c_1737]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_7742,plain,
% 4.09/1.03      ( X0 = u1_struct_0(k1_pre_topc(sK1,sK2))
% 4.09/1.03      | X0 != k2_struct_0(k1_pre_topc(sK1,sK2))
% 4.09/1.03      | u1_struct_0(k1_pre_topc(sK1,sK2)) != k2_struct_0(k1_pre_topc(sK1,sK2)) ),
% 4.09/1.03      inference(instantiation,[status(thm)],[c_5316]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_9661,plain,
% 4.09/1.03      ( u1_struct_0(k1_pre_topc(sK1,sK2)) != k2_struct_0(k1_pre_topc(sK1,sK2))
% 4.09/1.03      | k2_struct_0(k1_pre_topc(sK1,sK2)) = u1_struct_0(k1_pre_topc(sK1,sK2))
% 4.09/1.03      | k2_struct_0(k1_pre_topc(sK1,sK2)) != k2_struct_0(k1_pre_topc(sK1,sK2)) ),
% 4.09/1.03      inference(instantiation,[status(thm)],[c_7742]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_9662,plain,
% 4.09/1.03      ( k2_struct_0(k1_pre_topc(sK1,sK2)) = k2_struct_0(k1_pre_topc(sK1,sK2)) ),
% 4.09/1.03      inference(instantiation,[status(thm)],[c_1736]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_4611,plain,
% 4.09/1.03      ( v4_pre_topc(X0,X1)
% 4.09/1.03      | ~ v4_pre_topc(u1_struct_0(k1_pre_topc(sK1,sK3)),sK1)
% 4.09/1.03      | X0 != u1_struct_0(k1_pre_topc(sK1,sK3))
% 4.09/1.03      | X1 != sK1 ),
% 4.09/1.03      inference(instantiation,[status(thm)],[c_1745]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_7552,plain,
% 4.09/1.03      ( v4_pre_topc(X0,sK1)
% 4.09/1.03      | ~ v4_pre_topc(u1_struct_0(k1_pre_topc(sK1,sK3)),sK1)
% 4.09/1.03      | X0 != u1_struct_0(k1_pre_topc(sK1,sK3))
% 4.09/1.03      | sK1 != sK1 ),
% 4.09/1.03      inference(instantiation,[status(thm)],[c_4611]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_13655,plain,
% 4.09/1.03      ( v4_pre_topc(sK0(k1_pre_topc(sK1,sK2),u1_struct_0(k1_pre_topc(sK1,sK3))),sK1)
% 4.09/1.03      | ~ v4_pre_topc(u1_struct_0(k1_pre_topc(sK1,sK3)),sK1)
% 4.09/1.03      | sK0(k1_pre_topc(sK1,sK2),u1_struct_0(k1_pre_topc(sK1,sK3))) != u1_struct_0(k1_pre_topc(sK1,sK3))
% 4.09/1.03      | sK1 != sK1 ),
% 4.09/1.03      inference(instantiation,[status(thm)],[c_7552]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_13682,plain,
% 4.09/1.03      ( sK0(k1_pre_topc(sK1,sK2),u1_struct_0(k1_pre_topc(sK1,sK3))) != u1_struct_0(k1_pre_topc(sK1,sK3))
% 4.09/1.03      | sK1 != sK1
% 4.09/1.03      | v4_pre_topc(sK0(k1_pre_topc(sK1,sK2),u1_struct_0(k1_pre_topc(sK1,sK3))),sK1) = iProver_top
% 4.09/1.03      | v4_pre_topc(u1_struct_0(k1_pre_topc(sK1,sK3)),sK1) != iProver_top ),
% 4.09/1.03      inference(predicate_to_equality,[status(thm)],[c_13655]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_3111,plain,
% 4.09/1.03      ( m1_subset_1(X0,X1)
% 4.09/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
% 4.09/1.03      | X0 != X2
% 4.09/1.03      | X1 != k1_zfmisc_1(u1_struct_0(sK1)) ),
% 4.09/1.03      inference(instantiation,[status(thm)],[c_1739]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_4910,plain,
% 4.09/1.03      ( m1_subset_1(X0,X1)
% 4.09/1.03      | ~ m1_subset_1(u1_struct_0(k1_pre_topc(sK1,sK3)),k1_zfmisc_1(u1_struct_0(sK1)))
% 4.09/1.03      | X0 != u1_struct_0(k1_pre_topc(sK1,sK3))
% 4.09/1.03      | X1 != k1_zfmisc_1(u1_struct_0(sK1)) ),
% 4.09/1.03      inference(instantiation,[status(thm)],[c_3111]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_7703,plain,
% 4.09/1.03      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 4.09/1.03      | ~ m1_subset_1(u1_struct_0(k1_pre_topc(sK1,sK3)),k1_zfmisc_1(u1_struct_0(sK1)))
% 4.09/1.03      | X0 != u1_struct_0(k1_pre_topc(sK1,sK3))
% 4.09/1.03      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
% 4.09/1.03      inference(instantiation,[status(thm)],[c_4910]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_13654,plain,
% 4.09/1.03      ( m1_subset_1(sK0(k1_pre_topc(sK1,sK2),u1_struct_0(k1_pre_topc(sK1,sK3))),k1_zfmisc_1(u1_struct_0(sK1)))
% 4.09/1.03      | ~ m1_subset_1(u1_struct_0(k1_pre_topc(sK1,sK3)),k1_zfmisc_1(u1_struct_0(sK1)))
% 4.09/1.03      | sK0(k1_pre_topc(sK1,sK2),u1_struct_0(k1_pre_topc(sK1,sK3))) != u1_struct_0(k1_pre_topc(sK1,sK3))
% 4.09/1.03      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
% 4.09/1.03      inference(instantiation,[status(thm)],[c_7703]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_13684,plain,
% 4.09/1.03      ( sK0(k1_pre_topc(sK1,sK2),u1_struct_0(k1_pre_topc(sK1,sK3))) != u1_struct_0(k1_pre_topc(sK1,sK3))
% 4.09/1.03      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
% 4.09/1.03      | m1_subset_1(sK0(k1_pre_topc(sK1,sK2),u1_struct_0(k1_pre_topc(sK1,sK3))),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 4.09/1.03      | m1_subset_1(u1_struct_0(k1_pre_topc(sK1,sK3)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 4.09/1.03      inference(predicate_to_equality,[status(thm)],[c_13654]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_8,plain,
% 4.09/1.03      ( ~ v4_pre_topc(X0,X1)
% 4.09/1.03      | v4_pre_topc(X0,X2)
% 4.09/1.03      | ~ m1_pre_topc(X2,X1)
% 4.09/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
% 4.09/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.09/1.03      | ~ l1_pre_topc(X1) ),
% 4.09/1.03      inference(cnf_transformation,[],[f68]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_3138,plain,
% 4.09/1.03      ( v4_pre_topc(X0,k1_pre_topc(sK1,X1))
% 4.09/1.03      | ~ v4_pre_topc(X0,sK1)
% 4.09/1.03      | ~ m1_pre_topc(k1_pre_topc(sK1,X1),sK1)
% 4.09/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK1,X1))))
% 4.09/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 4.09/1.03      | ~ l1_pre_topc(sK1) ),
% 4.09/1.03      inference(instantiation,[status(thm)],[c_8]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_13704,plain,
% 4.09/1.03      ( v4_pre_topc(sK0(k1_pre_topc(sK1,sK2),u1_struct_0(k1_pre_topc(sK1,sK3))),k1_pre_topc(sK1,sK2))
% 4.09/1.03      | ~ v4_pre_topc(sK0(k1_pre_topc(sK1,sK2),u1_struct_0(k1_pre_topc(sK1,sK3))),sK1)
% 4.09/1.03      | ~ m1_pre_topc(k1_pre_topc(sK1,sK2),sK1)
% 4.09/1.03      | ~ m1_subset_1(sK0(k1_pre_topc(sK1,sK2),u1_struct_0(k1_pre_topc(sK1,sK3))),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK1,sK2))))
% 4.09/1.03      | ~ m1_subset_1(sK0(k1_pre_topc(sK1,sK2),u1_struct_0(k1_pre_topc(sK1,sK3))),k1_zfmisc_1(u1_struct_0(sK1)))
% 4.09/1.03      | ~ l1_pre_topc(sK1) ),
% 4.09/1.03      inference(instantiation,[status(thm)],[c_3138]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_13705,plain,
% 4.09/1.03      ( v4_pre_topc(sK0(k1_pre_topc(sK1,sK2),u1_struct_0(k1_pre_topc(sK1,sK3))),k1_pre_topc(sK1,sK2)) = iProver_top
% 4.09/1.03      | v4_pre_topc(sK0(k1_pre_topc(sK1,sK2),u1_struct_0(k1_pre_topc(sK1,sK3))),sK1) != iProver_top
% 4.09/1.03      | m1_pre_topc(k1_pre_topc(sK1,sK2),sK1) != iProver_top
% 4.09/1.03      | m1_subset_1(sK0(k1_pre_topc(sK1,sK2),u1_struct_0(k1_pre_topc(sK1,sK3))),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK1,sK2)))) != iProver_top
% 4.09/1.03      | m1_subset_1(sK0(k1_pre_topc(sK1,sK2),u1_struct_0(k1_pre_topc(sK1,sK3))),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 4.09/1.03      | l1_pre_topc(sK1) != iProver_top ),
% 4.09/1.03      inference(predicate_to_equality,[status(thm)],[c_13704]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_3577,plain,
% 4.09/1.03      ( v2_compts_1(X0,k1_pre_topc(sK1,sK2))
% 4.09/1.03      | ~ v4_pre_topc(X0,k1_pre_topc(sK1,sK2))
% 4.09/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK1,sK2))))
% 4.09/1.03      | ~ v1_compts_1(k1_pre_topc(sK1,sK2))
% 4.09/1.03      | ~ l1_pre_topc(k1_pre_topc(sK1,sK2)) ),
% 4.09/1.03      inference(instantiation,[status(thm)],[c_17]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_16728,plain,
% 4.09/1.03      ( v2_compts_1(sK0(k1_pre_topc(sK1,sK2),u1_struct_0(k1_pre_topc(sK1,sK3))),k1_pre_topc(sK1,sK2))
% 4.09/1.03      | ~ v4_pre_topc(sK0(k1_pre_topc(sK1,sK2),u1_struct_0(k1_pre_topc(sK1,sK3))),k1_pre_topc(sK1,sK2))
% 4.09/1.03      | ~ m1_subset_1(sK0(k1_pre_topc(sK1,sK2),u1_struct_0(k1_pre_topc(sK1,sK3))),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK1,sK2))))
% 4.09/1.03      | ~ v1_compts_1(k1_pre_topc(sK1,sK2))
% 4.09/1.03      | ~ l1_pre_topc(k1_pre_topc(sK1,sK2)) ),
% 4.09/1.03      inference(instantiation,[status(thm)],[c_3577]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_16729,plain,
% 4.09/1.03      ( v2_compts_1(sK0(k1_pre_topc(sK1,sK2),u1_struct_0(k1_pre_topc(sK1,sK3))),k1_pre_topc(sK1,sK2)) = iProver_top
% 4.09/1.03      | v4_pre_topc(sK0(k1_pre_topc(sK1,sK2),u1_struct_0(k1_pre_topc(sK1,sK3))),k1_pre_topc(sK1,sK2)) != iProver_top
% 4.09/1.03      | m1_subset_1(sK0(k1_pre_topc(sK1,sK2),u1_struct_0(k1_pre_topc(sK1,sK3))),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK1,sK2)))) != iProver_top
% 4.09/1.03      | v1_compts_1(k1_pre_topc(sK1,sK2)) != iProver_top
% 4.09/1.03      | l1_pre_topc(k1_pre_topc(sK1,sK2)) != iProver_top ),
% 4.09/1.03      inference(predicate_to_equality,[status(thm)],[c_16728]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_17929,plain,
% 4.09/1.03      ( v1_compts_1(k1_pre_topc(sK1,sK2)) != iProver_top ),
% 4.09/1.03      inference(global_propositional_subsumption,
% 4.09/1.03                [status(thm)],
% 4.09/1.03                [c_4640,c_24,c_27,c_23,c_28,c_22,c_29,c_31,c_32,c_33,
% 4.09/1.03                 c_2813,c_2814,c_2816,c_2819,c_2825,c_2839,c_2866,c_2966,
% 4.09/1.03                 c_2967,c_3597,c_3681,c_3697,c_4151,c_4963,c_5543,c_6292,
% 4.09/1.03                 c_6294,c_6296,c_6300,c_9661,c_9662,c_13682,c_13684,
% 4.09/1.03                 c_13705,c_16729]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_17934,plain,
% 4.09/1.03      ( sK2 = k1_xboole_0 ),
% 4.09/1.03      inference(superposition,[status(thm)],[c_3519,c_17929]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_18177,plain,
% 4.09/1.03      ( v1_compts_1(k1_pre_topc(sK1,k1_xboole_0)) != iProver_top ),
% 4.09/1.03      inference(demodulation,[status(thm)],[c_17934,c_17929]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_16,plain,
% 4.09/1.03      ( ~ v2_compts_1(k1_xboole_0,X0)
% 4.09/1.03      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
% 4.09/1.03      | v1_compts_1(k1_pre_topc(X0,k1_xboole_0))
% 4.09/1.03      | ~ l1_pre_topc(X0) ),
% 4.09/1.03      inference(cnf_transformation,[],[f71]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_3196,plain,
% 4.09/1.03      ( ~ v2_compts_1(k1_xboole_0,sK1)
% 4.09/1.03      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1)))
% 4.09/1.03      | v1_compts_1(k1_pre_topc(sK1,k1_xboole_0))
% 4.09/1.03      | ~ l1_pre_topc(sK1) ),
% 4.09/1.03      inference(instantiation,[status(thm)],[c_16]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_3199,plain,
% 4.09/1.03      ( v2_compts_1(k1_xboole_0,sK1) != iProver_top
% 4.09/1.03      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 4.09/1.03      | v1_compts_1(k1_pre_topc(sK1,k1_xboole_0)) = iProver_top
% 4.09/1.03      | l1_pre_topc(sK1) != iProver_top ),
% 4.09/1.03      inference(predicate_to_equality,[status(thm)],[c_3196]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_2709,plain,
% 4.09/1.03      ( v2_compts_1(X0,X1)
% 4.09/1.03      | ~ v2_compts_1(sK2,sK1)
% 4.09/1.03      | X0 != sK2
% 4.09/1.03      | X1 != sK1 ),
% 4.09/1.03      inference(instantiation,[status(thm)],[c_1746]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_2865,plain,
% 4.09/1.03      ( v2_compts_1(X0,sK1)
% 4.09/1.03      | ~ v2_compts_1(sK2,sK1)
% 4.09/1.03      | X0 != sK2
% 4.09/1.03      | sK1 != sK1 ),
% 4.09/1.03      inference(instantiation,[status(thm)],[c_2709]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_2867,plain,
% 4.09/1.03      ( X0 != sK2
% 4.09/1.03      | sK1 != sK1
% 4.09/1.03      | v2_compts_1(X0,sK1) = iProver_top
% 4.09/1.03      | v2_compts_1(sK2,sK1) != iProver_top ),
% 4.09/1.03      inference(predicate_to_equality,[status(thm)],[c_2865]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_2869,plain,
% 4.09/1.03      ( sK1 != sK1
% 4.09/1.03      | k1_xboole_0 != sK2
% 4.09/1.03      | v2_compts_1(sK2,sK1) != iProver_top
% 4.09/1.03      | v2_compts_1(k1_xboole_0,sK1) = iProver_top ),
% 4.09/1.03      inference(instantiation,[status(thm)],[c_2867]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_2694,plain,
% 4.09/1.03      ( m1_subset_1(X0,X1)
% 4.09/1.03      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 4.09/1.03      | X1 != k1_zfmisc_1(u1_struct_0(sK1))
% 4.09/1.03      | X0 != sK2 ),
% 4.09/1.03      inference(instantiation,[status(thm)],[c_1739]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_2838,plain,
% 4.09/1.03      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 4.09/1.03      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 4.09/1.03      | X0 != sK2
% 4.09/1.03      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
% 4.09/1.03      inference(instantiation,[status(thm)],[c_2694]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_2840,plain,
% 4.09/1.03      ( X0 != sK2
% 4.09/1.03      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
% 4.09/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 4.09/1.03      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 4.09/1.03      inference(predicate_to_equality,[status(thm)],[c_2838]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_2842,plain,
% 4.09/1.03      ( k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
% 4.09/1.03      | k1_xboole_0 != sK2
% 4.09/1.03      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 4.09/1.03      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 4.09/1.03      inference(instantiation,[status(thm)],[c_2840]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(c_2676,plain,
% 4.09/1.03      ( ~ v2_compts_1(sK2,sK1)
% 4.09/1.03      | v1_compts_1(k1_pre_topc(sK1,sK2))
% 4.09/1.03      | k1_xboole_0 = sK2 ),
% 4.09/1.03      inference(resolution,[status(thm)],[c_348,c_23]) ).
% 4.09/1.03  
% 4.09/1.03  cnf(contradiction,plain,
% 4.09/1.03      ( $false ),
% 4.09/1.03      inference(minisat,
% 4.09/1.03                [status(thm)],
% 4.09/1.03                [c_18177,c_16728,c_13704,c_13654,c_13655,c_9662,c_9661,
% 4.09/1.03                 c_6300,c_6290,c_6291,c_6292,c_6287,c_5543,c_5542,c_4963,
% 4.09/1.03                 c_4151,c_3697,c_3696,c_3681,c_3680,c_3596,c_3199,c_2966,
% 4.09/1.03                 c_2866,c_2869,c_2839,c_2842,c_2825,c_2819,c_2816,c_2814,
% 4.09/1.03                 c_2813,c_2676,c_33,c_18,c_19,c_31,c_20,c_30,c_21,c_29,
% 4.09/1.03                 c_22,c_28,c_23,c_27,c_24]) ).
% 4.09/1.03  
% 4.09/1.03  
% 4.09/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 4.09/1.03  
% 4.09/1.03  ------                               Statistics
% 4.09/1.03  
% 4.09/1.03  ------ Selected
% 4.09/1.03  
% 4.09/1.03  total_time:                             0.512
% 4.09/1.03  
%------------------------------------------------------------------------------
