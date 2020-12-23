%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1241+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:13 EST 2020

% Result     : Theorem 2.47s
% Output     : CNFRefutation 2.47s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 336 expanded)
%              Number of clauses        :   73 ( 110 expanded)
%              Number of leaves         :   14 ( 111 expanded)
%              Depth                    :   17
%              Number of atoms          :  356 (2293 expanded)
%              Number of equality atoms :  130 ( 627 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( k1_tops_1(X0,X2) = X2
                     => v3_pre_topc(X2,X0) )
                    & ( v3_pre_topc(X3,X1)
                     => k1_tops_1(X1,X3) = X3 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( ( k1_tops_1(X0,X2) = X2
                       => v3_pre_topc(X2,X0) )
                      & ( v3_pre_topc(X3,X1)
                       => k1_tops_1(X1,X3) = X3 ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ~ v3_pre_topc(X2,X0)
                      & k1_tops_1(X0,X2) = X2 )
                    | ( k1_tops_1(X1,X3) != X3
                      & v3_pre_topc(X3,X1) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ~ v3_pre_topc(X2,X0)
                      & k1_tops_1(X0,X2) = X2 )
                    | ( k1_tops_1(X1,X3) != X3
                      & v3_pre_topc(X3,X1) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( ( ~ v3_pre_topc(X2,X0)
              & k1_tops_1(X0,X2) = X2 )
            | ( k1_tops_1(X1,X3) != X3
              & v3_pre_topc(X3,X1) ) )
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ( ( ~ v3_pre_topc(X2,X0)
            & k1_tops_1(X0,X2) = X2 )
          | ( k1_tops_1(X1,sK3) != sK3
            & v3_pre_topc(sK3,X1) ) )
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ( ( ~ v3_pre_topc(X2,X0)
                  & k1_tops_1(X0,X2) = X2 )
                | ( k1_tops_1(X1,X3) != X3
                  & v3_pre_topc(X3,X1) ) )
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X3] :
            ( ( ( ~ v3_pre_topc(sK2,X0)
                & k1_tops_1(X0,sK2) = sK2 )
              | ( k1_tops_1(X1,X3) != X3
                & v3_pre_topc(X3,X1) ) )
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ~ v3_pre_topc(X2,X0)
                      & k1_tops_1(X0,X2) = X2 )
                    | ( k1_tops_1(X1,X3) != X3
                      & v3_pre_topc(X3,X1) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & l1_pre_topc(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ( ( ~ v3_pre_topc(X2,X0)
                    & k1_tops_1(X0,X2) = X2 )
                  | ( k1_tops_1(sK1,X3) != X3
                    & v3_pre_topc(X3,sK1) ) )
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ( ~ v3_pre_topc(X2,X0)
                        & k1_tops_1(X0,X2) = X2 )
                      | ( k1_tops_1(X1,X3) != X3
                        & v3_pre_topc(X3,X1) ) )
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & l1_pre_topc(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ~ v3_pre_topc(X2,sK0)
                      & k1_tops_1(sK0,X2) = X2 )
                    | ( k1_tops_1(X1,X3) != X3
                      & v3_pre_topc(X3,X1) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ( ( ~ v3_pre_topc(sK2,sK0)
        & k1_tops_1(sK0,sK2) = sK2 )
      | ( k1_tops_1(sK1,sK3) != sK3
        & v3_pre_topc(sK3,sK1) ) )
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f23,f22,f21,f20])).

fof(f37,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f24])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f35,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f36,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f24])).

fof(f40,plain,
    ( ~ v3_pre_topc(sK2,sK0)
    | v3_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f38,plain,
    ( k1_tops_1(sK0,sK2) = sK2
    | v3_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f12,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f33,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f34,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f39,plain,
    ( k1_tops_1(sK0,sK2) = sK2
    | k1_tops_1(sK1,sK3) != sK3 ),
    inference(cnf_transformation,[],[f24])).

fof(f41,plain,
    ( ~ v3_pre_topc(sK2,sK0)
    | k1_tops_1(sK1,sK3) != sK3 ),
    inference(cnf_transformation,[],[f24])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_614,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_960,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_614])).

cnf(c_5,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
    | ~ v3_pre_topc(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_14,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_225,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
    | ~ v3_pre_topc(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_14])).

cnf(c_226,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK1),X0),sK1)
    | ~ v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_225])).

cnf(c_610,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK1),X0_42),sK1)
    | ~ v3_pre_topc(X0_42,sK1)
    | ~ m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subtyping,[status(esa)],[c_226])).

cnf(c_964,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK1),X0_42),sK1) = iProver_top
    | v3_pre_topc(X0_42,sK1) != iProver_top
    | m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_610])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_620,plain,
    ( ~ m1_subset_1(X0_42,k1_zfmisc_1(X0_44))
    | m1_subset_1(k3_subset_1(X0_44,X0_42),k1_zfmisc_1(X0_44)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_955,plain,
    ( m1_subset_1(X0_42,k1_zfmisc_1(X0_44)) != iProver_top
    | m1_subset_1(k3_subset_1(X0_44,X0_42),k1_zfmisc_1(X0_44)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_620])).

cnf(c_7,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_285,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,X0) = X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_14])).

cnf(c_286,plain,
    ( ~ v4_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_pre_topc(sK1,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_285])).

cnf(c_606,plain,
    ( ~ v4_pre_topc(X0_42,sK1)
    | ~ m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_pre_topc(sK1,X0_42) = X0_42 ),
    inference(subtyping,[status(esa)],[c_286])).

cnf(c_968,plain,
    ( k2_pre_topc(sK1,X0_42) = X0_42
    | v4_pre_topc(X0_42,sK1) != iProver_top
    | m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_606])).

cnf(c_1534,plain,
    ( k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),X0_42)) = k3_subset_1(u1_struct_0(sK1),X0_42)
    | v4_pre_topc(k3_subset_1(u1_struct_0(sK1),X0_42),sK1) != iProver_top
    | m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_955,c_968])).

cnf(c_2363,plain,
    ( k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),X0_42)) = k3_subset_1(u1_struct_0(sK1),X0_42)
    | v3_pre_topc(X0_42,sK1) != iProver_top
    | m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_964,c_1534])).

cnf(c_2808,plain,
    ( k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK3)) = k3_subset_1(u1_struct_0(sK1),sK3)
    | v3_pre_topc(sK3,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_960,c_2363])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_20,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_21,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_9,negated_conjecture,
    ( v3_pre_topc(sK3,sK1)
    | ~ v3_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_23,plain,
    ( v3_pre_topc(sK3,sK1) = iProver_top
    | v3_pre_topc(sK2,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_622,plain,
    ( X0_42 = X0_42 ),
    theory(equality)).

cnf(c_637,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_622])).

cnf(c_11,negated_conjecture,
    ( v3_pre_topc(sK3,sK1)
    | k1_tops_1(sK0,sK2) = sK2 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_615,negated_conjecture,
    ( v3_pre_topc(sK3,sK1)
    | k1_tops_1(sK0,sK2) = sK2 ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_646,plain,
    ( k1_tops_1(sK0,sK2) = sK2
    | v3_pre_topc(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_615])).

cnf(c_2,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_16,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_179,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_16])).

cnf(c_180,plain,
    ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_179])).

cnf(c_15,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_184,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(k1_tops_1(sK0,X0),sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_180,c_15])).

cnf(c_185,plain,
    ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(renaming,[status(thm)],[c_184])).

cnf(c_612,plain,
    ( v3_pre_topc(k1_tops_1(sK0,X0_42),sK0)
    | ~ m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_185])).

cnf(c_649,plain,
    ( v3_pre_topc(k1_tops_1(sK0,X0_42),sK0) = iProver_top
    | m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_612])).

cnf(c_651,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK2),sK0) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_649])).

cnf(c_1106,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK3),sK1)
    | ~ v3_pre_topc(sK3,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_610])).

cnf(c_1107,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK3),sK1) = iProver_top
    | v3_pre_topc(sK3,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1106])).

cnf(c_1109,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_620])).

cnf(c_1110,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK3),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1109])).

cnf(c_628,plain,
    ( ~ v3_pre_topc(X0_42,X0_45)
    | v3_pre_topc(X1_42,X0_45)
    | X1_42 != X0_42 ),
    theory(equality)).

cnf(c_1149,plain,
    ( v3_pre_topc(X0_42,sK0)
    | ~ v3_pre_topc(k1_tops_1(sK0,X1_42),sK0)
    | X0_42 != k1_tops_1(sK0,X1_42) ),
    inference(instantiation,[status(thm)],[c_628])).

cnf(c_1150,plain,
    ( X0_42 != k1_tops_1(sK0,X1_42)
    | v3_pre_topc(X0_42,sK0) = iProver_top
    | v3_pre_topc(k1_tops_1(sK0,X1_42),sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1149])).

cnf(c_1152,plain,
    ( sK2 != k1_tops_1(sK0,sK2)
    | v3_pre_topc(k1_tops_1(sK0,sK2),sK0) != iProver_top
    | v3_pre_topc(sK2,sK0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1150])).

cnf(c_623,plain,
    ( X0_42 != X1_42
    | X2_42 != X1_42
    | X2_42 = X0_42 ),
    theory(equality)).

cnf(c_1335,plain,
    ( X0_42 != X1_42
    | X0_42 = k1_tops_1(sK0,X2_42)
    | k1_tops_1(sK0,X2_42) != X1_42 ),
    inference(instantiation,[status(thm)],[c_623])).

cnf(c_1336,plain,
    ( k1_tops_1(sK0,sK2) != sK2
    | sK2 = k1_tops_1(sK0,sK2)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1335])).

cnf(c_1400,plain,
    ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK3),sK1)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK3)) = k3_subset_1(u1_struct_0(sK1),sK3) ),
    inference(instantiation,[status(thm)],[c_606])).

cnf(c_1401,plain,
    ( k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK3)) = k3_subset_1(u1_struct_0(sK1),sK3)
    | v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK3),sK1) != iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1400])).

cnf(c_2936,plain,
    ( k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK3)) = k3_subset_1(u1_struct_0(sK1),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2808,c_20,c_21,c_23,c_637,c_646,c_651,c_1107,c_1110,c_1152,c_1336,c_1401])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_300,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_14])).

cnf(c_301,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k3_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),X0))) = k1_tops_1(sK1,X0) ),
    inference(unflattening,[status(thm)],[c_300])).

cnf(c_605,plain,
    ( ~ m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK1)))
    | k3_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),X0_42))) = k1_tops_1(sK1,X0_42) ),
    inference(subtyping,[status(esa)],[c_301])).

cnf(c_969,plain,
    ( k3_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),X0_42))) = k1_tops_1(sK1,X0_42)
    | m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_605])).

cnf(c_1652,plain,
    ( k3_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK3))) = k1_tops_1(sK1,sK3) ),
    inference(superposition,[status(thm)],[c_960,c_969])).

cnf(c_2939,plain,
    ( k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),sK3)) = k1_tops_1(sK1,sK3) ),
    inference(demodulation,[status(thm)],[c_2936,c_1652])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_619,plain,
    ( ~ m1_subset_1(X0_42,k1_zfmisc_1(X0_44))
    | k3_subset_1(X0_44,k3_subset_1(X0_44,X0_42)) = X0_42 ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_956,plain,
    ( k3_subset_1(X0_44,k3_subset_1(X0_44,X0_42)) = X0_42
    | m1_subset_1(X0_42,k1_zfmisc_1(X0_44)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_619])).

cnf(c_1274,plain,
    ( k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),sK3)) = sK3 ),
    inference(superposition,[status(thm)],[c_960,c_956])).

cnf(c_2940,plain,
    ( k1_tops_1(sK1,sK3) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_2939,c_1274])).

cnf(c_1151,plain,
    ( ~ v3_pre_topc(k1_tops_1(sK0,sK2),sK0)
    | v3_pre_topc(sK2,sK0)
    | sK2 != k1_tops_1(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_1149])).

cnf(c_650,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK2),sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_612])).

cnf(c_10,negated_conjecture,
    ( k1_tops_1(sK1,sK3) != sK3
    | k1_tops_1(sK0,sK2) = sK2 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_616,negated_conjecture,
    ( k1_tops_1(sK1,sK3) != sK3
    | k1_tops_1(sK0,sK2) = sK2 ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_8,negated_conjecture,
    ( ~ v3_pre_topc(sK2,sK0)
    | k1_tops_1(sK1,sK3) != sK3 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_618,negated_conjecture,
    ( ~ v3_pre_topc(sK2,sK0)
    | k1_tops_1(sK1,sK3) != sK3 ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2940,c_1336,c_1151,c_650,c_616,c_618,c_637,c_13])).


%------------------------------------------------------------------------------
