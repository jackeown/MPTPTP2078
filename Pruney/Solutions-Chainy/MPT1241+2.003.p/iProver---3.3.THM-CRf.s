%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:14:01 EST 2020

% Result     : Theorem 7.57s
% Output     : CNFRefutation 7.57s
% Verified   : 
% Statistics : Number of formulae       :  130 (1103 expanded)
%              Number of clauses        :   89 ( 362 expanded)
%              Number of leaves         :   11 ( 339 expanded)
%              Depth                    :   25
%              Number of atoms          :  394 (7020 expanded)
%              Number of equality atoms :  175 (2013 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    6 (   2 average)

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f12,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f35,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f33,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f34,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f36,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f24])).

fof(f40,plain,
    ( ~ v3_pre_topc(sK2,sK0)
    | v3_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f38,plain,
    ( k1_tops_1(sK0,sK2) = sK2
    | v3_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f39,plain,
    ( k1_tops_1(sK0,sK2) = sK2
    | k1_tops_1(sK1,sK3) != sK3 ),
    inference(cnf_transformation,[],[f24])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f41,plain,
    ( ~ v3_pre_topc(sK2,sK0)
    | k1_tops_1(sK1,sK3) != sK3 ),
    inference(cnf_transformation,[],[f24])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_150,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_447,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_150])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_162,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(X0_45))
    | m1_subset_1(k3_subset_1(X0_45,X0_43),k1_zfmisc_1(X0_45)) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_436,plain,
    ( m1_subset_1(X0_43,k1_zfmisc_1(X0_45)) != iProver_top
    | m1_subset_1(k3_subset_1(X0_45,X0_43),k1_zfmisc_1(X0_45)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_162])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_160,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_42)))
    | m1_subset_1(k2_pre_topc(X0_42,X0_43),k1_zfmisc_1(u1_struct_0(X0_42)))
    | ~ l1_pre_topc(X0_42) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_438,plain,
    ( m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_42))) != iProver_top
    | m1_subset_1(k2_pre_topc(X0_42,X0_43),k1_zfmisc_1(u1_struct_0(X0_42))) = iProver_top
    | l1_pre_topc(X0_42) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_160])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_161,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(X0_45))
    | k3_subset_1(X0_45,k3_subset_1(X0_45,X0_43)) = X0_43 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_437,plain,
    ( k3_subset_1(X0_45,k3_subset_1(X0_45,X0_43)) = X0_43
    | m1_subset_1(X0_43,k1_zfmisc_1(X0_45)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_161])).

cnf(c_950,plain,
    ( k3_subset_1(u1_struct_0(X0_42),k3_subset_1(u1_struct_0(X0_42),k2_pre_topc(X0_42,X0_43))) = k2_pre_topc(X0_42,X0_43)
    | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_42))) != iProver_top
    | l1_pre_topc(X0_42) != iProver_top ),
    inference(superposition,[status(thm)],[c_438,c_437])).

cnf(c_2514,plain,
    ( k3_subset_1(u1_struct_0(X0_42),k3_subset_1(u1_struct_0(X0_42),k2_pre_topc(X0_42,k3_subset_1(u1_struct_0(X0_42),X0_43)))) = k2_pre_topc(X0_42,k3_subset_1(u1_struct_0(X0_42),X0_43))
    | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_42))) != iProver_top
    | l1_pre_topc(X0_42) != iProver_top ),
    inference(superposition,[status(thm)],[c_436,c_950])).

cnf(c_14695,plain,
    ( k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK3)))) = k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK3))
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_447,c_2514])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_157,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_42)))
    | ~ l1_pre_topc(X0_42)
    | k3_subset_1(u1_struct_0(X0_42),k2_pre_topc(X0_42,k3_subset_1(u1_struct_0(X0_42),X0_43))) = k1_tops_1(X0_42,X0_43) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_441,plain,
    ( k3_subset_1(u1_struct_0(X0_42),k2_pre_topc(X0_42,k3_subset_1(u1_struct_0(X0_42),X0_43))) = k1_tops_1(X0_42,X0_43)
    | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_42))) != iProver_top
    | l1_pre_topc(X0_42) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_157])).

cnf(c_1639,plain,
    ( k3_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK3))) = k1_tops_1(sK1,sK3)
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_447,c_441])).

cnf(c_14,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_19,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1869,plain,
    ( k3_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK3))) = k1_tops_1(sK1,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1639,c_19])).

cnf(c_14749,plain,
    ( k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK3)) = k3_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,sK3))
    | l1_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_14695,c_1869])).

cnf(c_15889,plain,
    ( k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK3)) = k3_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14749,c_19])).

cnf(c_932,plain,
    ( k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),sK3)) = sK3 ),
    inference(superposition,[status(thm)],[c_447,c_437])).

cnf(c_6,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
    | v4_pre_topc(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_156,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0_42),X0_43),X0_42)
    | v4_pre_topc(X0_43,X0_42)
    | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_42)))
    | ~ l1_pre_topc(X0_42) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_442,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(X0_42),X0_43),X0_42) != iProver_top
    | v4_pre_topc(X0_43,X0_42) = iProver_top
    | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_42))) != iProver_top
    | l1_pre_topc(X0_42) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_156])).

cnf(c_1759,plain,
    ( v3_pre_topc(sK3,sK1) != iProver_top
    | v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK3),sK1) = iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_932,c_442])).

cnf(c_21,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_596,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_162])).

cnf(c_597,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK3),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_596])).

cnf(c_2103,plain,
    ( v3_pre_topc(sK3,sK1) != iProver_top
    | v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK3),sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1759,c_19,c_21,c_597])).

cnf(c_4,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_158,plain,
    ( ~ v4_pre_topc(X0_43,X0_42)
    | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_42)))
    | ~ l1_pre_topc(X0_42)
    | k2_pre_topc(X0_42,X0_43) = X0_43 ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_440,plain,
    ( k2_pre_topc(X0_42,X0_43) = X0_43
    | v4_pre_topc(X0_43,X0_42) != iProver_top
    | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_42))) != iProver_top
    | l1_pre_topc(X0_42) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_158])).

cnf(c_1078,plain,
    ( k2_pre_topc(X0_42,k3_subset_1(u1_struct_0(X0_42),X0_43)) = k3_subset_1(u1_struct_0(X0_42),X0_43)
    | v4_pre_topc(k3_subset_1(u1_struct_0(X0_42),X0_43),X0_42) != iProver_top
    | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_42))) != iProver_top
    | l1_pre_topc(X0_42) != iProver_top ),
    inference(superposition,[status(thm)],[c_436,c_440])).

cnf(c_4466,plain,
    ( k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK3)) = k3_subset_1(u1_struct_0(sK1),sK3)
    | v3_pre_topc(sK3,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2103,c_1078])).

cnf(c_5386,plain,
    ( k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK3)) = k3_subset_1(u1_struct_0(sK1),sK3)
    | v3_pre_topc(sK3,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4466,c_19,c_21])).

cnf(c_15893,plain,
    ( k3_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,sK3)) = k3_subset_1(u1_struct_0(sK1),sK3)
    | v3_pre_topc(sK3,sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_15889,c_5386])).

cnf(c_16,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_17,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_15,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_18,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_20,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_9,negated_conjecture,
    ( v3_pre_topc(sK3,sK1)
    | ~ v3_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_23,plain,
    ( v3_pre_topc(sK3,sK1) = iProver_top
    | v3_pre_topc(sK2,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_599,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_162])).

cnf(c_600,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_599])).

cnf(c_149,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_448,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_149])).

cnf(c_933,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_448,c_437])).

cnf(c_7,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
    | ~ v4_pre_topc(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_155,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(X0_42),X0_43),X0_42)
    | ~ v4_pre_topc(X0_43,X0_42)
    | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_42)))
    | ~ l1_pre_topc(X0_42) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_443,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(X0_42),X0_43),X0_42) = iProver_top
    | v4_pre_topc(X0_43,X0_42) != iProver_top
    | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_42))) != iProver_top
    | l1_pre_topc(X0_42) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_155])).

cnf(c_1785,plain,
    ( v3_pre_topc(sK2,sK0) = iProver_top
    | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK2),sK0) != iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_933,c_443])).

cnf(c_2256,plain,
    ( v3_pre_topc(sK2,sK0) = iProver_top
    | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK2),sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1785,c_18,c_20,c_600])).

cnf(c_14696,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)))) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2))
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_448,c_2514])).

cnf(c_11,negated_conjecture,
    ( v3_pre_topc(sK3,sK1)
    | k1_tops_1(sK0,sK2) = sK2 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_151,negated_conjecture,
    ( v3_pre_topc(sK3,sK1)
    | k1_tops_1(sK0,sK2) = sK2 ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_446,plain,
    ( k1_tops_1(sK0,sK2) = sK2
    | v3_pre_topc(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_151])).

cnf(c_5392,plain,
    ( k1_tops_1(sK0,sK2) = sK2
    | k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK3)) = k3_subset_1(u1_struct_0(sK1),sK3) ),
    inference(superposition,[status(thm)],[c_446,c_5386])).

cnf(c_5400,plain,
    ( k1_tops_1(sK0,sK2) = sK2
    | k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),sK3)) = k1_tops_1(sK1,sK3) ),
    inference(superposition,[status(thm)],[c_5392,c_1869])).

cnf(c_5403,plain,
    ( k1_tops_1(sK1,sK3) = sK3
    | k1_tops_1(sK0,sK2) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_5400,c_932])).

cnf(c_10,negated_conjecture,
    ( k1_tops_1(sK1,sK3) != sK3
    | k1_tops_1(sK0,sK2) = sK2 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_152,negated_conjecture,
    ( k1_tops_1(sK1,sK3) != sK3
    | k1_tops_1(sK0,sK2) = sK2 ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_5664,plain,
    ( k1_tops_1(sK0,sK2) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5403,c_152])).

cnf(c_1640,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2))) = k1_tops_1(sK0,sK2)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_448,c_441])).

cnf(c_194,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2))) = k1_tops_1(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_157])).

cnf(c_1899,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2))) = k1_tops_1(sK0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1640,c_15,c_13,c_194])).

cnf(c_5673,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2))) = sK2 ),
    inference(demodulation,[status(thm)],[c_5664,c_1899])).

cnf(c_14744,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)) = k3_subset_1(u1_struct_0(sK0),sK2)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_14696,c_5673])).

cnf(c_15864,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)) = k3_subset_1(u1_struct_0(sK0),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14744,c_18])).

cnf(c_3,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_159,plain,
    ( v4_pre_topc(X0_43,X0_42)
    | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_42)))
    | ~ v2_pre_topc(X0_42)
    | ~ l1_pre_topc(X0_42)
    | k2_pre_topc(X0_42,X0_43) != X0_43 ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_439,plain,
    ( k2_pre_topc(X0_42,X0_43) != X0_43
    | v4_pre_topc(X0_43,X0_42) = iProver_top
    | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_42))) != iProver_top
    | v2_pre_topc(X0_42) != iProver_top
    | l1_pre_topc(X0_42) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_159])).

cnf(c_15872,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK2),sK0) = iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_15864,c_439])).

cnf(c_16167,plain,
    ( k3_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,sK3)) = k3_subset_1(u1_struct_0(sK1),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15893,c_17,c_18,c_20,c_23,c_600,c_2256,c_15872])).

cnf(c_1874,plain,
    ( m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m1_subset_1(k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK3)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1869,c_436])).

cnf(c_2020,plain,
    ( m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_438,c_1874])).

cnf(c_3669,plain,
    ( m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2020,c_19,c_21,c_597])).

cnf(c_3680,plain,
    ( k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,sK3))) = k1_tops_1(sK1,sK3) ),
    inference(superposition,[status(thm)],[c_3669,c_437])).

cnf(c_16172,plain,
    ( k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),sK3)) = k1_tops_1(sK1,sK3) ),
    inference(demodulation,[status(thm)],[c_16167,c_3680])).

cnf(c_16174,plain,
    ( k1_tops_1(sK1,sK3) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_16172,c_932])).

cnf(c_8,negated_conjecture,
    ( ~ v3_pre_topc(sK2,sK0)
    | k1_tops_1(sK1,sK3) != sK3 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_154,negated_conjecture,
    ( ~ v3_pre_topc(sK2,sK0)
    | k1_tops_1(sK1,sK3) != sK3 ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_202,plain,
    ( k1_tops_1(sK1,sK3) != sK3
    | v3_pre_topc(sK2,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_154])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_16174,c_15872,c_2256,c_600,c_202,c_20,c_18,c_17])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:25:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.57/1.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.57/1.48  
% 7.57/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.57/1.48  
% 7.57/1.48  ------  iProver source info
% 7.57/1.48  
% 7.57/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.57/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.57/1.48  git: non_committed_changes: false
% 7.57/1.48  git: last_make_outside_of_git: false
% 7.57/1.48  
% 7.57/1.48  ------ 
% 7.57/1.48  ------ Parsing...
% 7.57/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.57/1.48  
% 7.57/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 7.57/1.48  
% 7.57/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.57/1.48  
% 7.57/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.57/1.48  ------ Proving...
% 7.57/1.48  ------ Problem Properties 
% 7.57/1.48  
% 7.57/1.48  
% 7.57/1.48  clauses                                 17
% 7.57/1.48  conjectures                             9
% 7.57/1.48  EPR                                     4
% 7.57/1.48  Horn                                    16
% 7.57/1.48  unary                                   5
% 7.57/1.48  binary                                  6
% 7.57/1.48  lits                                    40
% 7.57/1.48  lits eq                                 8
% 7.57/1.48  fd_pure                                 0
% 7.57/1.48  fd_pseudo                               0
% 7.57/1.48  fd_cond                                 0
% 7.57/1.48  fd_pseudo_cond                          0
% 7.57/1.48  AC symbols                              0
% 7.57/1.48  
% 7.57/1.48  ------ Input Options Time Limit: Unbounded
% 7.57/1.48  
% 7.57/1.48  
% 7.57/1.48  ------ 
% 7.57/1.48  Current options:
% 7.57/1.48  ------ 
% 7.57/1.48  
% 7.57/1.48  
% 7.57/1.48  
% 7.57/1.48  
% 7.57/1.48  ------ Proving...
% 7.57/1.48  
% 7.57/1.48  
% 7.57/1.48  % SZS status Theorem for theBenchmark.p
% 7.57/1.48  
% 7.57/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.57/1.48  
% 7.57/1.48  fof(f7,conjecture,(
% 7.57/1.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 7.57/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.57/1.48  
% 7.57/1.48  fof(f8,negated_conjecture,(
% 7.57/1.48    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 7.57/1.48    inference(negated_conjecture,[],[f7])).
% 7.57/1.48  
% 7.57/1.48  fof(f17,plain,(
% 7.57/1.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~v3_pre_topc(X2,X0) & k1_tops_1(X0,X2) = X2) | (k1_tops_1(X1,X3) != X3 & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 7.57/1.48    inference(ennf_transformation,[],[f8])).
% 7.57/1.48  
% 7.57/1.48  fof(f18,plain,(
% 7.57/1.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~v3_pre_topc(X2,X0) & k1_tops_1(X0,X2) = X2) | (k1_tops_1(X1,X3) != X3 & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 7.57/1.48    inference(flattening,[],[f17])).
% 7.57/1.48  
% 7.57/1.48  fof(f23,plain,(
% 7.57/1.48    ( ! [X2,X0,X1] : (? [X3] : (((~v3_pre_topc(X2,X0) & k1_tops_1(X0,X2) = X2) | (k1_tops_1(X1,X3) != X3 & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) => (((~v3_pre_topc(X2,X0) & k1_tops_1(X0,X2) = X2) | (k1_tops_1(X1,sK3) != sK3 & v3_pre_topc(sK3,X1))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X1))))) )),
% 7.57/1.48    introduced(choice_axiom,[])).
% 7.57/1.48  
% 7.57/1.48  fof(f22,plain,(
% 7.57/1.48    ( ! [X0,X1] : (? [X2] : (? [X3] : (((~v3_pre_topc(X2,X0) & k1_tops_1(X0,X2) = X2) | (k1_tops_1(X1,X3) != X3 & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X3] : (((~v3_pre_topc(sK2,X0) & k1_tops_1(X0,sK2) = sK2) | (k1_tops_1(X1,X3) != X3 & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 7.57/1.48    introduced(choice_axiom,[])).
% 7.57/1.48  
% 7.57/1.48  fof(f21,plain,(
% 7.57/1.48    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (((~v3_pre_topc(X2,X0) & k1_tops_1(X0,X2) = X2) | (k1_tops_1(X1,X3) != X3 & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) => (? [X2] : (? [X3] : (((~v3_pre_topc(X2,X0) & k1_tops_1(X0,X2) = X2) | (k1_tops_1(sK1,X3) != X3 & v3_pre_topc(X3,sK1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(sK1))) )),
% 7.57/1.48    introduced(choice_axiom,[])).
% 7.57/1.48  
% 7.57/1.48  fof(f20,plain,(
% 7.57/1.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~v3_pre_topc(X2,X0) & k1_tops_1(X0,X2) = X2) | (k1_tops_1(X1,X3) != X3 & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : (((~v3_pre_topc(X2,sK0) & k1_tops_1(sK0,X2) = X2) | (k1_tops_1(X1,X3) != X3 & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 7.57/1.48    introduced(choice_axiom,[])).
% 7.57/1.48  
% 7.57/1.48  fof(f24,plain,(
% 7.57/1.48    (((((~v3_pre_topc(sK2,sK0) & k1_tops_1(sK0,sK2) = sK2) | (k1_tops_1(sK1,sK3) != sK3 & v3_pre_topc(sK3,sK1))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 7.57/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f23,f22,f21,f20])).
% 7.57/1.48  
% 7.57/1.48  fof(f37,plain,(
% 7.57/1.48    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))),
% 7.57/1.48    inference(cnf_transformation,[],[f24])).
% 7.57/1.48  
% 7.57/1.48  fof(f1,axiom,(
% 7.57/1.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 7.57/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.57/1.48  
% 7.57/1.48  fof(f9,plain,(
% 7.57/1.48    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.57/1.48    inference(ennf_transformation,[],[f1])).
% 7.57/1.48  
% 7.57/1.48  fof(f25,plain,(
% 7.57/1.48    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.57/1.48    inference(cnf_transformation,[],[f9])).
% 7.57/1.48  
% 7.57/1.48  fof(f3,axiom,(
% 7.57/1.48    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 7.57/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.57/1.48  
% 7.57/1.48  fof(f11,plain,(
% 7.57/1.48    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 7.57/1.48    inference(ennf_transformation,[],[f3])).
% 7.57/1.48  
% 7.57/1.48  fof(f12,plain,(
% 7.57/1.48    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 7.57/1.48    inference(flattening,[],[f11])).
% 7.57/1.48  
% 7.57/1.48  fof(f27,plain,(
% 7.57/1.48    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.57/1.48    inference(cnf_transformation,[],[f12])).
% 7.57/1.48  
% 7.57/1.48  fof(f2,axiom,(
% 7.57/1.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 7.57/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.57/1.48  
% 7.57/1.48  fof(f10,plain,(
% 7.57/1.48    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.57/1.48    inference(ennf_transformation,[],[f2])).
% 7.57/1.48  
% 7.57/1.48  fof(f26,plain,(
% 7.57/1.48    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.57/1.48    inference(cnf_transformation,[],[f10])).
% 7.57/1.48  
% 7.57/1.48  fof(f5,axiom,(
% 7.57/1.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)))),
% 7.57/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.57/1.48  
% 7.57/1.48  fof(f15,plain,(
% 7.57/1.48    ! [X0] : (! [X1] : (k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.57/1.48    inference(ennf_transformation,[],[f5])).
% 7.57/1.48  
% 7.57/1.48  fof(f30,plain,(
% 7.57/1.48    ( ! [X0,X1] : (k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.57/1.48    inference(cnf_transformation,[],[f15])).
% 7.57/1.48  
% 7.57/1.48  fof(f35,plain,(
% 7.57/1.48    l1_pre_topc(sK1)),
% 7.57/1.48    inference(cnf_transformation,[],[f24])).
% 7.57/1.48  
% 7.57/1.48  fof(f6,axiom,(
% 7.57/1.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 7.57/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.57/1.48  
% 7.57/1.48  fof(f16,plain,(
% 7.57/1.48    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.57/1.48    inference(ennf_transformation,[],[f6])).
% 7.57/1.48  
% 7.57/1.48  fof(f19,plain,(
% 7.57/1.48    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.57/1.48    inference(nnf_transformation,[],[f16])).
% 7.57/1.48  
% 7.57/1.48  fof(f32,plain,(
% 7.57/1.48    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.57/1.48    inference(cnf_transformation,[],[f19])).
% 7.57/1.48  
% 7.57/1.48  fof(f4,axiom,(
% 7.57/1.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 7.57/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.57/1.48  
% 7.57/1.48  fof(f13,plain,(
% 7.57/1.48    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.57/1.48    inference(ennf_transformation,[],[f4])).
% 7.57/1.48  
% 7.57/1.48  fof(f14,plain,(
% 7.57/1.48    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.57/1.48    inference(flattening,[],[f13])).
% 7.57/1.48  
% 7.57/1.48  fof(f28,plain,(
% 7.57/1.48    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.57/1.48    inference(cnf_transformation,[],[f14])).
% 7.57/1.48  
% 7.57/1.48  fof(f33,plain,(
% 7.57/1.48    v2_pre_topc(sK0)),
% 7.57/1.48    inference(cnf_transformation,[],[f24])).
% 7.57/1.48  
% 7.57/1.48  fof(f34,plain,(
% 7.57/1.48    l1_pre_topc(sK0)),
% 7.57/1.48    inference(cnf_transformation,[],[f24])).
% 7.57/1.48  
% 7.57/1.48  fof(f36,plain,(
% 7.57/1.48    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 7.57/1.48    inference(cnf_transformation,[],[f24])).
% 7.57/1.48  
% 7.57/1.48  fof(f40,plain,(
% 7.57/1.48    ~v3_pre_topc(sK2,sK0) | v3_pre_topc(sK3,sK1)),
% 7.57/1.48    inference(cnf_transformation,[],[f24])).
% 7.57/1.48  
% 7.57/1.48  fof(f31,plain,(
% 7.57/1.48    ( ! [X0,X1] : (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.57/1.48    inference(cnf_transformation,[],[f19])).
% 7.57/1.48  
% 7.57/1.48  fof(f38,plain,(
% 7.57/1.48    k1_tops_1(sK0,sK2) = sK2 | v3_pre_topc(sK3,sK1)),
% 7.57/1.48    inference(cnf_transformation,[],[f24])).
% 7.57/1.48  
% 7.57/1.48  fof(f39,plain,(
% 7.57/1.48    k1_tops_1(sK0,sK2) = sK2 | k1_tops_1(sK1,sK3) != sK3),
% 7.57/1.48    inference(cnf_transformation,[],[f24])).
% 7.57/1.48  
% 7.57/1.48  fof(f29,plain,(
% 7.57/1.48    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.57/1.48    inference(cnf_transformation,[],[f14])).
% 7.57/1.48  
% 7.57/1.48  fof(f41,plain,(
% 7.57/1.48    ~v3_pre_topc(sK2,sK0) | k1_tops_1(sK1,sK3) != sK3),
% 7.57/1.48    inference(cnf_transformation,[],[f24])).
% 7.57/1.48  
% 7.57/1.48  cnf(c_12,negated_conjecture,
% 7.57/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 7.57/1.48      inference(cnf_transformation,[],[f37]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_150,negated_conjecture,
% 7.57/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 7.57/1.48      inference(subtyping,[status(esa)],[c_12]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_447,plain,
% 7.57/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 7.57/1.48      inference(predicate_to_equality,[status(thm)],[c_150]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_0,plain,
% 7.57/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.57/1.48      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 7.57/1.48      inference(cnf_transformation,[],[f25]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_162,plain,
% 7.57/1.48      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(X0_45))
% 7.57/1.48      | m1_subset_1(k3_subset_1(X0_45,X0_43),k1_zfmisc_1(X0_45)) ),
% 7.57/1.48      inference(subtyping,[status(esa)],[c_0]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_436,plain,
% 7.57/1.48      ( m1_subset_1(X0_43,k1_zfmisc_1(X0_45)) != iProver_top
% 7.57/1.48      | m1_subset_1(k3_subset_1(X0_45,X0_43),k1_zfmisc_1(X0_45)) = iProver_top ),
% 7.57/1.48      inference(predicate_to_equality,[status(thm)],[c_162]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_2,plain,
% 7.57/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.57/1.48      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.57/1.48      | ~ l1_pre_topc(X1) ),
% 7.57/1.48      inference(cnf_transformation,[],[f27]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_160,plain,
% 7.57/1.48      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_42)))
% 7.57/1.48      | m1_subset_1(k2_pre_topc(X0_42,X0_43),k1_zfmisc_1(u1_struct_0(X0_42)))
% 7.57/1.48      | ~ l1_pre_topc(X0_42) ),
% 7.57/1.48      inference(subtyping,[status(esa)],[c_2]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_438,plain,
% 7.57/1.48      ( m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_42))) != iProver_top
% 7.57/1.48      | m1_subset_1(k2_pre_topc(X0_42,X0_43),k1_zfmisc_1(u1_struct_0(X0_42))) = iProver_top
% 7.57/1.48      | l1_pre_topc(X0_42) != iProver_top ),
% 7.57/1.48      inference(predicate_to_equality,[status(thm)],[c_160]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_1,plain,
% 7.57/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.57/1.48      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 7.57/1.48      inference(cnf_transformation,[],[f26]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_161,plain,
% 7.57/1.48      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(X0_45))
% 7.57/1.48      | k3_subset_1(X0_45,k3_subset_1(X0_45,X0_43)) = X0_43 ),
% 7.57/1.48      inference(subtyping,[status(esa)],[c_1]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_437,plain,
% 7.57/1.48      ( k3_subset_1(X0_45,k3_subset_1(X0_45,X0_43)) = X0_43
% 7.57/1.48      | m1_subset_1(X0_43,k1_zfmisc_1(X0_45)) != iProver_top ),
% 7.57/1.48      inference(predicate_to_equality,[status(thm)],[c_161]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_950,plain,
% 7.57/1.48      ( k3_subset_1(u1_struct_0(X0_42),k3_subset_1(u1_struct_0(X0_42),k2_pre_topc(X0_42,X0_43))) = k2_pre_topc(X0_42,X0_43)
% 7.57/1.48      | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_42))) != iProver_top
% 7.57/1.48      | l1_pre_topc(X0_42) != iProver_top ),
% 7.57/1.48      inference(superposition,[status(thm)],[c_438,c_437]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_2514,plain,
% 7.57/1.48      ( k3_subset_1(u1_struct_0(X0_42),k3_subset_1(u1_struct_0(X0_42),k2_pre_topc(X0_42,k3_subset_1(u1_struct_0(X0_42),X0_43)))) = k2_pre_topc(X0_42,k3_subset_1(u1_struct_0(X0_42),X0_43))
% 7.57/1.48      | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_42))) != iProver_top
% 7.57/1.48      | l1_pre_topc(X0_42) != iProver_top ),
% 7.57/1.48      inference(superposition,[status(thm)],[c_436,c_950]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_14695,plain,
% 7.57/1.48      ( k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK3)))) = k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK3))
% 7.57/1.48      | l1_pre_topc(sK1) != iProver_top ),
% 7.57/1.48      inference(superposition,[status(thm)],[c_447,c_2514]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_5,plain,
% 7.57/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.57/1.48      | ~ l1_pre_topc(X1)
% 7.57/1.48      | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0) ),
% 7.57/1.48      inference(cnf_transformation,[],[f30]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_157,plain,
% 7.57/1.48      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_42)))
% 7.57/1.48      | ~ l1_pre_topc(X0_42)
% 7.57/1.48      | k3_subset_1(u1_struct_0(X0_42),k2_pre_topc(X0_42,k3_subset_1(u1_struct_0(X0_42),X0_43))) = k1_tops_1(X0_42,X0_43) ),
% 7.57/1.48      inference(subtyping,[status(esa)],[c_5]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_441,plain,
% 7.57/1.48      ( k3_subset_1(u1_struct_0(X0_42),k2_pre_topc(X0_42,k3_subset_1(u1_struct_0(X0_42),X0_43))) = k1_tops_1(X0_42,X0_43)
% 7.57/1.48      | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_42))) != iProver_top
% 7.57/1.48      | l1_pre_topc(X0_42) != iProver_top ),
% 7.57/1.48      inference(predicate_to_equality,[status(thm)],[c_157]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_1639,plain,
% 7.57/1.48      ( k3_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK3))) = k1_tops_1(sK1,sK3)
% 7.57/1.48      | l1_pre_topc(sK1) != iProver_top ),
% 7.57/1.48      inference(superposition,[status(thm)],[c_447,c_441]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_14,negated_conjecture,
% 7.57/1.48      ( l1_pre_topc(sK1) ),
% 7.57/1.48      inference(cnf_transformation,[],[f35]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_19,plain,
% 7.57/1.48      ( l1_pre_topc(sK1) = iProver_top ),
% 7.57/1.48      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_1869,plain,
% 7.57/1.48      ( k3_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK3))) = k1_tops_1(sK1,sK3) ),
% 7.57/1.48      inference(global_propositional_subsumption,
% 7.57/1.48                [status(thm)],
% 7.57/1.48                [c_1639,c_19]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_14749,plain,
% 7.57/1.48      ( k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK3)) = k3_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,sK3))
% 7.57/1.48      | l1_pre_topc(sK1) != iProver_top ),
% 7.57/1.48      inference(light_normalisation,[status(thm)],[c_14695,c_1869]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_15889,plain,
% 7.57/1.48      ( k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK3)) = k3_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,sK3)) ),
% 7.57/1.48      inference(global_propositional_subsumption,
% 7.57/1.48                [status(thm)],
% 7.57/1.48                [c_14749,c_19]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_932,plain,
% 7.57/1.48      ( k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),sK3)) = sK3 ),
% 7.57/1.48      inference(superposition,[status(thm)],[c_447,c_437]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_6,plain,
% 7.57/1.48      ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
% 7.57/1.48      | v4_pre_topc(X1,X0)
% 7.57/1.48      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 7.57/1.48      | ~ l1_pre_topc(X0) ),
% 7.57/1.48      inference(cnf_transformation,[],[f32]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_156,plain,
% 7.57/1.48      ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0_42),X0_43),X0_42)
% 7.57/1.48      | v4_pre_topc(X0_43,X0_42)
% 7.57/1.48      | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_42)))
% 7.57/1.48      | ~ l1_pre_topc(X0_42) ),
% 7.57/1.48      inference(subtyping,[status(esa)],[c_6]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_442,plain,
% 7.57/1.48      ( v3_pre_topc(k3_subset_1(u1_struct_0(X0_42),X0_43),X0_42) != iProver_top
% 7.57/1.48      | v4_pre_topc(X0_43,X0_42) = iProver_top
% 7.57/1.48      | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_42))) != iProver_top
% 7.57/1.48      | l1_pre_topc(X0_42) != iProver_top ),
% 7.57/1.48      inference(predicate_to_equality,[status(thm)],[c_156]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_1759,plain,
% 7.57/1.48      ( v3_pre_topc(sK3,sK1) != iProver_top
% 7.57/1.48      | v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK3),sK1) = iProver_top
% 7.57/1.48      | m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 7.57/1.48      | l1_pre_topc(sK1) != iProver_top ),
% 7.57/1.48      inference(superposition,[status(thm)],[c_932,c_442]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_21,plain,
% 7.57/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 7.57/1.48      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_596,plain,
% 7.57/1.48      ( m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 7.57/1.48      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 7.57/1.48      inference(instantiation,[status(thm)],[c_162]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_597,plain,
% 7.57/1.48      ( m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK3),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 7.57/1.48      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 7.57/1.48      inference(predicate_to_equality,[status(thm)],[c_596]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_2103,plain,
% 7.57/1.48      ( v3_pre_topc(sK3,sK1) != iProver_top
% 7.57/1.48      | v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK3),sK1) = iProver_top ),
% 7.57/1.48      inference(global_propositional_subsumption,
% 7.57/1.48                [status(thm)],
% 7.57/1.48                [c_1759,c_19,c_21,c_597]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_4,plain,
% 7.57/1.48      ( ~ v4_pre_topc(X0,X1)
% 7.57/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.57/1.48      | ~ l1_pre_topc(X1)
% 7.57/1.48      | k2_pre_topc(X1,X0) = X0 ),
% 7.57/1.48      inference(cnf_transformation,[],[f28]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_158,plain,
% 7.57/1.48      ( ~ v4_pre_topc(X0_43,X0_42)
% 7.57/1.48      | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_42)))
% 7.57/1.48      | ~ l1_pre_topc(X0_42)
% 7.57/1.48      | k2_pre_topc(X0_42,X0_43) = X0_43 ),
% 7.57/1.48      inference(subtyping,[status(esa)],[c_4]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_440,plain,
% 7.57/1.48      ( k2_pre_topc(X0_42,X0_43) = X0_43
% 7.57/1.48      | v4_pre_topc(X0_43,X0_42) != iProver_top
% 7.57/1.48      | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_42))) != iProver_top
% 7.57/1.48      | l1_pre_topc(X0_42) != iProver_top ),
% 7.57/1.48      inference(predicate_to_equality,[status(thm)],[c_158]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_1078,plain,
% 7.57/1.48      ( k2_pre_topc(X0_42,k3_subset_1(u1_struct_0(X0_42),X0_43)) = k3_subset_1(u1_struct_0(X0_42),X0_43)
% 7.57/1.48      | v4_pre_topc(k3_subset_1(u1_struct_0(X0_42),X0_43),X0_42) != iProver_top
% 7.57/1.48      | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_42))) != iProver_top
% 7.57/1.48      | l1_pre_topc(X0_42) != iProver_top ),
% 7.57/1.48      inference(superposition,[status(thm)],[c_436,c_440]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_4466,plain,
% 7.57/1.48      ( k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK3)) = k3_subset_1(u1_struct_0(sK1),sK3)
% 7.57/1.48      | v3_pre_topc(sK3,sK1) != iProver_top
% 7.57/1.48      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 7.57/1.48      | l1_pre_topc(sK1) != iProver_top ),
% 7.57/1.48      inference(superposition,[status(thm)],[c_2103,c_1078]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_5386,plain,
% 7.57/1.48      ( k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK3)) = k3_subset_1(u1_struct_0(sK1),sK3)
% 7.57/1.48      | v3_pre_topc(sK3,sK1) != iProver_top ),
% 7.57/1.48      inference(global_propositional_subsumption,
% 7.57/1.48                [status(thm)],
% 7.57/1.48                [c_4466,c_19,c_21]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_15893,plain,
% 7.57/1.48      ( k3_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,sK3)) = k3_subset_1(u1_struct_0(sK1),sK3)
% 7.57/1.48      | v3_pre_topc(sK3,sK1) != iProver_top ),
% 7.57/1.48      inference(demodulation,[status(thm)],[c_15889,c_5386]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_16,negated_conjecture,
% 7.57/1.48      ( v2_pre_topc(sK0) ),
% 7.57/1.48      inference(cnf_transformation,[],[f33]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_17,plain,
% 7.57/1.48      ( v2_pre_topc(sK0) = iProver_top ),
% 7.57/1.48      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_15,negated_conjecture,
% 7.57/1.48      ( l1_pre_topc(sK0) ),
% 7.57/1.48      inference(cnf_transformation,[],[f34]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_18,plain,
% 7.57/1.48      ( l1_pre_topc(sK0) = iProver_top ),
% 7.57/1.48      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_13,negated_conjecture,
% 7.57/1.48      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.57/1.48      inference(cnf_transformation,[],[f36]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_20,plain,
% 7.57/1.48      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 7.57/1.48      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_9,negated_conjecture,
% 7.57/1.48      ( v3_pre_topc(sK3,sK1) | ~ v3_pre_topc(sK2,sK0) ),
% 7.57/1.48      inference(cnf_transformation,[],[f40]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_23,plain,
% 7.57/1.48      ( v3_pre_topc(sK3,sK1) = iProver_top
% 7.57/1.48      | v3_pre_topc(sK2,sK0) != iProver_top ),
% 7.57/1.48      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_599,plain,
% 7.57/1.48      ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 7.57/1.48      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.57/1.48      inference(instantiation,[status(thm)],[c_162]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_600,plain,
% 7.57/1.48      ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 7.57/1.48      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.57/1.48      inference(predicate_to_equality,[status(thm)],[c_599]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_149,negated_conjecture,
% 7.57/1.48      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.57/1.48      inference(subtyping,[status(esa)],[c_13]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_448,plain,
% 7.57/1.48      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 7.57/1.48      inference(predicate_to_equality,[status(thm)],[c_149]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_933,plain,
% 7.57/1.48      ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2)) = sK2 ),
% 7.57/1.48      inference(superposition,[status(thm)],[c_448,c_437]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_7,plain,
% 7.57/1.48      ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
% 7.57/1.48      | ~ v4_pre_topc(X1,X0)
% 7.57/1.48      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 7.57/1.48      | ~ l1_pre_topc(X0) ),
% 7.57/1.48      inference(cnf_transformation,[],[f31]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_155,plain,
% 7.57/1.48      ( v3_pre_topc(k3_subset_1(u1_struct_0(X0_42),X0_43),X0_42)
% 7.57/1.48      | ~ v4_pre_topc(X0_43,X0_42)
% 7.57/1.48      | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_42)))
% 7.57/1.48      | ~ l1_pre_topc(X0_42) ),
% 7.57/1.48      inference(subtyping,[status(esa)],[c_7]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_443,plain,
% 7.57/1.48      ( v3_pre_topc(k3_subset_1(u1_struct_0(X0_42),X0_43),X0_42) = iProver_top
% 7.57/1.48      | v4_pre_topc(X0_43,X0_42) != iProver_top
% 7.57/1.48      | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_42))) != iProver_top
% 7.57/1.48      | l1_pre_topc(X0_42) != iProver_top ),
% 7.57/1.48      inference(predicate_to_equality,[status(thm)],[c_155]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_1785,plain,
% 7.57/1.48      ( v3_pre_topc(sK2,sK0) = iProver_top
% 7.57/1.48      | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK2),sK0) != iProver_top
% 7.57/1.48      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.57/1.48      | l1_pre_topc(sK0) != iProver_top ),
% 7.57/1.48      inference(superposition,[status(thm)],[c_933,c_443]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_2256,plain,
% 7.57/1.48      ( v3_pre_topc(sK2,sK0) = iProver_top
% 7.57/1.48      | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK2),sK0) != iProver_top ),
% 7.57/1.48      inference(global_propositional_subsumption,
% 7.57/1.48                [status(thm)],
% 7.57/1.48                [c_1785,c_18,c_20,c_600]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_14696,plain,
% 7.57/1.48      ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)))) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2))
% 7.57/1.48      | l1_pre_topc(sK0) != iProver_top ),
% 7.57/1.48      inference(superposition,[status(thm)],[c_448,c_2514]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_11,negated_conjecture,
% 7.57/1.48      ( v3_pre_topc(sK3,sK1) | k1_tops_1(sK0,sK2) = sK2 ),
% 7.57/1.48      inference(cnf_transformation,[],[f38]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_151,negated_conjecture,
% 7.57/1.48      ( v3_pre_topc(sK3,sK1) | k1_tops_1(sK0,sK2) = sK2 ),
% 7.57/1.48      inference(subtyping,[status(esa)],[c_11]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_446,plain,
% 7.57/1.48      ( k1_tops_1(sK0,sK2) = sK2 | v3_pre_topc(sK3,sK1) = iProver_top ),
% 7.57/1.48      inference(predicate_to_equality,[status(thm)],[c_151]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_5392,plain,
% 7.57/1.48      ( k1_tops_1(sK0,sK2) = sK2
% 7.57/1.48      | k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK3)) = k3_subset_1(u1_struct_0(sK1),sK3) ),
% 7.57/1.48      inference(superposition,[status(thm)],[c_446,c_5386]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_5400,plain,
% 7.57/1.48      ( k1_tops_1(sK0,sK2) = sK2
% 7.57/1.48      | k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),sK3)) = k1_tops_1(sK1,sK3) ),
% 7.57/1.48      inference(superposition,[status(thm)],[c_5392,c_1869]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_5403,plain,
% 7.57/1.48      ( k1_tops_1(sK1,sK3) = sK3 | k1_tops_1(sK0,sK2) = sK2 ),
% 7.57/1.48      inference(light_normalisation,[status(thm)],[c_5400,c_932]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_10,negated_conjecture,
% 7.57/1.48      ( k1_tops_1(sK1,sK3) != sK3 | k1_tops_1(sK0,sK2) = sK2 ),
% 7.57/1.48      inference(cnf_transformation,[],[f39]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_152,negated_conjecture,
% 7.57/1.48      ( k1_tops_1(sK1,sK3) != sK3 | k1_tops_1(sK0,sK2) = sK2 ),
% 7.57/1.48      inference(subtyping,[status(esa)],[c_10]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_5664,plain,
% 7.57/1.48      ( k1_tops_1(sK0,sK2) = sK2 ),
% 7.57/1.48      inference(global_propositional_subsumption,
% 7.57/1.48                [status(thm)],
% 7.57/1.48                [c_5403,c_152]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_1640,plain,
% 7.57/1.48      ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2))) = k1_tops_1(sK0,sK2)
% 7.57/1.48      | l1_pre_topc(sK0) != iProver_top ),
% 7.57/1.48      inference(superposition,[status(thm)],[c_448,c_441]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_194,plain,
% 7.57/1.48      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.57/1.48      | ~ l1_pre_topc(sK0)
% 7.57/1.48      | k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2))) = k1_tops_1(sK0,sK2) ),
% 7.57/1.48      inference(instantiation,[status(thm)],[c_157]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_1899,plain,
% 7.57/1.48      ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2))) = k1_tops_1(sK0,sK2) ),
% 7.57/1.48      inference(global_propositional_subsumption,
% 7.57/1.48                [status(thm)],
% 7.57/1.48                [c_1640,c_15,c_13,c_194]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_5673,plain,
% 7.57/1.48      ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2))) = sK2 ),
% 7.57/1.48      inference(demodulation,[status(thm)],[c_5664,c_1899]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_14744,plain,
% 7.57/1.48      ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)) = k3_subset_1(u1_struct_0(sK0),sK2)
% 7.57/1.48      | l1_pre_topc(sK0) != iProver_top ),
% 7.57/1.48      inference(light_normalisation,[status(thm)],[c_14696,c_5673]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_15864,plain,
% 7.57/1.48      ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)) = k3_subset_1(u1_struct_0(sK0),sK2) ),
% 7.57/1.48      inference(global_propositional_subsumption,
% 7.57/1.48                [status(thm)],
% 7.57/1.48                [c_14744,c_18]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_3,plain,
% 7.57/1.48      ( v4_pre_topc(X0,X1)
% 7.57/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.57/1.48      | ~ v2_pre_topc(X1)
% 7.57/1.48      | ~ l1_pre_topc(X1)
% 7.57/1.48      | k2_pre_topc(X1,X0) != X0 ),
% 7.57/1.48      inference(cnf_transformation,[],[f29]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_159,plain,
% 7.57/1.48      ( v4_pre_topc(X0_43,X0_42)
% 7.57/1.48      | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_42)))
% 7.57/1.48      | ~ v2_pre_topc(X0_42)
% 7.57/1.48      | ~ l1_pre_topc(X0_42)
% 7.57/1.48      | k2_pre_topc(X0_42,X0_43) != X0_43 ),
% 7.57/1.48      inference(subtyping,[status(esa)],[c_3]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_439,plain,
% 7.57/1.48      ( k2_pre_topc(X0_42,X0_43) != X0_43
% 7.57/1.48      | v4_pre_topc(X0_43,X0_42) = iProver_top
% 7.57/1.48      | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_42))) != iProver_top
% 7.57/1.48      | v2_pre_topc(X0_42) != iProver_top
% 7.57/1.48      | l1_pre_topc(X0_42) != iProver_top ),
% 7.57/1.48      inference(predicate_to_equality,[status(thm)],[c_159]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_15872,plain,
% 7.57/1.48      ( v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK2),sK0) = iProver_top
% 7.57/1.48      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.57/1.48      | v2_pre_topc(sK0) != iProver_top
% 7.57/1.48      | l1_pre_topc(sK0) != iProver_top ),
% 7.57/1.48      inference(superposition,[status(thm)],[c_15864,c_439]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_16167,plain,
% 7.57/1.48      ( k3_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,sK3)) = k3_subset_1(u1_struct_0(sK1),sK3) ),
% 7.57/1.48      inference(global_propositional_subsumption,
% 7.57/1.48                [status(thm)],
% 7.57/1.48                [c_15893,c_17,c_18,c_20,c_23,c_600,c_2256,c_15872]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_1874,plain,
% 7.57/1.48      ( m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 7.57/1.48      | m1_subset_1(k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK3)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 7.57/1.48      inference(superposition,[status(thm)],[c_1869,c_436]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_2020,plain,
% 7.57/1.48      ( m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 7.57/1.48      | m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 7.57/1.48      | l1_pre_topc(sK1) != iProver_top ),
% 7.57/1.48      inference(superposition,[status(thm)],[c_438,c_1874]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_3669,plain,
% 7.57/1.48      ( m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 7.57/1.48      inference(global_propositional_subsumption,
% 7.57/1.48                [status(thm)],
% 7.57/1.48                [c_2020,c_19,c_21,c_597]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_3680,plain,
% 7.57/1.48      ( k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,sK3))) = k1_tops_1(sK1,sK3) ),
% 7.57/1.48      inference(superposition,[status(thm)],[c_3669,c_437]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_16172,plain,
% 7.57/1.48      ( k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),sK3)) = k1_tops_1(sK1,sK3) ),
% 7.57/1.48      inference(demodulation,[status(thm)],[c_16167,c_3680]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_16174,plain,
% 7.57/1.48      ( k1_tops_1(sK1,sK3) = sK3 ),
% 7.57/1.48      inference(light_normalisation,[status(thm)],[c_16172,c_932]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_8,negated_conjecture,
% 7.57/1.48      ( ~ v3_pre_topc(sK2,sK0) | k1_tops_1(sK1,sK3) != sK3 ),
% 7.57/1.48      inference(cnf_transformation,[],[f41]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_154,negated_conjecture,
% 7.57/1.48      ( ~ v3_pre_topc(sK2,sK0) | k1_tops_1(sK1,sK3) != sK3 ),
% 7.57/1.48      inference(subtyping,[status(esa)],[c_8]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_202,plain,
% 7.57/1.48      ( k1_tops_1(sK1,sK3) != sK3 | v3_pre_topc(sK2,sK0) != iProver_top ),
% 7.57/1.48      inference(predicate_to_equality,[status(thm)],[c_154]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(contradiction,plain,
% 7.57/1.48      ( $false ),
% 7.57/1.48      inference(minisat,
% 7.57/1.48                [status(thm)],
% 7.57/1.48                [c_16174,c_15872,c_2256,c_600,c_202,c_20,c_18,c_17]) ).
% 7.57/1.48  
% 7.57/1.48  
% 7.57/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 7.57/1.48  
% 7.57/1.48  ------                               Statistics
% 7.57/1.48  
% 7.57/1.48  ------ Selected
% 7.57/1.48  
% 7.57/1.48  total_time:                             0.534
% 7.57/1.48  
%------------------------------------------------------------------------------
