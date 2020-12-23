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
% DateTime   : Thu Dec  3 12:26:24 EST 2020

% Result     : Theorem 1.65s
% Output     : CNFRefutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 328 expanded)
%              Number of clauses        :   80 ( 128 expanded)
%              Number of leaves         :   18 (  72 expanded)
%              Depth                    :   15
%              Number of atoms          :  389 (1287 expanded)
%              Number of equality atoms :  112 ( 181 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                            & v3_pre_topc(X3,X0) ) )
                    & r1_tarski(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ? [X2] :
                  ( ! [X3] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( ? [X3] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r1_tarski(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ? [X2] :
                  ( ! [X3] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X4] :
                  ( ? [X5] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X5) = X4
                      & v3_pre_topc(X5,X0)
                      & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r1_tarski(X4,X1)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f26])).

fof(f29,plain,(
    ! [X4,X1,X0] :
      ( ? [X5] :
          ( k9_subset_1(u1_struct_0(X0),X1,X5) = X4
          & v3_pre_topc(X5,X0)
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X0),X1,sK1(X0,X1,X4)) = X4
        & v3_pre_topc(sK1(X0,X1,X4),X0)
        & m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
              | ~ v3_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ! [X3] :
            ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK0(X0,X1)
            | ~ v3_pre_topc(X3,X0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & r1_tarski(sK0(X0,X1),X1)
        & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ( ! [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK0(X0,X1)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & r1_tarski(sK0(X0,X1),X1)
                & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X4] :
                  ( ( k9_subset_1(u1_struct_0(X0),X1,sK1(X0,X1,X4)) = X4
                    & v3_pre_topc(sK1(X0,X1,X4),X0)
                    & m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r1_tarski(X4,X1)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f29,f28])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | r1_tarski(sK0(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_xboole_0(X1) )
           => v2_tex_2(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f13,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_xboole_0(X1) )
           => v2_tex_2(X1,X0) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
     => ( ~ v2_tex_2(sK3,X0)
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0)))
        & v1_xboole_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v2_tex_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ v2_tex_2(X1,sK2)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ~ v2_tex_2(sK3,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & v1_xboole_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f25,f32,f31])).

fof(f49,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f52,plain,(
    ~ v2_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f34,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f50,plain,(
    v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f3,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f16])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( v2_tex_2(X1,X0)
      | k9_subset_1(u1_struct_0(X0),X1,X3) != sK0(X0,X1)
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f20,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f48,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f51,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_5,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1634,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0_48)) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1932,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0_48)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1634])).

cnf(c_9,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(sK0(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_17,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_420,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(sK0(X1,X0),X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_17])).

cnf(c_421,plain,
    ( v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(sK0(sK2,X0),X0) ),
    inference(unflattening,[status(thm)],[c_420])).

cnf(c_1624,plain,
    ( v2_tex_2(X0_46,sK2)
    | ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(sK0(sK2,X0_46),X0_46) ),
    inference(subtyping,[status(esa)],[c_421])).

cnf(c_1941,plain,
    ( v2_tex_2(X0_46,sK2) = iProver_top
    | m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(sK0(sK2,X0_46),X0_46) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1624])).

cnf(c_2393,plain,
    ( v2_tex_2(k1_xboole_0,sK2) = iProver_top
    | r1_tarski(sK0(sK2,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1932,c_1941])).

cnf(c_1679,plain,
    ( v2_tex_2(X0_46,sK2) = iProver_top
    | m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(sK0(sK2,X0_46),X0_46) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1624])).

cnf(c_1681,plain,
    ( v2_tex_2(k1_xboole_0,sK2) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(sK0(sK2,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1679])).

cnf(c_14,negated_conjecture,
    ( ~ v2_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1633,negated_conjecture,
    ( ~ v2_tex_2(sK3,sK2) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1933,plain,
    ( v2_tex_2(sK3,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1633])).

cnf(c_0,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_16,negated_conjecture,
    ( v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_241,plain,
    ( sK3 != X0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_16])).

cnf(c_242,plain,
    ( k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_241])).

cnf(c_1630,plain,
    ( k1_xboole_0 = sK3 ),
    inference(subtyping,[status(esa)],[c_242])).

cnf(c_1948,plain,
    ( v2_tex_2(k1_xboole_0,sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1933,c_1630])).

cnf(c_2068,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_1634])).

cnf(c_2073,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2068])).

cnf(c_2731,plain,
    ( r1_tarski(sK0(sK2,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2393,c_1681,c_1948,c_2073])).

cnf(c_2,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_tarski(X0,X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_215,plain,
    ( ~ r1_tarski(X0,X1)
    | v1_xboole_0(X0)
    | X0 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_3])).

cnf(c_216,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_215])).

cnf(c_230,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(resolution,[status(thm)],[c_216,c_0])).

cnf(c_1631,plain,
    ( ~ r1_tarski(X0_46,k1_xboole_0)
    | k1_xboole_0 = X0_46 ),
    inference(subtyping,[status(esa)],[c_230])).

cnf(c_1935,plain,
    ( k1_xboole_0 = X0_46
    | r1_tarski(X0_46,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1631])).

cnf(c_2849,plain,
    ( sK0(sK2,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2731,c_1935])).

cnf(c_1,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1636,plain,
    ( r1_tarski(k3_xboole_0(X0_46,X1_46),X0_46) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1930,plain,
    ( r1_tarski(k3_xboole_0(X0_46,X1_46),X0_46) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1636])).

cnf(c_2848,plain,
    ( k3_xboole_0(k1_xboole_0,X0_46) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1930,c_1935])).

cnf(c_2857,plain,
    ( k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2848])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1635,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(X0_48))
    | k9_subset_1(X0_48,X1_46,X0_46) = k3_xboole_0(X1_46,X0_46) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1931,plain,
    ( k9_subset_1(X0_48,X0_46,X1_46) = k3_xboole_0(X0_46,X1_46)
    | m1_subset_1(X1_46,k1_zfmisc_1(X0_48)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1635])).

cnf(c_2340,plain,
    ( k9_subset_1(X0_48,X0_46,k1_xboole_0) = k3_xboole_0(X0_46,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1932,c_1931])).

cnf(c_8,plain,
    ( v2_tex_2(X0,X1)
    | ~ v3_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),X0,X2) != sK0(X1,X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_435,plain,
    ( v2_tex_2(X0,X1)
    | ~ v3_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | k9_subset_1(u1_struct_0(X1),X0,X2) != sK0(X1,X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_17])).

cnf(c_436,plain,
    ( v2_tex_2(X0,sK2)
    | ~ v3_pre_topc(X1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | k9_subset_1(u1_struct_0(sK2),X0,X1) != sK0(sK2,X0) ),
    inference(unflattening,[status(thm)],[c_435])).

cnf(c_1623,plain,
    ( v2_tex_2(X0_46,sK2)
    | ~ v3_pre_topc(X1_46,sK2)
    | ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1_46,k1_zfmisc_1(u1_struct_0(sK2)))
    | k9_subset_1(u1_struct_0(sK2),X0_46,X1_46) != sK0(sK2,X0_46) ),
    inference(subtyping,[status(esa)],[c_436])).

cnf(c_1942,plain,
    ( k9_subset_1(u1_struct_0(sK2),X0_46,X1_46) != sK0(sK2,X0_46)
    | v2_tex_2(X0_46,sK2) = iProver_top
    | v3_pre_topc(X1_46,sK2) != iProver_top
    | m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X1_46,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1623])).

cnf(c_2841,plain,
    ( sK0(sK2,X0_46) != k3_xboole_0(X0_46,k1_xboole_0)
    | v2_tex_2(X0_46,sK2) = iProver_top
    | v3_pre_topc(k1_xboole_0,sK2) != iProver_top
    | m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2340,c_1942])).

cnf(c_2843,plain,
    ( sK0(sK2,k1_xboole_0) != k3_xboole_0(k1_xboole_0,k1_xboole_0)
    | v2_tex_2(k1_xboole_0,sK2) = iProver_top
    | v3_pre_topc(k1_xboole_0,sK2) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2841])).

cnf(c_1639,plain,
    ( X0_46 != X1_46
    | X2_46 != X1_46
    | X2_46 = X0_46 ),
    theory(equality)).

cnf(c_2373,plain,
    ( X0_46 != X1_46
    | X0_46 = k3_xboole_0(X2_46,X3_46)
    | k3_xboole_0(X2_46,X3_46) != X1_46 ),
    inference(instantiation,[status(thm)],[c_1639])).

cnf(c_2586,plain,
    ( sK0(sK2,X0_46) != X1_46
    | sK0(sK2,X0_46) = k3_xboole_0(X2_46,X3_46)
    | k3_xboole_0(X2_46,X3_46) != X1_46 ),
    inference(instantiation,[status(thm)],[c_2373])).

cnf(c_2588,plain,
    ( sK0(sK2,k1_xboole_0) = k3_xboole_0(k1_xboole_0,k1_xboole_0)
    | sK0(sK2,k1_xboole_0) != k1_xboole_0
    | k3_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2586])).

cnf(c_1638,plain,
    ( X0_46 = X0_46 ),
    theory(equality)).

cnf(c_2283,plain,
    ( k1_tops_1(sK2,sK3) = k1_tops_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1638])).

cnf(c_1640,plain,
    ( ~ r1_tarski(X0_46,X1_46)
    | r1_tarski(X2_46,X3_46)
    | X2_46 != X0_46
    | X3_46 != X1_46 ),
    theory(equality)).

cnf(c_2110,plain,
    ( r1_tarski(X0_46,X1_46)
    | ~ r1_tarski(k1_tops_1(sK2,sK3),sK3)
    | X0_46 != k1_tops_1(sK2,sK3)
    | X1_46 != sK3 ),
    inference(instantiation,[status(thm)],[c_1640])).

cnf(c_2282,plain,
    ( r1_tarski(k1_tops_1(sK2,sK3),X0_46)
    | ~ r1_tarski(k1_tops_1(sK2,sK3),sK3)
    | X0_46 != sK3
    | k1_tops_1(sK2,sK3) != k1_tops_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_2110])).

cnf(c_2285,plain,
    ( ~ r1_tarski(k1_tops_1(sK2,sK3),sK3)
    | r1_tarski(k1_tops_1(sK2,sK3),k1_xboole_0)
    | k1_tops_1(sK2,sK3) != k1_tops_1(sK2,sK3)
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_2282])).

cnf(c_2260,plain,
    ( ~ r1_tarski(k1_tops_1(sK2,sK3),k1_xboole_0)
    | k1_xboole_0 = k1_tops_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1631])).

cnf(c_1643,plain,
    ( ~ v3_pre_topc(X0_46,X0_49)
    | v3_pre_topc(X1_46,X0_49)
    | X1_46 != X0_46 ),
    theory(equality)).

cnf(c_2105,plain,
    ( v3_pre_topc(X0_46,sK2)
    | ~ v3_pre_topc(k1_tops_1(sK2,sK3),sK2)
    | X0_46 != k1_tops_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1643])).

cnf(c_2106,plain,
    ( X0_46 != k1_tops_1(sK2,sK3)
    | v3_pre_topc(X0_46,sK2) = iProver_top
    | v3_pre_topc(k1_tops_1(sK2,sK3),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2105])).

cnf(c_2108,plain,
    ( k1_xboole_0 != k1_tops_1(sK2,sK3)
    | v3_pre_topc(k1_tops_1(sK2,sK3),sK2) != iProver_top
    | v3_pre_topc(k1_xboole_0,sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2106])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_456,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_17])).

cnf(c_457,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(k1_tops_1(sK2,X0),X0) ),
    inference(unflattening,[status(thm)],[c_456])).

cnf(c_1622,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(k1_tops_1(sK2,X0_46),X0_46) ),
    inference(subtyping,[status(esa)],[c_457])).

cnf(c_2056,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(k1_tops_1(sK2,sK3),sK3) ),
    inference(instantiation,[status(thm)],[c_1622])).

cnf(c_6,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_18,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_250,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_18])).

cnf(c_251,plain,
    ( v3_pre_topc(k1_tops_1(sK2,X0),sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_250])).

cnf(c_255,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v3_pre_topc(k1_tops_1(sK2,X0),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_251,c_17])).

cnf(c_256,plain,
    ( v3_pre_topc(k1_tops_1(sK2,X0),sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(renaming,[status(thm)],[c_255])).

cnf(c_1629,plain,
    ( v3_pre_topc(k1_tops_1(sK2,X0_46),sK2)
    | ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(subtyping,[status(esa)],[c_256])).

cnf(c_2053,plain,
    ( v3_pre_topc(k1_tops_1(sK2,sK3),sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_1629])).

cnf(c_2054,plain,
    ( v3_pre_topc(k1_tops_1(sK2,sK3),sK2) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2053])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_22,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2849,c_2857,c_2843,c_2588,c_2283,c_2285,c_2260,c_2108,c_2073,c_2056,c_2054,c_1948,c_1630,c_22,c_15])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.11  % Command    : iproveropt_run.sh %d %s
% 0.11/0.32  % Computer   : n002.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 11:50:37 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  % Running in FOF mode
% 1.65/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.65/0.97  
% 1.65/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.65/0.97  
% 1.65/0.97  ------  iProver source info
% 1.65/0.97  
% 1.65/0.97  git: date: 2020-06-30 10:37:57 +0100
% 1.65/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.65/0.97  git: non_committed_changes: false
% 1.65/0.97  git: last_make_outside_of_git: false
% 1.65/0.97  
% 1.65/0.97  ------ 
% 1.65/0.97  
% 1.65/0.97  ------ Input Options
% 1.65/0.97  
% 1.65/0.97  --out_options                           all
% 1.65/0.97  --tptp_safe_out                         true
% 1.65/0.97  --problem_path                          ""
% 1.65/0.97  --include_path                          ""
% 1.65/0.97  --clausifier                            res/vclausify_rel
% 1.65/0.97  --clausifier_options                    --mode clausify
% 1.65/0.97  --stdin                                 false
% 1.65/0.97  --stats_out                             all
% 1.65/0.97  
% 1.65/0.97  ------ General Options
% 1.65/0.97  
% 1.65/0.97  --fof                                   false
% 1.65/0.97  --time_out_real                         305.
% 1.65/0.97  --time_out_virtual                      -1.
% 1.65/0.97  --symbol_type_check                     false
% 1.65/0.97  --clausify_out                          false
% 1.65/0.97  --sig_cnt_out                           false
% 1.65/0.97  --trig_cnt_out                          false
% 1.65/0.97  --trig_cnt_out_tolerance                1.
% 1.65/0.97  --trig_cnt_out_sk_spl                   false
% 1.65/0.97  --abstr_cl_out                          false
% 1.65/0.97  
% 1.65/0.97  ------ Global Options
% 1.65/0.97  
% 1.65/0.97  --schedule                              default
% 1.65/0.97  --add_important_lit                     false
% 1.65/0.97  --prop_solver_per_cl                    1000
% 1.65/0.97  --min_unsat_core                        false
% 1.65/0.97  --soft_assumptions                      false
% 1.65/0.97  --soft_lemma_size                       3
% 1.65/0.97  --prop_impl_unit_size                   0
% 1.65/0.97  --prop_impl_unit                        []
% 1.65/0.97  --share_sel_clauses                     true
% 1.65/0.97  --reset_solvers                         false
% 1.65/0.97  --bc_imp_inh                            [conj_cone]
% 1.65/0.97  --conj_cone_tolerance                   3.
% 1.65/0.97  --extra_neg_conj                        none
% 1.65/0.97  --large_theory_mode                     true
% 1.65/0.97  --prolific_symb_bound                   200
% 1.65/0.97  --lt_threshold                          2000
% 1.65/0.97  --clause_weak_htbl                      true
% 1.65/0.97  --gc_record_bc_elim                     false
% 1.65/0.97  
% 1.65/0.97  ------ Preprocessing Options
% 1.65/0.97  
% 1.65/0.97  --preprocessing_flag                    true
% 1.65/0.97  --time_out_prep_mult                    0.1
% 1.65/0.97  --splitting_mode                        input
% 1.65/0.97  --splitting_grd                         true
% 1.65/0.97  --splitting_cvd                         false
% 1.65/0.97  --splitting_cvd_svl                     false
% 1.65/0.97  --splitting_nvd                         32
% 1.65/0.97  --sub_typing                            true
% 1.65/0.97  --prep_gs_sim                           true
% 1.65/0.97  --prep_unflatten                        true
% 1.65/0.97  --prep_res_sim                          true
% 1.65/0.97  --prep_upred                            true
% 1.65/0.97  --prep_sem_filter                       exhaustive
% 1.65/0.97  --prep_sem_filter_out                   false
% 1.65/0.97  --pred_elim                             true
% 1.65/0.97  --res_sim_input                         true
% 1.65/0.97  --eq_ax_congr_red                       true
% 1.65/0.97  --pure_diseq_elim                       true
% 1.65/0.97  --brand_transform                       false
% 1.65/0.97  --non_eq_to_eq                          false
% 1.65/0.97  --prep_def_merge                        true
% 1.65/0.97  --prep_def_merge_prop_impl              false
% 1.65/0.97  --prep_def_merge_mbd                    true
% 1.65/0.97  --prep_def_merge_tr_red                 false
% 1.65/0.97  --prep_def_merge_tr_cl                  false
% 1.65/0.97  --smt_preprocessing                     true
% 1.65/0.97  --smt_ac_axioms                         fast
% 1.65/0.97  --preprocessed_out                      false
% 1.65/0.97  --preprocessed_stats                    false
% 1.65/0.97  
% 1.65/0.97  ------ Abstraction refinement Options
% 1.65/0.97  
% 1.65/0.97  --abstr_ref                             []
% 1.65/0.97  --abstr_ref_prep                        false
% 1.65/0.97  --abstr_ref_until_sat                   false
% 1.65/0.97  --abstr_ref_sig_restrict                funpre
% 1.65/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 1.65/0.97  --abstr_ref_under                       []
% 1.65/0.97  
% 1.65/0.97  ------ SAT Options
% 1.65/0.97  
% 1.65/0.97  --sat_mode                              false
% 1.65/0.97  --sat_fm_restart_options                ""
% 1.65/0.97  --sat_gr_def                            false
% 1.65/0.97  --sat_epr_types                         true
% 1.65/0.97  --sat_non_cyclic_types                  false
% 1.65/0.97  --sat_finite_models                     false
% 1.65/0.97  --sat_fm_lemmas                         false
% 1.65/0.97  --sat_fm_prep                           false
% 1.65/0.97  --sat_fm_uc_incr                        true
% 1.65/0.97  --sat_out_model                         small
% 1.65/0.97  --sat_out_clauses                       false
% 1.65/0.97  
% 1.65/0.97  ------ QBF Options
% 1.65/0.97  
% 1.65/0.97  --qbf_mode                              false
% 1.65/0.97  --qbf_elim_univ                         false
% 1.65/0.97  --qbf_dom_inst                          none
% 1.65/0.97  --qbf_dom_pre_inst                      false
% 1.65/0.97  --qbf_sk_in                             false
% 1.65/0.97  --qbf_pred_elim                         true
% 1.65/0.97  --qbf_split                             512
% 1.65/0.97  
% 1.65/0.97  ------ BMC1 Options
% 1.65/0.97  
% 1.65/0.97  --bmc1_incremental                      false
% 1.65/0.97  --bmc1_axioms                           reachable_all
% 1.65/0.97  --bmc1_min_bound                        0
% 1.65/0.97  --bmc1_max_bound                        -1
% 1.65/0.97  --bmc1_max_bound_default                -1
% 1.65/0.97  --bmc1_symbol_reachability              true
% 1.65/0.97  --bmc1_property_lemmas                  false
% 1.65/0.97  --bmc1_k_induction                      false
% 1.65/0.97  --bmc1_non_equiv_states                 false
% 1.65/0.97  --bmc1_deadlock                         false
% 1.65/0.97  --bmc1_ucm                              false
% 1.65/0.97  --bmc1_add_unsat_core                   none
% 1.65/0.97  --bmc1_unsat_core_children              false
% 1.65/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 1.65/0.97  --bmc1_out_stat                         full
% 1.65/0.97  --bmc1_ground_init                      false
% 1.65/0.97  --bmc1_pre_inst_next_state              false
% 1.65/0.97  --bmc1_pre_inst_state                   false
% 1.65/0.97  --bmc1_pre_inst_reach_state             false
% 1.65/0.97  --bmc1_out_unsat_core                   false
% 1.65/0.97  --bmc1_aig_witness_out                  false
% 1.65/0.97  --bmc1_verbose                          false
% 1.65/0.97  --bmc1_dump_clauses_tptp                false
% 1.65/0.97  --bmc1_dump_unsat_core_tptp             false
% 1.65/0.97  --bmc1_dump_file                        -
% 1.65/0.97  --bmc1_ucm_expand_uc_limit              128
% 1.65/0.97  --bmc1_ucm_n_expand_iterations          6
% 1.65/0.97  --bmc1_ucm_extend_mode                  1
% 1.65/0.97  --bmc1_ucm_init_mode                    2
% 1.65/0.97  --bmc1_ucm_cone_mode                    none
% 1.65/0.97  --bmc1_ucm_reduced_relation_type        0
% 1.65/0.97  --bmc1_ucm_relax_model                  4
% 1.65/0.97  --bmc1_ucm_full_tr_after_sat            true
% 1.65/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 1.65/0.97  --bmc1_ucm_layered_model                none
% 1.65/0.97  --bmc1_ucm_max_lemma_size               10
% 1.65/0.97  
% 1.65/0.97  ------ AIG Options
% 1.65/0.97  
% 1.65/0.97  --aig_mode                              false
% 1.65/0.97  
% 1.65/0.97  ------ Instantiation Options
% 1.65/0.97  
% 1.65/0.97  --instantiation_flag                    true
% 1.65/0.97  --inst_sos_flag                         false
% 1.65/0.97  --inst_sos_phase                        true
% 1.65/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.65/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.65/0.97  --inst_lit_sel_side                     num_symb
% 1.65/0.97  --inst_solver_per_active                1400
% 1.65/0.97  --inst_solver_calls_frac                1.
% 1.65/0.97  --inst_passive_queue_type               priority_queues
% 1.65/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.65/0.97  --inst_passive_queues_freq              [25;2]
% 1.65/0.97  --inst_dismatching                      true
% 1.65/0.97  --inst_eager_unprocessed_to_passive     true
% 1.65/0.97  --inst_prop_sim_given                   true
% 1.65/0.97  --inst_prop_sim_new                     false
% 1.65/0.97  --inst_subs_new                         false
% 1.65/0.97  --inst_eq_res_simp                      false
% 1.65/0.97  --inst_subs_given                       false
% 1.65/0.97  --inst_orphan_elimination               true
% 1.65/0.97  --inst_learning_loop_flag               true
% 1.65/0.97  --inst_learning_start                   3000
% 1.65/0.97  --inst_learning_factor                  2
% 1.65/0.97  --inst_start_prop_sim_after_learn       3
% 1.65/0.97  --inst_sel_renew                        solver
% 1.65/0.97  --inst_lit_activity_flag                true
% 1.65/0.97  --inst_restr_to_given                   false
% 1.65/0.97  --inst_activity_threshold               500
% 1.65/0.97  --inst_out_proof                        true
% 1.65/0.97  
% 1.65/0.97  ------ Resolution Options
% 1.65/0.97  
% 1.65/0.97  --resolution_flag                       true
% 1.65/0.97  --res_lit_sel                           adaptive
% 1.65/0.97  --res_lit_sel_side                      none
% 1.65/0.97  --res_ordering                          kbo
% 1.65/0.97  --res_to_prop_solver                    active
% 1.65/0.97  --res_prop_simpl_new                    false
% 1.65/0.97  --res_prop_simpl_given                  true
% 1.65/0.97  --res_passive_queue_type                priority_queues
% 1.65/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.65/0.97  --res_passive_queues_freq               [15;5]
% 1.65/0.97  --res_forward_subs                      full
% 1.65/0.97  --res_backward_subs                     full
% 1.65/0.97  --res_forward_subs_resolution           true
% 1.65/0.97  --res_backward_subs_resolution          true
% 1.65/0.97  --res_orphan_elimination                true
% 1.65/0.97  --res_time_limit                        2.
% 1.65/0.97  --res_out_proof                         true
% 1.65/0.97  
% 1.65/0.97  ------ Superposition Options
% 1.65/0.97  
% 1.65/0.97  --superposition_flag                    true
% 1.65/0.97  --sup_passive_queue_type                priority_queues
% 1.65/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.65/0.97  --sup_passive_queues_freq               [8;1;4]
% 1.65/0.97  --demod_completeness_check              fast
% 1.65/0.97  --demod_use_ground                      true
% 1.65/0.97  --sup_to_prop_solver                    passive
% 1.65/0.97  --sup_prop_simpl_new                    true
% 1.65/0.97  --sup_prop_simpl_given                  true
% 1.65/0.97  --sup_fun_splitting                     false
% 1.65/0.97  --sup_smt_interval                      50000
% 1.65/0.97  
% 1.65/0.97  ------ Superposition Simplification Setup
% 1.65/0.97  
% 1.65/0.97  --sup_indices_passive                   []
% 1.65/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.65/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.65/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.65/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 1.65/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.65/0.97  --sup_full_bw                           [BwDemod]
% 1.65/0.97  --sup_immed_triv                        [TrivRules]
% 1.65/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.65/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.65/0.97  --sup_immed_bw_main                     []
% 1.65/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.65/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 1.65/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.65/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.65/0.97  
% 1.65/0.97  ------ Combination Options
% 1.65/0.97  
% 1.65/0.97  --comb_res_mult                         3
% 1.65/0.97  --comb_sup_mult                         2
% 1.65/0.97  --comb_inst_mult                        10
% 1.65/0.97  
% 1.65/0.97  ------ Debug Options
% 1.65/0.97  
% 1.65/0.97  --dbg_backtrace                         false
% 1.65/0.97  --dbg_dump_prop_clauses                 false
% 1.65/0.97  --dbg_dump_prop_clauses_file            -
% 1.65/0.97  --dbg_out_stat                          false
% 1.65/0.97  ------ Parsing...
% 1.65/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.65/0.97  
% 1.65/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 1.65/0.97  
% 1.65/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.65/0.97  
% 1.65/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.65/0.97  ------ Proving...
% 1.65/0.97  ------ Problem Properties 
% 1.65/0.97  
% 1.65/0.97  
% 1.65/0.97  clauses                                 15
% 1.65/0.97  conjectures                             2
% 1.65/0.97  EPR                                     3
% 1.65/0.97  Horn                                    13
% 1.65/0.97  unary                                   5
% 1.65/0.97  binary                                  4
% 1.65/0.97  lits                                    39
% 1.65/0.97  lits eq                                 5
% 1.65/0.97  fd_pure                                 0
% 1.65/0.97  fd_pseudo                               0
% 1.65/0.97  fd_cond                                 1
% 1.65/0.97  fd_pseudo_cond                          0
% 1.65/0.97  AC symbols                              0
% 1.65/0.97  
% 1.65/0.97  ------ Schedule dynamic 5 is on 
% 1.65/0.97  
% 1.65/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.65/0.97  
% 1.65/0.97  
% 1.65/0.97  ------ 
% 1.65/0.97  Current options:
% 1.65/0.97  ------ 
% 1.65/0.97  
% 1.65/0.97  ------ Input Options
% 1.65/0.97  
% 1.65/0.97  --out_options                           all
% 1.65/0.97  --tptp_safe_out                         true
% 1.65/0.97  --problem_path                          ""
% 1.65/0.97  --include_path                          ""
% 1.65/0.97  --clausifier                            res/vclausify_rel
% 1.65/0.97  --clausifier_options                    --mode clausify
% 1.65/0.97  --stdin                                 false
% 1.65/0.97  --stats_out                             all
% 1.65/0.97  
% 1.65/0.97  ------ General Options
% 1.65/0.97  
% 1.65/0.97  --fof                                   false
% 1.65/0.97  --time_out_real                         305.
% 1.65/0.97  --time_out_virtual                      -1.
% 1.65/0.97  --symbol_type_check                     false
% 1.65/0.97  --clausify_out                          false
% 1.65/0.97  --sig_cnt_out                           false
% 1.65/0.97  --trig_cnt_out                          false
% 1.65/0.97  --trig_cnt_out_tolerance                1.
% 1.65/0.97  --trig_cnt_out_sk_spl                   false
% 1.65/0.97  --abstr_cl_out                          false
% 1.65/0.97  
% 1.65/0.97  ------ Global Options
% 1.65/0.97  
% 1.65/0.97  --schedule                              default
% 1.65/0.97  --add_important_lit                     false
% 1.65/0.97  --prop_solver_per_cl                    1000
% 1.65/0.97  --min_unsat_core                        false
% 1.65/0.97  --soft_assumptions                      false
% 1.65/0.97  --soft_lemma_size                       3
% 1.65/0.97  --prop_impl_unit_size                   0
% 1.65/0.97  --prop_impl_unit                        []
% 1.65/0.97  --share_sel_clauses                     true
% 1.65/0.97  --reset_solvers                         false
% 1.65/0.97  --bc_imp_inh                            [conj_cone]
% 1.65/0.97  --conj_cone_tolerance                   3.
% 1.65/0.97  --extra_neg_conj                        none
% 1.65/0.97  --large_theory_mode                     true
% 1.65/0.97  --prolific_symb_bound                   200
% 1.65/0.97  --lt_threshold                          2000
% 1.65/0.97  --clause_weak_htbl                      true
% 1.65/0.97  --gc_record_bc_elim                     false
% 1.65/0.97  
% 1.65/0.97  ------ Preprocessing Options
% 1.65/0.97  
% 1.65/0.97  --preprocessing_flag                    true
% 1.65/0.97  --time_out_prep_mult                    0.1
% 1.65/0.97  --splitting_mode                        input
% 1.65/0.97  --splitting_grd                         true
% 1.65/0.97  --splitting_cvd                         false
% 1.65/0.97  --splitting_cvd_svl                     false
% 1.65/0.97  --splitting_nvd                         32
% 1.65/0.97  --sub_typing                            true
% 1.65/0.97  --prep_gs_sim                           true
% 1.65/0.97  --prep_unflatten                        true
% 1.65/0.97  --prep_res_sim                          true
% 1.65/0.97  --prep_upred                            true
% 1.65/0.97  --prep_sem_filter                       exhaustive
% 1.65/0.97  --prep_sem_filter_out                   false
% 1.65/0.97  --pred_elim                             true
% 1.65/0.97  --res_sim_input                         true
% 1.65/0.97  --eq_ax_congr_red                       true
% 1.65/0.97  --pure_diseq_elim                       true
% 1.65/0.97  --brand_transform                       false
% 1.65/0.97  --non_eq_to_eq                          false
% 1.65/0.97  --prep_def_merge                        true
% 1.65/0.97  --prep_def_merge_prop_impl              false
% 1.65/0.97  --prep_def_merge_mbd                    true
% 1.65/0.97  --prep_def_merge_tr_red                 false
% 1.65/0.97  --prep_def_merge_tr_cl                  false
% 1.65/0.97  --smt_preprocessing                     true
% 1.65/0.97  --smt_ac_axioms                         fast
% 1.65/0.97  --preprocessed_out                      false
% 1.65/0.97  --preprocessed_stats                    false
% 1.65/0.97  
% 1.65/0.97  ------ Abstraction refinement Options
% 1.65/0.97  
% 1.65/0.97  --abstr_ref                             []
% 1.65/0.97  --abstr_ref_prep                        false
% 1.65/0.97  --abstr_ref_until_sat                   false
% 1.65/0.97  --abstr_ref_sig_restrict                funpre
% 1.65/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 1.65/0.97  --abstr_ref_under                       []
% 1.65/0.97  
% 1.65/0.97  ------ SAT Options
% 1.65/0.97  
% 1.65/0.97  --sat_mode                              false
% 1.65/0.97  --sat_fm_restart_options                ""
% 1.65/0.97  --sat_gr_def                            false
% 1.65/0.97  --sat_epr_types                         true
% 1.65/0.97  --sat_non_cyclic_types                  false
% 1.65/0.97  --sat_finite_models                     false
% 1.65/0.97  --sat_fm_lemmas                         false
% 1.65/0.97  --sat_fm_prep                           false
% 1.65/0.97  --sat_fm_uc_incr                        true
% 1.65/0.97  --sat_out_model                         small
% 1.65/0.97  --sat_out_clauses                       false
% 1.65/0.97  
% 1.65/0.97  ------ QBF Options
% 1.65/0.97  
% 1.65/0.97  --qbf_mode                              false
% 1.65/0.97  --qbf_elim_univ                         false
% 1.65/0.97  --qbf_dom_inst                          none
% 1.65/0.97  --qbf_dom_pre_inst                      false
% 1.65/0.97  --qbf_sk_in                             false
% 1.65/0.97  --qbf_pred_elim                         true
% 1.65/0.97  --qbf_split                             512
% 1.65/0.97  
% 1.65/0.97  ------ BMC1 Options
% 1.65/0.97  
% 1.65/0.97  --bmc1_incremental                      false
% 1.65/0.97  --bmc1_axioms                           reachable_all
% 1.65/0.97  --bmc1_min_bound                        0
% 1.65/0.97  --bmc1_max_bound                        -1
% 1.65/0.97  --bmc1_max_bound_default                -1
% 1.65/0.97  --bmc1_symbol_reachability              true
% 1.65/0.97  --bmc1_property_lemmas                  false
% 1.65/0.97  --bmc1_k_induction                      false
% 1.65/0.97  --bmc1_non_equiv_states                 false
% 1.65/0.97  --bmc1_deadlock                         false
% 1.65/0.97  --bmc1_ucm                              false
% 1.65/0.97  --bmc1_add_unsat_core                   none
% 1.65/0.97  --bmc1_unsat_core_children              false
% 1.65/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 1.65/0.97  --bmc1_out_stat                         full
% 1.65/0.97  --bmc1_ground_init                      false
% 1.65/0.97  --bmc1_pre_inst_next_state              false
% 1.65/0.97  --bmc1_pre_inst_state                   false
% 1.65/0.97  --bmc1_pre_inst_reach_state             false
% 1.65/0.97  --bmc1_out_unsat_core                   false
% 1.65/0.97  --bmc1_aig_witness_out                  false
% 1.65/0.97  --bmc1_verbose                          false
% 1.65/0.97  --bmc1_dump_clauses_tptp                false
% 1.65/0.97  --bmc1_dump_unsat_core_tptp             false
% 1.65/0.97  --bmc1_dump_file                        -
% 1.65/0.97  --bmc1_ucm_expand_uc_limit              128
% 1.65/0.97  --bmc1_ucm_n_expand_iterations          6
% 1.65/0.97  --bmc1_ucm_extend_mode                  1
% 1.65/0.97  --bmc1_ucm_init_mode                    2
% 1.65/0.97  --bmc1_ucm_cone_mode                    none
% 1.65/0.97  --bmc1_ucm_reduced_relation_type        0
% 1.65/0.97  --bmc1_ucm_relax_model                  4
% 1.65/0.97  --bmc1_ucm_full_tr_after_sat            true
% 1.65/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 1.65/0.97  --bmc1_ucm_layered_model                none
% 1.65/0.97  --bmc1_ucm_max_lemma_size               10
% 1.65/0.97  
% 1.65/0.97  ------ AIG Options
% 1.65/0.97  
% 1.65/0.97  --aig_mode                              false
% 1.65/0.97  
% 1.65/0.97  ------ Instantiation Options
% 1.65/0.97  
% 1.65/0.97  --instantiation_flag                    true
% 1.65/0.97  --inst_sos_flag                         false
% 1.65/0.97  --inst_sos_phase                        true
% 1.65/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.65/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.65/0.97  --inst_lit_sel_side                     none
% 1.65/0.97  --inst_solver_per_active                1400
% 1.65/0.97  --inst_solver_calls_frac                1.
% 1.65/0.97  --inst_passive_queue_type               priority_queues
% 1.65/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.65/0.97  --inst_passive_queues_freq              [25;2]
% 1.65/0.97  --inst_dismatching                      true
% 1.65/0.97  --inst_eager_unprocessed_to_passive     true
% 1.65/0.97  --inst_prop_sim_given                   true
% 1.65/0.97  --inst_prop_sim_new                     false
% 1.65/0.97  --inst_subs_new                         false
% 1.65/0.97  --inst_eq_res_simp                      false
% 1.65/0.97  --inst_subs_given                       false
% 1.65/0.97  --inst_orphan_elimination               true
% 1.65/0.97  --inst_learning_loop_flag               true
% 1.65/0.97  --inst_learning_start                   3000
% 1.65/0.97  --inst_learning_factor                  2
% 1.65/0.97  --inst_start_prop_sim_after_learn       3
% 1.65/0.97  --inst_sel_renew                        solver
% 1.65/0.97  --inst_lit_activity_flag                true
% 1.65/0.97  --inst_restr_to_given                   false
% 1.65/0.97  --inst_activity_threshold               500
% 1.65/0.97  --inst_out_proof                        true
% 1.65/0.97  
% 1.65/0.97  ------ Resolution Options
% 1.65/0.97  
% 1.65/0.97  --resolution_flag                       false
% 1.65/0.97  --res_lit_sel                           adaptive
% 1.65/0.97  --res_lit_sel_side                      none
% 1.65/0.97  --res_ordering                          kbo
% 1.65/0.97  --res_to_prop_solver                    active
% 1.65/0.97  --res_prop_simpl_new                    false
% 1.65/0.97  --res_prop_simpl_given                  true
% 1.65/0.97  --res_passive_queue_type                priority_queues
% 1.65/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.65/0.97  --res_passive_queues_freq               [15;5]
% 1.65/0.97  --res_forward_subs                      full
% 1.65/0.97  --res_backward_subs                     full
% 1.65/0.97  --res_forward_subs_resolution           true
% 1.65/0.97  --res_backward_subs_resolution          true
% 1.65/0.97  --res_orphan_elimination                true
% 1.65/0.97  --res_time_limit                        2.
% 1.65/0.97  --res_out_proof                         true
% 1.65/0.97  
% 1.65/0.97  ------ Superposition Options
% 1.65/0.97  
% 1.65/0.97  --superposition_flag                    true
% 1.65/0.97  --sup_passive_queue_type                priority_queues
% 1.65/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.65/0.97  --sup_passive_queues_freq               [8;1;4]
% 1.65/0.97  --demod_completeness_check              fast
% 1.65/0.97  --demod_use_ground                      true
% 1.65/0.97  --sup_to_prop_solver                    passive
% 1.65/0.97  --sup_prop_simpl_new                    true
% 1.65/0.97  --sup_prop_simpl_given                  true
% 1.65/0.97  --sup_fun_splitting                     false
% 1.65/0.97  --sup_smt_interval                      50000
% 1.65/0.97  
% 1.65/0.97  ------ Superposition Simplification Setup
% 1.65/0.97  
% 1.65/0.97  --sup_indices_passive                   []
% 1.65/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.65/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.65/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.65/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 1.65/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.65/0.97  --sup_full_bw                           [BwDemod]
% 1.65/0.97  --sup_immed_triv                        [TrivRules]
% 1.65/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.65/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.65/0.97  --sup_immed_bw_main                     []
% 1.65/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.65/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 1.65/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.65/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.65/0.97  
% 1.65/0.97  ------ Combination Options
% 1.65/0.97  
% 1.65/0.97  --comb_res_mult                         3
% 1.65/0.97  --comb_sup_mult                         2
% 1.65/0.97  --comb_inst_mult                        10
% 1.65/0.97  
% 1.65/0.97  ------ Debug Options
% 1.65/0.97  
% 1.65/0.97  --dbg_backtrace                         false
% 1.65/0.97  --dbg_dump_prop_clauses                 false
% 1.65/0.97  --dbg_dump_prop_clauses_file            -
% 1.65/0.97  --dbg_out_stat                          false
% 1.65/0.97  
% 1.65/0.97  
% 1.65/0.97  
% 1.65/0.97  
% 1.65/0.97  ------ Proving...
% 1.65/0.97  
% 1.65/0.97  
% 1.65/0.97  % SZS status Theorem for theBenchmark.p
% 1.65/0.97  
% 1.65/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 1.65/0.97  
% 1.65/0.97  fof(f6,axiom,(
% 1.65/0.97    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.65/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.65/0.97  
% 1.65/0.97  fof(f39,plain,(
% 1.65/0.97    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.65/0.97    inference(cnf_transformation,[],[f6])).
% 1.65/0.97  
% 1.65/0.97  fof(f10,axiom,(
% 1.65/0.97    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0))) & r1_tarski(X2,X1))))))),
% 1.65/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.65/0.97  
% 1.65/0.97  fof(f22,plain,(
% 1.65/0.97    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((? [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.65/0.97    inference(ennf_transformation,[],[f10])).
% 1.65/0.97  
% 1.65/0.97  fof(f23,plain,(
% 1.65/0.97    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.65/0.97    inference(flattening,[],[f22])).
% 1.65/0.97  
% 1.65/0.97  fof(f26,plain,(
% 1.65/0.97    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.65/0.97    inference(nnf_transformation,[],[f23])).
% 1.65/0.97  
% 1.65/0.97  fof(f27,plain,(
% 1.65/0.97    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (? [X5] : (k9_subset_1(u1_struct_0(X0),X1,X5) = X4 & v3_pre_topc(X5,X0) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.65/0.97    inference(rectify,[],[f26])).
% 1.65/0.97  
% 1.65/0.97  fof(f29,plain,(
% 1.65/0.97    ! [X4,X1,X0] : (? [X5] : (k9_subset_1(u1_struct_0(X0),X1,X5) = X4 & v3_pre_topc(X5,X0) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) => (k9_subset_1(u1_struct_0(X0),X1,sK1(X0,X1,X4)) = X4 & v3_pre_topc(sK1(X0,X1,X4),X0) & m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.65/0.97    introduced(choice_axiom,[])).
% 1.65/0.97  
% 1.65/0.97  fof(f28,plain,(
% 1.65/0.97    ! [X1,X0] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK0(X0,X1) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(sK0(X0,X1),X1) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.65/0.97    introduced(choice_axiom,[])).
% 1.65/0.97  
% 1.65/0.97  fof(f30,plain,(
% 1.65/0.97    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK0(X0,X1) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(sK0(X0,X1),X1) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : ((k9_subset_1(u1_struct_0(X0),X1,sK1(X0,X1,X4)) = X4 & v3_pre_topc(sK1(X0,X1,X4),X0) & m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.65/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f29,f28])).
% 1.65/0.97  
% 1.65/0.97  fof(f46,plain,(
% 1.65/0.97    ( ! [X0,X1] : (v2_tex_2(X1,X0) | r1_tarski(sK0(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.65/0.97    inference(cnf_transformation,[],[f30])).
% 1.65/0.97  
% 1.65/0.97  fof(f11,conjecture,(
% 1.65/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 1.65/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.65/0.97  
% 1.65/0.97  fof(f12,negated_conjecture,(
% 1.65/0.97    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 1.65/0.97    inference(negated_conjecture,[],[f11])).
% 1.65/0.97  
% 1.65/0.97  fof(f13,plain,(
% 1.65/0.97    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 1.65/0.97    inference(pure_predicate_removal,[],[f12])).
% 1.65/0.97  
% 1.65/0.97  fof(f24,plain,(
% 1.65/0.97    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.65/0.97    inference(ennf_transformation,[],[f13])).
% 1.65/0.97  
% 1.65/0.97  fof(f25,plain,(
% 1.65/0.97    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.65/0.97    inference(flattening,[],[f24])).
% 1.65/0.97  
% 1.65/0.97  fof(f32,plain,(
% 1.65/0.97    ( ! [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => (~v2_tex_2(sK3,X0) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(sK3))) )),
% 1.65/0.97    introduced(choice_axiom,[])).
% 1.65/0.97  
% 1.65/0.97  fof(f31,plain,(
% 1.65/0.97    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (~v2_tex_2(X1,sK2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) & v1_xboole_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2))),
% 1.65/0.97    introduced(choice_axiom,[])).
% 1.65/0.97  
% 1.65/0.97  fof(f33,plain,(
% 1.65/0.97    (~v2_tex_2(sK3,sK2) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) & v1_xboole_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2)),
% 1.65/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f25,f32,f31])).
% 1.65/0.97  
% 1.65/0.97  fof(f49,plain,(
% 1.65/0.97    l1_pre_topc(sK2)),
% 1.65/0.97    inference(cnf_transformation,[],[f33])).
% 1.65/0.97  
% 1.65/0.97  fof(f52,plain,(
% 1.65/0.97    ~v2_tex_2(sK3,sK2)),
% 1.65/0.97    inference(cnf_transformation,[],[f33])).
% 1.65/0.97  
% 1.65/0.97  fof(f1,axiom,(
% 1.65/0.97    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.65/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.65/0.97  
% 1.65/0.97  fof(f15,plain,(
% 1.65/0.97    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.65/0.97    inference(ennf_transformation,[],[f1])).
% 1.65/0.97  
% 1.65/0.97  fof(f34,plain,(
% 1.65/0.97    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 1.65/0.97    inference(cnf_transformation,[],[f15])).
% 1.65/0.97  
% 1.65/0.97  fof(f50,plain,(
% 1.65/0.97    v1_xboole_0(sK3)),
% 1.65/0.97    inference(cnf_transformation,[],[f33])).
% 1.65/0.97  
% 1.65/0.97  fof(f3,axiom,(
% 1.65/0.97    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.65/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.65/0.97  
% 1.65/0.97  fof(f36,plain,(
% 1.65/0.97    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.65/0.97    inference(cnf_transformation,[],[f3])).
% 1.65/0.97  
% 1.65/0.97  fof(f4,axiom,(
% 1.65/0.97    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 1.65/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.65/0.97  
% 1.65/0.97  fof(f16,plain,(
% 1.65/0.97    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 1.65/0.97    inference(ennf_transformation,[],[f4])).
% 1.65/0.97  
% 1.65/0.97  fof(f17,plain,(
% 1.65/0.97    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 1.65/0.97    inference(flattening,[],[f16])).
% 1.65/0.97  
% 1.65/0.97  fof(f37,plain,(
% 1.65/0.97    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 1.65/0.97    inference(cnf_transformation,[],[f17])).
% 1.65/0.97  
% 1.65/0.97  fof(f2,axiom,(
% 1.65/0.97    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.65/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.65/0.97  
% 1.65/0.97  fof(f35,plain,(
% 1.65/0.97    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.65/0.97    inference(cnf_transformation,[],[f2])).
% 1.65/0.97  
% 1.65/0.97  fof(f5,axiom,(
% 1.65/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 1.65/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.65/0.97  
% 1.65/0.97  fof(f18,plain,(
% 1.65/0.97    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.65/0.97    inference(ennf_transformation,[],[f5])).
% 1.65/0.97  
% 1.65/0.97  fof(f38,plain,(
% 1.65/0.97    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 1.65/0.97    inference(cnf_transformation,[],[f18])).
% 1.65/0.97  
% 1.65/0.97  fof(f47,plain,(
% 1.65/0.97    ( ! [X0,X3,X1] : (v2_tex_2(X1,X0) | k9_subset_1(u1_struct_0(X0),X1,X3) != sK0(X0,X1) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.65/0.97    inference(cnf_transformation,[],[f30])).
% 1.65/0.97  
% 1.65/0.97  fof(f9,axiom,(
% 1.65/0.97    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 1.65/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.65/0.97  
% 1.65/0.97  fof(f21,plain,(
% 1.65/0.97    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.65/0.97    inference(ennf_transformation,[],[f9])).
% 1.65/0.97  
% 1.65/0.97  fof(f41,plain,(
% 1.65/0.97    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.65/0.97    inference(cnf_transformation,[],[f21])).
% 1.65/0.97  
% 1.65/0.97  fof(f8,axiom,(
% 1.65/0.97    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 1.65/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.65/0.97  
% 1.65/0.97  fof(f19,plain,(
% 1.65/0.97    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.65/0.97    inference(ennf_transformation,[],[f8])).
% 1.65/0.97  
% 1.65/0.97  fof(f20,plain,(
% 1.65/0.97    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.65/0.97    inference(flattening,[],[f19])).
% 1.65/0.97  
% 1.65/0.97  fof(f40,plain,(
% 1.65/0.97    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.65/0.97    inference(cnf_transformation,[],[f20])).
% 1.65/0.97  
% 1.65/0.97  fof(f48,plain,(
% 1.65/0.97    v2_pre_topc(sK2)),
% 1.65/0.97    inference(cnf_transformation,[],[f33])).
% 1.65/0.97  
% 1.65/0.97  fof(f51,plain,(
% 1.65/0.97    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 1.65/0.97    inference(cnf_transformation,[],[f33])).
% 1.65/0.97  
% 1.65/0.97  cnf(c_5,plain,
% 1.65/0.97      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 1.65/0.97      inference(cnf_transformation,[],[f39]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_1634,plain,
% 1.65/0.97      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0_48)) ),
% 1.65/0.97      inference(subtyping,[status(esa)],[c_5]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_1932,plain,
% 1.65/0.97      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0_48)) = iProver_top ),
% 1.65/0.97      inference(predicate_to_equality,[status(thm)],[c_1634]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_9,plain,
% 1.65/0.97      ( v2_tex_2(X0,X1)
% 1.65/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.65/0.97      | r1_tarski(sK0(X1,X0),X0)
% 1.65/0.97      | ~ l1_pre_topc(X1) ),
% 1.65/0.97      inference(cnf_transformation,[],[f46]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_17,negated_conjecture,
% 1.65/0.97      ( l1_pre_topc(sK2) ),
% 1.65/0.97      inference(cnf_transformation,[],[f49]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_420,plain,
% 1.65/0.97      ( v2_tex_2(X0,X1)
% 1.65/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.65/0.97      | r1_tarski(sK0(X1,X0),X0)
% 1.65/0.97      | sK2 != X1 ),
% 1.65/0.97      inference(resolution_lifted,[status(thm)],[c_9,c_17]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_421,plain,
% 1.65/0.97      ( v2_tex_2(X0,sK2)
% 1.65/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.65/0.97      | r1_tarski(sK0(sK2,X0),X0) ),
% 1.65/0.97      inference(unflattening,[status(thm)],[c_420]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_1624,plain,
% 1.65/0.97      ( v2_tex_2(X0_46,sK2)
% 1.65/0.97      | ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.65/0.97      | r1_tarski(sK0(sK2,X0_46),X0_46) ),
% 1.65/0.97      inference(subtyping,[status(esa)],[c_421]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_1941,plain,
% 1.65/0.97      ( v2_tex_2(X0_46,sK2) = iProver_top
% 1.65/0.97      | m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.65/0.97      | r1_tarski(sK0(sK2,X0_46),X0_46) = iProver_top ),
% 1.65/0.97      inference(predicate_to_equality,[status(thm)],[c_1624]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_2393,plain,
% 1.65/0.97      ( v2_tex_2(k1_xboole_0,sK2) = iProver_top
% 1.65/0.97      | r1_tarski(sK0(sK2,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 1.65/0.97      inference(superposition,[status(thm)],[c_1932,c_1941]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_1679,plain,
% 1.65/0.97      ( v2_tex_2(X0_46,sK2) = iProver_top
% 1.65/0.97      | m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.65/0.97      | r1_tarski(sK0(sK2,X0_46),X0_46) = iProver_top ),
% 1.65/0.97      inference(predicate_to_equality,[status(thm)],[c_1624]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_1681,plain,
% 1.65/0.97      ( v2_tex_2(k1_xboole_0,sK2) = iProver_top
% 1.65/0.97      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.65/0.97      | r1_tarski(sK0(sK2,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 1.65/0.97      inference(instantiation,[status(thm)],[c_1679]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_14,negated_conjecture,
% 1.65/0.97      ( ~ v2_tex_2(sK3,sK2) ),
% 1.65/0.97      inference(cnf_transformation,[],[f52]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_1633,negated_conjecture,
% 1.65/0.97      ( ~ v2_tex_2(sK3,sK2) ),
% 1.65/0.97      inference(subtyping,[status(esa)],[c_14]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_1933,plain,
% 1.65/0.97      ( v2_tex_2(sK3,sK2) != iProver_top ),
% 1.65/0.97      inference(predicate_to_equality,[status(thm)],[c_1633]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_0,plain,
% 1.65/0.97      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 1.65/0.97      inference(cnf_transformation,[],[f34]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_16,negated_conjecture,
% 1.65/0.97      ( v1_xboole_0(sK3) ),
% 1.65/0.97      inference(cnf_transformation,[],[f50]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_241,plain,
% 1.65/0.97      ( sK3 != X0 | k1_xboole_0 = X0 ),
% 1.65/0.97      inference(resolution_lifted,[status(thm)],[c_0,c_16]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_242,plain,
% 1.65/0.97      ( k1_xboole_0 = sK3 ),
% 1.65/0.97      inference(unflattening,[status(thm)],[c_241]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_1630,plain,
% 1.65/0.97      ( k1_xboole_0 = sK3 ),
% 1.65/0.97      inference(subtyping,[status(esa)],[c_242]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_1948,plain,
% 1.65/0.97      ( v2_tex_2(k1_xboole_0,sK2) != iProver_top ),
% 1.65/0.97      inference(light_normalisation,[status(thm)],[c_1933,c_1630]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_2068,plain,
% 1.65/0.97      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 1.65/0.97      inference(instantiation,[status(thm)],[c_1634]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_2073,plain,
% 1.65/0.97      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 1.65/0.97      inference(predicate_to_equality,[status(thm)],[c_2068]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_2731,plain,
% 1.65/0.97      ( r1_tarski(sK0(sK2,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 1.65/0.97      inference(global_propositional_subsumption,
% 1.65/0.97                [status(thm)],
% 1.65/0.97                [c_2393,c_1681,c_1948,c_2073]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_2,plain,
% 1.65/0.97      ( r1_xboole_0(X0,k1_xboole_0) ),
% 1.65/0.97      inference(cnf_transformation,[],[f36]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_3,plain,
% 1.65/0.97      ( ~ r1_xboole_0(X0,X1) | ~ r1_tarski(X0,X1) | v1_xboole_0(X0) ),
% 1.65/0.97      inference(cnf_transformation,[],[f37]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_215,plain,
% 1.65/0.97      ( ~ r1_tarski(X0,X1)
% 1.65/0.97      | v1_xboole_0(X0)
% 1.65/0.97      | X0 != X2
% 1.65/0.97      | k1_xboole_0 != X1 ),
% 1.65/0.97      inference(resolution_lifted,[status(thm)],[c_2,c_3]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_216,plain,
% 1.65/0.97      ( ~ r1_tarski(X0,k1_xboole_0) | v1_xboole_0(X0) ),
% 1.65/0.97      inference(unflattening,[status(thm)],[c_215]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_230,plain,
% 1.65/0.97      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 1.65/0.97      inference(resolution,[status(thm)],[c_216,c_0]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_1631,plain,
% 1.65/0.97      ( ~ r1_tarski(X0_46,k1_xboole_0) | k1_xboole_0 = X0_46 ),
% 1.65/0.97      inference(subtyping,[status(esa)],[c_230]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_1935,plain,
% 1.65/0.97      ( k1_xboole_0 = X0_46
% 1.65/0.97      | r1_tarski(X0_46,k1_xboole_0) != iProver_top ),
% 1.65/0.97      inference(predicate_to_equality,[status(thm)],[c_1631]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_2849,plain,
% 1.65/0.97      ( sK0(sK2,k1_xboole_0) = k1_xboole_0 ),
% 1.65/0.97      inference(superposition,[status(thm)],[c_2731,c_1935]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_1,plain,
% 1.65/0.97      ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
% 1.65/0.97      inference(cnf_transformation,[],[f35]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_1636,plain,
% 1.65/0.97      ( r1_tarski(k3_xboole_0(X0_46,X1_46),X0_46) ),
% 1.65/0.97      inference(subtyping,[status(esa)],[c_1]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_1930,plain,
% 1.65/0.97      ( r1_tarski(k3_xboole_0(X0_46,X1_46),X0_46) = iProver_top ),
% 1.65/0.97      inference(predicate_to_equality,[status(thm)],[c_1636]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_2848,plain,
% 1.65/0.97      ( k3_xboole_0(k1_xboole_0,X0_46) = k1_xboole_0 ),
% 1.65/0.97      inference(superposition,[status(thm)],[c_1930,c_1935]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_2857,plain,
% 1.65/0.97      ( k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 1.65/0.97      inference(instantiation,[status(thm)],[c_2848]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_4,plain,
% 1.65/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.65/0.97      | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 1.65/0.97      inference(cnf_transformation,[],[f38]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_1635,plain,
% 1.65/0.97      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(X0_48))
% 1.65/0.97      | k9_subset_1(X0_48,X1_46,X0_46) = k3_xboole_0(X1_46,X0_46) ),
% 1.65/0.97      inference(subtyping,[status(esa)],[c_4]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_1931,plain,
% 1.65/0.97      ( k9_subset_1(X0_48,X0_46,X1_46) = k3_xboole_0(X0_46,X1_46)
% 1.65/0.97      | m1_subset_1(X1_46,k1_zfmisc_1(X0_48)) != iProver_top ),
% 1.65/0.97      inference(predicate_to_equality,[status(thm)],[c_1635]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_2340,plain,
% 1.65/0.97      ( k9_subset_1(X0_48,X0_46,k1_xboole_0) = k3_xboole_0(X0_46,k1_xboole_0) ),
% 1.65/0.97      inference(superposition,[status(thm)],[c_1932,c_1931]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_8,plain,
% 1.65/0.97      ( v2_tex_2(X0,X1)
% 1.65/0.97      | ~ v3_pre_topc(X2,X1)
% 1.65/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.65/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.65/0.97      | ~ l1_pre_topc(X1)
% 1.65/0.97      | k9_subset_1(u1_struct_0(X1),X0,X2) != sK0(X1,X0) ),
% 1.65/0.97      inference(cnf_transformation,[],[f47]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_435,plain,
% 1.65/0.97      ( v2_tex_2(X0,X1)
% 1.65/0.97      | ~ v3_pre_topc(X2,X1)
% 1.65/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.65/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.65/0.97      | k9_subset_1(u1_struct_0(X1),X0,X2) != sK0(X1,X0)
% 1.65/0.97      | sK2 != X1 ),
% 1.65/0.97      inference(resolution_lifted,[status(thm)],[c_8,c_17]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_436,plain,
% 1.65/0.97      ( v2_tex_2(X0,sK2)
% 1.65/0.97      | ~ v3_pre_topc(X1,sK2)
% 1.65/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.65/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.65/0.97      | k9_subset_1(u1_struct_0(sK2),X0,X1) != sK0(sK2,X0) ),
% 1.65/0.97      inference(unflattening,[status(thm)],[c_435]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_1623,plain,
% 1.65/0.97      ( v2_tex_2(X0_46,sK2)
% 1.65/0.97      | ~ v3_pre_topc(X1_46,sK2)
% 1.65/0.97      | ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.65/0.97      | ~ m1_subset_1(X1_46,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.65/0.97      | k9_subset_1(u1_struct_0(sK2),X0_46,X1_46) != sK0(sK2,X0_46) ),
% 1.65/0.97      inference(subtyping,[status(esa)],[c_436]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_1942,plain,
% 1.65/0.97      ( k9_subset_1(u1_struct_0(sK2),X0_46,X1_46) != sK0(sK2,X0_46)
% 1.65/0.97      | v2_tex_2(X0_46,sK2) = iProver_top
% 1.65/0.97      | v3_pre_topc(X1_46,sK2) != iProver_top
% 1.65/0.97      | m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.65/0.97      | m1_subset_1(X1_46,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 1.65/0.97      inference(predicate_to_equality,[status(thm)],[c_1623]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_2841,plain,
% 1.65/0.97      ( sK0(sK2,X0_46) != k3_xboole_0(X0_46,k1_xboole_0)
% 1.65/0.97      | v2_tex_2(X0_46,sK2) = iProver_top
% 1.65/0.97      | v3_pre_topc(k1_xboole_0,sK2) != iProver_top
% 1.65/0.97      | m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.65/0.97      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 1.65/0.97      inference(superposition,[status(thm)],[c_2340,c_1942]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_2843,plain,
% 1.65/0.97      ( sK0(sK2,k1_xboole_0) != k3_xboole_0(k1_xboole_0,k1_xboole_0)
% 1.65/0.97      | v2_tex_2(k1_xboole_0,sK2) = iProver_top
% 1.65/0.97      | v3_pre_topc(k1_xboole_0,sK2) != iProver_top
% 1.65/0.97      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 1.65/0.97      inference(instantiation,[status(thm)],[c_2841]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_1639,plain,
% 1.65/0.97      ( X0_46 != X1_46 | X2_46 != X1_46 | X2_46 = X0_46 ),
% 1.65/0.97      theory(equality) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_2373,plain,
% 1.65/0.97      ( X0_46 != X1_46
% 1.65/0.97      | X0_46 = k3_xboole_0(X2_46,X3_46)
% 1.65/0.97      | k3_xboole_0(X2_46,X3_46) != X1_46 ),
% 1.65/0.97      inference(instantiation,[status(thm)],[c_1639]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_2586,plain,
% 1.65/0.97      ( sK0(sK2,X0_46) != X1_46
% 1.65/0.97      | sK0(sK2,X0_46) = k3_xboole_0(X2_46,X3_46)
% 1.65/0.97      | k3_xboole_0(X2_46,X3_46) != X1_46 ),
% 1.65/0.97      inference(instantiation,[status(thm)],[c_2373]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_2588,plain,
% 1.65/0.97      ( sK0(sK2,k1_xboole_0) = k3_xboole_0(k1_xboole_0,k1_xboole_0)
% 1.65/0.97      | sK0(sK2,k1_xboole_0) != k1_xboole_0
% 1.65/0.97      | k3_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
% 1.65/0.97      inference(instantiation,[status(thm)],[c_2586]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_1638,plain,( X0_46 = X0_46 ),theory(equality) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_2283,plain,
% 1.65/0.97      ( k1_tops_1(sK2,sK3) = k1_tops_1(sK2,sK3) ),
% 1.65/0.97      inference(instantiation,[status(thm)],[c_1638]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_1640,plain,
% 1.65/0.97      ( ~ r1_tarski(X0_46,X1_46)
% 1.65/0.97      | r1_tarski(X2_46,X3_46)
% 1.65/0.97      | X2_46 != X0_46
% 1.65/0.97      | X3_46 != X1_46 ),
% 1.65/0.97      theory(equality) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_2110,plain,
% 1.65/0.97      ( r1_tarski(X0_46,X1_46)
% 1.65/0.97      | ~ r1_tarski(k1_tops_1(sK2,sK3),sK3)
% 1.65/0.97      | X0_46 != k1_tops_1(sK2,sK3)
% 1.65/0.97      | X1_46 != sK3 ),
% 1.65/0.97      inference(instantiation,[status(thm)],[c_1640]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_2282,plain,
% 1.65/0.97      ( r1_tarski(k1_tops_1(sK2,sK3),X0_46)
% 1.65/0.97      | ~ r1_tarski(k1_tops_1(sK2,sK3),sK3)
% 1.65/0.97      | X0_46 != sK3
% 1.65/0.97      | k1_tops_1(sK2,sK3) != k1_tops_1(sK2,sK3) ),
% 1.65/0.97      inference(instantiation,[status(thm)],[c_2110]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_2285,plain,
% 1.65/0.97      ( ~ r1_tarski(k1_tops_1(sK2,sK3),sK3)
% 1.65/0.97      | r1_tarski(k1_tops_1(sK2,sK3),k1_xboole_0)
% 1.65/0.97      | k1_tops_1(sK2,sK3) != k1_tops_1(sK2,sK3)
% 1.65/0.97      | k1_xboole_0 != sK3 ),
% 1.65/0.97      inference(instantiation,[status(thm)],[c_2282]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_2260,plain,
% 1.65/0.97      ( ~ r1_tarski(k1_tops_1(sK2,sK3),k1_xboole_0)
% 1.65/0.97      | k1_xboole_0 = k1_tops_1(sK2,sK3) ),
% 1.65/0.97      inference(instantiation,[status(thm)],[c_1631]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_1643,plain,
% 1.65/0.97      ( ~ v3_pre_topc(X0_46,X0_49)
% 1.65/0.97      | v3_pre_topc(X1_46,X0_49)
% 1.65/0.97      | X1_46 != X0_46 ),
% 1.65/0.97      theory(equality) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_2105,plain,
% 1.65/0.97      ( v3_pre_topc(X0_46,sK2)
% 1.65/0.97      | ~ v3_pre_topc(k1_tops_1(sK2,sK3),sK2)
% 1.65/0.97      | X0_46 != k1_tops_1(sK2,sK3) ),
% 1.65/0.97      inference(instantiation,[status(thm)],[c_1643]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_2106,plain,
% 1.65/0.97      ( X0_46 != k1_tops_1(sK2,sK3)
% 1.65/0.97      | v3_pre_topc(X0_46,sK2) = iProver_top
% 1.65/0.97      | v3_pre_topc(k1_tops_1(sK2,sK3),sK2) != iProver_top ),
% 1.65/0.97      inference(predicate_to_equality,[status(thm)],[c_2105]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_2108,plain,
% 1.65/0.97      ( k1_xboole_0 != k1_tops_1(sK2,sK3)
% 1.65/0.97      | v3_pre_topc(k1_tops_1(sK2,sK3),sK2) != iProver_top
% 1.65/0.97      | v3_pre_topc(k1_xboole_0,sK2) = iProver_top ),
% 1.65/0.97      inference(instantiation,[status(thm)],[c_2106]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_7,plain,
% 1.65/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.65/0.97      | r1_tarski(k1_tops_1(X1,X0),X0)
% 1.65/0.97      | ~ l1_pre_topc(X1) ),
% 1.65/0.97      inference(cnf_transformation,[],[f41]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_456,plain,
% 1.65/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.65/0.97      | r1_tarski(k1_tops_1(X1,X0),X0)
% 1.65/0.97      | sK2 != X1 ),
% 1.65/0.97      inference(resolution_lifted,[status(thm)],[c_7,c_17]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_457,plain,
% 1.65/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.65/0.97      | r1_tarski(k1_tops_1(sK2,X0),X0) ),
% 1.65/0.97      inference(unflattening,[status(thm)],[c_456]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_1622,plain,
% 1.65/0.97      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.65/0.97      | r1_tarski(k1_tops_1(sK2,X0_46),X0_46) ),
% 1.65/0.97      inference(subtyping,[status(esa)],[c_457]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_2056,plain,
% 1.65/0.97      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.65/0.97      | r1_tarski(k1_tops_1(sK2,sK3),sK3) ),
% 1.65/0.97      inference(instantiation,[status(thm)],[c_1622]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_6,plain,
% 1.65/0.97      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 1.65/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 1.65/0.97      | ~ v2_pre_topc(X0)
% 1.65/0.97      | ~ l1_pre_topc(X0) ),
% 1.65/0.97      inference(cnf_transformation,[],[f40]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_18,negated_conjecture,
% 1.65/0.97      ( v2_pre_topc(sK2) ),
% 1.65/0.97      inference(cnf_transformation,[],[f48]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_250,plain,
% 1.65/0.97      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 1.65/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 1.65/0.97      | ~ l1_pre_topc(X0)
% 1.65/0.97      | sK2 != X0 ),
% 1.65/0.97      inference(resolution_lifted,[status(thm)],[c_6,c_18]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_251,plain,
% 1.65/0.97      ( v3_pre_topc(k1_tops_1(sK2,X0),sK2)
% 1.65/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.65/0.97      | ~ l1_pre_topc(sK2) ),
% 1.65/0.97      inference(unflattening,[status(thm)],[c_250]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_255,plain,
% 1.65/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.65/0.97      | v3_pre_topc(k1_tops_1(sK2,X0),sK2) ),
% 1.65/0.97      inference(global_propositional_subsumption,
% 1.65/0.97                [status(thm)],
% 1.65/0.97                [c_251,c_17]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_256,plain,
% 1.65/0.97      ( v3_pre_topc(k1_tops_1(sK2,X0),sK2)
% 1.65/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 1.65/0.97      inference(renaming,[status(thm)],[c_255]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_1629,plain,
% 1.65/0.97      ( v3_pre_topc(k1_tops_1(sK2,X0_46),sK2)
% 1.65/0.97      | ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 1.65/0.97      inference(subtyping,[status(esa)],[c_256]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_2053,plain,
% 1.65/0.97      ( v3_pre_topc(k1_tops_1(sK2,sK3),sK2)
% 1.65/0.97      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 1.65/0.97      inference(instantiation,[status(thm)],[c_1629]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_2054,plain,
% 1.65/0.97      ( v3_pre_topc(k1_tops_1(sK2,sK3),sK2) = iProver_top
% 1.65/0.97      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 1.65/0.97      inference(predicate_to_equality,[status(thm)],[c_2053]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_15,negated_conjecture,
% 1.65/0.97      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 1.65/0.97      inference(cnf_transformation,[],[f51]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_22,plain,
% 1.65/0.97      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 1.65/0.97      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(contradiction,plain,
% 1.65/0.97      ( $false ),
% 1.65/0.97      inference(minisat,
% 1.65/0.97                [status(thm)],
% 1.65/0.97                [c_2849,c_2857,c_2843,c_2588,c_2283,c_2285,c_2260,c_2108,
% 1.65/0.97                 c_2073,c_2056,c_2054,c_1948,c_1630,c_22,c_15]) ).
% 1.65/0.97  
% 1.65/0.97  
% 1.65/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 1.65/0.97  
% 1.65/0.97  ------                               Statistics
% 1.65/0.97  
% 1.65/0.97  ------ General
% 1.65/0.97  
% 1.65/0.97  abstr_ref_over_cycles:                  0
% 1.65/0.97  abstr_ref_under_cycles:                 0
% 1.65/0.97  gc_basic_clause_elim:                   0
% 1.65/0.97  forced_gc_time:                         0
% 1.65/0.97  parsing_time:                           0.008
% 1.65/0.97  unif_index_cands_time:                  0.
% 1.65/0.97  unif_index_add_time:                    0.
% 1.65/0.97  orderings_time:                         0.
% 1.65/0.97  out_proof_time:                         0.007
% 1.65/0.97  total_time:                             0.1
% 1.65/0.97  num_of_symbols:                         53
% 1.65/0.97  num_of_terms:                           2001
% 1.65/0.97  
% 1.65/0.97  ------ Preprocessing
% 1.65/0.97  
% 1.65/0.97  num_of_splits:                          0
% 1.65/0.97  num_of_split_atoms:                     0
% 1.65/0.97  num_of_reused_defs:                     0
% 1.65/0.97  num_eq_ax_congr_red:                    36
% 1.65/0.97  num_of_sem_filtered_clauses:            1
% 1.65/0.97  num_of_subtypes:                        4
% 1.65/0.97  monotx_restored_types:                  0
% 1.65/0.97  sat_num_of_epr_types:                   0
% 1.65/0.97  sat_num_of_non_cyclic_types:            0
% 1.65/0.97  sat_guarded_non_collapsed_types:        1
% 1.65/0.97  num_pure_diseq_elim:                    0
% 1.65/0.97  simp_replaced_by:                       0
% 1.65/0.97  res_preprocessed:                       79
% 1.65/0.97  prep_upred:                             0
% 1.65/0.97  prep_unflattend:                        73
% 1.65/0.97  smt_new_axioms:                         0
% 1.65/0.97  pred_elim_cands:                        4
% 1.65/0.97  pred_elim:                              4
% 1.65/0.97  pred_elim_cl:                           4
% 1.65/0.97  pred_elim_cycles:                       11
% 1.65/0.97  merged_defs:                            0
% 1.65/0.97  merged_defs_ncl:                        0
% 1.65/0.97  bin_hyper_res:                          0
% 1.65/0.97  prep_cycles:                            4
% 1.65/0.97  pred_elim_time:                         0.025
% 1.65/0.97  splitting_time:                         0.
% 1.65/0.97  sem_filter_time:                        0.
% 1.65/0.97  monotx_time:                            0.
% 1.65/0.97  subtype_inf_time:                       0.
% 1.65/0.97  
% 1.65/0.97  ------ Problem properties
% 1.65/0.97  
% 1.65/0.97  clauses:                                15
% 1.65/0.97  conjectures:                            2
% 1.65/0.97  epr:                                    3
% 1.65/0.97  horn:                                   13
% 1.65/0.97  ground:                                 3
% 1.65/0.97  unary:                                  5
% 1.65/0.97  binary:                                 4
% 1.65/0.97  lits:                                   39
% 1.65/0.97  lits_eq:                                5
% 1.65/0.97  fd_pure:                                0
% 1.65/0.97  fd_pseudo:                              0
% 1.65/0.97  fd_cond:                                1
% 1.65/0.97  fd_pseudo_cond:                         0
% 1.65/0.97  ac_symbols:                             0
% 1.65/0.97  
% 1.65/0.97  ------ Propositional Solver
% 1.65/0.97  
% 1.65/0.97  prop_solver_calls:                      27
% 1.65/0.97  prop_fast_solver_calls:                 783
% 1.65/0.97  smt_solver_calls:                       0
% 1.65/0.97  smt_fast_solver_calls:                  0
% 1.65/0.97  prop_num_of_clauses:                    579
% 1.65/0.97  prop_preprocess_simplified:             2841
% 1.65/0.97  prop_fo_subsumed:                       12
% 1.65/0.97  prop_solver_time:                       0.
% 1.65/0.97  smt_solver_time:                        0.
% 1.65/0.97  smt_fast_solver_time:                   0.
% 1.65/0.97  prop_fast_solver_time:                  0.
% 1.65/0.97  prop_unsat_core_time:                   0.
% 1.65/0.97  
% 1.65/0.97  ------ QBF
% 1.65/0.97  
% 1.65/0.97  qbf_q_res:                              0
% 1.65/0.97  qbf_num_tautologies:                    0
% 1.65/0.97  qbf_prep_cycles:                        0
% 1.65/0.97  
% 1.65/0.97  ------ BMC1
% 1.65/0.97  
% 1.65/0.97  bmc1_current_bound:                     -1
% 1.65/0.97  bmc1_last_solved_bound:                 -1
% 1.65/0.97  bmc1_unsat_core_size:                   -1
% 1.65/0.97  bmc1_unsat_core_parents_size:           -1
% 1.65/0.97  bmc1_merge_next_fun:                    0
% 1.65/0.97  bmc1_unsat_core_clauses_time:           0.
% 1.65/0.97  
% 1.65/0.97  ------ Instantiation
% 1.65/0.97  
% 1.65/0.97  inst_num_of_clauses:                    134
% 1.65/0.97  inst_num_in_passive:                    32
% 1.65/0.97  inst_num_in_active:                     102
% 1.65/0.97  inst_num_in_unprocessed:                0
% 1.65/0.97  inst_num_of_loops:                      120
% 1.65/0.97  inst_num_of_learning_restarts:          0
% 1.65/0.97  inst_num_moves_active_passive:          14
% 1.65/0.97  inst_lit_activity:                      0
% 1.65/0.97  inst_lit_activity_moves:                0
% 1.65/0.97  inst_num_tautologies:                   0
% 1.65/0.97  inst_num_prop_implied:                  0
% 1.65/0.97  inst_num_existing_simplified:           0
% 1.65/0.97  inst_num_eq_res_simplified:             0
% 1.65/0.97  inst_num_child_elim:                    0
% 1.65/0.97  inst_num_of_dismatching_blockings:      23
% 1.65/0.97  inst_num_of_non_proper_insts:           101
% 1.65/0.97  inst_num_of_duplicates:                 0
% 1.65/0.97  inst_inst_num_from_inst_to_res:         0
% 1.65/0.97  inst_dismatching_checking_time:         0.
% 1.65/0.97  
% 1.65/0.97  ------ Resolution
% 1.65/0.97  
% 1.65/0.97  res_num_of_clauses:                     0
% 1.65/0.97  res_num_in_passive:                     0
% 1.65/0.97  res_num_in_active:                      0
% 1.65/0.97  res_num_of_loops:                       83
% 1.65/0.97  res_forward_subset_subsumed:            5
% 1.65/0.97  res_backward_subset_subsumed:           0
% 1.65/0.97  res_forward_subsumed:                   0
% 1.65/0.97  res_backward_subsumed:                  0
% 1.65/0.97  res_forward_subsumption_resolution:     4
% 1.65/0.97  res_backward_subsumption_resolution:    0
% 1.65/0.97  res_clause_to_clause_subsumption:       155
% 1.65/0.97  res_orphan_elimination:                 0
% 1.65/0.97  res_tautology_del:                      27
% 1.65/0.97  res_num_eq_res_simplified:              0
% 1.65/0.97  res_num_sel_changes:                    0
% 1.65/0.97  res_moves_from_active_to_pass:          0
% 1.65/0.97  
% 1.65/0.97  ------ Superposition
% 1.65/0.97  
% 1.65/0.97  sup_time_total:                         0.
% 1.65/0.97  sup_time_generating:                    0.
% 1.65/0.97  sup_time_sim_full:                      0.
% 1.65/0.97  sup_time_sim_immed:                     0.
% 1.65/0.97  
% 1.65/0.97  sup_num_of_clauses:                     33
% 1.65/0.97  sup_num_in_active:                      24
% 1.65/0.97  sup_num_in_passive:                     9
% 1.65/0.97  sup_num_of_loops:                       23
% 1.65/0.97  sup_fw_superposition:                   10
% 1.65/0.97  sup_bw_superposition:                   12
% 1.65/0.97  sup_immediate_simplified:               2
% 1.65/0.97  sup_given_eliminated:                   0
% 1.65/0.97  comparisons_done:                       0
% 1.65/0.97  comparisons_avoided:                    0
% 1.65/0.97  
% 1.65/0.97  ------ Simplifications
% 1.65/0.97  
% 1.65/0.97  
% 1.65/0.97  sim_fw_subset_subsumed:                 2
% 1.65/0.97  sim_bw_subset_subsumed:                 0
% 1.65/0.97  sim_fw_subsumed:                        1
% 1.65/0.97  sim_bw_subsumed:                        0
% 1.65/0.97  sim_fw_subsumption_res:                 0
% 1.65/0.97  sim_bw_subsumption_res:                 0
% 1.65/0.97  sim_tautology_del:                      0
% 1.65/0.97  sim_eq_tautology_del:                   0
% 1.65/0.97  sim_eq_res_simp:                        0
% 1.65/0.97  sim_fw_demodulated:                     0
% 1.65/0.97  sim_bw_demodulated:                     0
% 1.65/0.97  sim_light_normalised:                   2
% 1.65/0.97  sim_joinable_taut:                      0
% 1.65/0.97  sim_joinable_simp:                      0
% 1.65/0.97  sim_ac_normalised:                      0
% 1.65/0.97  sim_smt_subsumption:                    0
% 1.65/0.97  
%------------------------------------------------------------------------------
