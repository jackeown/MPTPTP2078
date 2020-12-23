%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:26:15 EST 2020

% Result     : Theorem 2.05s
% Output     : CNFRefutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 223 expanded)
%              Number of clauses        :   54 (  74 expanded)
%              Number of leaves         :   16 (  49 expanded)
%              Depth                    :   16
%              Number of atoms          :  344 ( 863 expanded)
%              Number of equality atoms :   86 ( 137 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f47,f46])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f26])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f64,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f39])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f44,f46])).

fof(f12,axiom,(
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
                            & v4_pre_topc(X3,X0) ) )
                    & r1_tarski(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v4_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v4_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ? [X2] :
                  ( ! [X3] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
                      | ~ v4_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( ? [X3] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                      & v4_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r1_tarski(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ? [X2] :
                  ( ! [X3] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
                      | ~ v4_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X4] :
                  ( ? [X5] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X5) = X4
                      & v4_pre_topc(X5,X0)
                      & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r1_tarski(X4,X1)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f29])).

fof(f32,plain,(
    ! [X4,X1,X0] :
      ( ? [X5] :
          ( k9_subset_1(u1_struct_0(X0),X1,X5) = X4
          & v4_pre_topc(X5,X0)
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X0),X1,sK1(X0,X1,X4)) = X4
        & v4_pre_topc(sK1(X0,X1,X4),X0)
        & m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
              | ~ v4_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ! [X3] :
            ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK0(X0,X1)
            | ~ v4_pre_topc(X3,X0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & r1_tarski(sK0(X0,X1),X1)
        & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ( ! [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK0(X0,X1)
                    | ~ v4_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & r1_tarski(sK0(X0,X1),X1)
                & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X4] :
                  ( ( k9_subset_1(u1_struct_0(X0),X1,sK1(X0,X1,X4)) = X4
                    & v4_pre_topc(sK1(X0,X1,X4),X0)
                    & m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r1_tarski(X4,X1)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f32,f31])).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( v2_tex_2(X1,X0)
      | k9_subset_1(u1_struct_0(X0),X1,X3) != sK0(X0,X1)
      | ~ v4_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_xboole_0(X1) )
           => v2_tex_2(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f15,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_xboole_0(X1) )
           => v2_tex_2(X1,X0) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
     => ( ~ v2_tex_2(sK3,X0)
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0)))
        & v1_xboole_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
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

fof(f36,plain,
    ( ~ v2_tex_2(sK3,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & v1_xboole_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f25,f35,f34])).

fof(f57,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f41,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f60,plain,(
    ~ v2_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f38,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f58,plain,(
    v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | r1_tarski(sK0(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f56,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_10,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1921,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k4_xboole_0(X2,k4_xboole_0(X2,X0)) = k9_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1922,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k9_subset_1(X2,X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3103,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k9_subset_1(X1,X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1921,c_1922])).

cnf(c_4,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1927,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1926,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3229,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1927,c_1926])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1924,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3268,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_1927,c_1924])).

cnf(c_4236,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_3268,c_3229])).

cnf(c_4980,plain,
    ( k9_subset_1(X0,X1,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3103,c_3229,c_4236])).

cnf(c_12,plain,
    ( v2_tex_2(X0,X1)
    | ~ v4_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),X0,X2) != sK0(X1,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_21,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_532,plain,
    ( v2_tex_2(X0,X1)
    | ~ v4_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | k9_subset_1(u1_struct_0(X1),X0,X2) != sK0(X1,X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_21])).

cnf(c_533,plain,
    ( v2_tex_2(X0,sK2)
    | ~ v4_pre_topc(X1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | k9_subset_1(u1_struct_0(sK2),X0,X1) != sK0(sK2,X0) ),
    inference(unflattening,[status(thm)],[c_532])).

cnf(c_1911,plain,
    ( k9_subset_1(u1_struct_0(sK2),X0,X1) != sK0(sK2,X0)
    | v2_tex_2(X0,sK2) = iProver_top
    | v4_pre_topc(X1,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_533])).

cnf(c_4983,plain,
    ( sK0(sK2,X0) != k1_xboole_0
    | v2_tex_2(X0,sK2) = iProver_top
    | v4_pre_topc(k1_xboole_0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4980,c_1911])).

cnf(c_4985,plain,
    ( sK0(sK2,k1_xboole_0) != k1_xboole_0
    | v2_tex_2(k1_xboole_0,sK2) = iProver_top
    | v4_pre_topc(k1_xboole_0,sK2) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4983])).

cnf(c_8,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_3337,plain,
    ( r1_tarski(k1_xboole_0,sK0(sK2,X0)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_3341,plain,
    ( r1_tarski(k1_xboole_0,sK0(sK2,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_3337])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_2495,plain,
    ( ~ r1_tarski(X0,sK0(sK2,X1))
    | ~ r1_tarski(sK0(sK2,X1),X0)
    | sK0(sK2,X1) = X0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2497,plain,
    ( ~ r1_tarski(sK0(sK2,k1_xboole_0),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK0(sK2,k1_xboole_0))
    | sK0(sK2,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2495])).

cnf(c_2068,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_2072,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2068])).

cnf(c_18,negated_conjecture,
    ( ~ v2_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1920,plain,
    ( v2_tex_2(sK3,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_20,negated_conjecture,
    ( v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_339,plain,
    ( sK3 != X0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_20])).

cnf(c_340,plain,
    ( k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_339])).

cnf(c_1938,plain,
    ( v2_tex_2(k1_xboole_0,sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1920,c_340])).

cnf(c_2028,plain,
    ( ~ v2_tex_2(k1_xboole_0,sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1938])).

cnf(c_13,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(sK0(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_517,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(sK0(X1,X0),X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_21])).

cnf(c_518,plain,
    ( v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(sK0(sK2,X0),X0) ),
    inference(unflattening,[status(thm)],[c_517])).

cnf(c_520,plain,
    ( v2_tex_2(k1_xboole_0,sK2)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(sK0(sK2,k1_xboole_0),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_518])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_11,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_22,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_291,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_22])).

cnf(c_292,plain,
    ( v4_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | ~ v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_291])).

cnf(c_296,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v4_pre_topc(X0,sK2)
    | ~ v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_292,c_21])).

cnf(c_297,plain,
    ( v4_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_296])).

cnf(c_316,plain,
    ( v4_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_297])).

cnf(c_317,plain,
    ( v4_pre_topc(k1_xboole_0,sK2)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(unflattening,[status(thm)],[c_316])).

cnf(c_323,plain,
    ( v4_pre_topc(k1_xboole_0,sK2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_317,c_10])).

cnf(c_325,plain,
    ( v4_pre_topc(k1_xboole_0,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_323])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4985,c_3341,c_2497,c_2072,c_2068,c_2028,c_1938,c_520,c_325])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 09:22:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.05/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.05/1.00  
% 2.05/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.05/1.00  
% 2.05/1.00  ------  iProver source info
% 2.05/1.00  
% 2.05/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.05/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.05/1.00  git: non_committed_changes: false
% 2.05/1.00  git: last_make_outside_of_git: false
% 2.05/1.00  
% 2.05/1.00  ------ 
% 2.05/1.00  
% 2.05/1.00  ------ Input Options
% 2.05/1.00  
% 2.05/1.00  --out_options                           all
% 2.05/1.00  --tptp_safe_out                         true
% 2.05/1.00  --problem_path                          ""
% 2.05/1.00  --include_path                          ""
% 2.05/1.00  --clausifier                            res/vclausify_rel
% 2.05/1.00  --clausifier_options                    --mode clausify
% 2.05/1.00  --stdin                                 false
% 2.05/1.00  --stats_out                             all
% 2.05/1.00  
% 2.05/1.00  ------ General Options
% 2.05/1.00  
% 2.05/1.00  --fof                                   false
% 2.05/1.00  --time_out_real                         305.
% 2.05/1.00  --time_out_virtual                      -1.
% 2.05/1.00  --symbol_type_check                     false
% 2.05/1.00  --clausify_out                          false
% 2.05/1.00  --sig_cnt_out                           false
% 2.05/1.00  --trig_cnt_out                          false
% 2.05/1.00  --trig_cnt_out_tolerance                1.
% 2.05/1.00  --trig_cnt_out_sk_spl                   false
% 2.05/1.00  --abstr_cl_out                          false
% 2.05/1.00  
% 2.05/1.00  ------ Global Options
% 2.05/1.00  
% 2.05/1.00  --schedule                              default
% 2.05/1.00  --add_important_lit                     false
% 2.05/1.00  --prop_solver_per_cl                    1000
% 2.05/1.00  --min_unsat_core                        false
% 2.05/1.00  --soft_assumptions                      false
% 2.05/1.00  --soft_lemma_size                       3
% 2.05/1.00  --prop_impl_unit_size                   0
% 2.05/1.00  --prop_impl_unit                        []
% 2.05/1.00  --share_sel_clauses                     true
% 2.05/1.00  --reset_solvers                         false
% 2.05/1.00  --bc_imp_inh                            [conj_cone]
% 2.05/1.00  --conj_cone_tolerance                   3.
% 2.05/1.00  --extra_neg_conj                        none
% 2.05/1.00  --large_theory_mode                     true
% 2.05/1.00  --prolific_symb_bound                   200
% 2.05/1.00  --lt_threshold                          2000
% 2.05/1.00  --clause_weak_htbl                      true
% 2.05/1.00  --gc_record_bc_elim                     false
% 2.05/1.00  
% 2.05/1.00  ------ Preprocessing Options
% 2.05/1.00  
% 2.05/1.00  --preprocessing_flag                    true
% 2.05/1.00  --time_out_prep_mult                    0.1
% 2.05/1.00  --splitting_mode                        input
% 2.05/1.00  --splitting_grd                         true
% 2.05/1.00  --splitting_cvd                         false
% 2.05/1.00  --splitting_cvd_svl                     false
% 2.05/1.00  --splitting_nvd                         32
% 2.05/1.00  --sub_typing                            true
% 2.05/1.00  --prep_gs_sim                           true
% 2.05/1.00  --prep_unflatten                        true
% 2.05/1.00  --prep_res_sim                          true
% 2.05/1.00  --prep_upred                            true
% 2.05/1.00  --prep_sem_filter                       exhaustive
% 2.05/1.00  --prep_sem_filter_out                   false
% 2.05/1.00  --pred_elim                             true
% 2.05/1.00  --res_sim_input                         true
% 2.05/1.00  --eq_ax_congr_red                       true
% 2.05/1.00  --pure_diseq_elim                       true
% 2.05/1.00  --brand_transform                       false
% 2.05/1.00  --non_eq_to_eq                          false
% 2.05/1.00  --prep_def_merge                        true
% 2.05/1.00  --prep_def_merge_prop_impl              false
% 2.05/1.00  --prep_def_merge_mbd                    true
% 2.05/1.00  --prep_def_merge_tr_red                 false
% 2.05/1.00  --prep_def_merge_tr_cl                  false
% 2.05/1.00  --smt_preprocessing                     true
% 2.05/1.00  --smt_ac_axioms                         fast
% 2.05/1.00  --preprocessed_out                      false
% 2.05/1.00  --preprocessed_stats                    false
% 2.05/1.00  
% 2.05/1.00  ------ Abstraction refinement Options
% 2.05/1.00  
% 2.05/1.00  --abstr_ref                             []
% 2.05/1.00  --abstr_ref_prep                        false
% 2.05/1.00  --abstr_ref_until_sat                   false
% 2.05/1.00  --abstr_ref_sig_restrict                funpre
% 2.05/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.05/1.00  --abstr_ref_under                       []
% 2.05/1.00  
% 2.05/1.00  ------ SAT Options
% 2.05/1.00  
% 2.05/1.00  --sat_mode                              false
% 2.05/1.00  --sat_fm_restart_options                ""
% 2.05/1.00  --sat_gr_def                            false
% 2.05/1.00  --sat_epr_types                         true
% 2.05/1.00  --sat_non_cyclic_types                  false
% 2.05/1.00  --sat_finite_models                     false
% 2.05/1.00  --sat_fm_lemmas                         false
% 2.05/1.00  --sat_fm_prep                           false
% 2.05/1.00  --sat_fm_uc_incr                        true
% 2.05/1.00  --sat_out_model                         small
% 2.05/1.00  --sat_out_clauses                       false
% 2.05/1.00  
% 2.05/1.00  ------ QBF Options
% 2.05/1.00  
% 2.05/1.00  --qbf_mode                              false
% 2.05/1.00  --qbf_elim_univ                         false
% 2.05/1.00  --qbf_dom_inst                          none
% 2.05/1.00  --qbf_dom_pre_inst                      false
% 2.05/1.00  --qbf_sk_in                             false
% 2.05/1.00  --qbf_pred_elim                         true
% 2.05/1.00  --qbf_split                             512
% 2.05/1.00  
% 2.05/1.00  ------ BMC1 Options
% 2.05/1.00  
% 2.05/1.00  --bmc1_incremental                      false
% 2.05/1.00  --bmc1_axioms                           reachable_all
% 2.05/1.00  --bmc1_min_bound                        0
% 2.05/1.00  --bmc1_max_bound                        -1
% 2.05/1.00  --bmc1_max_bound_default                -1
% 2.05/1.00  --bmc1_symbol_reachability              true
% 2.05/1.00  --bmc1_property_lemmas                  false
% 2.05/1.00  --bmc1_k_induction                      false
% 2.05/1.00  --bmc1_non_equiv_states                 false
% 2.05/1.00  --bmc1_deadlock                         false
% 2.05/1.00  --bmc1_ucm                              false
% 2.05/1.00  --bmc1_add_unsat_core                   none
% 2.05/1.00  --bmc1_unsat_core_children              false
% 2.05/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.05/1.00  --bmc1_out_stat                         full
% 2.05/1.00  --bmc1_ground_init                      false
% 2.05/1.00  --bmc1_pre_inst_next_state              false
% 2.05/1.00  --bmc1_pre_inst_state                   false
% 2.05/1.00  --bmc1_pre_inst_reach_state             false
% 2.05/1.00  --bmc1_out_unsat_core                   false
% 2.05/1.00  --bmc1_aig_witness_out                  false
% 2.05/1.00  --bmc1_verbose                          false
% 2.05/1.00  --bmc1_dump_clauses_tptp                false
% 2.05/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.05/1.00  --bmc1_dump_file                        -
% 2.05/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.05/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.05/1.00  --bmc1_ucm_extend_mode                  1
% 2.05/1.00  --bmc1_ucm_init_mode                    2
% 2.05/1.00  --bmc1_ucm_cone_mode                    none
% 2.05/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.05/1.00  --bmc1_ucm_relax_model                  4
% 2.05/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.05/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.05/1.00  --bmc1_ucm_layered_model                none
% 2.05/1.00  --bmc1_ucm_max_lemma_size               10
% 2.05/1.00  
% 2.05/1.00  ------ AIG Options
% 2.05/1.00  
% 2.05/1.00  --aig_mode                              false
% 2.05/1.00  
% 2.05/1.00  ------ Instantiation Options
% 2.05/1.00  
% 2.05/1.00  --instantiation_flag                    true
% 2.05/1.00  --inst_sos_flag                         false
% 2.05/1.00  --inst_sos_phase                        true
% 2.05/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.05/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.05/1.00  --inst_lit_sel_side                     num_symb
% 2.05/1.00  --inst_solver_per_active                1400
% 2.05/1.00  --inst_solver_calls_frac                1.
% 2.05/1.00  --inst_passive_queue_type               priority_queues
% 2.05/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.05/1.00  --inst_passive_queues_freq              [25;2]
% 2.05/1.00  --inst_dismatching                      true
% 2.05/1.00  --inst_eager_unprocessed_to_passive     true
% 2.05/1.00  --inst_prop_sim_given                   true
% 2.05/1.00  --inst_prop_sim_new                     false
% 2.05/1.00  --inst_subs_new                         false
% 2.05/1.00  --inst_eq_res_simp                      false
% 2.05/1.00  --inst_subs_given                       false
% 2.05/1.00  --inst_orphan_elimination               true
% 2.05/1.00  --inst_learning_loop_flag               true
% 2.05/1.00  --inst_learning_start                   3000
% 2.05/1.00  --inst_learning_factor                  2
% 2.05/1.00  --inst_start_prop_sim_after_learn       3
% 2.05/1.00  --inst_sel_renew                        solver
% 2.05/1.00  --inst_lit_activity_flag                true
% 2.05/1.00  --inst_restr_to_given                   false
% 2.05/1.00  --inst_activity_threshold               500
% 2.05/1.00  --inst_out_proof                        true
% 2.05/1.00  
% 2.05/1.00  ------ Resolution Options
% 2.05/1.00  
% 2.05/1.00  --resolution_flag                       true
% 2.05/1.00  --res_lit_sel                           adaptive
% 2.05/1.00  --res_lit_sel_side                      none
% 2.05/1.00  --res_ordering                          kbo
% 2.05/1.00  --res_to_prop_solver                    active
% 2.05/1.00  --res_prop_simpl_new                    false
% 2.05/1.00  --res_prop_simpl_given                  true
% 2.05/1.00  --res_passive_queue_type                priority_queues
% 2.05/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.05/1.00  --res_passive_queues_freq               [15;5]
% 2.05/1.00  --res_forward_subs                      full
% 2.05/1.00  --res_backward_subs                     full
% 2.05/1.00  --res_forward_subs_resolution           true
% 2.05/1.00  --res_backward_subs_resolution          true
% 2.05/1.00  --res_orphan_elimination                true
% 2.05/1.00  --res_time_limit                        2.
% 2.05/1.00  --res_out_proof                         true
% 2.05/1.00  
% 2.05/1.00  ------ Superposition Options
% 2.05/1.00  
% 2.05/1.00  --superposition_flag                    true
% 2.05/1.00  --sup_passive_queue_type                priority_queues
% 2.05/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.05/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.05/1.00  --demod_completeness_check              fast
% 2.05/1.00  --demod_use_ground                      true
% 2.05/1.00  --sup_to_prop_solver                    passive
% 2.05/1.00  --sup_prop_simpl_new                    true
% 2.05/1.00  --sup_prop_simpl_given                  true
% 2.05/1.00  --sup_fun_splitting                     false
% 2.05/1.00  --sup_smt_interval                      50000
% 2.05/1.00  
% 2.05/1.00  ------ Superposition Simplification Setup
% 2.05/1.00  
% 2.05/1.00  --sup_indices_passive                   []
% 2.05/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.05/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.05/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.05/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.05/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.05/1.00  --sup_full_bw                           [BwDemod]
% 2.05/1.00  --sup_immed_triv                        [TrivRules]
% 2.05/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.05/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.05/1.00  --sup_immed_bw_main                     []
% 2.05/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.05/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.05/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.05/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.05/1.00  
% 2.05/1.00  ------ Combination Options
% 2.05/1.00  
% 2.05/1.00  --comb_res_mult                         3
% 2.05/1.00  --comb_sup_mult                         2
% 2.05/1.00  --comb_inst_mult                        10
% 2.05/1.00  
% 2.05/1.00  ------ Debug Options
% 2.05/1.00  
% 2.05/1.00  --dbg_backtrace                         false
% 2.05/1.00  --dbg_dump_prop_clauses                 false
% 2.05/1.00  --dbg_dump_prop_clauses_file            -
% 2.05/1.00  --dbg_out_stat                          false
% 2.05/1.00  ------ Parsing...
% 2.05/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.05/1.00  
% 2.05/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.05/1.00  
% 2.05/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.05/1.00  
% 2.05/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.05/1.00  ------ Proving...
% 2.05/1.00  ------ Problem Properties 
% 2.05/1.00  
% 2.05/1.00  
% 2.05/1.00  clauses                                 19
% 2.05/1.00  conjectures                             2
% 2.05/1.00  EPR                                     7
% 2.05/1.00  Horn                                    17
% 2.05/1.00  unary                                   8
% 2.05/1.00  binary                                  4
% 2.05/1.00  lits                                    45
% 2.05/1.00  lits eq                                 8
% 2.05/1.00  fd_pure                                 0
% 2.05/1.00  fd_pseudo                               0
% 2.05/1.00  fd_cond                                 0
% 2.05/1.00  fd_pseudo_cond                          1
% 2.05/1.00  AC symbols                              0
% 2.05/1.00  
% 2.05/1.00  ------ Schedule dynamic 5 is on 
% 2.05/1.00  
% 2.05/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.05/1.00  
% 2.05/1.00  
% 2.05/1.00  ------ 
% 2.05/1.00  Current options:
% 2.05/1.00  ------ 
% 2.05/1.00  
% 2.05/1.00  ------ Input Options
% 2.05/1.00  
% 2.05/1.00  --out_options                           all
% 2.05/1.00  --tptp_safe_out                         true
% 2.05/1.00  --problem_path                          ""
% 2.05/1.00  --include_path                          ""
% 2.05/1.00  --clausifier                            res/vclausify_rel
% 2.05/1.00  --clausifier_options                    --mode clausify
% 2.05/1.00  --stdin                                 false
% 2.05/1.00  --stats_out                             all
% 2.05/1.00  
% 2.05/1.00  ------ General Options
% 2.05/1.00  
% 2.05/1.00  --fof                                   false
% 2.05/1.00  --time_out_real                         305.
% 2.05/1.00  --time_out_virtual                      -1.
% 2.05/1.00  --symbol_type_check                     false
% 2.05/1.00  --clausify_out                          false
% 2.05/1.00  --sig_cnt_out                           false
% 2.05/1.00  --trig_cnt_out                          false
% 2.05/1.00  --trig_cnt_out_tolerance                1.
% 2.05/1.00  --trig_cnt_out_sk_spl                   false
% 2.05/1.00  --abstr_cl_out                          false
% 2.05/1.00  
% 2.05/1.00  ------ Global Options
% 2.05/1.00  
% 2.05/1.00  --schedule                              default
% 2.05/1.00  --add_important_lit                     false
% 2.05/1.00  --prop_solver_per_cl                    1000
% 2.05/1.00  --min_unsat_core                        false
% 2.05/1.00  --soft_assumptions                      false
% 2.05/1.00  --soft_lemma_size                       3
% 2.05/1.00  --prop_impl_unit_size                   0
% 2.05/1.00  --prop_impl_unit                        []
% 2.05/1.00  --share_sel_clauses                     true
% 2.05/1.00  --reset_solvers                         false
% 2.05/1.00  --bc_imp_inh                            [conj_cone]
% 2.05/1.00  --conj_cone_tolerance                   3.
% 2.05/1.00  --extra_neg_conj                        none
% 2.05/1.00  --large_theory_mode                     true
% 2.05/1.00  --prolific_symb_bound                   200
% 2.05/1.00  --lt_threshold                          2000
% 2.05/1.00  --clause_weak_htbl                      true
% 2.05/1.00  --gc_record_bc_elim                     false
% 2.05/1.00  
% 2.05/1.00  ------ Preprocessing Options
% 2.05/1.00  
% 2.05/1.00  --preprocessing_flag                    true
% 2.05/1.00  --time_out_prep_mult                    0.1
% 2.05/1.00  --splitting_mode                        input
% 2.05/1.00  --splitting_grd                         true
% 2.05/1.00  --splitting_cvd                         false
% 2.05/1.00  --splitting_cvd_svl                     false
% 2.05/1.00  --splitting_nvd                         32
% 2.05/1.00  --sub_typing                            true
% 2.05/1.00  --prep_gs_sim                           true
% 2.05/1.00  --prep_unflatten                        true
% 2.05/1.00  --prep_res_sim                          true
% 2.05/1.00  --prep_upred                            true
% 2.05/1.00  --prep_sem_filter                       exhaustive
% 2.05/1.00  --prep_sem_filter_out                   false
% 2.05/1.00  --pred_elim                             true
% 2.05/1.00  --res_sim_input                         true
% 2.05/1.00  --eq_ax_congr_red                       true
% 2.05/1.00  --pure_diseq_elim                       true
% 2.05/1.00  --brand_transform                       false
% 2.05/1.00  --non_eq_to_eq                          false
% 2.05/1.00  --prep_def_merge                        true
% 2.05/1.00  --prep_def_merge_prop_impl              false
% 2.05/1.00  --prep_def_merge_mbd                    true
% 2.05/1.00  --prep_def_merge_tr_red                 false
% 2.05/1.00  --prep_def_merge_tr_cl                  false
% 2.05/1.00  --smt_preprocessing                     true
% 2.05/1.00  --smt_ac_axioms                         fast
% 2.05/1.00  --preprocessed_out                      false
% 2.05/1.00  --preprocessed_stats                    false
% 2.05/1.00  
% 2.05/1.00  ------ Abstraction refinement Options
% 2.05/1.00  
% 2.05/1.00  --abstr_ref                             []
% 2.05/1.00  --abstr_ref_prep                        false
% 2.05/1.00  --abstr_ref_until_sat                   false
% 2.05/1.00  --abstr_ref_sig_restrict                funpre
% 2.05/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.05/1.00  --abstr_ref_under                       []
% 2.05/1.00  
% 2.05/1.00  ------ SAT Options
% 2.05/1.00  
% 2.05/1.00  --sat_mode                              false
% 2.05/1.00  --sat_fm_restart_options                ""
% 2.05/1.00  --sat_gr_def                            false
% 2.05/1.00  --sat_epr_types                         true
% 2.05/1.00  --sat_non_cyclic_types                  false
% 2.05/1.00  --sat_finite_models                     false
% 2.05/1.00  --sat_fm_lemmas                         false
% 2.05/1.00  --sat_fm_prep                           false
% 2.05/1.00  --sat_fm_uc_incr                        true
% 2.05/1.00  --sat_out_model                         small
% 2.05/1.00  --sat_out_clauses                       false
% 2.05/1.00  
% 2.05/1.00  ------ QBF Options
% 2.05/1.00  
% 2.05/1.00  --qbf_mode                              false
% 2.05/1.00  --qbf_elim_univ                         false
% 2.05/1.00  --qbf_dom_inst                          none
% 2.05/1.00  --qbf_dom_pre_inst                      false
% 2.05/1.00  --qbf_sk_in                             false
% 2.05/1.00  --qbf_pred_elim                         true
% 2.05/1.00  --qbf_split                             512
% 2.05/1.00  
% 2.05/1.00  ------ BMC1 Options
% 2.05/1.00  
% 2.05/1.00  --bmc1_incremental                      false
% 2.05/1.00  --bmc1_axioms                           reachable_all
% 2.05/1.00  --bmc1_min_bound                        0
% 2.05/1.00  --bmc1_max_bound                        -1
% 2.05/1.00  --bmc1_max_bound_default                -1
% 2.05/1.00  --bmc1_symbol_reachability              true
% 2.05/1.00  --bmc1_property_lemmas                  false
% 2.05/1.00  --bmc1_k_induction                      false
% 2.05/1.00  --bmc1_non_equiv_states                 false
% 2.05/1.00  --bmc1_deadlock                         false
% 2.05/1.00  --bmc1_ucm                              false
% 2.05/1.00  --bmc1_add_unsat_core                   none
% 2.05/1.00  --bmc1_unsat_core_children              false
% 2.05/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.05/1.00  --bmc1_out_stat                         full
% 2.05/1.00  --bmc1_ground_init                      false
% 2.05/1.00  --bmc1_pre_inst_next_state              false
% 2.05/1.00  --bmc1_pre_inst_state                   false
% 2.05/1.00  --bmc1_pre_inst_reach_state             false
% 2.05/1.00  --bmc1_out_unsat_core                   false
% 2.05/1.00  --bmc1_aig_witness_out                  false
% 2.05/1.00  --bmc1_verbose                          false
% 2.05/1.00  --bmc1_dump_clauses_tptp                false
% 2.05/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.05/1.00  --bmc1_dump_file                        -
% 2.05/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.05/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.05/1.00  --bmc1_ucm_extend_mode                  1
% 2.05/1.00  --bmc1_ucm_init_mode                    2
% 2.05/1.00  --bmc1_ucm_cone_mode                    none
% 2.05/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.05/1.00  --bmc1_ucm_relax_model                  4
% 2.05/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.05/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.05/1.00  --bmc1_ucm_layered_model                none
% 2.05/1.00  --bmc1_ucm_max_lemma_size               10
% 2.05/1.00  
% 2.05/1.00  ------ AIG Options
% 2.05/1.00  
% 2.05/1.00  --aig_mode                              false
% 2.05/1.00  
% 2.05/1.00  ------ Instantiation Options
% 2.05/1.00  
% 2.05/1.00  --instantiation_flag                    true
% 2.05/1.00  --inst_sos_flag                         false
% 2.05/1.00  --inst_sos_phase                        true
% 2.05/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.05/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.05/1.00  --inst_lit_sel_side                     none
% 2.05/1.00  --inst_solver_per_active                1400
% 2.05/1.00  --inst_solver_calls_frac                1.
% 2.05/1.00  --inst_passive_queue_type               priority_queues
% 2.05/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.05/1.00  --inst_passive_queues_freq              [25;2]
% 2.05/1.00  --inst_dismatching                      true
% 2.05/1.00  --inst_eager_unprocessed_to_passive     true
% 2.05/1.00  --inst_prop_sim_given                   true
% 2.05/1.00  --inst_prop_sim_new                     false
% 2.05/1.00  --inst_subs_new                         false
% 2.05/1.00  --inst_eq_res_simp                      false
% 2.05/1.00  --inst_subs_given                       false
% 2.05/1.00  --inst_orphan_elimination               true
% 2.05/1.00  --inst_learning_loop_flag               true
% 2.05/1.00  --inst_learning_start                   3000
% 2.05/1.00  --inst_learning_factor                  2
% 2.05/1.00  --inst_start_prop_sim_after_learn       3
% 2.05/1.00  --inst_sel_renew                        solver
% 2.05/1.00  --inst_lit_activity_flag                true
% 2.05/1.00  --inst_restr_to_given                   false
% 2.05/1.00  --inst_activity_threshold               500
% 2.05/1.00  --inst_out_proof                        true
% 2.05/1.00  
% 2.05/1.00  ------ Resolution Options
% 2.05/1.00  
% 2.05/1.00  --resolution_flag                       false
% 2.05/1.00  --res_lit_sel                           adaptive
% 2.05/1.00  --res_lit_sel_side                      none
% 2.05/1.00  --res_ordering                          kbo
% 2.05/1.00  --res_to_prop_solver                    active
% 2.05/1.00  --res_prop_simpl_new                    false
% 2.05/1.00  --res_prop_simpl_given                  true
% 2.05/1.00  --res_passive_queue_type                priority_queues
% 2.05/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.05/1.00  --res_passive_queues_freq               [15;5]
% 2.05/1.00  --res_forward_subs                      full
% 2.05/1.00  --res_backward_subs                     full
% 2.05/1.00  --res_forward_subs_resolution           true
% 2.05/1.00  --res_backward_subs_resolution          true
% 2.05/1.00  --res_orphan_elimination                true
% 2.05/1.00  --res_time_limit                        2.
% 2.05/1.00  --res_out_proof                         true
% 2.05/1.00  
% 2.05/1.00  ------ Superposition Options
% 2.05/1.00  
% 2.05/1.00  --superposition_flag                    true
% 2.05/1.00  --sup_passive_queue_type                priority_queues
% 2.05/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.05/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.05/1.00  --demod_completeness_check              fast
% 2.05/1.00  --demod_use_ground                      true
% 2.05/1.00  --sup_to_prop_solver                    passive
% 2.05/1.00  --sup_prop_simpl_new                    true
% 2.05/1.00  --sup_prop_simpl_given                  true
% 2.05/1.00  --sup_fun_splitting                     false
% 2.05/1.00  --sup_smt_interval                      50000
% 2.05/1.00  
% 2.05/1.00  ------ Superposition Simplification Setup
% 2.05/1.00  
% 2.05/1.00  --sup_indices_passive                   []
% 2.05/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.05/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.05/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.05/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.05/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.05/1.00  --sup_full_bw                           [BwDemod]
% 2.05/1.00  --sup_immed_triv                        [TrivRules]
% 2.05/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.05/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.05/1.00  --sup_immed_bw_main                     []
% 2.05/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.05/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.05/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.05/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.05/1.00  
% 2.05/1.00  ------ Combination Options
% 2.05/1.00  
% 2.05/1.00  --comb_res_mult                         3
% 2.05/1.00  --comb_sup_mult                         2
% 2.05/1.00  --comb_inst_mult                        10
% 2.05/1.00  
% 2.05/1.00  ------ Debug Options
% 2.05/1.00  
% 2.05/1.00  --dbg_backtrace                         false
% 2.05/1.00  --dbg_dump_prop_clauses                 false
% 2.05/1.00  --dbg_dump_prop_clauses_file            -
% 2.05/1.00  --dbg_out_stat                          false
% 2.05/1.00  
% 2.05/1.00  
% 2.05/1.00  
% 2.05/1.00  
% 2.05/1.00  ------ Proving...
% 2.05/1.00  
% 2.05/1.00  
% 2.05/1.00  % SZS status Theorem for theBenchmark.p
% 2.05/1.00  
% 2.05/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.05/1.00  
% 2.05/1.00  fof(f9,axiom,(
% 2.05/1.00    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.05/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/1.00  
% 2.05/1.00  fof(f48,plain,(
% 2.05/1.00    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.05/1.00    inference(cnf_transformation,[],[f9])).
% 2.05/1.00  
% 2.05/1.00  fof(f8,axiom,(
% 2.05/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 2.05/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/1.00  
% 2.05/1.00  fof(f19,plain,(
% 2.05/1.00    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 2.05/1.00    inference(ennf_transformation,[],[f8])).
% 2.05/1.00  
% 2.05/1.00  fof(f47,plain,(
% 2.05/1.00    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 2.05/1.00    inference(cnf_transformation,[],[f19])).
% 2.05/1.00  
% 2.05/1.00  fof(f7,axiom,(
% 2.05/1.00    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 2.05/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/1.00  
% 2.05/1.00  fof(f46,plain,(
% 2.05/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 2.05/1.00    inference(cnf_transformation,[],[f7])).
% 2.05/1.00  
% 2.05/1.00  fof(f62,plain,(
% 2.05/1.00    ( ! [X2,X0,X1] : (k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 2.05/1.00    inference(definition_unfolding,[],[f47,f46])).
% 2.05/1.00  
% 2.05/1.00  fof(f3,axiom,(
% 2.05/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.05/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/1.00  
% 2.05/1.00  fof(f26,plain,(
% 2.05/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.05/1.00    inference(nnf_transformation,[],[f3])).
% 2.05/1.00  
% 2.05/1.00  fof(f27,plain,(
% 2.05/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.05/1.00    inference(flattening,[],[f26])).
% 2.05/1.00  
% 2.05/1.00  fof(f39,plain,(
% 2.05/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.05/1.00    inference(cnf_transformation,[],[f27])).
% 2.05/1.00  
% 2.05/1.00  fof(f64,plain,(
% 2.05/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.05/1.00    inference(equality_resolution,[],[f39])).
% 2.05/1.00  
% 2.05/1.00  fof(f4,axiom,(
% 2.05/1.00    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 2.05/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/1.00  
% 2.05/1.00  fof(f28,plain,(
% 2.05/1.00    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 2.05/1.00    inference(nnf_transformation,[],[f4])).
% 2.05/1.00  
% 2.05/1.00  fof(f43,plain,(
% 2.05/1.00    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 2.05/1.00    inference(cnf_transformation,[],[f28])).
% 2.05/1.00  
% 2.05/1.00  fof(f5,axiom,(
% 2.05/1.00    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.05/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/1.00  
% 2.05/1.00  fof(f18,plain,(
% 2.05/1.00    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.05/1.00    inference(ennf_transformation,[],[f5])).
% 2.05/1.00  
% 2.05/1.00  fof(f44,plain,(
% 2.05/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 2.05/1.00    inference(cnf_transformation,[],[f18])).
% 2.05/1.00  
% 2.05/1.00  fof(f61,plain,(
% 2.05/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 2.05/1.00    inference(definition_unfolding,[],[f44,f46])).
% 2.05/1.00  
% 2.05/1.00  fof(f12,axiom,(
% 2.05/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0))) & r1_tarski(X2,X1))))))),
% 2.05/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/1.00  
% 2.05/1.00  fof(f22,plain,(
% 2.05/1.00    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((? [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.05/1.00    inference(ennf_transformation,[],[f12])).
% 2.05/1.00  
% 2.05/1.00  fof(f23,plain,(
% 2.05/1.00    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.05/1.00    inference(flattening,[],[f22])).
% 2.05/1.00  
% 2.05/1.00  fof(f29,plain,(
% 2.05/1.00    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.05/1.00    inference(nnf_transformation,[],[f23])).
% 2.05/1.00  
% 2.05/1.00  fof(f30,plain,(
% 2.05/1.00    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (? [X5] : (k9_subset_1(u1_struct_0(X0),X1,X5) = X4 & v4_pre_topc(X5,X0) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.05/1.00    inference(rectify,[],[f29])).
% 2.05/1.00  
% 2.05/1.00  fof(f32,plain,(
% 2.05/1.00    ! [X4,X1,X0] : (? [X5] : (k9_subset_1(u1_struct_0(X0),X1,X5) = X4 & v4_pre_topc(X5,X0) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) => (k9_subset_1(u1_struct_0(X0),X1,sK1(X0,X1,X4)) = X4 & v4_pre_topc(sK1(X0,X1,X4),X0) & m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.05/1.00    introduced(choice_axiom,[])).
% 2.05/1.00  
% 2.05/1.00  fof(f31,plain,(
% 2.05/1.00    ! [X1,X0] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK0(X0,X1) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(sK0(X0,X1),X1) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.05/1.00    introduced(choice_axiom,[])).
% 2.05/1.00  
% 2.05/1.00  fof(f33,plain,(
% 2.05/1.00    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK0(X0,X1) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(sK0(X0,X1),X1) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : ((k9_subset_1(u1_struct_0(X0),X1,sK1(X0,X1,X4)) = X4 & v4_pre_topc(sK1(X0,X1,X4),X0) & m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.05/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f32,f31])).
% 2.05/1.00  
% 2.05/1.00  fof(f55,plain,(
% 2.05/1.00    ( ! [X0,X3,X1] : (v2_tex_2(X1,X0) | k9_subset_1(u1_struct_0(X0),X1,X3) != sK0(X0,X1) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.05/1.00    inference(cnf_transformation,[],[f33])).
% 2.05/1.00  
% 2.05/1.00  fof(f13,conjecture,(
% 2.05/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 2.05/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/1.00  
% 2.05/1.00  fof(f14,negated_conjecture,(
% 2.05/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 2.05/1.00    inference(negated_conjecture,[],[f13])).
% 2.05/1.00  
% 2.05/1.00  fof(f15,plain,(
% 2.05/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 2.05/1.00    inference(pure_predicate_removal,[],[f14])).
% 2.05/1.00  
% 2.05/1.00  fof(f24,plain,(
% 2.05/1.00    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.05/1.00    inference(ennf_transformation,[],[f15])).
% 2.05/1.00  
% 2.05/1.00  fof(f25,plain,(
% 2.05/1.00    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.05/1.00    inference(flattening,[],[f24])).
% 2.05/1.00  
% 2.05/1.00  fof(f35,plain,(
% 2.05/1.00    ( ! [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => (~v2_tex_2(sK3,X0) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(sK3))) )),
% 2.05/1.00    introduced(choice_axiom,[])).
% 2.05/1.00  
% 2.05/1.00  fof(f34,plain,(
% 2.05/1.00    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (~v2_tex_2(X1,sK2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) & v1_xboole_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2))),
% 2.05/1.00    introduced(choice_axiom,[])).
% 2.05/1.00  
% 2.05/1.00  fof(f36,plain,(
% 2.05/1.00    (~v2_tex_2(sK3,sK2) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) & v1_xboole_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2)),
% 2.05/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f25,f35,f34])).
% 2.05/1.00  
% 2.05/1.00  fof(f57,plain,(
% 2.05/1.00    l1_pre_topc(sK2)),
% 2.05/1.00    inference(cnf_transformation,[],[f36])).
% 2.05/1.00  
% 2.05/1.00  fof(f6,axiom,(
% 2.05/1.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.05/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/1.00  
% 2.05/1.00  fof(f45,plain,(
% 2.05/1.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.05/1.00    inference(cnf_transformation,[],[f6])).
% 2.05/1.00  
% 2.05/1.00  fof(f41,plain,(
% 2.05/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.05/1.00    inference(cnf_transformation,[],[f27])).
% 2.05/1.00  
% 2.05/1.00  fof(f60,plain,(
% 2.05/1.00    ~v2_tex_2(sK3,sK2)),
% 2.05/1.00    inference(cnf_transformation,[],[f36])).
% 2.05/1.00  
% 2.05/1.00  fof(f2,axiom,(
% 2.05/1.00    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 2.05/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/1.00  
% 2.05/1.00  fof(f17,plain,(
% 2.05/1.00    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 2.05/1.00    inference(ennf_transformation,[],[f2])).
% 2.05/1.00  
% 2.05/1.00  fof(f38,plain,(
% 2.05/1.00    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 2.05/1.00    inference(cnf_transformation,[],[f17])).
% 2.05/1.00  
% 2.05/1.00  fof(f58,plain,(
% 2.05/1.00    v1_xboole_0(sK3)),
% 2.05/1.00    inference(cnf_transformation,[],[f36])).
% 2.05/1.00  
% 2.05/1.00  fof(f54,plain,(
% 2.05/1.00    ( ! [X0,X1] : (v2_tex_2(X1,X0) | r1_tarski(sK0(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.05/1.00    inference(cnf_transformation,[],[f33])).
% 2.05/1.00  
% 2.05/1.00  fof(f1,axiom,(
% 2.05/1.00    v1_xboole_0(k1_xboole_0)),
% 2.05/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/1.00  
% 2.05/1.00  fof(f37,plain,(
% 2.05/1.00    v1_xboole_0(k1_xboole_0)),
% 2.05/1.00    inference(cnf_transformation,[],[f1])).
% 2.05/1.00  
% 2.05/1.00  fof(f11,axiom,(
% 2.05/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_xboole_0(X1) => v4_pre_topc(X1,X0))))),
% 2.05/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/1.00  
% 2.05/1.00  fof(f20,plain,(
% 2.05/1.00    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) | ~v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.05/1.00    inference(ennf_transformation,[],[f11])).
% 2.05/1.00  
% 2.05/1.00  fof(f21,plain,(
% 2.05/1.00    ! [X0] : (! [X1] : (v4_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.05/1.00    inference(flattening,[],[f20])).
% 2.05/1.00  
% 2.05/1.00  fof(f49,plain,(
% 2.05/1.00    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.05/1.00    inference(cnf_transformation,[],[f21])).
% 2.05/1.00  
% 2.05/1.00  fof(f56,plain,(
% 2.05/1.00    v2_pre_topc(sK2)),
% 2.05/1.00    inference(cnf_transformation,[],[f36])).
% 2.05/1.00  
% 2.05/1.00  cnf(c_10,plain,
% 2.05/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 2.05/1.00      inference(cnf_transformation,[],[f48]) ).
% 2.05/1.00  
% 2.05/1.00  cnf(c_1921,plain,
% 2.05/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.05/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.05/1.00  
% 2.05/1.00  cnf(c_9,plain,
% 2.05/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.05/1.00      | k4_xboole_0(X2,k4_xboole_0(X2,X0)) = k9_subset_1(X1,X2,X0) ),
% 2.05/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.05/1.00  
% 2.05/1.00  cnf(c_1922,plain,
% 2.05/1.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k9_subset_1(X2,X0,X1)
% 2.05/1.00      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 2.05/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.05/1.00  
% 2.05/1.00  cnf(c_3103,plain,
% 2.05/1.00      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k9_subset_1(X1,X0,k1_xboole_0) ),
% 2.05/1.00      inference(superposition,[status(thm)],[c_1921,c_1922]) ).
% 2.05/1.00  
% 2.05/1.00  cnf(c_4,plain,
% 2.05/1.00      ( r1_tarski(X0,X0) ),
% 2.05/1.00      inference(cnf_transformation,[],[f64]) ).
% 2.05/1.00  
% 2.05/1.00  cnf(c_1927,plain,
% 2.05/1.00      ( r1_tarski(X0,X0) = iProver_top ),
% 2.05/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.05/1.00  
% 2.05/1.00  cnf(c_5,plain,
% 2.05/1.00      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 2.05/1.00      inference(cnf_transformation,[],[f43]) ).
% 2.05/1.00  
% 2.05/1.00  cnf(c_1926,plain,
% 2.05/1.00      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 2.05/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 2.05/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.05/1.00  
% 2.05/1.00  cnf(c_3229,plain,
% 2.05/1.00      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 2.05/1.00      inference(superposition,[status(thm)],[c_1927,c_1926]) ).
% 2.05/1.00  
% 2.05/1.00  cnf(c_7,plain,
% 2.05/1.00      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 2.05/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.05/1.00  
% 2.05/1.00  cnf(c_1924,plain,
% 2.05/1.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
% 2.05/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 2.05/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.05/1.00  
% 2.05/1.00  cnf(c_3268,plain,
% 2.05/1.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
% 2.05/1.00      inference(superposition,[status(thm)],[c_1927,c_1924]) ).
% 2.05/1.00  
% 2.05/1.00  cnf(c_4236,plain,
% 2.05/1.00      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 2.05/1.00      inference(light_normalisation,[status(thm)],[c_3268,c_3229]) ).
% 2.05/1.00  
% 2.05/1.00  cnf(c_4980,plain,
% 2.05/1.00      ( k9_subset_1(X0,X1,k1_xboole_0) = k1_xboole_0 ),
% 2.05/1.00      inference(light_normalisation,[status(thm)],[c_3103,c_3229,c_4236]) ).
% 2.05/1.00  
% 2.05/1.00  cnf(c_12,plain,
% 2.05/1.00      ( v2_tex_2(X0,X1)
% 2.05/1.00      | ~ v4_pre_topc(X2,X1)
% 2.05/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.05/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.05/1.00      | ~ l1_pre_topc(X1)
% 2.05/1.00      | k9_subset_1(u1_struct_0(X1),X0,X2) != sK0(X1,X0) ),
% 2.05/1.00      inference(cnf_transformation,[],[f55]) ).
% 2.05/1.00  
% 2.05/1.00  cnf(c_21,negated_conjecture,
% 2.05/1.00      ( l1_pre_topc(sK2) ),
% 2.05/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.05/1.00  
% 2.05/1.00  cnf(c_532,plain,
% 2.05/1.00      ( v2_tex_2(X0,X1)
% 2.05/1.00      | ~ v4_pre_topc(X2,X1)
% 2.05/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.05/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.05/1.00      | k9_subset_1(u1_struct_0(X1),X0,X2) != sK0(X1,X0)
% 2.05/1.00      | sK2 != X1 ),
% 2.05/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_21]) ).
% 2.05/1.00  
% 2.05/1.00  cnf(c_533,plain,
% 2.05/1.00      ( v2_tex_2(X0,sK2)
% 2.05/1.00      | ~ v4_pre_topc(X1,sK2)
% 2.05/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.05/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.05/1.00      | k9_subset_1(u1_struct_0(sK2),X0,X1) != sK0(sK2,X0) ),
% 2.05/1.00      inference(unflattening,[status(thm)],[c_532]) ).
% 2.05/1.00  
% 2.05/1.00  cnf(c_1911,plain,
% 2.05/1.00      ( k9_subset_1(u1_struct_0(sK2),X0,X1) != sK0(sK2,X0)
% 2.05/1.00      | v2_tex_2(X0,sK2) = iProver_top
% 2.05/1.00      | v4_pre_topc(X1,sK2) != iProver_top
% 2.05/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.05/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 2.05/1.00      inference(predicate_to_equality,[status(thm)],[c_533]) ).
% 2.05/1.00  
% 2.05/1.00  cnf(c_4983,plain,
% 2.05/1.00      ( sK0(sK2,X0) != k1_xboole_0
% 2.05/1.00      | v2_tex_2(X0,sK2) = iProver_top
% 2.05/1.00      | v4_pre_topc(k1_xboole_0,sK2) != iProver_top
% 2.05/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.05/1.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 2.05/1.00      inference(superposition,[status(thm)],[c_4980,c_1911]) ).
% 2.05/1.00  
% 2.05/1.00  cnf(c_4985,plain,
% 2.05/1.00      ( sK0(sK2,k1_xboole_0) != k1_xboole_0
% 2.05/1.00      | v2_tex_2(k1_xboole_0,sK2) = iProver_top
% 2.05/1.00      | v4_pre_topc(k1_xboole_0,sK2) != iProver_top
% 2.05/1.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 2.05/1.00      inference(instantiation,[status(thm)],[c_4983]) ).
% 2.05/1.00  
% 2.05/1.00  cnf(c_8,plain,
% 2.05/1.00      ( r1_tarski(k1_xboole_0,X0) ),
% 2.05/1.00      inference(cnf_transformation,[],[f45]) ).
% 2.05/1.00  
% 2.05/1.00  cnf(c_3337,plain,
% 2.05/1.00      ( r1_tarski(k1_xboole_0,sK0(sK2,X0)) ),
% 2.05/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 2.05/1.00  
% 2.05/1.00  cnf(c_3341,plain,
% 2.05/1.00      ( r1_tarski(k1_xboole_0,sK0(sK2,k1_xboole_0)) ),
% 2.05/1.00      inference(instantiation,[status(thm)],[c_3337]) ).
% 2.05/1.00  
% 2.05/1.00  cnf(c_2,plain,
% 2.05/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 2.05/1.00      inference(cnf_transformation,[],[f41]) ).
% 2.05/1.00  
% 2.05/1.00  cnf(c_2495,plain,
% 2.05/1.00      ( ~ r1_tarski(X0,sK0(sK2,X1))
% 2.05/1.00      | ~ r1_tarski(sK0(sK2,X1),X0)
% 2.05/1.00      | sK0(sK2,X1) = X0 ),
% 2.05/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 2.05/1.00  
% 2.05/1.00  cnf(c_2497,plain,
% 2.05/1.00      ( ~ r1_tarski(sK0(sK2,k1_xboole_0),k1_xboole_0)
% 2.05/1.00      | ~ r1_tarski(k1_xboole_0,sK0(sK2,k1_xboole_0))
% 2.05/1.00      | sK0(sK2,k1_xboole_0) = k1_xboole_0 ),
% 2.05/1.00      inference(instantiation,[status(thm)],[c_2495]) ).
% 2.05/1.00  
% 2.05/1.00  cnf(c_2068,plain,
% 2.05/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.05/1.00      inference(instantiation,[status(thm)],[c_10]) ).
% 2.05/1.00  
% 2.05/1.00  cnf(c_2072,plain,
% 2.05/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 2.05/1.00      inference(predicate_to_equality,[status(thm)],[c_2068]) ).
% 2.05/1.00  
% 2.05/1.00  cnf(c_18,negated_conjecture,
% 2.05/1.00      ( ~ v2_tex_2(sK3,sK2) ),
% 2.05/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.05/1.00  
% 2.05/1.00  cnf(c_1920,plain,
% 2.05/1.00      ( v2_tex_2(sK3,sK2) != iProver_top ),
% 2.05/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.05/1.00  
% 2.05/1.00  cnf(c_1,plain,
% 2.05/1.00      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 2.05/1.00      inference(cnf_transformation,[],[f38]) ).
% 2.05/1.00  
% 2.05/1.00  cnf(c_20,negated_conjecture,
% 2.05/1.00      ( v1_xboole_0(sK3) ),
% 2.05/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.05/1.00  
% 2.05/1.00  cnf(c_339,plain,
% 2.05/1.00      ( sK3 != X0 | k1_xboole_0 = X0 ),
% 2.05/1.00      inference(resolution_lifted,[status(thm)],[c_1,c_20]) ).
% 2.05/1.00  
% 2.05/1.00  cnf(c_340,plain,
% 2.05/1.00      ( k1_xboole_0 = sK3 ),
% 2.05/1.00      inference(unflattening,[status(thm)],[c_339]) ).
% 2.05/1.00  
% 2.05/1.00  cnf(c_1938,plain,
% 2.05/1.00      ( v2_tex_2(k1_xboole_0,sK2) != iProver_top ),
% 2.05/1.00      inference(light_normalisation,[status(thm)],[c_1920,c_340]) ).
% 2.05/1.00  
% 2.05/1.00  cnf(c_2028,plain,
% 2.05/1.00      ( ~ v2_tex_2(k1_xboole_0,sK2) ),
% 2.05/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_1938]) ).
% 2.05/1.00  
% 2.05/1.00  cnf(c_13,plain,
% 2.05/1.00      ( v2_tex_2(X0,X1)
% 2.05/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.05/1.00      | r1_tarski(sK0(X1,X0),X0)
% 2.05/1.00      | ~ l1_pre_topc(X1) ),
% 2.05/1.00      inference(cnf_transformation,[],[f54]) ).
% 2.05/1.00  
% 2.05/1.00  cnf(c_517,plain,
% 2.05/1.00      ( v2_tex_2(X0,X1)
% 2.05/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.05/1.00      | r1_tarski(sK0(X1,X0),X0)
% 2.05/1.00      | sK2 != X1 ),
% 2.05/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_21]) ).
% 2.05/1.00  
% 2.05/1.00  cnf(c_518,plain,
% 2.05/1.00      ( v2_tex_2(X0,sK2)
% 2.05/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.05/1.00      | r1_tarski(sK0(sK2,X0),X0) ),
% 2.05/1.00      inference(unflattening,[status(thm)],[c_517]) ).
% 2.05/1.00  
% 2.05/1.00  cnf(c_520,plain,
% 2.05/1.00      ( v2_tex_2(k1_xboole_0,sK2)
% 2.05/1.00      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.05/1.00      | r1_tarski(sK0(sK2,k1_xboole_0),k1_xboole_0) ),
% 2.05/1.00      inference(instantiation,[status(thm)],[c_518]) ).
% 2.05/1.00  
% 2.05/1.00  cnf(c_0,plain,
% 2.05/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 2.05/1.00      inference(cnf_transformation,[],[f37]) ).
% 2.05/1.00  
% 2.05/1.00  cnf(c_11,plain,
% 2.05/1.00      ( v4_pre_topc(X0,X1)
% 2.05/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.05/1.01      | ~ v2_pre_topc(X1)
% 2.05/1.01      | ~ l1_pre_topc(X1)
% 2.05/1.01      | ~ v1_xboole_0(X0) ),
% 2.05/1.01      inference(cnf_transformation,[],[f49]) ).
% 2.05/1.01  
% 2.05/1.01  cnf(c_22,negated_conjecture,
% 2.05/1.01      ( v2_pre_topc(sK2) ),
% 2.05/1.01      inference(cnf_transformation,[],[f56]) ).
% 2.05/1.01  
% 2.05/1.01  cnf(c_291,plain,
% 2.05/1.01      ( v4_pre_topc(X0,X1)
% 2.05/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.05/1.01      | ~ l1_pre_topc(X1)
% 2.05/1.01      | ~ v1_xboole_0(X0)
% 2.05/1.01      | sK2 != X1 ),
% 2.05/1.01      inference(resolution_lifted,[status(thm)],[c_11,c_22]) ).
% 2.05/1.01  
% 2.05/1.01  cnf(c_292,plain,
% 2.05/1.01      ( v4_pre_topc(X0,sK2)
% 2.05/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.05/1.01      | ~ l1_pre_topc(sK2)
% 2.05/1.01      | ~ v1_xboole_0(X0) ),
% 2.05/1.01      inference(unflattening,[status(thm)],[c_291]) ).
% 2.05/1.01  
% 2.05/1.01  cnf(c_296,plain,
% 2.05/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.05/1.01      | v4_pre_topc(X0,sK2)
% 2.05/1.01      | ~ v1_xboole_0(X0) ),
% 2.05/1.01      inference(global_propositional_subsumption,
% 2.05/1.01                [status(thm)],
% 2.05/1.01                [c_292,c_21]) ).
% 2.05/1.01  
% 2.05/1.01  cnf(c_297,plain,
% 2.05/1.01      ( v4_pre_topc(X0,sK2)
% 2.05/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.05/1.01      | ~ v1_xboole_0(X0) ),
% 2.05/1.01      inference(renaming,[status(thm)],[c_296]) ).
% 2.05/1.01  
% 2.05/1.01  cnf(c_316,plain,
% 2.05/1.01      ( v4_pre_topc(X0,sK2)
% 2.05/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.05/1.01      | k1_xboole_0 != X0 ),
% 2.05/1.01      inference(resolution_lifted,[status(thm)],[c_0,c_297]) ).
% 2.05/1.01  
% 2.05/1.01  cnf(c_317,plain,
% 2.05/1.01      ( v4_pre_topc(k1_xboole_0,sK2)
% 2.05/1.01      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.05/1.01      inference(unflattening,[status(thm)],[c_316]) ).
% 2.05/1.01  
% 2.05/1.01  cnf(c_323,plain,
% 2.05/1.01      ( v4_pre_topc(k1_xboole_0,sK2) ),
% 2.05/1.01      inference(forward_subsumption_resolution,
% 2.05/1.01                [status(thm)],
% 2.05/1.01                [c_317,c_10]) ).
% 2.05/1.01  
% 2.05/1.01  cnf(c_325,plain,
% 2.05/1.01      ( v4_pre_topc(k1_xboole_0,sK2) = iProver_top ),
% 2.05/1.01      inference(predicate_to_equality,[status(thm)],[c_323]) ).
% 2.05/1.01  
% 2.05/1.01  cnf(contradiction,plain,
% 2.05/1.01      ( $false ),
% 2.05/1.01      inference(minisat,
% 2.05/1.01                [status(thm)],
% 2.05/1.01                [c_4985,c_3341,c_2497,c_2072,c_2068,c_2028,c_1938,c_520,
% 2.05/1.01                 c_325]) ).
% 2.05/1.01  
% 2.05/1.01  
% 2.05/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.05/1.01  
% 2.05/1.01  ------                               Statistics
% 2.05/1.01  
% 2.05/1.01  ------ General
% 2.05/1.01  
% 2.05/1.01  abstr_ref_over_cycles:                  0
% 2.05/1.01  abstr_ref_under_cycles:                 0
% 2.05/1.01  gc_basic_clause_elim:                   0
% 2.05/1.01  forced_gc_time:                         0
% 2.05/1.01  parsing_time:                           0.01
% 2.05/1.01  unif_index_cands_time:                  0.
% 2.05/1.01  unif_index_add_time:                    0.
% 2.05/1.01  orderings_time:                         0.
% 2.05/1.01  out_proof_time:                         0.011
% 2.05/1.01  total_time:                             0.222
% 2.05/1.01  num_of_symbols:                         47
% 2.05/1.01  num_of_terms:                           3735
% 2.05/1.01  
% 2.05/1.01  ------ Preprocessing
% 2.05/1.01  
% 2.05/1.01  num_of_splits:                          0
% 2.05/1.01  num_of_split_atoms:                     0
% 2.05/1.01  num_of_reused_defs:                     0
% 2.05/1.01  num_eq_ax_congr_red:                    21
% 2.05/1.01  num_of_sem_filtered_clauses:            1
% 2.05/1.01  num_of_subtypes:                        0
% 2.05/1.01  monotx_restored_types:                  0
% 2.05/1.01  sat_num_of_epr_types:                   0
% 2.05/1.01  sat_num_of_non_cyclic_types:            0
% 2.05/1.01  sat_guarded_non_collapsed_types:        0
% 2.05/1.01  num_pure_diseq_elim:                    0
% 2.05/1.01  simp_replaced_by:                       0
% 2.05/1.01  res_preprocessed:                       104
% 2.05/1.01  prep_upred:                             0
% 2.05/1.01  prep_unflattend:                        29
% 2.05/1.01  smt_new_axioms:                         0
% 2.05/1.01  pred_elim_cands:                        4
% 2.05/1.01  pred_elim:                              3
% 2.05/1.01  pred_elim_cl:                           3
% 2.05/1.01  pred_elim_cycles:                       8
% 2.05/1.01  merged_defs:                            8
% 2.05/1.01  merged_defs_ncl:                        0
% 2.05/1.01  bin_hyper_res:                          8
% 2.05/1.01  prep_cycles:                            4
% 2.05/1.01  pred_elim_time:                         0.019
% 2.05/1.01  splitting_time:                         0.
% 2.05/1.01  sem_filter_time:                        0.
% 2.05/1.01  monotx_time:                            0.001
% 2.05/1.01  subtype_inf_time:                       0.
% 2.05/1.01  
% 2.05/1.01  ------ Problem properties
% 2.05/1.01  
% 2.05/1.01  clauses:                                19
% 2.05/1.01  conjectures:                            2
% 2.05/1.01  epr:                                    7
% 2.05/1.01  horn:                                   17
% 2.05/1.01  ground:                                 5
% 2.05/1.01  unary:                                  8
% 2.05/1.01  binary:                                 4
% 2.05/1.01  lits:                                   45
% 2.05/1.01  lits_eq:                                8
% 2.05/1.01  fd_pure:                                0
% 2.05/1.01  fd_pseudo:                              0
% 2.05/1.01  fd_cond:                                0
% 2.05/1.01  fd_pseudo_cond:                         1
% 2.05/1.01  ac_symbols:                             0
% 2.05/1.01  
% 2.05/1.01  ------ Propositional Solver
% 2.05/1.01  
% 2.05/1.01  prop_solver_calls:                      26
% 2.05/1.01  prop_fast_solver_calls:                 959
% 2.05/1.01  smt_solver_calls:                       0
% 2.05/1.01  smt_fast_solver_calls:                  0
% 2.05/1.01  prop_num_of_clauses:                    1441
% 2.05/1.01  prop_preprocess_simplified:             4724
% 2.05/1.01  prop_fo_subsumed:                       24
% 2.05/1.01  prop_solver_time:                       0.
% 2.05/1.01  smt_solver_time:                        0.
% 2.05/1.01  smt_fast_solver_time:                   0.
% 2.05/1.01  prop_fast_solver_time:                  0.
% 2.05/1.01  prop_unsat_core_time:                   0.
% 2.05/1.01  
% 2.05/1.01  ------ QBF
% 2.05/1.01  
% 2.05/1.01  qbf_q_res:                              0
% 2.05/1.01  qbf_num_tautologies:                    0
% 2.05/1.01  qbf_prep_cycles:                        0
% 2.05/1.01  
% 2.05/1.01  ------ BMC1
% 2.05/1.01  
% 2.05/1.01  bmc1_current_bound:                     -1
% 2.05/1.01  bmc1_last_solved_bound:                 -1
% 2.05/1.01  bmc1_unsat_core_size:                   -1
% 2.05/1.01  bmc1_unsat_core_parents_size:           -1
% 2.05/1.01  bmc1_merge_next_fun:                    0
% 2.05/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.05/1.01  
% 2.05/1.01  ------ Instantiation
% 2.05/1.01  
% 2.05/1.01  inst_num_of_clauses:                    405
% 2.05/1.01  inst_num_in_passive:                    73
% 2.05/1.01  inst_num_in_active:                     202
% 2.05/1.01  inst_num_in_unprocessed:                131
% 2.05/1.01  inst_num_of_loops:                      230
% 2.05/1.01  inst_num_of_learning_restarts:          0
% 2.05/1.01  inst_num_moves_active_passive:          26
% 2.05/1.01  inst_lit_activity:                      0
% 2.05/1.01  inst_lit_activity_moves:                0
% 2.05/1.01  inst_num_tautologies:                   0
% 2.05/1.01  inst_num_prop_implied:                  0
% 2.05/1.01  inst_num_existing_simplified:           0
% 2.05/1.01  inst_num_eq_res_simplified:             0
% 2.05/1.01  inst_num_child_elim:                    0
% 2.05/1.01  inst_num_of_dismatching_blockings:      120
% 2.05/1.01  inst_num_of_non_proper_insts:           418
% 2.05/1.01  inst_num_of_duplicates:                 0
% 2.05/1.01  inst_inst_num_from_inst_to_res:         0
% 2.05/1.01  inst_dismatching_checking_time:         0.
% 2.05/1.01  
% 2.05/1.01  ------ Resolution
% 2.05/1.01  
% 2.05/1.01  res_num_of_clauses:                     0
% 2.05/1.01  res_num_in_passive:                     0
% 2.05/1.01  res_num_in_active:                      0
% 2.05/1.01  res_num_of_loops:                       108
% 2.05/1.01  res_forward_subset_subsumed:            44
% 2.05/1.01  res_backward_subset_subsumed:           2
% 2.05/1.01  res_forward_subsumed:                   0
% 2.05/1.01  res_backward_subsumed:                  0
% 2.05/1.01  res_forward_subsumption_resolution:     4
% 2.05/1.01  res_backward_subsumption_resolution:    0
% 2.05/1.01  res_clause_to_clause_subsumption:       694
% 2.05/1.01  res_orphan_elimination:                 0
% 2.05/1.01  res_tautology_del:                      57
% 2.05/1.01  res_num_eq_res_simplified:              0
% 2.05/1.01  res_num_sel_changes:                    0
% 2.05/1.01  res_moves_from_active_to_pass:          0
% 2.05/1.01  
% 2.05/1.01  ------ Superposition
% 2.05/1.01  
% 2.05/1.01  sup_time_total:                         0.
% 2.05/1.01  sup_time_generating:                    0.
% 2.05/1.01  sup_time_sim_full:                      0.
% 2.05/1.01  sup_time_sim_immed:                     0.
% 2.05/1.01  
% 2.05/1.01  sup_num_of_clauses:                     73
% 2.05/1.01  sup_num_in_active:                      46
% 2.05/1.01  sup_num_in_passive:                     27
% 2.05/1.01  sup_num_of_loops:                       45
% 2.05/1.01  sup_fw_superposition:                   45
% 2.05/1.01  sup_bw_superposition:                   22
% 2.05/1.01  sup_immediate_simplified:               5
% 2.05/1.01  sup_given_eliminated:                   0
% 2.05/1.01  comparisons_done:                       0
% 2.05/1.01  comparisons_avoided:                    0
% 2.05/1.01  
% 2.05/1.01  ------ Simplifications
% 2.05/1.01  
% 2.05/1.01  
% 2.05/1.01  sim_fw_subset_subsumed:                 2
% 2.05/1.01  sim_bw_subset_subsumed:                 1
% 2.05/1.01  sim_fw_subsumed:                        2
% 2.05/1.01  sim_bw_subsumed:                        0
% 2.05/1.01  sim_fw_subsumption_res:                 0
% 2.05/1.01  sim_bw_subsumption_res:                 0
% 2.05/1.01  sim_tautology_del:                      2
% 2.05/1.01  sim_eq_tautology_del:                   1
% 2.05/1.01  sim_eq_res_simp:                        0
% 2.05/1.01  sim_fw_demodulated:                     1
% 2.05/1.01  sim_bw_demodulated:                     0
% 2.05/1.01  sim_light_normalised:                   9
% 2.05/1.01  sim_joinable_taut:                      0
% 2.05/1.01  sim_joinable_simp:                      0
% 2.05/1.01  sim_ac_normalised:                      0
% 2.05/1.01  sim_smt_subsumption:                    0
% 2.05/1.01  
%------------------------------------------------------------------------------
