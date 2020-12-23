%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:26:15 EST 2020

% Result     : Theorem 1.62s
% Output     : CNFRefutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 219 expanded)
%              Number of clauses        :   50 (  74 expanded)
%              Number of leaves         :   14 (  51 expanded)
%              Depth                    :   21
%              Number of atoms          :  312 ( 921 expanded)
%              Number of equality atoms :   90 ( 132 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

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

fof(f54,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | r1_tarski(sK0(X0,X1),X1)
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

fof(f6,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f45,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f18])).

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

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f47,f46])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( v2_tex_2(X1,X0)
      | k9_subset_1(u1_struct_0(X0),X1,X3) != sK0(X0,X1)
      | ~ v4_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
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

cnf(c_1895,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_13,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(sK0(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_21,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_508,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(sK0(X1,X0),X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_21])).

cnf(c_509,plain,
    ( v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(sK0(sK2,X0),X0) ),
    inference(unflattening,[status(thm)],[c_508])).

cnf(c_1886,plain,
    ( v2_tex_2(X0,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(sK0(sK2,X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_509])).

cnf(c_2382,plain,
    ( v2_tex_2(k1_xboole_0,sK2) = iProver_top
    | r1_tarski(sK0(sK2,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1895,c_1886])).

cnf(c_510,plain,
    ( v2_tex_2(X0,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(sK0(sK2,X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_509])).

cnf(c_512,plain,
    ( v2_tex_2(k1_xboole_0,sK2) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(sK0(sK2,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_510])).

cnf(c_18,negated_conjecture,
    ( ~ v2_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1894,plain,
    ( v2_tex_2(sK3,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_20,negated_conjecture,
    ( v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_330,plain,
    ( sK3 != X0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_20])).

cnf(c_331,plain,
    ( k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_330])).

cnf(c_1911,plain,
    ( v2_tex_2(k1_xboole_0,sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1894,c_331])).

cnf(c_2039,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_2043,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2039])).

cnf(c_2592,plain,
    ( r1_tarski(sK0(sK2,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2382,c_512,c_1911,c_2043])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1897,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2597,plain,
    ( sK0(sK2,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2592,c_1897])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k4_xboole_0(X2,k4_xboole_0(X2,X0)) = k9_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1896,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k9_subset_1(X2,X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2959,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k9_subset_1(X1,X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1895,c_1896])).

cnf(c_7,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_2979,plain,
    ( k9_subset_1(X0,X1,k1_xboole_0) = k4_xboole_0(X1,X1) ),
    inference(light_normalisation,[status(thm)],[c_2959,c_7])).

cnf(c_12,plain,
    ( v2_tex_2(X0,X1)
    | ~ v4_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),X0,X2) != sK0(X1,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_523,plain,
    ( v2_tex_2(X0,X1)
    | ~ v4_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | k9_subset_1(u1_struct_0(X1),X0,X2) != sK0(X1,X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_21])).

cnf(c_524,plain,
    ( v2_tex_2(X0,sK2)
    | ~ v4_pre_topc(X1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | k9_subset_1(u1_struct_0(sK2),X0,X1) != sK0(sK2,X0) ),
    inference(unflattening,[status(thm)],[c_523])).

cnf(c_1885,plain,
    ( k9_subset_1(u1_struct_0(sK2),X0,X1) != sK0(sK2,X0)
    | v2_tex_2(X0,sK2) = iProver_top
    | v4_pre_topc(X1,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_524])).

cnf(c_3093,plain,
    ( k4_xboole_0(X0,X0) != sK0(sK2,X0)
    | v2_tex_2(X0,sK2) = iProver_top
    | v4_pre_topc(k1_xboole_0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2979,c_1885])).

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

cnf(c_282,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_22])).

cnf(c_283,plain,
    ( v4_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | ~ v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_282])).

cnf(c_287,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v4_pre_topc(X0,sK2)
    | ~ v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_283,c_21])).

cnf(c_288,plain,
    ( v4_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_287])).

cnf(c_307,plain,
    ( v4_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_288])).

cnf(c_308,plain,
    ( v4_pre_topc(k1_xboole_0,sK2)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(unflattening,[status(thm)],[c_307])).

cnf(c_314,plain,
    ( v4_pre_topc(k1_xboole_0,sK2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_308,c_10])).

cnf(c_316,plain,
    ( v4_pre_topc(k1_xboole_0,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_314])).

cnf(c_3372,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | k4_xboole_0(X0,X0) != sK0(sK2,X0)
    | v2_tex_2(X0,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3093,c_316,c_2043])).

cnf(c_3373,plain,
    ( k4_xboole_0(X0,X0) != sK0(sK2,X0)
    | v2_tex_2(X0,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3372])).

cnf(c_3382,plain,
    ( k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | v2_tex_2(k1_xboole_0,sK2) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2597,c_3373])).

cnf(c_3386,plain,
    ( k1_xboole_0 != k1_xboole_0
    | v2_tex_2(k1_xboole_0,sK2) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3382,c_7])).

cnf(c_3387,plain,
    ( v2_tex_2(k1_xboole_0,sK2) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3386])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3387,c_2043,c_1911])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.31  % Computer   : n003.cluster.edu
% 0.12/0.31  % Model      : x86_64 x86_64
% 0.12/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.31  % Memory     : 8042.1875MB
% 0.12/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 11:25:42 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  % Running in FOF mode
% 1.62/0.96  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.62/0.96  
% 1.62/0.96  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.62/0.96  
% 1.62/0.96  ------  iProver source info
% 1.62/0.96  
% 1.62/0.96  git: date: 2020-06-30 10:37:57 +0100
% 1.62/0.96  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.62/0.96  git: non_committed_changes: false
% 1.62/0.96  git: last_make_outside_of_git: false
% 1.62/0.96  
% 1.62/0.96  ------ 
% 1.62/0.96  
% 1.62/0.96  ------ Input Options
% 1.62/0.96  
% 1.62/0.96  --out_options                           all
% 1.62/0.96  --tptp_safe_out                         true
% 1.62/0.96  --problem_path                          ""
% 1.62/0.96  --include_path                          ""
% 1.62/0.96  --clausifier                            res/vclausify_rel
% 1.62/0.96  --clausifier_options                    --mode clausify
% 1.62/0.96  --stdin                                 false
% 1.62/0.96  --stats_out                             all
% 1.62/0.96  
% 1.62/0.96  ------ General Options
% 1.62/0.96  
% 1.62/0.96  --fof                                   false
% 1.62/0.96  --time_out_real                         305.
% 1.62/0.96  --time_out_virtual                      -1.
% 1.62/0.96  --symbol_type_check                     false
% 1.62/0.96  --clausify_out                          false
% 1.62/0.96  --sig_cnt_out                           false
% 1.62/0.96  --trig_cnt_out                          false
% 1.62/0.96  --trig_cnt_out_tolerance                1.
% 1.62/0.96  --trig_cnt_out_sk_spl                   false
% 1.62/0.96  --abstr_cl_out                          false
% 1.62/0.96  
% 1.62/0.96  ------ Global Options
% 1.62/0.96  
% 1.62/0.96  --schedule                              default
% 1.62/0.96  --add_important_lit                     false
% 1.62/0.96  --prop_solver_per_cl                    1000
% 1.62/0.96  --min_unsat_core                        false
% 1.62/0.96  --soft_assumptions                      false
% 1.62/0.96  --soft_lemma_size                       3
% 1.62/0.96  --prop_impl_unit_size                   0
% 1.62/0.96  --prop_impl_unit                        []
% 1.62/0.96  --share_sel_clauses                     true
% 1.62/0.96  --reset_solvers                         false
% 1.62/0.96  --bc_imp_inh                            [conj_cone]
% 1.62/0.96  --conj_cone_tolerance                   3.
% 1.62/0.96  --extra_neg_conj                        none
% 1.62/0.96  --large_theory_mode                     true
% 1.62/0.96  --prolific_symb_bound                   200
% 1.62/0.96  --lt_threshold                          2000
% 1.62/0.96  --clause_weak_htbl                      true
% 1.62/0.96  --gc_record_bc_elim                     false
% 1.62/0.96  
% 1.62/0.96  ------ Preprocessing Options
% 1.62/0.96  
% 1.62/0.96  --preprocessing_flag                    true
% 1.62/0.96  --time_out_prep_mult                    0.1
% 1.62/0.96  --splitting_mode                        input
% 1.62/0.96  --splitting_grd                         true
% 1.62/0.96  --splitting_cvd                         false
% 1.62/0.96  --splitting_cvd_svl                     false
% 1.62/0.96  --splitting_nvd                         32
% 1.62/0.96  --sub_typing                            true
% 1.62/0.96  --prep_gs_sim                           true
% 1.62/0.96  --prep_unflatten                        true
% 1.62/0.96  --prep_res_sim                          true
% 1.62/0.96  --prep_upred                            true
% 1.62/0.96  --prep_sem_filter                       exhaustive
% 1.62/0.96  --prep_sem_filter_out                   false
% 1.62/0.96  --pred_elim                             true
% 1.62/0.96  --res_sim_input                         true
% 1.62/0.96  --eq_ax_congr_red                       true
% 1.62/0.96  --pure_diseq_elim                       true
% 1.62/0.96  --brand_transform                       false
% 1.62/0.96  --non_eq_to_eq                          false
% 1.62/0.96  --prep_def_merge                        true
% 1.62/0.96  --prep_def_merge_prop_impl              false
% 1.62/0.96  --prep_def_merge_mbd                    true
% 1.62/0.96  --prep_def_merge_tr_red                 false
% 1.62/0.96  --prep_def_merge_tr_cl                  false
% 1.62/0.96  --smt_preprocessing                     true
% 1.62/0.96  --smt_ac_axioms                         fast
% 1.62/0.96  --preprocessed_out                      false
% 1.62/0.96  --preprocessed_stats                    false
% 1.62/0.96  
% 1.62/0.96  ------ Abstraction refinement Options
% 1.62/0.96  
% 1.62/0.96  --abstr_ref                             []
% 1.62/0.96  --abstr_ref_prep                        false
% 1.62/0.96  --abstr_ref_until_sat                   false
% 1.62/0.96  --abstr_ref_sig_restrict                funpre
% 1.62/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 1.62/0.96  --abstr_ref_under                       []
% 1.62/0.96  
% 1.62/0.96  ------ SAT Options
% 1.62/0.96  
% 1.62/0.96  --sat_mode                              false
% 1.62/0.96  --sat_fm_restart_options                ""
% 1.62/0.96  --sat_gr_def                            false
% 1.62/0.96  --sat_epr_types                         true
% 1.62/0.96  --sat_non_cyclic_types                  false
% 1.62/0.96  --sat_finite_models                     false
% 1.62/0.96  --sat_fm_lemmas                         false
% 1.62/0.96  --sat_fm_prep                           false
% 1.62/0.96  --sat_fm_uc_incr                        true
% 1.62/0.96  --sat_out_model                         small
% 1.62/0.96  --sat_out_clauses                       false
% 1.62/0.96  
% 1.62/0.96  ------ QBF Options
% 1.62/0.96  
% 1.62/0.96  --qbf_mode                              false
% 1.62/0.96  --qbf_elim_univ                         false
% 1.62/0.96  --qbf_dom_inst                          none
% 1.62/0.96  --qbf_dom_pre_inst                      false
% 1.62/0.96  --qbf_sk_in                             false
% 1.62/0.96  --qbf_pred_elim                         true
% 1.62/0.96  --qbf_split                             512
% 1.62/0.96  
% 1.62/0.96  ------ BMC1 Options
% 1.62/0.96  
% 1.62/0.96  --bmc1_incremental                      false
% 1.62/0.96  --bmc1_axioms                           reachable_all
% 1.62/0.96  --bmc1_min_bound                        0
% 1.62/0.96  --bmc1_max_bound                        -1
% 1.62/0.96  --bmc1_max_bound_default                -1
% 1.62/0.96  --bmc1_symbol_reachability              true
% 1.62/0.96  --bmc1_property_lemmas                  false
% 1.62/0.96  --bmc1_k_induction                      false
% 1.62/0.96  --bmc1_non_equiv_states                 false
% 1.62/0.96  --bmc1_deadlock                         false
% 1.62/0.96  --bmc1_ucm                              false
% 1.62/0.96  --bmc1_add_unsat_core                   none
% 1.62/0.96  --bmc1_unsat_core_children              false
% 1.62/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 1.62/0.96  --bmc1_out_stat                         full
% 1.62/0.96  --bmc1_ground_init                      false
% 1.62/0.96  --bmc1_pre_inst_next_state              false
% 1.62/0.96  --bmc1_pre_inst_state                   false
% 1.62/0.96  --bmc1_pre_inst_reach_state             false
% 1.62/0.96  --bmc1_out_unsat_core                   false
% 1.62/0.96  --bmc1_aig_witness_out                  false
% 1.62/0.96  --bmc1_verbose                          false
% 1.62/0.96  --bmc1_dump_clauses_tptp                false
% 1.62/0.96  --bmc1_dump_unsat_core_tptp             false
% 1.62/0.96  --bmc1_dump_file                        -
% 1.62/0.96  --bmc1_ucm_expand_uc_limit              128
% 1.62/0.96  --bmc1_ucm_n_expand_iterations          6
% 1.62/0.96  --bmc1_ucm_extend_mode                  1
% 1.62/0.96  --bmc1_ucm_init_mode                    2
% 1.62/0.96  --bmc1_ucm_cone_mode                    none
% 1.62/0.96  --bmc1_ucm_reduced_relation_type        0
% 1.62/0.96  --bmc1_ucm_relax_model                  4
% 1.62/0.96  --bmc1_ucm_full_tr_after_sat            true
% 1.62/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 1.62/0.96  --bmc1_ucm_layered_model                none
% 1.62/0.96  --bmc1_ucm_max_lemma_size               10
% 1.62/0.96  
% 1.62/0.96  ------ AIG Options
% 1.62/0.96  
% 1.62/0.96  --aig_mode                              false
% 1.62/0.96  
% 1.62/0.96  ------ Instantiation Options
% 1.62/0.96  
% 1.62/0.96  --instantiation_flag                    true
% 1.62/0.96  --inst_sos_flag                         false
% 1.62/0.96  --inst_sos_phase                        true
% 1.62/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.62/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.62/0.96  --inst_lit_sel_side                     num_symb
% 1.62/0.96  --inst_solver_per_active                1400
% 1.62/0.96  --inst_solver_calls_frac                1.
% 1.62/0.96  --inst_passive_queue_type               priority_queues
% 1.62/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.62/0.96  --inst_passive_queues_freq              [25;2]
% 1.62/0.96  --inst_dismatching                      true
% 1.62/0.96  --inst_eager_unprocessed_to_passive     true
% 1.62/0.96  --inst_prop_sim_given                   true
% 1.62/0.96  --inst_prop_sim_new                     false
% 1.62/0.96  --inst_subs_new                         false
% 1.62/0.96  --inst_eq_res_simp                      false
% 1.62/0.96  --inst_subs_given                       false
% 1.62/0.96  --inst_orphan_elimination               true
% 1.62/0.96  --inst_learning_loop_flag               true
% 1.62/0.96  --inst_learning_start                   3000
% 1.62/0.96  --inst_learning_factor                  2
% 1.62/0.96  --inst_start_prop_sim_after_learn       3
% 1.62/0.96  --inst_sel_renew                        solver
% 1.62/0.96  --inst_lit_activity_flag                true
% 1.62/0.96  --inst_restr_to_given                   false
% 1.62/0.96  --inst_activity_threshold               500
% 1.62/0.96  --inst_out_proof                        true
% 1.62/0.96  
% 1.62/0.96  ------ Resolution Options
% 1.62/0.96  
% 1.62/0.96  --resolution_flag                       true
% 1.62/0.96  --res_lit_sel                           adaptive
% 1.62/0.96  --res_lit_sel_side                      none
% 1.62/0.96  --res_ordering                          kbo
% 1.62/0.96  --res_to_prop_solver                    active
% 1.62/0.96  --res_prop_simpl_new                    false
% 1.62/0.96  --res_prop_simpl_given                  true
% 1.62/0.96  --res_passive_queue_type                priority_queues
% 1.62/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.62/0.96  --res_passive_queues_freq               [15;5]
% 1.62/0.96  --res_forward_subs                      full
% 1.62/0.96  --res_backward_subs                     full
% 1.62/0.96  --res_forward_subs_resolution           true
% 1.62/0.96  --res_backward_subs_resolution          true
% 1.62/0.96  --res_orphan_elimination                true
% 1.62/0.96  --res_time_limit                        2.
% 1.62/0.96  --res_out_proof                         true
% 1.62/0.96  
% 1.62/0.96  ------ Superposition Options
% 1.62/0.96  
% 1.62/0.96  --superposition_flag                    true
% 1.62/0.96  --sup_passive_queue_type                priority_queues
% 1.62/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.62/0.96  --sup_passive_queues_freq               [8;1;4]
% 1.62/0.96  --demod_completeness_check              fast
% 1.62/0.96  --demod_use_ground                      true
% 1.62/0.96  --sup_to_prop_solver                    passive
% 1.62/0.96  --sup_prop_simpl_new                    true
% 1.62/0.96  --sup_prop_simpl_given                  true
% 1.62/0.96  --sup_fun_splitting                     false
% 1.62/0.96  --sup_smt_interval                      50000
% 1.62/0.96  
% 1.62/0.96  ------ Superposition Simplification Setup
% 1.62/0.96  
% 1.62/0.96  --sup_indices_passive                   []
% 1.62/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.62/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.62/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.62/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 1.62/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.62/0.96  --sup_full_bw                           [BwDemod]
% 1.62/0.96  --sup_immed_triv                        [TrivRules]
% 1.62/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.62/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.62/0.96  --sup_immed_bw_main                     []
% 1.62/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.62/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 1.62/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.62/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.62/0.96  
% 1.62/0.96  ------ Combination Options
% 1.62/0.96  
% 1.62/0.96  --comb_res_mult                         3
% 1.62/0.96  --comb_sup_mult                         2
% 1.62/0.96  --comb_inst_mult                        10
% 1.62/0.96  
% 1.62/0.96  ------ Debug Options
% 1.62/0.96  
% 1.62/0.96  --dbg_backtrace                         false
% 1.62/0.96  --dbg_dump_prop_clauses                 false
% 1.62/0.96  --dbg_dump_prop_clauses_file            -
% 1.62/0.96  --dbg_out_stat                          false
% 1.62/0.96  ------ Parsing...
% 1.62/0.96  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.62/0.96  
% 1.62/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 1.62/0.96  
% 1.62/0.96  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.62/0.96  
% 1.62/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.62/0.96  ------ Proving...
% 1.62/0.96  ------ Problem Properties 
% 1.62/0.96  
% 1.62/0.96  
% 1.62/0.96  clauses                                 19
% 1.62/0.96  conjectures                             2
% 1.62/0.96  EPR                                     7
% 1.62/0.96  Horn                                    17
% 1.62/0.96  unary                                   8
% 1.62/0.96  binary                                  4
% 1.62/0.96  lits                                    45
% 1.62/0.96  lits eq                                 9
% 1.62/0.96  fd_pure                                 0
% 1.62/0.96  fd_pseudo                               0
% 1.62/0.96  fd_cond                                 1
% 1.62/0.96  fd_pseudo_cond                          1
% 1.62/0.96  AC symbols                              0
% 1.62/0.96  
% 1.62/0.96  ------ Schedule dynamic 5 is on 
% 1.62/0.96  
% 1.62/0.96  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.62/0.96  
% 1.62/0.96  
% 1.62/0.96  ------ 
% 1.62/0.96  Current options:
% 1.62/0.96  ------ 
% 1.62/0.96  
% 1.62/0.96  ------ Input Options
% 1.62/0.96  
% 1.62/0.96  --out_options                           all
% 1.62/0.96  --tptp_safe_out                         true
% 1.62/0.96  --problem_path                          ""
% 1.62/0.96  --include_path                          ""
% 1.62/0.96  --clausifier                            res/vclausify_rel
% 1.62/0.96  --clausifier_options                    --mode clausify
% 1.62/0.96  --stdin                                 false
% 1.62/0.96  --stats_out                             all
% 1.62/0.96  
% 1.62/0.96  ------ General Options
% 1.62/0.96  
% 1.62/0.96  --fof                                   false
% 1.62/0.96  --time_out_real                         305.
% 1.62/0.96  --time_out_virtual                      -1.
% 1.62/0.96  --symbol_type_check                     false
% 1.62/0.96  --clausify_out                          false
% 1.62/0.96  --sig_cnt_out                           false
% 1.62/0.96  --trig_cnt_out                          false
% 1.62/0.96  --trig_cnt_out_tolerance                1.
% 1.62/0.96  --trig_cnt_out_sk_spl                   false
% 1.62/0.96  --abstr_cl_out                          false
% 1.62/0.96  
% 1.62/0.96  ------ Global Options
% 1.62/0.96  
% 1.62/0.96  --schedule                              default
% 1.62/0.96  --add_important_lit                     false
% 1.62/0.96  --prop_solver_per_cl                    1000
% 1.62/0.96  --min_unsat_core                        false
% 1.62/0.96  --soft_assumptions                      false
% 1.62/0.96  --soft_lemma_size                       3
% 1.62/0.96  --prop_impl_unit_size                   0
% 1.62/0.96  --prop_impl_unit                        []
% 1.62/0.96  --share_sel_clauses                     true
% 1.62/0.96  --reset_solvers                         false
% 1.62/0.96  --bc_imp_inh                            [conj_cone]
% 1.62/0.96  --conj_cone_tolerance                   3.
% 1.62/0.96  --extra_neg_conj                        none
% 1.62/0.96  --large_theory_mode                     true
% 1.62/0.96  --prolific_symb_bound                   200
% 1.62/0.96  --lt_threshold                          2000
% 1.62/0.96  --clause_weak_htbl                      true
% 1.62/0.96  --gc_record_bc_elim                     false
% 1.62/0.96  
% 1.62/0.96  ------ Preprocessing Options
% 1.62/0.96  
% 1.62/0.96  --preprocessing_flag                    true
% 1.62/0.96  --time_out_prep_mult                    0.1
% 1.62/0.96  --splitting_mode                        input
% 1.62/0.96  --splitting_grd                         true
% 1.62/0.96  --splitting_cvd                         false
% 1.62/0.96  --splitting_cvd_svl                     false
% 1.62/0.96  --splitting_nvd                         32
% 1.62/0.96  --sub_typing                            true
% 1.62/0.96  --prep_gs_sim                           true
% 1.62/0.96  --prep_unflatten                        true
% 1.62/0.96  --prep_res_sim                          true
% 1.62/0.96  --prep_upred                            true
% 1.62/0.96  --prep_sem_filter                       exhaustive
% 1.62/0.96  --prep_sem_filter_out                   false
% 1.62/0.96  --pred_elim                             true
% 1.62/0.96  --res_sim_input                         true
% 1.62/0.96  --eq_ax_congr_red                       true
% 1.62/0.96  --pure_diseq_elim                       true
% 1.62/0.96  --brand_transform                       false
% 1.62/0.96  --non_eq_to_eq                          false
% 1.62/0.96  --prep_def_merge                        true
% 1.62/0.96  --prep_def_merge_prop_impl              false
% 1.62/0.96  --prep_def_merge_mbd                    true
% 1.62/0.96  --prep_def_merge_tr_red                 false
% 1.62/0.96  --prep_def_merge_tr_cl                  false
% 1.62/0.96  --smt_preprocessing                     true
% 1.62/0.96  --smt_ac_axioms                         fast
% 1.62/0.96  --preprocessed_out                      false
% 1.62/0.96  --preprocessed_stats                    false
% 1.62/0.96  
% 1.62/0.96  ------ Abstraction refinement Options
% 1.62/0.96  
% 1.62/0.96  --abstr_ref                             []
% 1.62/0.96  --abstr_ref_prep                        false
% 1.62/0.96  --abstr_ref_until_sat                   false
% 1.62/0.96  --abstr_ref_sig_restrict                funpre
% 1.62/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 1.62/0.96  --abstr_ref_under                       []
% 1.62/0.96  
% 1.62/0.96  ------ SAT Options
% 1.62/0.96  
% 1.62/0.96  --sat_mode                              false
% 1.62/0.96  --sat_fm_restart_options                ""
% 1.62/0.96  --sat_gr_def                            false
% 1.62/0.96  --sat_epr_types                         true
% 1.62/0.96  --sat_non_cyclic_types                  false
% 1.62/0.96  --sat_finite_models                     false
% 1.62/0.96  --sat_fm_lemmas                         false
% 1.62/0.96  --sat_fm_prep                           false
% 1.62/0.96  --sat_fm_uc_incr                        true
% 1.62/0.96  --sat_out_model                         small
% 1.62/0.96  --sat_out_clauses                       false
% 1.62/0.96  
% 1.62/0.96  ------ QBF Options
% 1.62/0.96  
% 1.62/0.96  --qbf_mode                              false
% 1.62/0.96  --qbf_elim_univ                         false
% 1.62/0.96  --qbf_dom_inst                          none
% 1.62/0.96  --qbf_dom_pre_inst                      false
% 1.62/0.96  --qbf_sk_in                             false
% 1.62/0.96  --qbf_pred_elim                         true
% 1.62/0.96  --qbf_split                             512
% 1.62/0.96  
% 1.62/0.96  ------ BMC1 Options
% 1.62/0.96  
% 1.62/0.96  --bmc1_incremental                      false
% 1.62/0.96  --bmc1_axioms                           reachable_all
% 1.62/0.96  --bmc1_min_bound                        0
% 1.62/0.96  --bmc1_max_bound                        -1
% 1.62/0.96  --bmc1_max_bound_default                -1
% 1.62/0.96  --bmc1_symbol_reachability              true
% 1.62/0.96  --bmc1_property_lemmas                  false
% 1.62/0.96  --bmc1_k_induction                      false
% 1.62/0.96  --bmc1_non_equiv_states                 false
% 1.62/0.96  --bmc1_deadlock                         false
% 1.62/0.96  --bmc1_ucm                              false
% 1.62/0.96  --bmc1_add_unsat_core                   none
% 1.62/0.96  --bmc1_unsat_core_children              false
% 1.62/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 1.62/0.96  --bmc1_out_stat                         full
% 1.62/0.96  --bmc1_ground_init                      false
% 1.62/0.96  --bmc1_pre_inst_next_state              false
% 1.62/0.96  --bmc1_pre_inst_state                   false
% 1.62/0.96  --bmc1_pre_inst_reach_state             false
% 1.62/0.96  --bmc1_out_unsat_core                   false
% 1.62/0.96  --bmc1_aig_witness_out                  false
% 1.62/0.96  --bmc1_verbose                          false
% 1.62/0.96  --bmc1_dump_clauses_tptp                false
% 1.62/0.96  --bmc1_dump_unsat_core_tptp             false
% 1.62/0.96  --bmc1_dump_file                        -
% 1.62/0.96  --bmc1_ucm_expand_uc_limit              128
% 1.62/0.96  --bmc1_ucm_n_expand_iterations          6
% 1.62/0.96  --bmc1_ucm_extend_mode                  1
% 1.62/0.96  --bmc1_ucm_init_mode                    2
% 1.62/0.96  --bmc1_ucm_cone_mode                    none
% 1.62/0.96  --bmc1_ucm_reduced_relation_type        0
% 1.62/0.96  --bmc1_ucm_relax_model                  4
% 1.62/0.96  --bmc1_ucm_full_tr_after_sat            true
% 1.62/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 1.62/0.96  --bmc1_ucm_layered_model                none
% 1.62/0.96  --bmc1_ucm_max_lemma_size               10
% 1.62/0.96  
% 1.62/0.96  ------ AIG Options
% 1.62/0.96  
% 1.62/0.96  --aig_mode                              false
% 1.62/0.96  
% 1.62/0.96  ------ Instantiation Options
% 1.62/0.96  
% 1.62/0.96  --instantiation_flag                    true
% 1.62/0.96  --inst_sos_flag                         false
% 1.62/0.96  --inst_sos_phase                        true
% 1.62/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.62/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.62/0.96  --inst_lit_sel_side                     none
% 1.62/0.96  --inst_solver_per_active                1400
% 1.62/0.96  --inst_solver_calls_frac                1.
% 1.62/0.96  --inst_passive_queue_type               priority_queues
% 1.62/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.62/0.96  --inst_passive_queues_freq              [25;2]
% 1.62/0.96  --inst_dismatching                      true
% 1.62/0.96  --inst_eager_unprocessed_to_passive     true
% 1.62/0.96  --inst_prop_sim_given                   true
% 1.62/0.96  --inst_prop_sim_new                     false
% 1.62/0.96  --inst_subs_new                         false
% 1.62/0.96  --inst_eq_res_simp                      false
% 1.62/0.96  --inst_subs_given                       false
% 1.62/0.96  --inst_orphan_elimination               true
% 1.62/0.96  --inst_learning_loop_flag               true
% 1.62/0.96  --inst_learning_start                   3000
% 1.62/0.96  --inst_learning_factor                  2
% 1.62/0.96  --inst_start_prop_sim_after_learn       3
% 1.62/0.96  --inst_sel_renew                        solver
% 1.62/0.96  --inst_lit_activity_flag                true
% 1.62/0.96  --inst_restr_to_given                   false
% 1.62/0.96  --inst_activity_threshold               500
% 1.62/0.96  --inst_out_proof                        true
% 1.62/0.96  
% 1.62/0.96  ------ Resolution Options
% 1.62/0.96  
% 1.62/0.96  --resolution_flag                       false
% 1.62/0.96  --res_lit_sel                           adaptive
% 1.62/0.96  --res_lit_sel_side                      none
% 1.62/0.96  --res_ordering                          kbo
% 1.62/0.96  --res_to_prop_solver                    active
% 1.62/0.96  --res_prop_simpl_new                    false
% 1.62/0.96  --res_prop_simpl_given                  true
% 1.62/0.96  --res_passive_queue_type                priority_queues
% 1.62/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.62/0.96  --res_passive_queues_freq               [15;5]
% 1.62/0.96  --res_forward_subs                      full
% 1.62/0.96  --res_backward_subs                     full
% 1.62/0.96  --res_forward_subs_resolution           true
% 1.62/0.96  --res_backward_subs_resolution          true
% 1.62/0.96  --res_orphan_elimination                true
% 1.62/0.96  --res_time_limit                        2.
% 1.62/0.96  --res_out_proof                         true
% 1.62/0.96  
% 1.62/0.96  ------ Superposition Options
% 1.62/0.96  
% 1.62/0.96  --superposition_flag                    true
% 1.62/0.96  --sup_passive_queue_type                priority_queues
% 1.62/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.62/0.96  --sup_passive_queues_freq               [8;1;4]
% 1.62/0.96  --demod_completeness_check              fast
% 1.62/0.96  --demod_use_ground                      true
% 1.62/0.96  --sup_to_prop_solver                    passive
% 1.62/0.96  --sup_prop_simpl_new                    true
% 1.62/0.96  --sup_prop_simpl_given                  true
% 1.62/0.96  --sup_fun_splitting                     false
% 1.62/0.96  --sup_smt_interval                      50000
% 1.62/0.96  
% 1.62/0.96  ------ Superposition Simplification Setup
% 1.62/0.96  
% 1.62/0.96  --sup_indices_passive                   []
% 1.62/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.62/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.62/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.62/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 1.62/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.62/0.96  --sup_full_bw                           [BwDemod]
% 1.62/0.96  --sup_immed_triv                        [TrivRules]
% 1.62/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.62/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.62/0.96  --sup_immed_bw_main                     []
% 1.62/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.62/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 1.62/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.62/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.62/0.96  
% 1.62/0.96  ------ Combination Options
% 1.62/0.96  
% 1.62/0.96  --comb_res_mult                         3
% 1.62/0.96  --comb_sup_mult                         2
% 1.62/0.96  --comb_inst_mult                        10
% 1.62/0.96  
% 1.62/0.96  ------ Debug Options
% 1.62/0.96  
% 1.62/0.96  --dbg_backtrace                         false
% 1.62/0.96  --dbg_dump_prop_clauses                 false
% 1.62/0.96  --dbg_dump_prop_clauses_file            -
% 1.62/0.96  --dbg_out_stat                          false
% 1.62/0.96  
% 1.62/0.96  
% 1.62/0.96  
% 1.62/0.96  
% 1.62/0.96  ------ Proving...
% 1.62/0.96  
% 1.62/0.96  
% 1.62/0.96  % SZS status Theorem for theBenchmark.p
% 1.62/0.96  
% 1.62/0.96  % SZS output start CNFRefutation for theBenchmark.p
% 1.62/0.96  
% 1.62/0.96  fof(f9,axiom,(
% 1.62/0.96    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.62/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.62/0.96  
% 1.62/0.96  fof(f48,plain,(
% 1.62/0.96    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.62/0.96    inference(cnf_transformation,[],[f9])).
% 1.62/0.96  
% 1.62/0.96  fof(f12,axiom,(
% 1.62/0.96    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0))) & r1_tarski(X2,X1))))))),
% 1.62/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.62/0.96  
% 1.62/0.96  fof(f22,plain,(
% 1.62/0.96    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((? [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.62/0.96    inference(ennf_transformation,[],[f12])).
% 1.62/0.96  
% 1.62/0.96  fof(f23,plain,(
% 1.62/0.96    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.62/0.96    inference(flattening,[],[f22])).
% 1.62/0.96  
% 1.62/0.96  fof(f29,plain,(
% 1.62/0.96    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.62/0.96    inference(nnf_transformation,[],[f23])).
% 1.62/0.96  
% 1.62/0.96  fof(f30,plain,(
% 1.62/0.96    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (? [X5] : (k9_subset_1(u1_struct_0(X0),X1,X5) = X4 & v4_pre_topc(X5,X0) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.62/0.96    inference(rectify,[],[f29])).
% 1.62/0.96  
% 1.62/0.96  fof(f32,plain,(
% 1.62/0.96    ! [X4,X1,X0] : (? [X5] : (k9_subset_1(u1_struct_0(X0),X1,X5) = X4 & v4_pre_topc(X5,X0) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) => (k9_subset_1(u1_struct_0(X0),X1,sK1(X0,X1,X4)) = X4 & v4_pre_topc(sK1(X0,X1,X4),X0) & m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.62/0.96    introduced(choice_axiom,[])).
% 1.62/0.96  
% 1.62/0.96  fof(f31,plain,(
% 1.62/0.96    ! [X1,X0] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK0(X0,X1) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(sK0(X0,X1),X1) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.62/0.96    introduced(choice_axiom,[])).
% 1.62/0.96  
% 1.62/0.96  fof(f33,plain,(
% 1.62/0.96    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK0(X0,X1) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(sK0(X0,X1),X1) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : ((k9_subset_1(u1_struct_0(X0),X1,sK1(X0,X1,X4)) = X4 & v4_pre_topc(sK1(X0,X1,X4),X0) & m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.62/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f32,f31])).
% 1.62/0.96  
% 1.62/0.96  fof(f54,plain,(
% 1.62/0.96    ( ! [X0,X1] : (v2_tex_2(X1,X0) | r1_tarski(sK0(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.62/0.96    inference(cnf_transformation,[],[f33])).
% 1.62/0.96  
% 1.62/0.96  fof(f13,conjecture,(
% 1.62/0.96    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 1.62/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.62/0.96  
% 1.62/0.96  fof(f14,negated_conjecture,(
% 1.62/0.96    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 1.62/0.96    inference(negated_conjecture,[],[f13])).
% 1.62/0.96  
% 1.62/0.96  fof(f15,plain,(
% 1.62/0.96    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 1.62/0.96    inference(pure_predicate_removal,[],[f14])).
% 1.62/0.96  
% 1.62/0.96  fof(f24,plain,(
% 1.62/0.96    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.62/0.96    inference(ennf_transformation,[],[f15])).
% 1.62/0.96  
% 1.62/0.96  fof(f25,plain,(
% 1.62/0.96    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.62/0.96    inference(flattening,[],[f24])).
% 1.62/0.96  
% 1.62/0.96  fof(f35,plain,(
% 1.62/0.96    ( ! [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => (~v2_tex_2(sK3,X0) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(sK3))) )),
% 1.62/0.96    introduced(choice_axiom,[])).
% 1.62/0.96  
% 1.62/0.96  fof(f34,plain,(
% 1.62/0.96    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (~v2_tex_2(X1,sK2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) & v1_xboole_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2))),
% 1.62/0.96    introduced(choice_axiom,[])).
% 1.62/0.96  
% 1.62/0.96  fof(f36,plain,(
% 1.62/0.96    (~v2_tex_2(sK3,sK2) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) & v1_xboole_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2)),
% 1.62/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f25,f35,f34])).
% 1.62/0.96  
% 1.62/0.96  fof(f57,plain,(
% 1.62/0.96    l1_pre_topc(sK2)),
% 1.62/0.96    inference(cnf_transformation,[],[f36])).
% 1.62/0.96  
% 1.62/0.96  fof(f60,plain,(
% 1.62/0.96    ~v2_tex_2(sK3,sK2)),
% 1.62/0.96    inference(cnf_transformation,[],[f36])).
% 1.62/0.96  
% 1.62/0.96  fof(f2,axiom,(
% 1.62/0.96    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.62/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.62/0.96  
% 1.62/0.96  fof(f17,plain,(
% 1.62/0.96    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.62/0.96    inference(ennf_transformation,[],[f2])).
% 1.62/0.96  
% 1.62/0.96  fof(f38,plain,(
% 1.62/0.96    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 1.62/0.96    inference(cnf_transformation,[],[f17])).
% 1.62/0.96  
% 1.62/0.96  fof(f58,plain,(
% 1.62/0.96    v1_xboole_0(sK3)),
% 1.62/0.96    inference(cnf_transformation,[],[f36])).
% 1.62/0.96  
% 1.62/0.96  fof(f6,axiom,(
% 1.62/0.96    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 1.62/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.62/0.96  
% 1.62/0.96  fof(f18,plain,(
% 1.62/0.96    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 1.62/0.96    inference(ennf_transformation,[],[f6])).
% 1.62/0.96  
% 1.62/0.96  fof(f45,plain,(
% 1.62/0.96    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 1.62/0.96    inference(cnf_transformation,[],[f18])).
% 1.62/0.96  
% 1.62/0.96  fof(f8,axiom,(
% 1.62/0.96    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 1.62/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.62/0.96  
% 1.62/0.96  fof(f19,plain,(
% 1.62/0.96    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.62/0.96    inference(ennf_transformation,[],[f8])).
% 1.62/0.96  
% 1.62/0.96  fof(f47,plain,(
% 1.62/0.96    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 1.62/0.96    inference(cnf_transformation,[],[f19])).
% 1.62/0.96  
% 1.62/0.96  fof(f7,axiom,(
% 1.62/0.96    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 1.62/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.62/0.96  
% 1.62/0.96  fof(f46,plain,(
% 1.62/0.96    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 1.62/0.96    inference(cnf_transformation,[],[f7])).
% 1.62/0.96  
% 1.62/0.96  fof(f61,plain,(
% 1.62/0.96    ( ! [X2,X0,X1] : (k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 1.62/0.96    inference(definition_unfolding,[],[f47,f46])).
% 1.62/0.96  
% 1.62/0.96  fof(f5,axiom,(
% 1.62/0.96    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.62/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.62/0.96  
% 1.62/0.96  fof(f44,plain,(
% 1.62/0.96    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.62/0.96    inference(cnf_transformation,[],[f5])).
% 1.62/0.96  
% 1.62/0.96  fof(f55,plain,(
% 1.62/0.96    ( ! [X0,X3,X1] : (v2_tex_2(X1,X0) | k9_subset_1(u1_struct_0(X0),X1,X3) != sK0(X0,X1) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.62/0.96    inference(cnf_transformation,[],[f33])).
% 1.62/0.96  
% 1.62/0.96  fof(f1,axiom,(
% 1.62/0.96    v1_xboole_0(k1_xboole_0)),
% 1.62/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.62/0.96  
% 1.62/0.96  fof(f37,plain,(
% 1.62/0.96    v1_xboole_0(k1_xboole_0)),
% 1.62/0.96    inference(cnf_transformation,[],[f1])).
% 1.62/0.96  
% 1.62/0.96  fof(f11,axiom,(
% 1.62/0.96    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_xboole_0(X1) => v4_pre_topc(X1,X0))))),
% 1.62/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.62/0.96  
% 1.62/0.96  fof(f20,plain,(
% 1.62/0.96    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) | ~v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.62/0.96    inference(ennf_transformation,[],[f11])).
% 1.62/0.96  
% 1.62/0.96  fof(f21,plain,(
% 1.62/0.96    ! [X0] : (! [X1] : (v4_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.62/0.96    inference(flattening,[],[f20])).
% 1.62/0.96  
% 1.62/0.96  fof(f49,plain,(
% 1.62/0.96    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.62/0.96    inference(cnf_transformation,[],[f21])).
% 1.62/0.96  
% 1.62/0.96  fof(f56,plain,(
% 1.62/0.96    v2_pre_topc(sK2)),
% 1.62/0.96    inference(cnf_transformation,[],[f36])).
% 1.62/0.96  
% 1.62/0.96  cnf(c_10,plain,
% 1.62/0.96      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 1.62/0.96      inference(cnf_transformation,[],[f48]) ).
% 1.62/0.96  
% 1.62/0.96  cnf(c_1895,plain,
% 1.62/0.96      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 1.62/0.96      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 1.62/0.96  
% 1.62/0.96  cnf(c_13,plain,
% 1.62/0.96      ( v2_tex_2(X0,X1)
% 1.62/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.62/0.96      | r1_tarski(sK0(X1,X0),X0)
% 1.62/0.96      | ~ l1_pre_topc(X1) ),
% 1.62/0.96      inference(cnf_transformation,[],[f54]) ).
% 1.62/0.96  
% 1.62/0.96  cnf(c_21,negated_conjecture,
% 1.62/0.96      ( l1_pre_topc(sK2) ),
% 1.62/0.96      inference(cnf_transformation,[],[f57]) ).
% 1.62/0.96  
% 1.62/0.96  cnf(c_508,plain,
% 1.62/0.96      ( v2_tex_2(X0,X1)
% 1.62/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.62/0.96      | r1_tarski(sK0(X1,X0),X0)
% 1.62/0.96      | sK2 != X1 ),
% 1.62/0.96      inference(resolution_lifted,[status(thm)],[c_13,c_21]) ).
% 1.62/0.96  
% 1.62/0.96  cnf(c_509,plain,
% 1.62/0.96      ( v2_tex_2(X0,sK2)
% 1.62/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.62/0.96      | r1_tarski(sK0(sK2,X0),X0) ),
% 1.62/0.96      inference(unflattening,[status(thm)],[c_508]) ).
% 1.62/0.96  
% 1.62/0.96  cnf(c_1886,plain,
% 1.62/0.96      ( v2_tex_2(X0,sK2) = iProver_top
% 1.62/0.96      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.62/0.96      | r1_tarski(sK0(sK2,X0),X0) = iProver_top ),
% 1.62/0.96      inference(predicate_to_equality,[status(thm)],[c_509]) ).
% 1.62/0.96  
% 1.62/0.96  cnf(c_2382,plain,
% 1.62/0.96      ( v2_tex_2(k1_xboole_0,sK2) = iProver_top
% 1.62/0.96      | r1_tarski(sK0(sK2,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 1.62/0.96      inference(superposition,[status(thm)],[c_1895,c_1886]) ).
% 1.62/0.96  
% 1.62/0.96  cnf(c_510,plain,
% 1.62/0.96      ( v2_tex_2(X0,sK2) = iProver_top
% 1.62/0.96      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.62/0.96      | r1_tarski(sK0(sK2,X0),X0) = iProver_top ),
% 1.62/0.96      inference(predicate_to_equality,[status(thm)],[c_509]) ).
% 1.62/0.96  
% 1.62/0.96  cnf(c_512,plain,
% 1.62/0.96      ( v2_tex_2(k1_xboole_0,sK2) = iProver_top
% 1.62/0.96      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.62/0.96      | r1_tarski(sK0(sK2,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 1.62/0.96      inference(instantiation,[status(thm)],[c_510]) ).
% 1.62/0.96  
% 1.62/0.96  cnf(c_18,negated_conjecture,
% 1.62/0.96      ( ~ v2_tex_2(sK3,sK2) ),
% 1.62/0.96      inference(cnf_transformation,[],[f60]) ).
% 1.62/0.96  
% 1.62/0.96  cnf(c_1894,plain,
% 1.62/0.96      ( v2_tex_2(sK3,sK2) != iProver_top ),
% 1.62/0.96      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 1.62/0.96  
% 1.62/0.96  cnf(c_1,plain,
% 1.62/0.96      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 1.62/0.96      inference(cnf_transformation,[],[f38]) ).
% 1.62/0.96  
% 1.62/0.96  cnf(c_20,negated_conjecture,
% 1.62/0.96      ( v1_xboole_0(sK3) ),
% 1.62/0.96      inference(cnf_transformation,[],[f58]) ).
% 1.62/0.96  
% 1.62/0.96  cnf(c_330,plain,
% 1.62/0.96      ( sK3 != X0 | k1_xboole_0 = X0 ),
% 1.62/0.96      inference(resolution_lifted,[status(thm)],[c_1,c_20]) ).
% 1.62/0.96  
% 1.62/0.96  cnf(c_331,plain,
% 1.62/0.96      ( k1_xboole_0 = sK3 ),
% 1.62/0.96      inference(unflattening,[status(thm)],[c_330]) ).
% 1.62/0.96  
% 1.62/0.96  cnf(c_1911,plain,
% 1.62/0.96      ( v2_tex_2(k1_xboole_0,sK2) != iProver_top ),
% 1.62/0.96      inference(light_normalisation,[status(thm)],[c_1894,c_331]) ).
% 1.62/0.96  
% 1.62/0.96  cnf(c_2039,plain,
% 1.62/0.96      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 1.62/0.96      inference(instantiation,[status(thm)],[c_10]) ).
% 1.62/0.96  
% 1.62/0.96  cnf(c_2043,plain,
% 1.62/0.96      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 1.62/0.96      inference(predicate_to_equality,[status(thm)],[c_2039]) ).
% 1.62/0.96  
% 1.62/0.96  cnf(c_2592,plain,
% 1.62/0.96      ( r1_tarski(sK0(sK2,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 1.62/0.96      inference(global_propositional_subsumption,
% 1.62/0.96                [status(thm)],
% 1.62/0.96                [c_2382,c_512,c_1911,c_2043]) ).
% 1.62/0.96  
% 1.62/0.96  cnf(c_8,plain,
% 1.62/0.96      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 1.62/0.96      inference(cnf_transformation,[],[f45]) ).
% 1.62/0.96  
% 1.62/0.96  cnf(c_1897,plain,
% 1.62/0.96      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 1.62/0.96      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 1.62/0.96  
% 1.62/0.96  cnf(c_2597,plain,
% 1.62/0.96      ( sK0(sK2,k1_xboole_0) = k1_xboole_0 ),
% 1.62/0.96      inference(superposition,[status(thm)],[c_2592,c_1897]) ).
% 1.62/0.96  
% 1.62/0.96  cnf(c_9,plain,
% 1.62/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.62/0.96      | k4_xboole_0(X2,k4_xboole_0(X2,X0)) = k9_subset_1(X1,X2,X0) ),
% 1.62/0.96      inference(cnf_transformation,[],[f61]) ).
% 1.62/0.96  
% 1.62/0.96  cnf(c_1896,plain,
% 1.62/0.96      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k9_subset_1(X2,X0,X1)
% 1.62/0.96      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 1.62/0.96      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 1.62/0.96  
% 1.62/0.96  cnf(c_2959,plain,
% 1.62/0.96      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k9_subset_1(X1,X0,k1_xboole_0) ),
% 1.62/0.96      inference(superposition,[status(thm)],[c_1895,c_1896]) ).
% 1.62/0.96  
% 1.62/0.96  cnf(c_7,plain,
% 1.62/0.96      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 1.62/0.96      inference(cnf_transformation,[],[f44]) ).
% 1.62/0.96  
% 1.62/0.96  cnf(c_2979,plain,
% 1.62/0.96      ( k9_subset_1(X0,X1,k1_xboole_0) = k4_xboole_0(X1,X1) ),
% 1.62/0.96      inference(light_normalisation,[status(thm)],[c_2959,c_7]) ).
% 1.62/0.96  
% 1.62/0.96  cnf(c_12,plain,
% 1.62/0.96      ( v2_tex_2(X0,X1)
% 1.62/0.96      | ~ v4_pre_topc(X2,X1)
% 1.62/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.62/0.96      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.62/0.96      | ~ l1_pre_topc(X1)
% 1.62/0.96      | k9_subset_1(u1_struct_0(X1),X0,X2) != sK0(X1,X0) ),
% 1.62/0.96      inference(cnf_transformation,[],[f55]) ).
% 1.62/0.96  
% 1.62/0.96  cnf(c_523,plain,
% 1.62/0.96      ( v2_tex_2(X0,X1)
% 1.62/0.96      | ~ v4_pre_topc(X2,X1)
% 1.62/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.62/0.96      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.62/0.96      | k9_subset_1(u1_struct_0(X1),X0,X2) != sK0(X1,X0)
% 1.62/0.96      | sK2 != X1 ),
% 1.62/0.96      inference(resolution_lifted,[status(thm)],[c_12,c_21]) ).
% 1.62/0.96  
% 1.62/0.96  cnf(c_524,plain,
% 1.62/0.96      ( v2_tex_2(X0,sK2)
% 1.62/0.96      | ~ v4_pre_topc(X1,sK2)
% 1.62/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.62/0.96      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.62/0.96      | k9_subset_1(u1_struct_0(sK2),X0,X1) != sK0(sK2,X0) ),
% 1.62/0.96      inference(unflattening,[status(thm)],[c_523]) ).
% 1.62/0.96  
% 1.62/0.96  cnf(c_1885,plain,
% 1.62/0.96      ( k9_subset_1(u1_struct_0(sK2),X0,X1) != sK0(sK2,X0)
% 1.62/0.96      | v2_tex_2(X0,sK2) = iProver_top
% 1.62/0.96      | v4_pre_topc(X1,sK2) != iProver_top
% 1.62/0.96      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.62/0.96      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 1.62/0.96      inference(predicate_to_equality,[status(thm)],[c_524]) ).
% 1.62/0.96  
% 1.62/0.96  cnf(c_3093,plain,
% 1.62/0.96      ( k4_xboole_0(X0,X0) != sK0(sK2,X0)
% 1.62/0.96      | v2_tex_2(X0,sK2) = iProver_top
% 1.62/0.96      | v4_pre_topc(k1_xboole_0,sK2) != iProver_top
% 1.62/0.96      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.62/0.96      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 1.62/0.96      inference(superposition,[status(thm)],[c_2979,c_1885]) ).
% 1.62/0.96  
% 1.62/0.96  cnf(c_0,plain,
% 1.62/0.96      ( v1_xboole_0(k1_xboole_0) ),
% 1.62/0.96      inference(cnf_transformation,[],[f37]) ).
% 1.62/0.96  
% 1.62/0.96  cnf(c_11,plain,
% 1.62/0.96      ( v4_pre_topc(X0,X1)
% 1.62/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.62/0.96      | ~ v2_pre_topc(X1)
% 1.62/0.96      | ~ l1_pre_topc(X1)
% 1.62/0.96      | ~ v1_xboole_0(X0) ),
% 1.62/0.96      inference(cnf_transformation,[],[f49]) ).
% 1.62/0.96  
% 1.62/0.96  cnf(c_22,negated_conjecture,
% 1.62/0.96      ( v2_pre_topc(sK2) ),
% 1.62/0.96      inference(cnf_transformation,[],[f56]) ).
% 1.62/0.96  
% 1.62/0.96  cnf(c_282,plain,
% 1.62/0.96      ( v4_pre_topc(X0,X1)
% 1.62/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.62/0.96      | ~ l1_pre_topc(X1)
% 1.62/0.96      | ~ v1_xboole_0(X0)
% 1.62/0.96      | sK2 != X1 ),
% 1.62/0.96      inference(resolution_lifted,[status(thm)],[c_11,c_22]) ).
% 1.62/0.96  
% 1.62/0.96  cnf(c_283,plain,
% 1.62/0.96      ( v4_pre_topc(X0,sK2)
% 1.62/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.62/0.96      | ~ l1_pre_topc(sK2)
% 1.62/0.96      | ~ v1_xboole_0(X0) ),
% 1.62/0.96      inference(unflattening,[status(thm)],[c_282]) ).
% 1.62/0.96  
% 1.62/0.96  cnf(c_287,plain,
% 1.62/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.62/0.96      | v4_pre_topc(X0,sK2)
% 1.62/0.96      | ~ v1_xboole_0(X0) ),
% 1.62/0.96      inference(global_propositional_subsumption,
% 1.62/0.96                [status(thm)],
% 1.62/0.96                [c_283,c_21]) ).
% 1.62/0.96  
% 1.62/0.96  cnf(c_288,plain,
% 1.62/0.96      ( v4_pre_topc(X0,sK2)
% 1.62/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.62/0.96      | ~ v1_xboole_0(X0) ),
% 1.62/0.96      inference(renaming,[status(thm)],[c_287]) ).
% 1.62/0.96  
% 1.62/0.96  cnf(c_307,plain,
% 1.62/0.96      ( v4_pre_topc(X0,sK2)
% 1.62/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.62/0.96      | k1_xboole_0 != X0 ),
% 1.62/0.96      inference(resolution_lifted,[status(thm)],[c_0,c_288]) ).
% 1.62/0.96  
% 1.62/0.96  cnf(c_308,plain,
% 1.62/0.96      ( v4_pre_topc(k1_xboole_0,sK2)
% 1.62/0.96      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 1.62/0.96      inference(unflattening,[status(thm)],[c_307]) ).
% 1.62/0.96  
% 1.62/0.96  cnf(c_314,plain,
% 1.62/0.96      ( v4_pre_topc(k1_xboole_0,sK2) ),
% 1.62/0.96      inference(forward_subsumption_resolution,
% 1.62/0.96                [status(thm)],
% 1.62/0.96                [c_308,c_10]) ).
% 1.62/0.96  
% 1.62/0.96  cnf(c_316,plain,
% 1.62/0.96      ( v4_pre_topc(k1_xboole_0,sK2) = iProver_top ),
% 1.62/0.96      inference(predicate_to_equality,[status(thm)],[c_314]) ).
% 1.62/0.96  
% 1.62/0.96  cnf(c_3372,plain,
% 1.62/0.96      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.62/0.96      | k4_xboole_0(X0,X0) != sK0(sK2,X0)
% 1.62/0.96      | v2_tex_2(X0,sK2) = iProver_top ),
% 1.62/0.96      inference(global_propositional_subsumption,
% 1.62/0.96                [status(thm)],
% 1.62/0.96                [c_3093,c_316,c_2043]) ).
% 1.62/0.96  
% 1.62/0.96  cnf(c_3373,plain,
% 1.62/0.96      ( k4_xboole_0(X0,X0) != sK0(sK2,X0)
% 1.62/0.96      | v2_tex_2(X0,sK2) = iProver_top
% 1.62/0.96      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 1.62/0.96      inference(renaming,[status(thm)],[c_3372]) ).
% 1.62/0.96  
% 1.62/0.96  cnf(c_3382,plain,
% 1.62/0.96      ( k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 1.62/0.96      | v2_tex_2(k1_xboole_0,sK2) = iProver_top
% 1.62/0.96      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 1.62/0.96      inference(superposition,[status(thm)],[c_2597,c_3373]) ).
% 1.62/0.96  
% 1.62/0.96  cnf(c_3386,plain,
% 1.62/0.96      ( k1_xboole_0 != k1_xboole_0
% 1.62/0.96      | v2_tex_2(k1_xboole_0,sK2) = iProver_top
% 1.62/0.96      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 1.62/0.96      inference(demodulation,[status(thm)],[c_3382,c_7]) ).
% 1.62/0.96  
% 1.62/0.96  cnf(c_3387,plain,
% 1.62/0.96      ( v2_tex_2(k1_xboole_0,sK2) = iProver_top
% 1.62/0.96      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 1.62/0.96      inference(equality_resolution_simp,[status(thm)],[c_3386]) ).
% 1.62/0.96  
% 1.62/0.96  cnf(contradiction,plain,
% 1.62/0.96      ( $false ),
% 1.62/0.96      inference(minisat,[status(thm)],[c_3387,c_2043,c_1911]) ).
% 1.62/0.96  
% 1.62/0.96  
% 1.62/0.96  % SZS output end CNFRefutation for theBenchmark.p
% 1.62/0.96  
% 1.62/0.96  ------                               Statistics
% 1.62/0.96  
% 1.62/0.96  ------ General
% 1.62/0.96  
% 1.62/0.96  abstr_ref_over_cycles:                  0
% 1.62/0.96  abstr_ref_under_cycles:                 0
% 1.62/0.96  gc_basic_clause_elim:                   0
% 1.62/0.96  forced_gc_time:                         0
% 1.62/0.96  parsing_time:                           0.009
% 1.62/0.96  unif_index_cands_time:                  0.
% 1.62/0.96  unif_index_add_time:                    0.
% 1.62/0.96  orderings_time:                         0.
% 1.62/0.96  out_proof_time:                         0.013
% 1.62/0.96  total_time:                             0.122
% 1.62/0.96  num_of_symbols:                         47
% 1.62/0.96  num_of_terms:                           2088
% 1.62/0.96  
% 1.62/0.96  ------ Preprocessing
% 1.62/0.96  
% 1.62/0.96  num_of_splits:                          0
% 1.62/0.96  num_of_split_atoms:                     0
% 1.62/0.96  num_of_reused_defs:                     0
% 1.62/0.96  num_eq_ax_congr_red:                    18
% 1.62/0.96  num_of_sem_filtered_clauses:            1
% 1.62/0.96  num_of_subtypes:                        0
% 1.62/0.96  monotx_restored_types:                  0
% 1.62/0.96  sat_num_of_epr_types:                   0
% 1.62/0.96  sat_num_of_non_cyclic_types:            0
% 1.62/0.96  sat_guarded_non_collapsed_types:        0
% 1.62/0.96  num_pure_diseq_elim:                    0
% 1.62/0.96  simp_replaced_by:                       0
% 1.62/0.96  res_preprocessed:                       104
% 1.62/0.96  prep_upred:                             0
% 1.62/0.96  prep_unflattend:                        29
% 1.62/0.96  smt_new_axioms:                         0
% 1.62/0.96  pred_elim_cands:                        4
% 1.62/0.96  pred_elim:                              3
% 1.62/0.96  pred_elim_cl:                           3
% 1.62/0.96  pred_elim_cycles:                       8
% 1.62/0.96  merged_defs:                            8
% 1.62/0.96  merged_defs_ncl:                        0
% 1.62/0.96  bin_hyper_res:                          8
% 1.62/0.96  prep_cycles:                            4
% 1.62/0.96  pred_elim_time:                         0.018
% 1.62/0.96  splitting_time:                         0.
% 1.62/0.96  sem_filter_time:                        0.
% 1.62/0.96  monotx_time:                            0.
% 1.62/0.96  subtype_inf_time:                       0.
% 1.62/0.96  
% 1.62/0.96  ------ Problem properties
% 1.62/0.96  
% 1.62/0.96  clauses:                                19
% 1.62/0.96  conjectures:                            2
% 1.62/0.96  epr:                                    7
% 1.62/0.96  horn:                                   17
% 1.62/0.96  ground:                                 5
% 1.62/0.96  unary:                                  8
% 1.62/0.96  binary:                                 4
% 1.62/0.96  lits:                                   45
% 1.62/0.96  lits_eq:                                9
% 1.62/0.96  fd_pure:                                0
% 1.62/0.96  fd_pseudo:                              0
% 1.62/0.96  fd_cond:                                1
% 1.62/0.96  fd_pseudo_cond:                         1
% 1.62/0.96  ac_symbols:                             0
% 1.62/0.96  
% 1.62/0.96  ------ Propositional Solver
% 1.62/0.96  
% 1.62/0.96  prop_solver_calls:                      25
% 1.62/0.96  prop_fast_solver_calls:                 862
% 1.62/0.96  smt_solver_calls:                       0
% 1.62/0.96  smt_fast_solver_calls:                  0
% 1.62/0.96  prop_num_of_clauses:                    801
% 1.62/0.96  prop_preprocess_simplified:             3698
% 1.62/0.96  prop_fo_subsumed:                       19
% 1.62/0.96  prop_solver_time:                       0.
% 1.62/0.96  smt_solver_time:                        0.
% 1.62/0.96  smt_fast_solver_time:                   0.
% 1.62/0.96  prop_fast_solver_time:                  0.
% 1.62/0.96  prop_unsat_core_time:                   0.
% 1.62/0.96  
% 1.62/0.96  ------ QBF
% 1.62/0.96  
% 1.62/0.96  qbf_q_res:                              0
% 1.62/0.96  qbf_num_tautologies:                    0
% 1.62/0.96  qbf_prep_cycles:                        0
% 1.62/0.96  
% 1.62/0.96  ------ BMC1
% 1.62/0.96  
% 1.62/0.96  bmc1_current_bound:                     -1
% 1.62/0.96  bmc1_last_solved_bound:                 -1
% 1.62/0.96  bmc1_unsat_core_size:                   -1
% 1.62/0.96  bmc1_unsat_core_parents_size:           -1
% 1.62/0.96  bmc1_merge_next_fun:                    0
% 1.62/0.96  bmc1_unsat_core_clauses_time:           0.
% 1.62/0.96  
% 1.62/0.96  ------ Instantiation
% 1.62/0.96  
% 1.62/0.96  inst_num_of_clauses:                    231
% 1.62/0.96  inst_num_in_passive:                    13
% 1.62/0.96  inst_num_in_active:                     133
% 1.62/0.96  inst_num_in_unprocessed:                86
% 1.62/0.96  inst_num_of_loops:                      140
% 1.62/0.96  inst_num_of_learning_restarts:          0
% 1.62/0.96  inst_num_moves_active_passive:          5
% 1.62/0.96  inst_lit_activity:                      0
% 1.62/0.96  inst_lit_activity_moves:                0
% 1.62/0.96  inst_num_tautologies:                   0
% 1.62/0.96  inst_num_prop_implied:                  0
% 1.62/0.96  inst_num_existing_simplified:           0
% 1.62/0.96  inst_num_eq_res_simplified:             0
% 1.62/0.96  inst_num_child_elim:                    0
% 1.62/0.96  inst_num_of_dismatching_blockings:      40
% 1.62/0.96  inst_num_of_non_proper_insts:           245
% 1.62/0.96  inst_num_of_duplicates:                 0
% 1.62/0.96  inst_inst_num_from_inst_to_res:         0
% 1.62/0.96  inst_dismatching_checking_time:         0.
% 1.62/0.96  
% 1.62/0.96  ------ Resolution
% 1.62/0.96  
% 1.62/0.96  res_num_of_clauses:                     0
% 1.62/0.96  res_num_in_passive:                     0
% 1.62/0.96  res_num_in_active:                      0
% 1.62/0.96  res_num_of_loops:                       108
% 1.62/0.96  res_forward_subset_subsumed:            13
% 1.62/0.96  res_backward_subset_subsumed:           2
% 1.62/0.96  res_forward_subsumed:                   0
% 1.62/0.96  res_backward_subsumed:                  0
% 1.62/0.96  res_forward_subsumption_resolution:     4
% 1.62/0.96  res_backward_subsumption_resolution:    0
% 1.62/0.96  res_clause_to_clause_subsumption:       253
% 1.62/0.96  res_orphan_elimination:                 0
% 1.62/0.96  res_tautology_del:                      41
% 1.62/0.96  res_num_eq_res_simplified:              0
% 1.62/0.96  res_num_sel_changes:                    0
% 1.62/0.96  res_moves_from_active_to_pass:          0
% 1.62/0.96  
% 1.62/0.96  ------ Superposition
% 1.62/0.96  
% 1.62/0.96  sup_time_total:                         0.
% 1.62/0.96  sup_time_generating:                    0.
% 1.62/0.96  sup_time_sim_full:                      0.
% 1.62/0.96  sup_time_sim_immed:                     0.
% 1.62/0.96  
% 1.62/0.96  sup_num_of_clauses:                     38
% 1.62/0.96  sup_num_in_active:                      26
% 1.62/0.96  sup_num_in_passive:                     12
% 1.62/0.96  sup_num_of_loops:                       26
% 1.62/0.96  sup_fw_superposition:                   18
% 1.62/0.96  sup_bw_superposition:                   14
% 1.62/0.96  sup_immediate_simplified:               9
% 1.62/0.96  sup_given_eliminated:                   0
% 1.62/0.96  comparisons_done:                       0
% 1.62/0.96  comparisons_avoided:                    0
% 1.62/0.96  
% 1.62/0.96  ------ Simplifications
% 1.62/0.96  
% 1.62/0.96  
% 1.62/0.96  sim_fw_subset_subsumed:                 1
% 1.62/0.96  sim_bw_subset_subsumed:                 0
% 1.62/0.96  sim_fw_subsumed:                        5
% 1.62/0.96  sim_bw_subsumed:                        0
% 1.62/0.96  sim_fw_subsumption_res:                 0
% 1.62/0.96  sim_bw_subsumption_res:                 0
% 1.62/0.96  sim_tautology_del:                      4
% 1.62/0.96  sim_eq_tautology_del:                   0
% 1.62/0.96  sim_eq_res_simp:                        1
% 1.62/0.96  sim_fw_demodulated:                     1
% 1.62/0.96  sim_bw_demodulated:                     1
% 1.62/0.96  sim_light_normalised:                   8
% 1.62/0.96  sim_joinable_taut:                      0
% 1.62/0.96  sim_joinable_simp:                      0
% 1.62/0.96  sim_ac_normalised:                      0
% 1.62/0.96  sim_smt_subsumption:                    0
% 1.62/0.96  
%------------------------------------------------------------------------------
