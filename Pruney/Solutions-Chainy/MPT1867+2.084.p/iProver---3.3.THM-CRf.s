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
% DateTime   : Thu Dec  3 12:26:22 EST 2020

% Result     : Theorem 2.05s
% Output     : CNFRefutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 254 expanded)
%              Number of clauses        :   50 (  75 expanded)
%              Number of leaves         :   14 (  61 expanded)
%              Depth                    :   17
%              Number of atoms          :  307 (1112 expanded)
%              Number of equality atoms :   88 ( 132 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f5,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f43,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ? [X1] :
          ( v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( v4_pre_topc(sK0(X0),X0)
        & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ( v4_pre_topc(sK0(X0),X0)
        & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f28])).

fof(f48,plain,(
    ! [X0] :
      ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

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

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
     => ( ~ v2_tex_2(sK4,X0)
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0)))
        & v1_xboole_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v2_tex_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ v2_tex_2(X1,sK3)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(sK3)
      & v2_pre_topc(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ~ v2_tex_2(sK4,sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    & v1_xboole_0(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f26,f36,f35])).

fof(f56,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f57,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f46,f44])).

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
    inference(ennf_transformation,[],[f12])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

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
    inference(nnf_transformation,[],[f24])).

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f33,plain,(
    ! [X4,X1,X0] :
      ( ? [X5] :
          ( k9_subset_1(u1_struct_0(X0),X1,X5) = X4
          & v4_pre_topc(X5,X0)
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X0),X1,sK2(X0,X1,X4)) = X4
        & v4_pre_topc(sK2(X0,X1,X4),X0)
        & m1_subset_1(sK2(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
              | ~ v4_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ! [X3] :
            ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK1(X0,X1)
            | ~ v4_pre_topc(X3,X0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & r1_tarski(sK1(X0,X1),X1)
        & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ( ! [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK1(X0,X1)
                    | ~ v4_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & r1_tarski(sK1(X0,X1),X1)
                & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X4] :
                  ( ( k9_subset_1(u1_struct_0(X0),X1,sK2(X0,X1,X4)) = X4
                    & v4_pre_topc(sK2(X0,X1,X4),X0)
                    & m1_subset_1(sK2(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r1_tarski(X4,X1)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f31,f33,f32])).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( v2_tex_2(X1,X0)
      | k9_subset_1(u1_struct_0(X0),X1,X3) != sK1(X0,X1)
      | ~ v4_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f49,plain,(
    ! [X0] :
      ( v4_pre_topc(sK0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f9,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | r1_tarski(sK1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f60,plain,(
    ~ v2_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f38,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f58,plain,(
    v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_3,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_2218,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_2217,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3354,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2218,c_2217])).

cnf(c_10,plain,
    ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_21,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_288,plain,
    ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_21])).

cnf(c_289,plain,
    ( m1_subset_1(sK0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_288])).

cnf(c_20,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_291,plain,
    ( m1_subset_1(sK0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_289,c_20])).

cnf(c_2211,plain,
    ( m1_subset_1(sK0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_291])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k4_xboole_0(X2,k4_xboole_0(X2,X0)) = k9_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2215,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k9_subset_1(X2,X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3206,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,sK0(sK3))) = k9_subset_1(u1_struct_0(sK3),X0,sK0(sK3)) ),
    inference(superposition,[status(thm)],[c_2211,c_2215])).

cnf(c_11,plain,
    ( v2_tex_2(X0,X1)
    | ~ v4_pre_topc(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),X0,X2) != sK1(X1,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_470,plain,
    ( v2_tex_2(X0,X1)
    | ~ v4_pre_topc(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k9_subset_1(u1_struct_0(X1),X0,X2) != sK1(X1,X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_20])).

cnf(c_471,plain,
    ( v2_tex_2(X0,sK3)
    | ~ v4_pre_topc(X1,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | k9_subset_1(u1_struct_0(sK3),X0,X1) != sK1(sK3,X0) ),
    inference(unflattening,[status(thm)],[c_470])).

cnf(c_2204,plain,
    ( k9_subset_1(u1_struct_0(sK3),X0,X1) != sK1(sK3,X0)
    | v2_tex_2(X0,sK3) = iProver_top
    | v4_pre_topc(X1,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_471])).

cnf(c_3559,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,sK0(sK3))) != sK1(sK3,X0)
    | v2_tex_2(X0,sK3) = iProver_top
    | v4_pre_topc(sK0(sK3),sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3206,c_2204])).

cnf(c_23,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_290,plain,
    ( m1_subset_1(sK0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_289])).

cnf(c_9,plain,
    ( v4_pre_topc(sK0(X0),X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_299,plain,
    ( v4_pre_topc(sK0(X0),X0)
    | ~ l1_pre_topc(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_21])).

cnf(c_300,plain,
    ( v4_pre_topc(sK0(sK3),sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_299])).

cnf(c_301,plain,
    ( v4_pre_topc(sK0(sK3),sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_300])).

cnf(c_3672,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | k4_xboole_0(X0,k4_xboole_0(X0,sK0(sK3))) != sK1(sK3,X0)
    | v2_tex_2(X0,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3559,c_23,c_290,c_301])).

cnf(c_3673,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,sK0(sK3))) != sK1(sK3,X0)
    | v2_tex_2(X0,sK3) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3672])).

cnf(c_4033,plain,
    ( sK1(sK3,k1_xboole_0) != k1_xboole_0
    | v2_tex_2(k1_xboole_0,sK3) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3354,c_3673])).

cnf(c_8,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_2214,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_12,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(sK1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_455,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(sK1(X1,X0),X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_20])).

cnf(c_456,plain,
    ( v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | r1_tarski(sK1(sK3,X0),X0) ),
    inference(unflattening,[status(thm)],[c_455])).

cnf(c_2205,plain,
    ( v2_tex_2(X0,sK3) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r1_tarski(sK1(sK3,X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_456])).

cnf(c_2734,plain,
    ( v2_tex_2(k1_xboole_0,sK3) = iProver_top
    | r1_tarski(sK1(sK3,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2214,c_2205])).

cnf(c_457,plain,
    ( v2_tex_2(X0,sK3) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r1_tarski(sK1(sK3,X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_456])).

cnf(c_459,plain,
    ( v2_tex_2(k1_xboole_0,sK3) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r1_tarski(sK1(sK3,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_457])).

cnf(c_17,negated_conjecture,
    ( ~ v2_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2213,plain,
    ( v2_tex_2(sK4,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_0,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_19,negated_conjecture,
    ( v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_282,plain,
    ( sK4 != X0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_19])).

cnf(c_283,plain,
    ( k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_282])).

cnf(c_2227,plain,
    ( v2_tex_2(k1_xboole_0,sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2213,c_283])).

cnf(c_2364,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2367,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2364])).

cnf(c_3135,plain,
    ( r1_tarski(sK1(sK3,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2734,c_459,c_2227,c_2367])).

cnf(c_3355,plain,
    ( sK1(sK3,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3135,c_2217])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4033,c_3355,c_2367,c_2227])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:15:11 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  % Running in FOF mode
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
% 2.05/1.00  EPR                                     3
% 2.05/1.00  Horn                                    17
% 2.05/1.00  unary                                   8
% 2.05/1.00  binary                                  5
% 2.05/1.00  lits                                    44
% 2.05/1.00  lits eq                                 9
% 2.05/1.00  fd_pure                                 0
% 2.05/1.00  fd_pseudo                               0
% 2.05/1.00  fd_cond                                 1
% 2.05/1.00  fd_pseudo_cond                          0
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
% 2.05/1.00  fof(f3,axiom,(
% 2.05/1.00    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.05/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/1.00  
% 2.05/1.00  fof(f41,plain,(
% 2.05/1.00    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.05/1.00    inference(cnf_transformation,[],[f3])).
% 2.05/1.00  
% 2.05/1.00  fof(f5,axiom,(
% 2.05/1.00    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 2.05/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/1.00  
% 2.05/1.00  fof(f18,plain,(
% 2.05/1.00    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 2.05/1.00    inference(ennf_transformation,[],[f5])).
% 2.05/1.00  
% 2.05/1.00  fof(f43,plain,(
% 2.05/1.00    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 2.05/1.00    inference(cnf_transformation,[],[f18])).
% 2.05/1.00  
% 2.05/1.00  fof(f11,axiom,(
% 2.05/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ? [X1] : (v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.05/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/1.00  
% 2.05/1.00  fof(f21,plain,(
% 2.05/1.00    ! [X0] : (? [X1] : (v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.05/1.00    inference(ennf_transformation,[],[f11])).
% 2.05/1.00  
% 2.05/1.00  fof(f22,plain,(
% 2.05/1.00    ! [X0] : (? [X1] : (v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.05/1.00    inference(flattening,[],[f21])).
% 2.05/1.00  
% 2.05/1.00  fof(f28,plain,(
% 2.05/1.00    ! [X0] : (? [X1] : (v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (v4_pre_topc(sK0(X0),X0) & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.05/1.00    introduced(choice_axiom,[])).
% 2.05/1.00  
% 2.05/1.00  fof(f29,plain,(
% 2.05/1.00    ! [X0] : ((v4_pre_topc(sK0(X0),X0) & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.05/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f28])).
% 2.05/1.00  
% 2.05/1.00  fof(f48,plain,(
% 2.05/1.00    ( ! [X0] : (m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.05/1.00    inference(cnf_transformation,[],[f29])).
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
% 2.05/1.00  fof(f25,plain,(
% 2.05/1.00    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.05/1.00    inference(ennf_transformation,[],[f15])).
% 2.05/1.00  
% 2.05/1.00  fof(f26,plain,(
% 2.05/1.00    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.05/1.00    inference(flattening,[],[f25])).
% 2.05/1.00  
% 2.05/1.00  fof(f36,plain,(
% 2.05/1.00    ( ! [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => (~v2_tex_2(sK4,X0) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(sK4))) )),
% 2.05/1.00    introduced(choice_axiom,[])).
% 2.05/1.00  
% 2.05/1.00  fof(f35,plain,(
% 2.05/1.00    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (~v2_tex_2(X1,sK3) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) & v1_xboole_0(X1)) & l1_pre_topc(sK3) & v2_pre_topc(sK3))),
% 2.05/1.00    introduced(choice_axiom,[])).
% 2.05/1.00  
% 2.05/1.00  fof(f37,plain,(
% 2.05/1.00    (~v2_tex_2(sK4,sK3) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) & v1_xboole_0(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3)),
% 2.05/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f26,f36,f35])).
% 2.05/1.00  
% 2.05/1.00  fof(f56,plain,(
% 2.05/1.00    v2_pre_topc(sK3)),
% 2.05/1.00    inference(cnf_transformation,[],[f37])).
% 2.05/1.00  
% 2.05/1.00  fof(f57,plain,(
% 2.05/1.00    l1_pre_topc(sK3)),
% 2.05/1.00    inference(cnf_transformation,[],[f37])).
% 2.05/1.00  
% 2.05/1.00  fof(f8,axiom,(
% 2.05/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 2.05/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/1.00  
% 2.05/1.00  fof(f20,plain,(
% 2.05/1.00    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 2.05/1.00    inference(ennf_transformation,[],[f8])).
% 2.05/1.00  
% 2.05/1.00  fof(f46,plain,(
% 2.05/1.00    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 2.05/1.00    inference(cnf_transformation,[],[f20])).
% 2.05/1.00  
% 2.05/1.00  fof(f6,axiom,(
% 2.05/1.00    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 2.05/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/1.00  
% 2.05/1.00  fof(f44,plain,(
% 2.05/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 2.05/1.00    inference(cnf_transformation,[],[f6])).
% 2.05/1.00  
% 2.05/1.00  fof(f61,plain,(
% 2.05/1.00    ( ! [X2,X0,X1] : (k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 2.05/1.00    inference(definition_unfolding,[],[f46,f44])).
% 2.05/1.00  
% 2.05/1.00  fof(f12,axiom,(
% 2.05/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0))) & r1_tarski(X2,X1))))))),
% 2.05/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/1.00  
% 2.05/1.00  fof(f23,plain,(
% 2.05/1.00    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((? [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.05/1.00    inference(ennf_transformation,[],[f12])).
% 2.05/1.00  
% 2.05/1.00  fof(f24,plain,(
% 2.05/1.00    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.05/1.00    inference(flattening,[],[f23])).
% 2.05/1.00  
% 2.05/1.00  fof(f30,plain,(
% 2.05/1.00    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.05/1.00    inference(nnf_transformation,[],[f24])).
% 2.05/1.00  
% 2.05/1.00  fof(f31,plain,(
% 2.05/1.00    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (? [X5] : (k9_subset_1(u1_struct_0(X0),X1,X5) = X4 & v4_pre_topc(X5,X0) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.05/1.00    inference(rectify,[],[f30])).
% 2.05/1.00  
% 2.05/1.00  fof(f33,plain,(
% 2.05/1.00    ! [X4,X1,X0] : (? [X5] : (k9_subset_1(u1_struct_0(X0),X1,X5) = X4 & v4_pre_topc(X5,X0) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) => (k9_subset_1(u1_struct_0(X0),X1,sK2(X0,X1,X4)) = X4 & v4_pre_topc(sK2(X0,X1,X4),X0) & m1_subset_1(sK2(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.05/1.00    introduced(choice_axiom,[])).
% 2.05/1.00  
% 2.05/1.00  fof(f32,plain,(
% 2.05/1.00    ! [X1,X0] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK1(X0,X1) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(sK1(X0,X1),X1) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.05/1.00    introduced(choice_axiom,[])).
% 2.05/1.00  
% 2.05/1.00  fof(f34,plain,(
% 2.05/1.00    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK1(X0,X1) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(sK1(X0,X1),X1) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : ((k9_subset_1(u1_struct_0(X0),X1,sK2(X0,X1,X4)) = X4 & v4_pre_topc(sK2(X0,X1,X4),X0) & m1_subset_1(sK2(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.05/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f31,f33,f32])).
% 2.05/1.00  
% 2.05/1.00  fof(f55,plain,(
% 2.05/1.00    ( ! [X0,X3,X1] : (v2_tex_2(X1,X0) | k9_subset_1(u1_struct_0(X0),X1,X3) != sK1(X0,X1) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.05/1.00    inference(cnf_transformation,[],[f34])).
% 2.05/1.00  
% 2.05/1.00  fof(f49,plain,(
% 2.05/1.00    ( ! [X0] : (v4_pre_topc(sK0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.05/1.00    inference(cnf_transformation,[],[f29])).
% 2.05/1.00  
% 2.05/1.00  fof(f9,axiom,(
% 2.05/1.00    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.05/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/1.00  
% 2.05/1.00  fof(f47,plain,(
% 2.05/1.00    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.05/1.00    inference(cnf_transformation,[],[f9])).
% 2.05/1.00  
% 2.05/1.00  fof(f54,plain,(
% 2.05/1.00    ( ! [X0,X1] : (v2_tex_2(X1,X0) | r1_tarski(sK1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.05/1.00    inference(cnf_transformation,[],[f34])).
% 2.05/1.00  
% 2.05/1.00  fof(f60,plain,(
% 2.05/1.00    ~v2_tex_2(sK4,sK3)),
% 2.05/1.00    inference(cnf_transformation,[],[f37])).
% 2.05/1.00  
% 2.05/1.00  fof(f1,axiom,(
% 2.05/1.00    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 2.05/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/1.00  
% 2.05/1.00  fof(f17,plain,(
% 2.05/1.00    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 2.05/1.00    inference(ennf_transformation,[],[f1])).
% 2.05/1.00  
% 2.05/1.00  fof(f38,plain,(
% 2.05/1.00    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 2.05/1.00    inference(cnf_transformation,[],[f17])).
% 2.05/1.00  
% 2.05/1.00  fof(f58,plain,(
% 2.05/1.00    v1_xboole_0(sK4)),
% 2.05/1.00    inference(cnf_transformation,[],[f37])).
% 2.05/1.00  
% 2.05/1.00  cnf(c_3,plain,
% 2.05/1.00      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 2.05/1.00      inference(cnf_transformation,[],[f41]) ).
% 2.05/1.00  
% 2.05/1.00  cnf(c_2218,plain,
% 2.05/1.00      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 2.05/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.05/1.00  
% 2.05/1.00  cnf(c_5,plain,
% 2.05/1.00      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 2.05/1.00      inference(cnf_transformation,[],[f43]) ).
% 2.05/1.00  
% 2.05/1.00  cnf(c_2217,plain,
% 2.05/1.00      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 2.05/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.05/1.00  
% 2.05/1.00  cnf(c_3354,plain,
% 2.05/1.00      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.05/1.00      inference(superposition,[status(thm)],[c_2218,c_2217]) ).
% 2.05/1.00  
% 2.05/1.00  cnf(c_10,plain,
% 2.05/1.00      ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 2.05/1.00      | ~ v2_pre_topc(X0)
% 2.05/1.00      | ~ l1_pre_topc(X0) ),
% 2.05/1.00      inference(cnf_transformation,[],[f48]) ).
% 2.05/1.00  
% 2.05/1.00  cnf(c_21,negated_conjecture,
% 2.05/1.00      ( v2_pre_topc(sK3) ),
% 2.05/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.05/1.00  
% 2.05/1.00  cnf(c_288,plain,
% 2.05/1.00      ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 2.05/1.00      | ~ l1_pre_topc(X0)
% 2.05/1.00      | sK3 != X0 ),
% 2.05/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_21]) ).
% 2.05/1.00  
% 2.05/1.00  cnf(c_289,plain,
% 2.05/1.00      ( m1_subset_1(sK0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.05/1.00      | ~ l1_pre_topc(sK3) ),
% 2.05/1.00      inference(unflattening,[status(thm)],[c_288]) ).
% 2.05/1.00  
% 2.05/1.00  cnf(c_20,negated_conjecture,
% 2.05/1.00      ( l1_pre_topc(sK3) ),
% 2.05/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.05/1.00  
% 2.05/1.00  cnf(c_291,plain,
% 2.05/1.00      ( m1_subset_1(sK0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.05/1.00      inference(global_propositional_subsumption,
% 2.05/1.00                [status(thm)],
% 2.05/1.00                [c_289,c_20]) ).
% 2.05/1.00  
% 2.05/1.00  cnf(c_2211,plain,
% 2.05/1.00      ( m1_subset_1(sK0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 2.05/1.00      inference(predicate_to_equality,[status(thm)],[c_291]) ).
% 2.05/1.00  
% 2.05/1.00  cnf(c_7,plain,
% 2.05/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.05/1.00      | k4_xboole_0(X2,k4_xboole_0(X2,X0)) = k9_subset_1(X1,X2,X0) ),
% 2.05/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.05/1.00  
% 2.05/1.00  cnf(c_2215,plain,
% 2.05/1.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k9_subset_1(X2,X0,X1)
% 2.05/1.00      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 2.05/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.05/1.00  
% 2.05/1.00  cnf(c_3206,plain,
% 2.05/1.00      ( k4_xboole_0(X0,k4_xboole_0(X0,sK0(sK3))) = k9_subset_1(u1_struct_0(sK3),X0,sK0(sK3)) ),
% 2.05/1.00      inference(superposition,[status(thm)],[c_2211,c_2215]) ).
% 2.05/1.00  
% 2.05/1.00  cnf(c_11,plain,
% 2.05/1.00      ( v2_tex_2(X0,X1)
% 2.05/1.00      | ~ v4_pre_topc(X2,X1)
% 2.05/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.05/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.05/1.00      | ~ l1_pre_topc(X1)
% 2.05/1.00      | k9_subset_1(u1_struct_0(X1),X0,X2) != sK1(X1,X0) ),
% 2.05/1.00      inference(cnf_transformation,[],[f55]) ).
% 2.05/1.00  
% 2.05/1.00  cnf(c_470,plain,
% 2.05/1.00      ( v2_tex_2(X0,X1)
% 2.05/1.00      | ~ v4_pre_topc(X2,X1)
% 2.05/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.05/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.05/1.00      | k9_subset_1(u1_struct_0(X1),X0,X2) != sK1(X1,X0)
% 2.05/1.00      | sK3 != X1 ),
% 2.05/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_20]) ).
% 2.05/1.00  
% 2.05/1.00  cnf(c_471,plain,
% 2.05/1.00      ( v2_tex_2(X0,sK3)
% 2.05/1.00      | ~ v4_pre_topc(X1,sK3)
% 2.05/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.05/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.05/1.00      | k9_subset_1(u1_struct_0(sK3),X0,X1) != sK1(sK3,X0) ),
% 2.05/1.00      inference(unflattening,[status(thm)],[c_470]) ).
% 2.05/1.00  
% 2.05/1.00  cnf(c_2204,plain,
% 2.05/1.00      ( k9_subset_1(u1_struct_0(sK3),X0,X1) != sK1(sK3,X0)
% 2.05/1.00      | v2_tex_2(X0,sK3) = iProver_top
% 2.05/1.00      | v4_pre_topc(X1,sK3) != iProver_top
% 2.05/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.05/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.05/1.00      inference(predicate_to_equality,[status(thm)],[c_471]) ).
% 2.05/1.00  
% 2.05/1.00  cnf(c_3559,plain,
% 2.05/1.00      ( k4_xboole_0(X0,k4_xboole_0(X0,sK0(sK3))) != sK1(sK3,X0)
% 2.05/1.00      | v2_tex_2(X0,sK3) = iProver_top
% 2.05/1.00      | v4_pre_topc(sK0(sK3),sK3) != iProver_top
% 2.05/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.05/1.00      | m1_subset_1(sK0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.05/1.00      inference(superposition,[status(thm)],[c_3206,c_2204]) ).
% 2.05/1.00  
% 2.05/1.00  cnf(c_23,plain,
% 2.05/1.00      ( l1_pre_topc(sK3) = iProver_top ),
% 2.05/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.05/1.00  
% 2.05/1.00  cnf(c_290,plain,
% 2.05/1.00      ( m1_subset_1(sK0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 2.05/1.00      | l1_pre_topc(sK3) != iProver_top ),
% 2.05/1.00      inference(predicate_to_equality,[status(thm)],[c_289]) ).
% 2.05/1.00  
% 2.05/1.00  cnf(c_9,plain,
% 2.05/1.00      ( v4_pre_topc(sK0(X0),X0) | ~ v2_pre_topc(X0) | ~ l1_pre_topc(X0) ),
% 2.05/1.00      inference(cnf_transformation,[],[f49]) ).
% 2.05/1.00  
% 2.05/1.00  cnf(c_299,plain,
% 2.05/1.00      ( v4_pre_topc(sK0(X0),X0) | ~ l1_pre_topc(X0) | sK3 != X0 ),
% 2.05/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_21]) ).
% 2.05/1.00  
% 2.05/1.00  cnf(c_300,plain,
% 2.05/1.00      ( v4_pre_topc(sK0(sK3),sK3) | ~ l1_pre_topc(sK3) ),
% 2.05/1.00      inference(unflattening,[status(thm)],[c_299]) ).
% 2.05/1.00  
% 2.05/1.00  cnf(c_301,plain,
% 2.05/1.00      ( v4_pre_topc(sK0(sK3),sK3) = iProver_top
% 2.05/1.00      | l1_pre_topc(sK3) != iProver_top ),
% 2.05/1.00      inference(predicate_to_equality,[status(thm)],[c_300]) ).
% 2.05/1.00  
% 2.05/1.00  cnf(c_3672,plain,
% 2.05/1.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.05/1.00      | k4_xboole_0(X0,k4_xboole_0(X0,sK0(sK3))) != sK1(sK3,X0)
% 2.05/1.00      | v2_tex_2(X0,sK3) = iProver_top ),
% 2.05/1.00      inference(global_propositional_subsumption,
% 2.05/1.00                [status(thm)],
% 2.05/1.00                [c_3559,c_23,c_290,c_301]) ).
% 2.05/1.00  
% 2.05/1.00  cnf(c_3673,plain,
% 2.05/1.00      ( k4_xboole_0(X0,k4_xboole_0(X0,sK0(sK3))) != sK1(sK3,X0)
% 2.05/1.00      | v2_tex_2(X0,sK3) = iProver_top
% 2.05/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.05/1.00      inference(renaming,[status(thm)],[c_3672]) ).
% 2.05/1.00  
% 2.05/1.00  cnf(c_4033,plain,
% 2.05/1.00      ( sK1(sK3,k1_xboole_0) != k1_xboole_0
% 2.05/1.00      | v2_tex_2(k1_xboole_0,sK3) = iProver_top
% 2.05/1.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.05/1.00      inference(superposition,[status(thm)],[c_3354,c_3673]) ).
% 2.05/1.00  
% 2.05/1.00  cnf(c_8,plain,
% 2.05/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 2.05/1.00      inference(cnf_transformation,[],[f47]) ).
% 2.05/1.00  
% 2.05/1.00  cnf(c_2214,plain,
% 2.05/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.05/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.05/1.00  
% 2.05/1.00  cnf(c_12,plain,
% 2.05/1.00      ( v2_tex_2(X0,X1)
% 2.05/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.05/1.00      | r1_tarski(sK1(X1,X0),X0)
% 2.05/1.00      | ~ l1_pre_topc(X1) ),
% 2.05/1.00      inference(cnf_transformation,[],[f54]) ).
% 2.05/1.00  
% 2.05/1.00  cnf(c_455,plain,
% 2.05/1.00      ( v2_tex_2(X0,X1)
% 2.05/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.05/1.00      | r1_tarski(sK1(X1,X0),X0)
% 2.05/1.00      | sK3 != X1 ),
% 2.05/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_20]) ).
% 2.05/1.00  
% 2.05/1.00  cnf(c_456,plain,
% 2.05/1.00      ( v2_tex_2(X0,sK3)
% 2.05/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.05/1.00      | r1_tarski(sK1(sK3,X0),X0) ),
% 2.05/1.00      inference(unflattening,[status(thm)],[c_455]) ).
% 2.05/1.00  
% 2.05/1.00  cnf(c_2205,plain,
% 2.05/1.00      ( v2_tex_2(X0,sK3) = iProver_top
% 2.05/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.05/1.00      | r1_tarski(sK1(sK3,X0),X0) = iProver_top ),
% 2.05/1.00      inference(predicate_to_equality,[status(thm)],[c_456]) ).
% 2.05/1.00  
% 2.05/1.00  cnf(c_2734,plain,
% 2.05/1.00      ( v2_tex_2(k1_xboole_0,sK3) = iProver_top
% 2.05/1.00      | r1_tarski(sK1(sK3,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 2.05/1.00      inference(superposition,[status(thm)],[c_2214,c_2205]) ).
% 2.05/1.00  
% 2.05/1.00  cnf(c_457,plain,
% 2.05/1.00      ( v2_tex_2(X0,sK3) = iProver_top
% 2.05/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.05/1.00      | r1_tarski(sK1(sK3,X0),X0) = iProver_top ),
% 2.05/1.00      inference(predicate_to_equality,[status(thm)],[c_456]) ).
% 2.05/1.00  
% 2.05/1.00  cnf(c_459,plain,
% 2.05/1.00      ( v2_tex_2(k1_xboole_0,sK3) = iProver_top
% 2.05/1.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.05/1.00      | r1_tarski(sK1(sK3,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 2.05/1.00      inference(instantiation,[status(thm)],[c_457]) ).
% 2.05/1.00  
% 2.05/1.00  cnf(c_17,negated_conjecture,
% 2.05/1.00      ( ~ v2_tex_2(sK4,sK3) ),
% 2.05/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.05/1.00  
% 2.05/1.00  cnf(c_2213,plain,
% 2.05/1.00      ( v2_tex_2(sK4,sK3) != iProver_top ),
% 2.05/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.05/1.00  
% 2.05/1.00  cnf(c_0,plain,
% 2.05/1.00      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 2.05/1.00      inference(cnf_transformation,[],[f38]) ).
% 2.05/1.00  
% 2.05/1.00  cnf(c_19,negated_conjecture,
% 2.05/1.00      ( v1_xboole_0(sK4) ),
% 2.05/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.05/1.00  
% 2.05/1.00  cnf(c_282,plain,
% 2.05/1.00      ( sK4 != X0 | k1_xboole_0 = X0 ),
% 2.05/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_19]) ).
% 2.05/1.00  
% 2.05/1.00  cnf(c_283,plain,
% 2.05/1.00      ( k1_xboole_0 = sK4 ),
% 2.05/1.00      inference(unflattening,[status(thm)],[c_282]) ).
% 2.05/1.00  
% 2.05/1.00  cnf(c_2227,plain,
% 2.05/1.00      ( v2_tex_2(k1_xboole_0,sK3) != iProver_top ),
% 2.05/1.00      inference(light_normalisation,[status(thm)],[c_2213,c_283]) ).
% 2.05/1.00  
% 2.05/1.00  cnf(c_2364,plain,
% 2.05/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.05/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 2.05/1.00  
% 2.05/1.00  cnf(c_2367,plain,
% 2.05/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 2.05/1.00      inference(predicate_to_equality,[status(thm)],[c_2364]) ).
% 2.05/1.00  
% 2.05/1.00  cnf(c_3135,plain,
% 2.05/1.00      ( r1_tarski(sK1(sK3,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 2.05/1.00      inference(global_propositional_subsumption,
% 2.05/1.00                [status(thm)],
% 2.05/1.00                [c_2734,c_459,c_2227,c_2367]) ).
% 2.05/1.00  
% 2.05/1.00  cnf(c_3355,plain,
% 2.05/1.00      ( sK1(sK3,k1_xboole_0) = k1_xboole_0 ),
% 2.05/1.00      inference(superposition,[status(thm)],[c_3135,c_2217]) ).
% 2.05/1.00  
% 2.05/1.00  cnf(contradiction,plain,
% 2.05/1.00      ( $false ),
% 2.05/1.00      inference(minisat,[status(thm)],[c_4033,c_3355,c_2367,c_2227]) ).
% 2.05/1.00  
% 2.05/1.00  
% 2.05/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.05/1.00  
% 2.05/1.00  ------                               Statistics
% 2.05/1.00  
% 2.05/1.00  ------ General
% 2.05/1.00  
% 2.05/1.00  abstr_ref_over_cycles:                  0
% 2.05/1.00  abstr_ref_under_cycles:                 0
% 2.05/1.00  gc_basic_clause_elim:                   0
% 2.05/1.00  forced_gc_time:                         0
% 2.05/1.00  parsing_time:                           0.02
% 2.05/1.00  unif_index_cands_time:                  0.
% 2.05/1.00  unif_index_add_time:                    0.
% 2.05/1.00  orderings_time:                         0.
% 2.05/1.00  out_proof_time:                         0.009
% 2.05/1.00  total_time:                             0.155
% 2.05/1.00  num_of_symbols:                         48
% 2.05/1.00  num_of_terms:                           2413
% 2.05/1.00  
% 2.05/1.00  ------ Preprocessing
% 2.05/1.00  
% 2.05/1.00  num_of_splits:                          0
% 2.05/1.00  num_of_split_atoms:                     0
% 2.05/1.00  num_of_reused_defs:                     0
% 2.05/1.00  num_eq_ax_congr_red:                    19
% 2.05/1.00  num_of_sem_filtered_clauses:            1
% 2.05/1.00  num_of_subtypes:                        0
% 2.05/1.00  monotx_restored_types:                  0
% 2.05/1.00  sat_num_of_epr_types:                   0
% 2.05/1.00  sat_num_of_non_cyclic_types:            0
% 2.05/1.00  sat_guarded_non_collapsed_types:        0
% 2.05/1.00  num_pure_diseq_elim:                    0
% 2.05/1.00  simp_replaced_by:                       0
% 2.05/1.00  res_preprocessed:                       106
% 2.05/1.00  prep_upred:                             0
% 2.05/1.00  prep_unflattend:                        79
% 2.05/1.00  smt_new_axioms:                         0
% 2.05/1.00  pred_elim_cands:                        4
% 2.05/1.00  pred_elim:                              3
% 2.05/1.00  pred_elim_cl:                           3
% 2.05/1.00  pred_elim_cycles:                       10
% 2.05/1.00  merged_defs:                            8
% 2.05/1.00  merged_defs_ncl:                        0
% 2.05/1.00  bin_hyper_res:                          8
% 2.05/1.00  prep_cycles:                            4
% 2.05/1.00  pred_elim_time:                         0.023
% 2.05/1.00  splitting_time:                         0.
% 2.05/1.00  sem_filter_time:                        0.
% 2.05/1.00  monotx_time:                            0.
% 2.05/1.00  subtype_inf_time:                       0.
% 2.05/1.00  
% 2.05/1.00  ------ Problem properties
% 2.05/1.00  
% 2.05/1.00  clauses:                                19
% 2.05/1.00  conjectures:                            2
% 2.05/1.00  epr:                                    3
% 2.05/1.00  horn:                                   17
% 2.05/1.00  ground:                                 5
% 2.05/1.00  unary:                                  8
% 2.05/1.00  binary:                                 5
% 2.05/1.00  lits:                                   44
% 2.05/1.00  lits_eq:                                9
% 2.05/1.00  fd_pure:                                0
% 2.05/1.00  fd_pseudo:                              0
% 2.05/1.00  fd_cond:                                1
% 2.05/1.00  fd_pseudo_cond:                         0
% 2.05/1.00  ac_symbols:                             0
% 2.05/1.00  
% 2.05/1.00  ------ Propositional Solver
% 2.05/1.00  
% 2.05/1.00  prop_solver_calls:                      26
% 2.05/1.00  prop_fast_solver_calls:                 941
% 2.05/1.00  smt_solver_calls:                       0
% 2.05/1.00  smt_fast_solver_calls:                  0
% 2.05/1.00  prop_num_of_clauses:                    945
% 2.05/1.00  prop_preprocess_simplified:             3923
% 2.05/1.00  prop_fo_subsumed:                       18
% 2.05/1.00  prop_solver_time:                       0.
% 2.05/1.00  smt_solver_time:                        0.
% 2.05/1.00  smt_fast_solver_time:                   0.
% 2.05/1.00  prop_fast_solver_time:                  0.
% 2.05/1.00  prop_unsat_core_time:                   0.
% 2.05/1.00  
% 2.05/1.00  ------ QBF
% 2.05/1.00  
% 2.05/1.00  qbf_q_res:                              0
% 2.05/1.00  qbf_num_tautologies:                    0
% 2.05/1.00  qbf_prep_cycles:                        0
% 2.05/1.00  
% 2.05/1.00  ------ BMC1
% 2.05/1.00  
% 2.05/1.00  bmc1_current_bound:                     -1
% 2.05/1.00  bmc1_last_solved_bound:                 -1
% 2.05/1.00  bmc1_unsat_core_size:                   -1
% 2.05/1.00  bmc1_unsat_core_parents_size:           -1
% 2.05/1.00  bmc1_merge_next_fun:                    0
% 2.05/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.05/1.00  
% 2.05/1.00  ------ Instantiation
% 2.05/1.00  
% 2.05/1.00  inst_num_of_clauses:                    261
% 2.05/1.00  inst_num_in_passive:                    55
% 2.05/1.00  inst_num_in_active:                     179
% 2.05/1.00  inst_num_in_unprocessed:                28
% 2.05/1.00  inst_num_of_loops:                      190
% 2.05/1.00  inst_num_of_learning_restarts:          0
% 2.05/1.00  inst_num_moves_active_passive:          8
% 2.05/1.00  inst_lit_activity:                      0
% 2.05/1.00  inst_lit_activity_moves:                0
% 2.05/1.00  inst_num_tautologies:                   0
% 2.05/1.00  inst_num_prop_implied:                  0
% 2.05/1.00  inst_num_existing_simplified:           0
% 2.05/1.00  inst_num_eq_res_simplified:             0
% 2.05/1.00  inst_num_child_elim:                    0
% 2.05/1.00  inst_num_of_dismatching_blockings:      57
% 2.05/1.00  inst_num_of_non_proper_insts:           261
% 2.05/1.00  inst_num_of_duplicates:                 0
% 2.05/1.00  inst_inst_num_from_inst_to_res:         0
% 2.05/1.00  inst_dismatching_checking_time:         0.
% 2.05/1.00  
% 2.05/1.00  ------ Resolution
% 2.05/1.00  
% 2.05/1.00  res_num_of_clauses:                     0
% 2.05/1.00  res_num_in_passive:                     0
% 2.05/1.00  res_num_in_active:                      0
% 2.05/1.00  res_num_of_loops:                       110
% 2.05/1.00  res_forward_subset_subsumed:            21
% 2.05/1.00  res_backward_subset_subsumed:           2
% 2.05/1.00  res_forward_subsumed:                   0
% 2.05/1.00  res_backward_subsumed:                  0
% 2.05/1.00  res_forward_subsumption_resolution:     3
% 2.05/1.00  res_backward_subsumption_resolution:    0
% 2.05/1.00  res_clause_to_clause_subsumption:       301
% 2.05/1.00  res_orphan_elimination:                 0
% 2.05/1.00  res_tautology_del:                      51
% 2.05/1.00  res_num_eq_res_simplified:              0
% 2.05/1.00  res_num_sel_changes:                    0
% 2.05/1.00  res_moves_from_active_to_pass:          0
% 2.05/1.00  
% 2.05/1.00  ------ Superposition
% 2.05/1.00  
% 2.05/1.00  sup_time_total:                         0.
% 2.05/1.00  sup_time_generating:                    0.
% 2.05/1.00  sup_time_sim_full:                      0.
% 2.05/1.00  sup_time_sim_immed:                     0.
% 2.05/1.00  
% 2.05/1.00  sup_num_of_clauses:                     63
% 2.05/1.00  sup_num_in_active:                      37
% 2.05/1.00  sup_num_in_passive:                     26
% 2.05/1.00  sup_num_of_loops:                       36
% 2.05/1.00  sup_fw_superposition:                   37
% 2.05/1.00  sup_bw_superposition:                   15
% 2.05/1.00  sup_immediate_simplified:               6
% 2.05/1.00  sup_given_eliminated:                   0
% 2.05/1.00  comparisons_done:                       0
% 2.05/1.00  comparisons_avoided:                    0
% 2.05/1.00  
% 2.05/1.00  ------ Simplifications
% 2.05/1.00  
% 2.05/1.00  
% 2.05/1.00  sim_fw_subset_subsumed:                 2
% 2.05/1.00  sim_bw_subset_subsumed:                 0
% 2.05/1.00  sim_fw_subsumed:                        3
% 2.05/1.00  sim_bw_subsumed:                        0
% 2.05/1.00  sim_fw_subsumption_res:                 2
% 2.05/1.00  sim_bw_subsumption_res:                 0
% 2.05/1.00  sim_tautology_del:                      0
% 2.05/1.00  sim_eq_tautology_del:                   1
% 2.05/1.00  sim_eq_res_simp:                        0
% 2.05/1.00  sim_fw_demodulated:                     1
% 2.05/1.00  sim_bw_demodulated:                     0
% 2.05/1.00  sim_light_normalised:                   3
% 2.05/1.00  sim_joinable_taut:                      0
% 2.05/1.00  sim_joinable_simp:                      0
% 2.05/1.00  sim_ac_normalised:                      0
% 2.05/1.00  sim_smt_subsumption:                    0
% 2.05/1.00  
%------------------------------------------------------------------------------
