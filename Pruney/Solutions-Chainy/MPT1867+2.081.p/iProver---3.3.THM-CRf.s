%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:26:21 EST 2020

% Result     : Theorem 15.40s
% Output     : CNFRefutation 15.40s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 219 expanded)
%              Number of clauses        :   58 (  93 expanded)
%              Number of leaves         :   15 (  44 expanded)
%              Depth                    :   20
%              Number of atoms          :  335 ( 722 expanded)
%              Number of equality atoms :  109 ( 151 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ? [X1] :
          ( v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( v3_pre_topc(sK1(X0),X0)
        & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ( v3_pre_topc(sK1(X0),X0)
        & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f24,f34])).

fof(f56,plain,(
    ! [X0] :
      ( m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f48,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f11,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f39,plain,(
    ! [X4,X1,X0] :
      ( ? [X5] :
          ( k9_subset_1(u1_struct_0(X0),X1,X5) = X4
          & v3_pre_topc(X5,X0)
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X0),X1,sK3(X0,X1,X4)) = X4
        & v3_pre_topc(sK3(X0,X1,X4),X0)
        & m1_subset_1(sK3(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
              | ~ v3_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ! [X3] :
            ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1)
            | ~ v3_pre_topc(X3,X0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & r1_tarski(sK2(X0,X1),X1)
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ( ! [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & r1_tarski(sK2(X0,X1),X1)
                & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X4] :
                  ( ( k9_subset_1(u1_struct_0(X0),X1,sK3(X0,X1,X4)) = X4
                    & v3_pre_topc(sK3(X0,X1,X4),X0)
                    & m1_subset_1(sK3(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r1_tarski(X4,X1)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f37,f39,f38])).

fof(f63,plain,(
    ! [X0,X3,X1] :
      ( v2_tex_2(X1,X0)
      | k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1)
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | r1_tarski(sK2(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f57,plain,(
    ! [X0] :
      ( v3_pre_topc(sK1(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_xboole_0(X1) )
           => v2_tex_2(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f14,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_xboole_0(X1) )
           => v2_tex_2(X1,X0) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
     => ( ~ v2_tex_2(sK5,X0)
        & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
        & v1_xboole_0(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v2_tex_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ v2_tex_2(X1,sK4)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(sK4)
      & v2_pre_topc(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ~ v2_tex_2(sK5,sK4)
    & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    & v1_xboole_0(sK5)
    & l1_pre_topc(sK4)
    & v2_pre_topc(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f28,f42,f41])).

fof(f66,plain,(
    v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f43])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f47,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f68,plain,(
    ~ v2_tex_2(sK5,sK4) ),
    inference(cnf_transformation,[],[f43])).

fof(f65,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f43])).

fof(f64,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_13,plain,
    ( m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_909,plain,
    ( m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_8,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_914,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_912,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1433,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_914,c_912])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X0,X2) = k9_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_9,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_174,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_9])).

cnf(c_175,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_174])).

cnf(c_217,plain,
    ( ~ r1_tarski(X0,X1)
    | k9_subset_1(X1,X0,X2) = k9_subset_1(X1,X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_5,c_175])).

cnf(c_897,plain,
    ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_217])).

cnf(c_3406,plain,
    ( k9_subset_1(X0,k1_xboole_0,X1) = k9_subset_1(X0,X1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1433,c_897])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_218,plain,
    ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
    | ~ r1_tarski(X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_6,c_175])).

cnf(c_896,plain,
    ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) = iProver_top
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_218])).

cnf(c_1434,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k9_subset_1(X1,X2,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_896,c_912])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_915,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2282,plain,
    ( k9_subset_1(k1_xboole_0,X0,X1) = k1_xboole_0
    | r1_tarski(X1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1434,c_915])).

cnf(c_2447,plain,
    ( k9_subset_1(k1_xboole_0,X0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1433,c_2282])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_219,plain,
    ( ~ r1_tarski(X0,X1)
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_7,c_175])).

cnf(c_895,plain,
    ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_219])).

cnf(c_1836,plain,
    ( k9_subset_1(X0,X1,k1_xboole_0) = k3_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1433,c_895])).

cnf(c_2464,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2447,c_1836])).

cnf(c_2551,plain,
    ( k9_subset_1(X0,X1,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2464,c_1836])).

cnf(c_3416,plain,
    ( k9_subset_1(X0,k1_xboole_0,X1) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3406,c_2551])).

cnf(c_14,plain,
    ( v2_tex_2(X0,X1)
    | ~ v3_pre_topc(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),X0,X2) != sK2(X1,X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_908,plain,
    ( k9_subset_1(u1_struct_0(X0),X1,X2) != sK2(X0,X1)
    | v2_tex_2(X1,X0) = iProver_top
    | v3_pre_topc(X2,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3584,plain,
    ( sK2(X0,k1_xboole_0) != k1_xboole_0
    | v2_tex_2(k1_xboole_0,X0) = iProver_top
    | v3_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3416,c_908])).

cnf(c_1759,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1762,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1759])).

cnf(c_15,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(sK2(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_907,plain,
    ( v2_tex_2(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(sK2(X1,X0),X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2653,plain,
    ( v2_tex_2(k1_xboole_0,X0) = iProver_top
    | r1_tarski(sK2(X0,k1_xboole_0),k1_xboole_0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_914,c_907])).

cnf(c_3898,plain,
    ( sK2(X0,k1_xboole_0) = k1_xboole_0
    | v2_tex_2(k1_xboole_0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2653,c_915])).

cnf(c_56498,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v3_pre_topc(X1,X0) != iProver_top
    | v2_tex_2(k1_xboole_0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3584,c_1762,c_3898])).

cnf(c_56499,plain,
    ( v2_tex_2(k1_xboole_0,X0) = iProver_top
    | v3_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_56498])).

cnf(c_56510,plain,
    ( v2_tex_2(k1_xboole_0,X0) = iProver_top
    | v3_pre_topc(sK1(X0),X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_909,c_56499])).

cnf(c_12,plain,
    ( v3_pre_topc(sK1(X0),X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_51,plain,
    ( v3_pre_topc(sK1(X0),X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_57162,plain,
    ( v2_tex_2(k1_xboole_0,X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_56510,c_51])).

cnf(c_22,negated_conjecture,
    ( v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_900,plain,
    ( v1_xboole_0(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_916,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1241,plain,
    ( sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_900,c_916])).

cnf(c_20,negated_conjecture,
    ( ~ v2_tex_2(sK5,sK4) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_902,plain,
    ( v2_tex_2(sK5,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1244,plain,
    ( v2_tex_2(k1_xboole_0,sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1241,c_902])).

cnf(c_57171,plain,
    ( v2_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_57162,c_1244])).

cnf(c_23,negated_conjecture,
    ( l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_26,plain,
    ( l1_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_24,negated_conjecture,
    ( v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_25,plain,
    ( v2_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_57171,c_26,c_25])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:48:56 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 15.40/2.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.40/2.49  
% 15.40/2.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.40/2.49  
% 15.40/2.49  ------  iProver source info
% 15.40/2.49  
% 15.40/2.49  git: date: 2020-06-30 10:37:57 +0100
% 15.40/2.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.40/2.49  git: non_committed_changes: false
% 15.40/2.49  git: last_make_outside_of_git: false
% 15.40/2.49  
% 15.40/2.49  ------ 
% 15.40/2.49  ------ Parsing...
% 15.40/2.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.40/2.49  
% 15.40/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 15.40/2.49  
% 15.40/2.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.40/2.49  
% 15.40/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.40/2.49  ------ Proving...
% 15.40/2.49  ------ Problem Properties 
% 15.40/2.49  
% 15.40/2.49  
% 15.40/2.49  clauses                                 25
% 15.40/2.49  conjectures                             5
% 15.40/2.49  EPR                                     7
% 15.40/2.49  Horn                                    22
% 15.40/2.49  unary                                   6
% 15.40/2.49  binary                                  9
% 15.40/2.49  lits                                    68
% 15.40/2.49  lits eq                                 6
% 15.40/2.49  fd_pure                                 0
% 15.40/2.49  fd_pseudo                               0
% 15.40/2.49  fd_cond                                 2
% 15.40/2.49  fd_pseudo_cond                          0
% 15.40/2.49  AC symbols                              0
% 15.40/2.49  
% 15.40/2.49  ------ Input Options Time Limit: Unbounded
% 15.40/2.49  
% 15.40/2.49  
% 15.40/2.49  ------ 
% 15.40/2.49  Current options:
% 15.40/2.49  ------ 
% 15.40/2.49  
% 15.40/2.49  
% 15.40/2.49  
% 15.40/2.49  
% 15.40/2.49  ------ Proving...
% 15.40/2.49  
% 15.40/2.49  
% 15.40/2.49  % SZS status Theorem for theBenchmark.p
% 15.40/2.49  
% 15.40/2.49  % SZS output start CNFRefutation for theBenchmark.p
% 15.40/2.49  
% 15.40/2.49  fof(f10,axiom,(
% 15.40/2.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ? [X1] : (v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 15.40/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.40/2.49  
% 15.40/2.49  fof(f23,plain,(
% 15.40/2.49    ! [X0] : (? [X1] : (v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 15.40/2.49    inference(ennf_transformation,[],[f10])).
% 15.40/2.49  
% 15.40/2.49  fof(f24,plain,(
% 15.40/2.49    ! [X0] : (? [X1] : (v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 15.40/2.49    inference(flattening,[],[f23])).
% 15.40/2.49  
% 15.40/2.49  fof(f34,plain,(
% 15.40/2.49    ! [X0] : (? [X1] : (v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (v3_pre_topc(sK1(X0),X0) & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 15.40/2.49    introduced(choice_axiom,[])).
% 15.40/2.49  
% 15.40/2.49  fof(f35,plain,(
% 15.40/2.49    ! [X0] : ((v3_pre_topc(sK1(X0),X0) & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 15.40/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f24,f34])).
% 15.40/2.49  
% 15.40/2.49  fof(f56,plain,(
% 15.40/2.49    ( ! [X0] : (m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 15.40/2.49    inference(cnf_transformation,[],[f35])).
% 15.40/2.49  
% 15.40/2.49  fof(f7,axiom,(
% 15.40/2.49    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 15.40/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.40/2.49  
% 15.40/2.49  fof(f52,plain,(
% 15.40/2.49    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 15.40/2.49    inference(cnf_transformation,[],[f7])).
% 15.40/2.49  
% 15.40/2.49  fof(f8,axiom,(
% 15.40/2.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 15.40/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.40/2.49  
% 15.40/2.49  fof(f33,plain,(
% 15.40/2.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 15.40/2.49    inference(nnf_transformation,[],[f8])).
% 15.40/2.49  
% 15.40/2.49  fof(f53,plain,(
% 15.40/2.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 15.40/2.49    inference(cnf_transformation,[],[f33])).
% 15.40/2.49  
% 15.40/2.49  fof(f4,axiom,(
% 15.40/2.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1))),
% 15.40/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.40/2.49  
% 15.40/2.49  fof(f18,plain,(
% 15.40/2.49    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 15.40/2.49    inference(ennf_transformation,[],[f4])).
% 15.40/2.49  
% 15.40/2.49  fof(f49,plain,(
% 15.40/2.49    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 15.40/2.49    inference(cnf_transformation,[],[f18])).
% 15.40/2.49  
% 15.40/2.49  fof(f54,plain,(
% 15.40/2.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 15.40/2.49    inference(cnf_transformation,[],[f33])).
% 15.40/2.49  
% 15.40/2.49  fof(f5,axiom,(
% 15.40/2.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 15.40/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.40/2.49  
% 15.40/2.49  fof(f19,plain,(
% 15.40/2.49    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 15.40/2.49    inference(ennf_transformation,[],[f5])).
% 15.40/2.49  
% 15.40/2.49  fof(f50,plain,(
% 15.40/2.49    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 15.40/2.49    inference(cnf_transformation,[],[f19])).
% 15.40/2.49  
% 15.40/2.49  fof(f3,axiom,(
% 15.40/2.49    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 15.40/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.40/2.49  
% 15.40/2.49  fof(f17,plain,(
% 15.40/2.49    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 15.40/2.49    inference(ennf_transformation,[],[f3])).
% 15.40/2.49  
% 15.40/2.49  fof(f48,plain,(
% 15.40/2.49    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 15.40/2.49    inference(cnf_transformation,[],[f17])).
% 15.40/2.49  
% 15.40/2.49  fof(f6,axiom,(
% 15.40/2.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 15.40/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.40/2.49  
% 15.40/2.49  fof(f20,plain,(
% 15.40/2.49    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 15.40/2.49    inference(ennf_transformation,[],[f6])).
% 15.40/2.49  
% 15.40/2.49  fof(f51,plain,(
% 15.40/2.49    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 15.40/2.49    inference(cnf_transformation,[],[f20])).
% 15.40/2.49  
% 15.40/2.49  fof(f11,axiom,(
% 15.40/2.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0))) & r1_tarski(X2,X1))))))),
% 15.40/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.40/2.49  
% 15.40/2.49  fof(f25,plain,(
% 15.40/2.49    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((? [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 15.40/2.49    inference(ennf_transformation,[],[f11])).
% 15.40/2.49  
% 15.40/2.49  fof(f26,plain,(
% 15.40/2.49    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 15.40/2.49    inference(flattening,[],[f25])).
% 15.40/2.49  
% 15.40/2.49  fof(f36,plain,(
% 15.40/2.49    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 15.40/2.49    inference(nnf_transformation,[],[f26])).
% 15.40/2.49  
% 15.40/2.49  fof(f37,plain,(
% 15.40/2.49    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (? [X5] : (k9_subset_1(u1_struct_0(X0),X1,X5) = X4 & v3_pre_topc(X5,X0) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 15.40/2.49    inference(rectify,[],[f36])).
% 15.40/2.49  
% 15.40/2.49  fof(f39,plain,(
% 15.40/2.49    ! [X4,X1,X0] : (? [X5] : (k9_subset_1(u1_struct_0(X0),X1,X5) = X4 & v3_pre_topc(X5,X0) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) => (k9_subset_1(u1_struct_0(X0),X1,sK3(X0,X1,X4)) = X4 & v3_pre_topc(sK3(X0,X1,X4),X0) & m1_subset_1(sK3(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))))),
% 15.40/2.49    introduced(choice_axiom,[])).
% 15.40/2.49  
% 15.40/2.49  fof(f38,plain,(
% 15.40/2.49    ! [X1,X0] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(sK2(X0,X1),X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 15.40/2.49    introduced(choice_axiom,[])).
% 15.40/2.49  
% 15.40/2.49  fof(f40,plain,(
% 15.40/2.49    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(sK2(X0,X1),X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : ((k9_subset_1(u1_struct_0(X0),X1,sK3(X0,X1,X4)) = X4 & v3_pre_topc(sK3(X0,X1,X4),X0) & m1_subset_1(sK3(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 15.40/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f37,f39,f38])).
% 15.40/2.49  
% 15.40/2.49  fof(f63,plain,(
% 15.40/2.49    ( ! [X0,X3,X1] : (v2_tex_2(X1,X0) | k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 15.40/2.49    inference(cnf_transformation,[],[f40])).
% 15.40/2.49  
% 15.40/2.49  fof(f62,plain,(
% 15.40/2.49    ( ! [X0,X1] : (v2_tex_2(X1,X0) | r1_tarski(sK2(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 15.40/2.49    inference(cnf_transformation,[],[f40])).
% 15.40/2.49  
% 15.40/2.49  fof(f57,plain,(
% 15.40/2.49    ( ! [X0] : (v3_pre_topc(sK1(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 15.40/2.49    inference(cnf_transformation,[],[f35])).
% 15.40/2.49  
% 15.40/2.49  fof(f12,conjecture,(
% 15.40/2.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 15.40/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.40/2.49  
% 15.40/2.49  fof(f13,negated_conjecture,(
% 15.40/2.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 15.40/2.49    inference(negated_conjecture,[],[f12])).
% 15.40/2.49  
% 15.40/2.49  fof(f14,plain,(
% 15.40/2.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 15.40/2.49    inference(pure_predicate_removal,[],[f13])).
% 15.40/2.49  
% 15.40/2.49  fof(f27,plain,(
% 15.40/2.49    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 15.40/2.49    inference(ennf_transformation,[],[f14])).
% 15.40/2.49  
% 15.40/2.49  fof(f28,plain,(
% 15.40/2.49    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 15.40/2.49    inference(flattening,[],[f27])).
% 15.40/2.49  
% 15.40/2.49  fof(f42,plain,(
% 15.40/2.49    ( ! [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => (~v2_tex_2(sK5,X0) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(sK5))) )),
% 15.40/2.49    introduced(choice_axiom,[])).
% 15.40/2.49  
% 15.40/2.49  fof(f41,plain,(
% 15.40/2.49    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (~v2_tex_2(X1,sK4) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) & v1_xboole_0(X1)) & l1_pre_topc(sK4) & v2_pre_topc(sK4))),
% 15.40/2.49    introduced(choice_axiom,[])).
% 15.40/2.49  
% 15.40/2.49  fof(f43,plain,(
% 15.40/2.49    (~v2_tex_2(sK5,sK4) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) & v1_xboole_0(sK5)) & l1_pre_topc(sK4) & v2_pre_topc(sK4)),
% 15.40/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f28,f42,f41])).
% 15.40/2.49  
% 15.40/2.49  fof(f66,plain,(
% 15.40/2.49    v1_xboole_0(sK5)),
% 15.40/2.49    inference(cnf_transformation,[],[f43])).
% 15.40/2.49  
% 15.40/2.49  fof(f2,axiom,(
% 15.40/2.49    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 15.40/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.40/2.49  
% 15.40/2.49  fof(f16,plain,(
% 15.40/2.49    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 15.40/2.49    inference(ennf_transformation,[],[f2])).
% 15.40/2.49  
% 15.40/2.49  fof(f47,plain,(
% 15.40/2.49    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 15.40/2.49    inference(cnf_transformation,[],[f16])).
% 15.40/2.49  
% 15.40/2.49  fof(f68,plain,(
% 15.40/2.49    ~v2_tex_2(sK5,sK4)),
% 15.40/2.49    inference(cnf_transformation,[],[f43])).
% 15.40/2.49  
% 15.40/2.49  fof(f65,plain,(
% 15.40/2.49    l1_pre_topc(sK4)),
% 15.40/2.49    inference(cnf_transformation,[],[f43])).
% 15.40/2.49  
% 15.40/2.49  fof(f64,plain,(
% 15.40/2.49    v2_pre_topc(sK4)),
% 15.40/2.49    inference(cnf_transformation,[],[f43])).
% 15.40/2.49  
% 15.40/2.49  cnf(c_13,plain,
% 15.40/2.49      ( m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 15.40/2.49      | ~ v2_pre_topc(X0)
% 15.40/2.49      | ~ l1_pre_topc(X0) ),
% 15.40/2.49      inference(cnf_transformation,[],[f56]) ).
% 15.40/2.49  
% 15.40/2.49  cnf(c_909,plain,
% 15.40/2.49      ( m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 15.40/2.49      | v2_pre_topc(X0) != iProver_top
% 15.40/2.49      | l1_pre_topc(X0) != iProver_top ),
% 15.40/2.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 15.40/2.49  
% 15.40/2.49  cnf(c_8,plain,
% 15.40/2.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 15.40/2.49      inference(cnf_transformation,[],[f52]) ).
% 15.40/2.49  
% 15.40/2.49  cnf(c_914,plain,
% 15.40/2.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 15.40/2.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 15.40/2.49  
% 15.40/2.49  cnf(c_10,plain,
% 15.40/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 15.40/2.49      inference(cnf_transformation,[],[f53]) ).
% 15.40/2.49  
% 15.40/2.49  cnf(c_912,plain,
% 15.40/2.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 15.40/2.49      | r1_tarski(X0,X1) = iProver_top ),
% 15.40/2.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 15.40/2.49  
% 15.40/2.49  cnf(c_1433,plain,
% 15.40/2.49      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 15.40/2.49      inference(superposition,[status(thm)],[c_914,c_912]) ).
% 15.40/2.49  
% 15.40/2.49  cnf(c_5,plain,
% 15.40/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.40/2.49      | k9_subset_1(X1,X0,X2) = k9_subset_1(X1,X2,X0) ),
% 15.40/2.49      inference(cnf_transformation,[],[f49]) ).
% 15.40/2.49  
% 15.40/2.49  cnf(c_9,plain,
% 15.40/2.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 15.40/2.49      inference(cnf_transformation,[],[f54]) ).
% 15.40/2.49  
% 15.40/2.49  cnf(c_174,plain,
% 15.40/2.49      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 15.40/2.49      inference(prop_impl,[status(thm)],[c_9]) ).
% 15.40/2.49  
% 15.40/2.49  cnf(c_175,plain,
% 15.40/2.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 15.40/2.49      inference(renaming,[status(thm)],[c_174]) ).
% 15.40/2.49  
% 15.40/2.49  cnf(c_217,plain,
% 15.40/2.49      ( ~ r1_tarski(X0,X1)
% 15.40/2.49      | k9_subset_1(X1,X0,X2) = k9_subset_1(X1,X2,X0) ),
% 15.40/2.49      inference(bin_hyper_res,[status(thm)],[c_5,c_175]) ).
% 15.40/2.49  
% 15.40/2.49  cnf(c_897,plain,
% 15.40/2.49      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
% 15.40/2.49      | r1_tarski(X1,X0) != iProver_top ),
% 15.40/2.49      inference(predicate_to_equality,[status(thm)],[c_217]) ).
% 15.40/2.49  
% 15.40/2.49  cnf(c_3406,plain,
% 15.40/2.49      ( k9_subset_1(X0,k1_xboole_0,X1) = k9_subset_1(X0,X1,k1_xboole_0) ),
% 15.40/2.49      inference(superposition,[status(thm)],[c_1433,c_897]) ).
% 15.40/2.49  
% 15.40/2.49  cnf(c_6,plain,
% 15.40/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.40/2.49      | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 15.40/2.49      inference(cnf_transformation,[],[f50]) ).
% 15.40/2.49  
% 15.40/2.49  cnf(c_218,plain,
% 15.40/2.49      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
% 15.40/2.49      | ~ r1_tarski(X2,X0) ),
% 15.40/2.49      inference(bin_hyper_res,[status(thm)],[c_6,c_175]) ).
% 15.40/2.49  
% 15.40/2.49  cnf(c_896,plain,
% 15.40/2.49      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) = iProver_top
% 15.40/2.49      | r1_tarski(X2,X0) != iProver_top ),
% 15.40/2.49      inference(predicate_to_equality,[status(thm)],[c_218]) ).
% 15.40/2.49  
% 15.40/2.49  cnf(c_1434,plain,
% 15.40/2.49      ( r1_tarski(X0,X1) != iProver_top
% 15.40/2.49      | r1_tarski(k9_subset_1(X1,X2,X0),X1) = iProver_top ),
% 15.40/2.49      inference(superposition,[status(thm)],[c_896,c_912]) ).
% 15.40/2.49  
% 15.40/2.49  cnf(c_4,plain,
% 15.40/2.49      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 15.40/2.49      inference(cnf_transformation,[],[f48]) ).
% 15.40/2.49  
% 15.40/2.49  cnf(c_915,plain,
% 15.40/2.49      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 15.40/2.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 15.40/2.49  
% 15.40/2.49  cnf(c_2282,plain,
% 15.40/2.49      ( k9_subset_1(k1_xboole_0,X0,X1) = k1_xboole_0
% 15.40/2.49      | r1_tarski(X1,k1_xboole_0) != iProver_top ),
% 15.40/2.49      inference(superposition,[status(thm)],[c_1434,c_915]) ).
% 15.40/2.49  
% 15.40/2.49  cnf(c_2447,plain,
% 15.40/2.49      ( k9_subset_1(k1_xboole_0,X0,k1_xboole_0) = k1_xboole_0 ),
% 15.40/2.49      inference(superposition,[status(thm)],[c_1433,c_2282]) ).
% 15.40/2.49  
% 15.40/2.49  cnf(c_7,plain,
% 15.40/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.40/2.49      | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 15.40/2.49      inference(cnf_transformation,[],[f51]) ).
% 15.40/2.49  
% 15.40/2.49  cnf(c_219,plain,
% 15.40/2.49      ( ~ r1_tarski(X0,X1) | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 15.40/2.49      inference(bin_hyper_res,[status(thm)],[c_7,c_175]) ).
% 15.40/2.49  
% 15.40/2.49  cnf(c_895,plain,
% 15.40/2.49      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
% 15.40/2.49      | r1_tarski(X2,X0) != iProver_top ),
% 15.40/2.49      inference(predicate_to_equality,[status(thm)],[c_219]) ).
% 15.40/2.49  
% 15.40/2.49  cnf(c_1836,plain,
% 15.40/2.49      ( k9_subset_1(X0,X1,k1_xboole_0) = k3_xboole_0(X1,k1_xboole_0) ),
% 15.40/2.49      inference(superposition,[status(thm)],[c_1433,c_895]) ).
% 15.40/2.49  
% 15.40/2.49  cnf(c_2464,plain,
% 15.40/2.49      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 15.40/2.49      inference(superposition,[status(thm)],[c_2447,c_1836]) ).
% 15.40/2.49  
% 15.40/2.49  cnf(c_2551,plain,
% 15.40/2.49      ( k9_subset_1(X0,X1,k1_xboole_0) = k1_xboole_0 ),
% 15.40/2.49      inference(demodulation,[status(thm)],[c_2464,c_1836]) ).
% 15.40/2.49  
% 15.40/2.49  cnf(c_3416,plain,
% 15.40/2.49      ( k9_subset_1(X0,k1_xboole_0,X1) = k1_xboole_0 ),
% 15.40/2.49      inference(light_normalisation,[status(thm)],[c_3406,c_2551]) ).
% 15.40/2.49  
% 15.40/2.49  cnf(c_14,plain,
% 15.40/2.49      ( v2_tex_2(X0,X1)
% 15.40/2.49      | ~ v3_pre_topc(X2,X1)
% 15.40/2.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 15.40/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.40/2.49      | ~ l1_pre_topc(X1)
% 15.40/2.49      | k9_subset_1(u1_struct_0(X1),X0,X2) != sK2(X1,X0) ),
% 15.40/2.49      inference(cnf_transformation,[],[f63]) ).
% 15.40/2.49  
% 15.40/2.49  cnf(c_908,plain,
% 15.40/2.49      ( k9_subset_1(u1_struct_0(X0),X1,X2) != sK2(X0,X1)
% 15.40/2.49      | v2_tex_2(X1,X0) = iProver_top
% 15.40/2.49      | v3_pre_topc(X2,X0) != iProver_top
% 15.40/2.49      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 15.40/2.49      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 15.40/2.49      | l1_pre_topc(X0) != iProver_top ),
% 15.40/2.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 15.40/2.49  
% 15.40/2.49  cnf(c_3584,plain,
% 15.40/2.49      ( sK2(X0,k1_xboole_0) != k1_xboole_0
% 15.40/2.49      | v2_tex_2(k1_xboole_0,X0) = iProver_top
% 15.40/2.49      | v3_pre_topc(X1,X0) != iProver_top
% 15.40/2.49      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 15.40/2.49      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 15.40/2.49      | l1_pre_topc(X0) != iProver_top ),
% 15.40/2.49      inference(superposition,[status(thm)],[c_3416,c_908]) ).
% 15.40/2.49  
% 15.40/2.49  cnf(c_1759,plain,
% 15.40/2.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) ),
% 15.40/2.49      inference(instantiation,[status(thm)],[c_8]) ).
% 15.40/2.49  
% 15.40/2.49  cnf(c_1762,plain,
% 15.40/2.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top ),
% 15.40/2.49      inference(predicate_to_equality,[status(thm)],[c_1759]) ).
% 15.40/2.49  
% 15.40/2.49  cnf(c_15,plain,
% 15.40/2.49      ( v2_tex_2(X0,X1)
% 15.40/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.40/2.49      | r1_tarski(sK2(X1,X0),X0)
% 15.40/2.49      | ~ l1_pre_topc(X1) ),
% 15.40/2.49      inference(cnf_transformation,[],[f62]) ).
% 15.40/2.49  
% 15.40/2.49  cnf(c_907,plain,
% 15.40/2.49      ( v2_tex_2(X0,X1) = iProver_top
% 15.40/2.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 15.40/2.49      | r1_tarski(sK2(X1,X0),X0) = iProver_top
% 15.40/2.49      | l1_pre_topc(X1) != iProver_top ),
% 15.40/2.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 15.40/2.49  
% 15.40/2.49  cnf(c_2653,plain,
% 15.40/2.49      ( v2_tex_2(k1_xboole_0,X0) = iProver_top
% 15.40/2.49      | r1_tarski(sK2(X0,k1_xboole_0),k1_xboole_0) = iProver_top
% 15.40/2.49      | l1_pre_topc(X0) != iProver_top ),
% 15.40/2.49      inference(superposition,[status(thm)],[c_914,c_907]) ).
% 15.40/2.49  
% 15.40/2.49  cnf(c_3898,plain,
% 15.40/2.49      ( sK2(X0,k1_xboole_0) = k1_xboole_0
% 15.40/2.49      | v2_tex_2(k1_xboole_0,X0) = iProver_top
% 15.40/2.49      | l1_pre_topc(X0) != iProver_top ),
% 15.40/2.49      inference(superposition,[status(thm)],[c_2653,c_915]) ).
% 15.40/2.49  
% 15.40/2.49  cnf(c_56498,plain,
% 15.40/2.49      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 15.40/2.49      | v3_pre_topc(X1,X0) != iProver_top
% 15.40/2.49      | v2_tex_2(k1_xboole_0,X0) = iProver_top
% 15.40/2.49      | l1_pre_topc(X0) != iProver_top ),
% 15.40/2.49      inference(global_propositional_subsumption,
% 15.40/2.49                [status(thm)],
% 15.40/2.49                [c_3584,c_1762,c_3898]) ).
% 15.40/2.49  
% 15.40/2.49  cnf(c_56499,plain,
% 15.40/2.49      ( v2_tex_2(k1_xboole_0,X0) = iProver_top
% 15.40/2.49      | v3_pre_topc(X1,X0) != iProver_top
% 15.40/2.49      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 15.40/2.49      | l1_pre_topc(X0) != iProver_top ),
% 15.40/2.49      inference(renaming,[status(thm)],[c_56498]) ).
% 15.40/2.49  
% 15.40/2.49  cnf(c_56510,plain,
% 15.40/2.49      ( v2_tex_2(k1_xboole_0,X0) = iProver_top
% 15.40/2.49      | v3_pre_topc(sK1(X0),X0) != iProver_top
% 15.40/2.49      | v2_pre_topc(X0) != iProver_top
% 15.40/2.49      | l1_pre_topc(X0) != iProver_top ),
% 15.40/2.49      inference(superposition,[status(thm)],[c_909,c_56499]) ).
% 15.40/2.49  
% 15.40/2.49  cnf(c_12,plain,
% 15.40/2.49      ( v3_pre_topc(sK1(X0),X0) | ~ v2_pre_topc(X0) | ~ l1_pre_topc(X0) ),
% 15.40/2.49      inference(cnf_transformation,[],[f57]) ).
% 15.40/2.49  
% 15.40/2.49  cnf(c_51,plain,
% 15.40/2.49      ( v3_pre_topc(sK1(X0),X0) = iProver_top
% 15.40/2.49      | v2_pre_topc(X0) != iProver_top
% 15.40/2.49      | l1_pre_topc(X0) != iProver_top ),
% 15.40/2.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 15.40/2.49  
% 15.40/2.49  cnf(c_57162,plain,
% 15.40/2.49      ( v2_tex_2(k1_xboole_0,X0) = iProver_top
% 15.40/2.49      | v2_pre_topc(X0) != iProver_top
% 15.40/2.49      | l1_pre_topc(X0) != iProver_top ),
% 15.40/2.49      inference(global_propositional_subsumption,
% 15.40/2.49                [status(thm)],
% 15.40/2.49                [c_56510,c_51]) ).
% 15.40/2.49  
% 15.40/2.49  cnf(c_22,negated_conjecture,
% 15.40/2.49      ( v1_xboole_0(sK5) ),
% 15.40/2.49      inference(cnf_transformation,[],[f66]) ).
% 15.40/2.49  
% 15.40/2.49  cnf(c_900,plain,
% 15.40/2.49      ( v1_xboole_0(sK5) = iProver_top ),
% 15.40/2.49      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 15.40/2.49  
% 15.40/2.49  cnf(c_3,plain,
% 15.40/2.49      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 15.40/2.49      inference(cnf_transformation,[],[f47]) ).
% 15.40/2.49  
% 15.40/2.49  cnf(c_916,plain,
% 15.40/2.49      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 15.40/2.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 15.40/2.49  
% 15.40/2.49  cnf(c_1241,plain,
% 15.40/2.49      ( sK5 = k1_xboole_0 ),
% 15.40/2.49      inference(superposition,[status(thm)],[c_900,c_916]) ).
% 15.40/2.49  
% 15.40/2.49  cnf(c_20,negated_conjecture,
% 15.40/2.49      ( ~ v2_tex_2(sK5,sK4) ),
% 15.40/2.49      inference(cnf_transformation,[],[f68]) ).
% 15.40/2.49  
% 15.40/2.49  cnf(c_902,plain,
% 15.40/2.49      ( v2_tex_2(sK5,sK4) != iProver_top ),
% 15.40/2.49      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 15.40/2.49  
% 15.40/2.49  cnf(c_1244,plain,
% 15.40/2.49      ( v2_tex_2(k1_xboole_0,sK4) != iProver_top ),
% 15.40/2.49      inference(demodulation,[status(thm)],[c_1241,c_902]) ).
% 15.40/2.49  
% 15.40/2.49  cnf(c_57171,plain,
% 15.40/2.49      ( v2_pre_topc(sK4) != iProver_top
% 15.40/2.49      | l1_pre_topc(sK4) != iProver_top ),
% 15.40/2.49      inference(superposition,[status(thm)],[c_57162,c_1244]) ).
% 15.40/2.49  
% 15.40/2.49  cnf(c_23,negated_conjecture,
% 15.40/2.49      ( l1_pre_topc(sK4) ),
% 15.40/2.49      inference(cnf_transformation,[],[f65]) ).
% 15.40/2.49  
% 15.40/2.49  cnf(c_26,plain,
% 15.40/2.49      ( l1_pre_topc(sK4) = iProver_top ),
% 15.40/2.49      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 15.40/2.49  
% 15.40/2.49  cnf(c_24,negated_conjecture,
% 15.40/2.49      ( v2_pre_topc(sK4) ),
% 15.40/2.49      inference(cnf_transformation,[],[f64]) ).
% 15.40/2.49  
% 15.40/2.49  cnf(c_25,plain,
% 15.40/2.49      ( v2_pre_topc(sK4) = iProver_top ),
% 15.40/2.49      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 15.40/2.49  
% 15.40/2.49  cnf(contradiction,plain,
% 15.40/2.49      ( $false ),
% 15.40/2.49      inference(minisat,[status(thm)],[c_57171,c_26,c_25]) ).
% 15.40/2.49  
% 15.40/2.49  
% 15.40/2.49  % SZS output end CNFRefutation for theBenchmark.p
% 15.40/2.49  
% 15.40/2.49  ------                               Statistics
% 15.40/2.49  
% 15.40/2.49  ------ Selected
% 15.40/2.49  
% 15.40/2.49  total_time:                             1.533
% 15.40/2.49  
%------------------------------------------------------------------------------
