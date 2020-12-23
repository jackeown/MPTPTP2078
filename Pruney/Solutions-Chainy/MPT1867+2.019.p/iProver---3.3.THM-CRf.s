%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:26:10 EST 2020

% Result     : Theorem 3.15s
% Output     : CNFRefutation 3.15s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 314 expanded)
%              Number of clauses        :   53 ( 104 expanded)
%              Number of leaves         :   15 (  75 expanded)
%              Depth                    :   18
%              Number of atoms          :  340 (1257 expanded)
%              Number of equality atoms :  101 ( 198 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0] :
    ? [X1] :
      ( v1_xboole_0(X1)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( v1_xboole_0(sK1(X0))
        & m1_subset_1(sK1(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( v1_xboole_0(sK1(X0))
      & m1_subset_1(sK1(X0),k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f5,f24])).

fof(f42,plain,(
    ! [X0] : v1_xboole_0(sK1(X0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_xboole_0(X1) )
           => v2_tex_2(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f11,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_xboole_0(X1) )
           => v2_tex_2(X1,X0) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
     => ( ~ v2_tex_2(sK5,X0)
        & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
        & v1_xboole_0(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
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

fof(f34,plain,
    ( ~ v2_tex_2(sK5,sK4)
    & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    & v1_xboole_0(sK5)
    & l1_pre_topc(sK4)
    & v2_pre_topc(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f19,f33,f32])).

fof(f54,plain,(
    v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f34])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f41,plain,(
    ! [X0] : m1_subset_1(sK1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f8,axiom,(
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

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

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
    inference(nnf_transformation,[],[f17])).

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f30,plain,(
    ! [X4,X1,X0] :
      ( ? [X5] :
          ( k9_subset_1(u1_struct_0(X0),X1,X5) = X4
          & v3_pre_topc(X5,X0)
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X0),X1,sK3(X0,X1,X4)) = X4
        & v3_pre_topc(sK3(X0,X1,X4),X0)
        & m1_subset_1(sK3(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
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

fof(f31,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f28,f30,f29])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | r1_tarski(sK2(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f20])).

fof(f37,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f56,plain,(
    ~ v2_tex_2(sK5,sK4) ),
    inference(cnf_transformation,[],[f34])).

fof(f53,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f34])).

fof(f3,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] : m1_subset_1(sK0(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f3,f22])).

fof(f39,plain,(
    ! [X0] : m1_subset_1(sK0(X0),X0) ),
    inference(cnf_transformation,[],[f23])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f51,plain,(
    ! [X0,X3,X1] :
      ( v2_tex_2(X1,X0)
      | k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1)
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v3_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f55,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f34])).

fof(f52,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_6,plain,
    ( v1_xboole_0(sK1(X0)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_907,plain,
    ( v1_xboole_0(sK1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_19,negated_conjecture,
    ( v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_894,plain,
    ( v1_xboole_0(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_909,plain,
    ( X0 = X1
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1809,plain,
    ( sK5 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_894,c_909])).

cnf(c_1909,plain,
    ( sK1(X0) = sK5 ),
    inference(superposition,[status(thm)],[c_907,c_1809])).

cnf(c_7,plain,
    ( m1_subset_1(sK1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_906,plain,
    ( m1_subset_1(sK1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1915,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(X0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1909,c_906])).

cnf(c_12,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(sK2(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_901,plain,
    ( v2_tex_2(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(sK2(X1,X0),X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2389,plain,
    ( v2_tex_2(sK5,X0) = iProver_top
    | r1_tarski(sK2(X0,sK5),sK5) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1915,c_901])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_904,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2070,plain,
    ( r1_tarski(sK5,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1915,c_904])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_911,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2360,plain,
    ( sK5 = X0
    | r1_tarski(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2070,c_911])).

cnf(c_3263,plain,
    ( sK2(X0,sK5) = sK5
    | v2_tex_2(sK5,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2389,c_2360])).

cnf(c_17,negated_conjecture,
    ( ~ v2_tex_2(sK5,sK4) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_896,plain,
    ( v2_tex_2(sK5,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3431,plain,
    ( sK2(sK4,sK5) = sK5
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3263,c_896])).

cnf(c_20,negated_conjecture,
    ( l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_23,plain,
    ( l1_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_26,plain,
    ( v2_tex_2(sK5,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3273,plain,
    ( sK2(sK4,sK5) = sK5
    | v2_tex_2(sK5,sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3263])).

cnf(c_3434,plain,
    ( sK2(sK4,sK5) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3431,c_23,c_26,c_3273])).

cnf(c_4,plain,
    ( m1_subset_1(sK0(X0),X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_908,plain,
    ( m1_subset_1(sK0(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1635,plain,
    ( r1_tarski(sK0(k1_zfmisc_1(X0)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_908,c_904])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X2) = X2 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_8,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_146,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_8])).

cnf(c_147,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_146])).

cnf(c_181,plain,
    ( ~ r1_tarski(X0,X1)
    | k9_subset_1(X1,X2,X2) = X2 ),
    inference(bin_hyper_res,[status(thm)],[c_5,c_147])).

cnf(c_891,plain,
    ( k9_subset_1(X0,X1,X1) = X1
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_181])).

cnf(c_3808,plain,
    ( k9_subset_1(X0,X1,X1) = X1 ),
    inference(superposition,[status(thm)],[c_1635,c_891])).

cnf(c_11,plain,
    ( v2_tex_2(X0,X1)
    | ~ v3_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),X0,X2) != sK2(X1,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_902,plain,
    ( k9_subset_1(u1_struct_0(X0),X1,X2) != sK2(X0,X1)
    | v2_tex_2(X1,X0) = iProver_top
    | v3_pre_topc(X2,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_5509,plain,
    ( sK2(X0,X1) != X1
    | v2_tex_2(X1,X0) = iProver_top
    | v3_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3808,c_902])).

cnf(c_6098,plain,
    ( v2_tex_2(sK5,sK4) = iProver_top
    | v3_pre_topc(sK5,sK4) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3434,c_5509])).

cnf(c_10,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1120,plain,
    ( v3_pre_topc(sK5,X0)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_xboole_0(sK5) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1121,plain,
    ( v3_pre_topc(sK5,X0) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1120])).

cnf(c_1123,plain,
    ( v3_pre_topc(sK5,sK4) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v1_xboole_0(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1121])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_25,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_24,plain,
    ( v1_xboole_0(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_21,negated_conjecture,
    ( v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_22,plain,
    ( v2_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6098,c_1123,c_26,c_25,c_24,c_23,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:12:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.15/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.15/1.00  
% 3.15/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.15/1.00  
% 3.15/1.00  ------  iProver source info
% 3.15/1.00  
% 3.15/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.15/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.15/1.00  git: non_committed_changes: false
% 3.15/1.00  git: last_make_outside_of_git: false
% 3.15/1.00  
% 3.15/1.00  ------ 
% 3.15/1.00  ------ Parsing...
% 3.15/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.15/1.00  
% 3.15/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 3.15/1.00  
% 3.15/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.15/1.00  
% 3.15/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.15/1.00  ------ Proving...
% 3.15/1.00  ------ Problem Properties 
% 3.15/1.00  
% 3.15/1.00  
% 3.15/1.00  clauses                                 21
% 3.15/1.00  conjectures                             5
% 3.15/1.00  EPR                                     7
% 3.15/1.00  Horn                                    19
% 3.15/1.00  unary                                   9
% 3.15/1.00  binary                                  3
% 3.15/1.00  lits                                    58
% 3.15/1.00  lits eq                                 5
% 3.15/1.00  fd_pure                                 0
% 3.15/1.00  fd_pseudo                               0
% 3.15/1.00  fd_cond                                 0
% 3.15/1.00  fd_pseudo_cond                          2
% 3.15/1.00  AC symbols                              0
% 3.15/1.00  
% 3.15/1.00  ------ Input Options Time Limit: Unbounded
% 3.15/1.00  
% 3.15/1.00  
% 3.15/1.00  ------ 
% 3.15/1.00  Current options:
% 3.15/1.00  ------ 
% 3.15/1.00  
% 3.15/1.00  
% 3.15/1.00  
% 3.15/1.00  
% 3.15/1.00  ------ Proving...
% 3.15/1.00  
% 3.15/1.00  
% 3.15/1.00  % SZS status Theorem for theBenchmark.p
% 3.15/1.00  
% 3.15/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.15/1.00  
% 3.15/1.00  fof(f5,axiom,(
% 3.15/1.00    ! [X0] : ? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.15/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.15/1.00  
% 3.15/1.00  fof(f24,plain,(
% 3.15/1.00    ! [X0] : (? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (v1_xboole_0(sK1(X0)) & m1_subset_1(sK1(X0),k1_zfmisc_1(X0))))),
% 3.15/1.00    introduced(choice_axiom,[])).
% 3.15/1.00  
% 3.15/1.00  fof(f25,plain,(
% 3.15/1.00    ! [X0] : (v1_xboole_0(sK1(X0)) & m1_subset_1(sK1(X0),k1_zfmisc_1(X0)))),
% 3.15/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f5,f24])).
% 3.15/1.00  
% 3.15/1.00  fof(f42,plain,(
% 3.15/1.00    ( ! [X0] : (v1_xboole_0(sK1(X0))) )),
% 3.15/1.00    inference(cnf_transformation,[],[f25])).
% 3.15/1.00  
% 3.15/1.00  fof(f9,conjecture,(
% 3.15/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 3.15/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.15/1.00  
% 3.15/1.00  fof(f10,negated_conjecture,(
% 3.15/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 3.15/1.00    inference(negated_conjecture,[],[f9])).
% 3.15/1.00  
% 3.15/1.00  fof(f11,plain,(
% 3.15/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 3.15/1.00    inference(pure_predicate_removal,[],[f10])).
% 3.15/1.00  
% 3.15/1.00  fof(f18,plain,(
% 3.15/1.00    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.15/1.00    inference(ennf_transformation,[],[f11])).
% 3.15/1.00  
% 3.15/1.00  fof(f19,plain,(
% 3.15/1.00    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.15/1.00    inference(flattening,[],[f18])).
% 3.15/1.00  
% 3.15/1.00  fof(f33,plain,(
% 3.15/1.00    ( ! [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => (~v2_tex_2(sK5,X0) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(sK5))) )),
% 3.15/1.00    introduced(choice_axiom,[])).
% 3.15/1.00  
% 3.15/1.00  fof(f32,plain,(
% 3.15/1.00    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (~v2_tex_2(X1,sK4) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) & v1_xboole_0(X1)) & l1_pre_topc(sK4) & v2_pre_topc(sK4))),
% 3.15/1.00    introduced(choice_axiom,[])).
% 3.15/1.00  
% 3.15/1.00  fof(f34,plain,(
% 3.15/1.00    (~v2_tex_2(sK5,sK4) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) & v1_xboole_0(sK5)) & l1_pre_topc(sK4) & v2_pre_topc(sK4)),
% 3.15/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f19,f33,f32])).
% 3.15/1.00  
% 3.15/1.00  fof(f54,plain,(
% 3.15/1.00    v1_xboole_0(sK5)),
% 3.15/1.00    inference(cnf_transformation,[],[f34])).
% 3.15/1.00  
% 3.15/1.00  fof(f2,axiom,(
% 3.15/1.00    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 3.15/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.15/1.00  
% 3.15/1.00  fof(f12,plain,(
% 3.15/1.00    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 3.15/1.00    inference(ennf_transformation,[],[f2])).
% 3.15/1.00  
% 3.15/1.00  fof(f38,plain,(
% 3.15/1.00    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 3.15/1.00    inference(cnf_transformation,[],[f12])).
% 3.15/1.00  
% 3.15/1.00  fof(f41,plain,(
% 3.15/1.00    ( ! [X0] : (m1_subset_1(sK1(X0),k1_zfmisc_1(X0))) )),
% 3.15/1.00    inference(cnf_transformation,[],[f25])).
% 3.15/1.00  
% 3.15/1.00  fof(f8,axiom,(
% 3.15/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0))) & r1_tarski(X2,X1))))))),
% 3.15/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.15/1.00  
% 3.15/1.00  fof(f16,plain,(
% 3.15/1.00    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((? [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.15/1.00    inference(ennf_transformation,[],[f8])).
% 3.15/1.00  
% 3.15/1.00  fof(f17,plain,(
% 3.15/1.00    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.15/1.00    inference(flattening,[],[f16])).
% 3.15/1.00  
% 3.15/1.00  fof(f27,plain,(
% 3.15/1.00    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.15/1.00    inference(nnf_transformation,[],[f17])).
% 3.15/1.00  
% 3.15/1.00  fof(f28,plain,(
% 3.15/1.00    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (? [X5] : (k9_subset_1(u1_struct_0(X0),X1,X5) = X4 & v3_pre_topc(X5,X0) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.15/1.00    inference(rectify,[],[f27])).
% 3.15/1.00  
% 3.15/1.00  fof(f30,plain,(
% 3.15/1.00    ! [X4,X1,X0] : (? [X5] : (k9_subset_1(u1_struct_0(X0),X1,X5) = X4 & v3_pre_topc(X5,X0) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) => (k9_subset_1(u1_struct_0(X0),X1,sK3(X0,X1,X4)) = X4 & v3_pre_topc(sK3(X0,X1,X4),X0) & m1_subset_1(sK3(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.15/1.00    introduced(choice_axiom,[])).
% 3.15/1.00  
% 3.15/1.00  fof(f29,plain,(
% 3.15/1.00    ! [X1,X0] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(sK2(X0,X1),X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.15/1.00    introduced(choice_axiom,[])).
% 3.15/1.00  
% 3.15/1.00  fof(f31,plain,(
% 3.15/1.00    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(sK2(X0,X1),X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : ((k9_subset_1(u1_struct_0(X0),X1,sK3(X0,X1,X4)) = X4 & v3_pre_topc(sK3(X0,X1,X4),X0) & m1_subset_1(sK3(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.15/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f28,f30,f29])).
% 3.15/1.00  
% 3.15/1.00  fof(f50,plain,(
% 3.15/1.00    ( ! [X0,X1] : (v2_tex_2(X1,X0) | r1_tarski(sK2(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.15/1.00    inference(cnf_transformation,[],[f31])).
% 3.15/1.00  
% 3.15/1.00  fof(f6,axiom,(
% 3.15/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.15/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.15/1.00  
% 3.15/1.00  fof(f26,plain,(
% 3.15/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.15/1.00    inference(nnf_transformation,[],[f6])).
% 3.15/1.00  
% 3.15/1.00  fof(f43,plain,(
% 3.15/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.15/1.00    inference(cnf_transformation,[],[f26])).
% 3.15/1.00  
% 3.15/1.00  fof(f1,axiom,(
% 3.15/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.15/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.15/1.00  
% 3.15/1.00  fof(f20,plain,(
% 3.15/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.15/1.00    inference(nnf_transformation,[],[f1])).
% 3.15/1.00  
% 3.15/1.00  fof(f21,plain,(
% 3.15/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.15/1.00    inference(flattening,[],[f20])).
% 3.15/1.00  
% 3.15/1.00  fof(f37,plain,(
% 3.15/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.15/1.00    inference(cnf_transformation,[],[f21])).
% 3.15/1.00  
% 3.15/1.00  fof(f56,plain,(
% 3.15/1.00    ~v2_tex_2(sK5,sK4)),
% 3.15/1.00    inference(cnf_transformation,[],[f34])).
% 3.15/1.00  
% 3.15/1.00  fof(f53,plain,(
% 3.15/1.00    l1_pre_topc(sK4)),
% 3.15/1.00    inference(cnf_transformation,[],[f34])).
% 3.15/1.00  
% 3.15/1.00  fof(f3,axiom,(
% 3.15/1.00    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 3.15/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.15/1.00  
% 3.15/1.00  fof(f22,plain,(
% 3.15/1.00    ! [X0] : (? [X1] : m1_subset_1(X1,X0) => m1_subset_1(sK0(X0),X0))),
% 3.15/1.00    introduced(choice_axiom,[])).
% 3.15/1.00  
% 3.15/1.00  fof(f23,plain,(
% 3.15/1.00    ! [X0] : m1_subset_1(sK0(X0),X0)),
% 3.15/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f3,f22])).
% 3.15/1.00  
% 3.15/1.00  fof(f39,plain,(
% 3.15/1.00    ( ! [X0] : (m1_subset_1(sK0(X0),X0)) )),
% 3.15/1.00    inference(cnf_transformation,[],[f23])).
% 3.15/1.00  
% 3.15/1.00  fof(f4,axiom,(
% 3.15/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X1) = X1)),
% 3.15/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.15/1.00  
% 3.15/1.00  fof(f13,plain,(
% 3.15/1.00    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 3.15/1.00    inference(ennf_transformation,[],[f4])).
% 3.15/1.00  
% 3.15/1.00  fof(f40,plain,(
% 3.15/1.00    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.15/1.00    inference(cnf_transformation,[],[f13])).
% 3.15/1.00  
% 3.15/1.00  fof(f44,plain,(
% 3.15/1.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.15/1.00    inference(cnf_transformation,[],[f26])).
% 3.15/1.00  
% 3.15/1.00  fof(f51,plain,(
% 3.15/1.00    ( ! [X0,X3,X1] : (v2_tex_2(X1,X0) | k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.15/1.00    inference(cnf_transformation,[],[f31])).
% 3.15/1.00  
% 3.15/1.00  fof(f7,axiom,(
% 3.15/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_xboole_0(X1) => v3_pre_topc(X1,X0))))),
% 3.15/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.15/1.00  
% 3.15/1.00  fof(f14,plain,(
% 3.15/1.00    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) | ~v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.15/1.00    inference(ennf_transformation,[],[f7])).
% 3.15/1.00  
% 3.15/1.00  fof(f15,plain,(
% 3.15/1.00    ! [X0] : (! [X1] : (v3_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.15/1.00    inference(flattening,[],[f14])).
% 3.15/1.00  
% 3.15/1.00  fof(f45,plain,(
% 3.15/1.00    ( ! [X0,X1] : (v3_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.15/1.00    inference(cnf_transformation,[],[f15])).
% 3.15/1.00  
% 3.15/1.00  fof(f55,plain,(
% 3.15/1.00    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))),
% 3.15/1.00    inference(cnf_transformation,[],[f34])).
% 3.15/1.00  
% 3.15/1.00  fof(f52,plain,(
% 3.15/1.00    v2_pre_topc(sK4)),
% 3.15/1.00    inference(cnf_transformation,[],[f34])).
% 3.15/1.00  
% 3.15/1.00  cnf(c_6,plain,
% 3.15/1.00      ( v1_xboole_0(sK1(X0)) ),
% 3.15/1.00      inference(cnf_transformation,[],[f42]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_907,plain,
% 3.15/1.00      ( v1_xboole_0(sK1(X0)) = iProver_top ),
% 3.15/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_19,negated_conjecture,
% 3.15/1.00      ( v1_xboole_0(sK5) ),
% 3.15/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_894,plain,
% 3.15/1.00      ( v1_xboole_0(sK5) = iProver_top ),
% 3.15/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_3,plain,
% 3.15/1.00      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X0 = X1 ),
% 3.15/1.00      inference(cnf_transformation,[],[f38]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_909,plain,
% 3.15/1.00      ( X0 = X1
% 3.15/1.00      | v1_xboole_0(X0) != iProver_top
% 3.15/1.00      | v1_xboole_0(X1) != iProver_top ),
% 3.15/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_1809,plain,
% 3.15/1.00      ( sK5 = X0 | v1_xboole_0(X0) != iProver_top ),
% 3.15/1.00      inference(superposition,[status(thm)],[c_894,c_909]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_1909,plain,
% 3.15/1.00      ( sK1(X0) = sK5 ),
% 3.15/1.00      inference(superposition,[status(thm)],[c_907,c_1809]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_7,plain,
% 3.15/1.00      ( m1_subset_1(sK1(X0),k1_zfmisc_1(X0)) ),
% 3.15/1.00      inference(cnf_transformation,[],[f41]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_906,plain,
% 3.15/1.00      ( m1_subset_1(sK1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 3.15/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_1915,plain,
% 3.15/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(X0)) = iProver_top ),
% 3.15/1.00      inference(demodulation,[status(thm)],[c_1909,c_906]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_12,plain,
% 3.15/1.00      ( v2_tex_2(X0,X1)
% 3.15/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.15/1.00      | r1_tarski(sK2(X1,X0),X0)
% 3.15/1.00      | ~ l1_pre_topc(X1) ),
% 3.15/1.00      inference(cnf_transformation,[],[f50]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_901,plain,
% 3.15/1.00      ( v2_tex_2(X0,X1) = iProver_top
% 3.15/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.15/1.00      | r1_tarski(sK2(X1,X0),X0) = iProver_top
% 3.15/1.00      | l1_pre_topc(X1) != iProver_top ),
% 3.15/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_2389,plain,
% 3.15/1.00      ( v2_tex_2(sK5,X0) = iProver_top
% 3.15/1.00      | r1_tarski(sK2(X0,sK5),sK5) = iProver_top
% 3.15/1.00      | l1_pre_topc(X0) != iProver_top ),
% 3.15/1.00      inference(superposition,[status(thm)],[c_1915,c_901]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_9,plain,
% 3.15/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.15/1.00      inference(cnf_transformation,[],[f43]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_904,plain,
% 3.15/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.15/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.15/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_2070,plain,
% 3.15/1.00      ( r1_tarski(sK5,X0) = iProver_top ),
% 3.15/1.00      inference(superposition,[status(thm)],[c_1915,c_904]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_0,plain,
% 3.15/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.15/1.00      inference(cnf_transformation,[],[f37]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_911,plain,
% 3.15/1.00      ( X0 = X1
% 3.15/1.00      | r1_tarski(X0,X1) != iProver_top
% 3.15/1.00      | r1_tarski(X1,X0) != iProver_top ),
% 3.15/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_2360,plain,
% 3.15/1.00      ( sK5 = X0 | r1_tarski(X0,sK5) != iProver_top ),
% 3.15/1.00      inference(superposition,[status(thm)],[c_2070,c_911]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_3263,plain,
% 3.15/1.00      ( sK2(X0,sK5) = sK5
% 3.15/1.00      | v2_tex_2(sK5,X0) = iProver_top
% 3.15/1.00      | l1_pre_topc(X0) != iProver_top ),
% 3.15/1.00      inference(superposition,[status(thm)],[c_2389,c_2360]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_17,negated_conjecture,
% 3.15/1.00      ( ~ v2_tex_2(sK5,sK4) ),
% 3.15/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_896,plain,
% 3.15/1.00      ( v2_tex_2(sK5,sK4) != iProver_top ),
% 3.15/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_3431,plain,
% 3.15/1.00      ( sK2(sK4,sK5) = sK5 | l1_pre_topc(sK4) != iProver_top ),
% 3.15/1.00      inference(superposition,[status(thm)],[c_3263,c_896]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_20,negated_conjecture,
% 3.15/1.00      ( l1_pre_topc(sK4) ),
% 3.15/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_23,plain,
% 3.15/1.00      ( l1_pre_topc(sK4) = iProver_top ),
% 3.15/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_26,plain,
% 3.15/1.00      ( v2_tex_2(sK5,sK4) != iProver_top ),
% 3.15/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_3273,plain,
% 3.15/1.00      ( sK2(sK4,sK5) = sK5
% 3.15/1.00      | v2_tex_2(sK5,sK4) = iProver_top
% 3.15/1.00      | l1_pre_topc(sK4) != iProver_top ),
% 3.15/1.00      inference(instantiation,[status(thm)],[c_3263]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_3434,plain,
% 3.15/1.00      ( sK2(sK4,sK5) = sK5 ),
% 3.15/1.00      inference(global_propositional_subsumption,
% 3.15/1.00                [status(thm)],
% 3.15/1.00                [c_3431,c_23,c_26,c_3273]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_4,plain,
% 3.15/1.00      ( m1_subset_1(sK0(X0),X0) ),
% 3.15/1.00      inference(cnf_transformation,[],[f39]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_908,plain,
% 3.15/1.00      ( m1_subset_1(sK0(X0),X0) = iProver_top ),
% 3.15/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_1635,plain,
% 3.15/1.00      ( r1_tarski(sK0(k1_zfmisc_1(X0)),X0) = iProver_top ),
% 3.15/1.00      inference(superposition,[status(thm)],[c_908,c_904]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_5,plain,
% 3.15/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | k9_subset_1(X1,X2,X2) = X2 ),
% 3.15/1.00      inference(cnf_transformation,[],[f40]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_8,plain,
% 3.15/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.15/1.00      inference(cnf_transformation,[],[f44]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_146,plain,
% 3.15/1.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.15/1.00      inference(prop_impl,[status(thm)],[c_8]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_147,plain,
% 3.15/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.15/1.00      inference(renaming,[status(thm)],[c_146]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_181,plain,
% 3.15/1.00      ( ~ r1_tarski(X0,X1) | k9_subset_1(X1,X2,X2) = X2 ),
% 3.15/1.00      inference(bin_hyper_res,[status(thm)],[c_5,c_147]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_891,plain,
% 3.15/1.00      ( k9_subset_1(X0,X1,X1) = X1 | r1_tarski(X2,X0) != iProver_top ),
% 3.15/1.00      inference(predicate_to_equality,[status(thm)],[c_181]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_3808,plain,
% 3.15/1.00      ( k9_subset_1(X0,X1,X1) = X1 ),
% 3.15/1.00      inference(superposition,[status(thm)],[c_1635,c_891]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_11,plain,
% 3.15/1.00      ( v2_tex_2(X0,X1)
% 3.15/1.00      | ~ v3_pre_topc(X2,X1)
% 3.15/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.15/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.15/1.00      | ~ l1_pre_topc(X1)
% 3.15/1.00      | k9_subset_1(u1_struct_0(X1),X0,X2) != sK2(X1,X0) ),
% 3.15/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_902,plain,
% 3.15/1.00      ( k9_subset_1(u1_struct_0(X0),X1,X2) != sK2(X0,X1)
% 3.15/1.00      | v2_tex_2(X1,X0) = iProver_top
% 3.15/1.00      | v3_pre_topc(X2,X0) != iProver_top
% 3.15/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.15/1.00      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.15/1.00      | l1_pre_topc(X0) != iProver_top ),
% 3.15/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_5509,plain,
% 3.15/1.00      ( sK2(X0,X1) != X1
% 3.15/1.00      | v2_tex_2(X1,X0) = iProver_top
% 3.15/1.00      | v3_pre_topc(X1,X0) != iProver_top
% 3.15/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.15/1.00      | l1_pre_topc(X0) != iProver_top ),
% 3.15/1.00      inference(superposition,[status(thm)],[c_3808,c_902]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_6098,plain,
% 3.15/1.00      ( v2_tex_2(sK5,sK4) = iProver_top
% 3.15/1.00      | v3_pre_topc(sK5,sK4) != iProver_top
% 3.15/1.00      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.15/1.00      | l1_pre_topc(sK4) != iProver_top ),
% 3.15/1.00      inference(superposition,[status(thm)],[c_3434,c_5509]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_10,plain,
% 3.15/1.00      ( v3_pre_topc(X0,X1)
% 3.15/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.15/1.00      | ~ v2_pre_topc(X1)
% 3.15/1.00      | ~ l1_pre_topc(X1)
% 3.15/1.00      | ~ v1_xboole_0(X0) ),
% 3.15/1.00      inference(cnf_transformation,[],[f45]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_1120,plain,
% 3.15/1.00      ( v3_pre_topc(sK5,X0)
% 3.15/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
% 3.15/1.00      | ~ v2_pre_topc(X0)
% 3.15/1.00      | ~ l1_pre_topc(X0)
% 3.15/1.00      | ~ v1_xboole_0(sK5) ),
% 3.15/1.00      inference(instantiation,[status(thm)],[c_10]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_1121,plain,
% 3.15/1.00      ( v3_pre_topc(sK5,X0) = iProver_top
% 3.15/1.00      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.15/1.00      | v2_pre_topc(X0) != iProver_top
% 3.15/1.00      | l1_pre_topc(X0) != iProver_top
% 3.15/1.00      | v1_xboole_0(sK5) != iProver_top ),
% 3.15/1.00      inference(predicate_to_equality,[status(thm)],[c_1120]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_1123,plain,
% 3.15/1.00      ( v3_pre_topc(sK5,sK4) = iProver_top
% 3.15/1.00      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.15/1.00      | v2_pre_topc(sK4) != iProver_top
% 3.15/1.00      | l1_pre_topc(sK4) != iProver_top
% 3.15/1.00      | v1_xboole_0(sK5) != iProver_top ),
% 3.15/1.00      inference(instantiation,[status(thm)],[c_1121]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_18,negated_conjecture,
% 3.15/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 3.15/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_25,plain,
% 3.15/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 3.15/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_24,plain,
% 3.15/1.00      ( v1_xboole_0(sK5) = iProver_top ),
% 3.15/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_21,negated_conjecture,
% 3.15/1.00      ( v2_pre_topc(sK4) ),
% 3.15/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_22,plain,
% 3.15/1.00      ( v2_pre_topc(sK4) = iProver_top ),
% 3.15/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(contradiction,plain,
% 3.15/1.00      ( $false ),
% 3.15/1.00      inference(minisat,
% 3.15/1.00                [status(thm)],
% 3.15/1.00                [c_6098,c_1123,c_26,c_25,c_24,c_23,c_22]) ).
% 3.15/1.00  
% 3.15/1.00  
% 3.15/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.15/1.00  
% 3.15/1.00  ------                               Statistics
% 3.15/1.00  
% 3.15/1.00  ------ Selected
% 3.15/1.00  
% 3.15/1.00  total_time:                             0.174
% 3.15/1.00  
%------------------------------------------------------------------------------
