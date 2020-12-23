%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:26:13 EST 2020

% Result     : Theorem 3.69s
% Output     : CNFRefutation 3.69s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 427 expanded)
%              Number of clauses        :   69 ( 133 expanded)
%              Number of leaves         :   15 ( 101 expanded)
%              Depth                    :   18
%              Number of atoms          :  374 (1763 expanded)
%              Number of equality atoms :  102 ( 201 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ? [X0] : v1_xboole_0(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,
    ( ? [X0] : v1_xboole_0(X0)
   => v1_xboole_0(sK0) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f1,f32])).

fof(f54,plain,(
    v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_xboole_0(X1) )
           => v2_tex_2(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f18,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_xboole_0(X1) )
           => v2_tex_2(X1,X0) ) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f52,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
     => ( ~ v2_tex_2(sK7,X0)
        & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X0)))
        & v1_xboole_0(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v2_tex_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ v2_tex_2(X1,sK6)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(sK6)
      & v2_pre_topc(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( ~ v2_tex_2(sK7,sK6)
    & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    & v1_xboole_0(sK7)
    & l1_pre_topc(sK6)
    & v2_pre_topc(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f31,f52,f51])).

fof(f84,plain,(
    v1_xboole_0(sK7) ),
    inference(cnf_transformation,[],[f53])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f85,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f53])).

fof(f15,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f47,plain,(
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
    inference(rectify,[],[f46])).

fof(f49,plain,(
    ! [X4,X1,X0] :
      ( ? [X5] :
          ( k9_subset_1(u1_struct_0(X0),X1,X5) = X4
          & v4_pre_topc(X5,X0)
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X0),X1,sK5(X0,X1,X4)) = X4
        & v4_pre_topc(sK5(X0,X1,X4),X0)
        & m1_subset_1(sK5(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
              | ~ v4_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ! [X3] :
            ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK4(X0,X1)
            | ~ v4_pre_topc(X3,X0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & r1_tarski(sK4(X0,X1),X1)
        & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ( ! [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK4(X0,X1)
                    | ~ v4_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & r1_tarski(sK4(X0,X1),X1)
                & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X4] :
                  ( ( k9_subset_1(u1_struct_0(X0),X1,sK5(X0,X1,X4)) = X4
                    & v4_pre_topc(sK5(X0,X1,X4),X0)
                    & m1_subset_1(sK5(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r1_tarski(X4,X1)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f47,f49,f48])).

fof(f80,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | r1_tarski(sK4(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f83,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f53])).

fof(f86,plain,(
    ~ v2_tex_2(sK7,sK6) ),
    inference(cnf_transformation,[],[f53])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f37])).

fof(f59,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f10,axiom,(
    ! [X0] :
    ? [X1] :
      ( v1_xboole_0(X1)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( v1_xboole_0(sK3(X0))
        & m1_subset_1(sK3(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( v1_xboole_0(sK3(X0))
      & m1_subset_1(sK3(X0),k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f10,f43])).

fof(f69,plain,(
    ! [X0] : m1_subset_1(sK3(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f44])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f70,plain,(
    ! [X0] : v1_xboole_0(sK3(X0)) ),
    inference(cnf_transformation,[],[f44])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f72,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f88,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f57])).

fof(f81,plain,(
    ! [X0,X3,X1] :
      ( v2_tex_2(X1,X0)
      | k9_subset_1(u1_struct_0(X0),X1,X3) != sK4(X0,X1)
      | ~ v4_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f75,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f82,plain,(
    v2_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_0,plain,
    ( v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2346,plain,
    ( v1_xboole_0(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_30,negated_conjecture,
    ( v1_xboole_0(sK7) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_2326,plain,
    ( v1_xboole_0(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_7,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2340,plain,
    ( X0 = X1
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_5504,plain,
    ( sK7 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2326,c_2340])).

cnf(c_5680,plain,
    ( sK7 = sK0 ),
    inference(superposition,[status(thm)],[c_2346,c_5504])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_2327,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_23,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(sK4(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_31,negated_conjecture,
    ( l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_593,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(sK4(X1,X0),X0)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_31])).

cnf(c_594,plain,
    ( v2_tex_2(X0,sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | r1_tarski(sK4(sK6,X0),X0) ),
    inference(unflattening,[status(thm)],[c_593])).

cnf(c_2319,plain,
    ( v2_tex_2(X0,sK6) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r1_tarski(sK4(sK6,X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_594])).

cnf(c_2884,plain,
    ( v2_tex_2(sK7,sK6) = iProver_top
    | r1_tarski(sK4(sK6,sK7),sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_2327,c_2319])).

cnf(c_36,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_28,negated_conjecture,
    ( ~ v2_tex_2(sK7,sK6) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_939,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | r1_tarski(sK4(sK6,X0),X0)
    | sK6 != sK6
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_594])).

cnf(c_940,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | r1_tarski(sK4(sK6,sK7),sK7) ),
    inference(unflattening,[status(thm)],[c_939])).

cnf(c_941,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r1_tarski(sK4(sK6,sK7),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_940])).

cnf(c_3247,plain,
    ( r1_tarski(sK4(sK6,sK7),sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2884,c_36,c_941])).

cnf(c_5882,plain,
    ( r1_tarski(sK4(sK6,sK0),sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5680,c_3247])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2343,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_6893,plain,
    ( sK4(sK6,sK0) = sK0
    | r1_tarski(sK0,sK4(sK6,sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5882,c_2343])).

cnf(c_16,plain,
    ( m1_subset_1(sK3(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_2333,plain,
    ( m1_subset_1(sK3(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2331,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_4979,plain,
    ( r1_tarski(sK3(X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2333,c_2331])).

cnf(c_15,plain,
    ( v1_xboole_0(sK3(X0)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2334,plain,
    ( v1_xboole_0(sK3(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_5681,plain,
    ( sK3(X0) = sK7 ),
    inference(superposition,[status(thm)],[c_2334,c_5504])).

cnf(c_6189,plain,
    ( sK3(X0) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_5681,c_5680])).

cnf(c_7319,plain,
    ( r1_tarski(sK0,X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4979,c_6189])).

cnf(c_10534,plain,
    ( sK4(sK6,sK0) = sK0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6893,c_7319])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X2) = X2 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_17,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_251,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_17])).

cnf(c_252,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_251])).

cnf(c_305,plain,
    ( ~ r1_tarski(X0,X1)
    | k9_subset_1(X1,X2,X2) = X2 ),
    inference(bin_hyper_res,[status(thm)],[c_14,c_252])).

cnf(c_2325,plain,
    ( k9_subset_1(X0,X1,X1) = X1
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_305])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_11112,plain,
    ( k9_subset_1(X0,X1,X1) = X1 ),
    inference(resolution,[status(thm)],[c_305,c_5])).

cnf(c_15120,plain,
    ( k9_subset_1(X0,X1,X1) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2325,c_11112])).

cnf(c_22,plain,
    ( v2_tex_2(X0,X1)
    | ~ v4_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),X0,X2) != sK4(X1,X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_608,plain,
    ( v2_tex_2(X0,X1)
    | ~ v4_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | k9_subset_1(u1_struct_0(X1),X0,X2) != sK4(X1,X0)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_31])).

cnf(c_609,plain,
    ( v2_tex_2(X0,sK6)
    | ~ v4_pre_topc(X1,sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))
    | k9_subset_1(u1_struct_0(sK6),X0,X1) != sK4(sK6,X0) ),
    inference(unflattening,[status(thm)],[c_608])).

cnf(c_2318,plain,
    ( k9_subset_1(u1_struct_0(sK6),X0,X1) != sK4(sK6,X0)
    | v2_tex_2(X0,sK6) = iProver_top
    | v4_pre_topc(X1,sK6) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_609])).

cnf(c_15123,plain,
    ( sK4(sK6,X0) != X0
    | v2_tex_2(X0,sK6) = iProver_top
    | v4_pre_topc(X0,sK6) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
    inference(superposition,[status(thm)],[c_15120,c_2318])).

cnf(c_15361,plain,
    ( v2_tex_2(sK0,sK6) = iProver_top
    | v4_pre_topc(sK0,sK6) != iProver_top
    | m1_subset_1(sK0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
    inference(superposition,[status(thm)],[c_10534,c_15123])).

cnf(c_2328,plain,
    ( v2_tex_2(sK7,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_5885,plain,
    ( v2_tex_2(sK0,sK6) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5680,c_2328])).

cnf(c_5884,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5680,c_2327])).

cnf(c_21,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_32,negated_conjecture,
    ( v2_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_419,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(X0)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_32])).

cnf(c_420,plain,
    ( v4_pre_topc(X0,sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ l1_pre_topc(sK6)
    | ~ v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_419])).

cnf(c_424,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | v4_pre_topc(X0,sK6)
    | ~ v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_420,c_31])).

cnf(c_425,plain,
    ( v4_pre_topc(X0,sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_424])).

cnf(c_2324,plain,
    ( v4_pre_topc(X0,sK6) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_425])).

cnf(c_2646,plain,
    ( v4_pre_topc(sK7,sK6) = iProver_top
    | v1_xboole_0(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2327,c_2324])).

cnf(c_35,plain,
    ( v1_xboole_0(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_2567,plain,
    ( v4_pre_topc(sK7,sK6)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ v1_xboole_0(sK7) ),
    inference(instantiation,[status(thm)],[c_425])).

cnf(c_2568,plain,
    ( v4_pre_topc(sK7,sK6) = iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | v1_xboole_0(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2567])).

cnf(c_2700,plain,
    ( v4_pre_topc(sK7,sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2646,c_35,c_36,c_2568])).

cnf(c_5883,plain,
    ( v4_pre_topc(sK0,sK6) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5680,c_2700])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_15361,c_5885,c_5884,c_5883])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:34:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.69/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.69/0.99  
% 3.69/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.69/0.99  
% 3.69/0.99  ------  iProver source info
% 3.69/0.99  
% 3.69/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.69/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.69/0.99  git: non_committed_changes: false
% 3.69/0.99  git: last_make_outside_of_git: false
% 3.69/0.99  
% 3.69/0.99  ------ 
% 3.69/0.99  ------ Parsing...
% 3.69/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.69/0.99  
% 3.69/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.69/0.99  
% 3.69/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.69/0.99  
% 3.69/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.69/0.99  ------ Proving...
% 3.69/0.99  ------ Problem Properties 
% 3.69/0.99  
% 3.69/0.99  
% 3.69/0.99  clauses                                 30
% 3.69/0.99  conjectures                             3
% 3.69/0.99  EPR                                     7
% 3.69/0.99  Horn                                    26
% 3.69/0.99  unary                                   10
% 3.69/0.99  binary                                  6
% 3.69/0.99  lits                                    72
% 3.69/0.99  lits eq                                 14
% 3.69/0.99  fd_pure                                 0
% 3.69/0.99  fd_pseudo                               0
% 3.69/0.99  fd_cond                                 0
% 3.69/0.99  fd_pseudo_cond                          6
% 3.69/0.99  AC symbols                              0
% 3.69/0.99  
% 3.69/0.99  ------ Input Options Time Limit: Unbounded
% 3.69/0.99  
% 3.69/0.99  
% 3.69/0.99  ------ 
% 3.69/0.99  Current options:
% 3.69/0.99  ------ 
% 3.69/0.99  
% 3.69/0.99  
% 3.69/0.99  
% 3.69/0.99  
% 3.69/0.99  ------ Proving...
% 3.69/0.99  
% 3.69/0.99  
% 3.69/0.99  % SZS status Theorem for theBenchmark.p
% 3.69/0.99  
% 3.69/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.69/0.99  
% 3.69/0.99  fof(f1,axiom,(
% 3.69/0.99    ? [X0] : v1_xboole_0(X0)),
% 3.69/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/0.99  
% 3.69/0.99  fof(f32,plain,(
% 3.69/0.99    ? [X0] : v1_xboole_0(X0) => v1_xboole_0(sK0)),
% 3.69/0.99    introduced(choice_axiom,[])).
% 3.69/0.99  
% 3.69/0.99  fof(f33,plain,(
% 3.69/0.99    v1_xboole_0(sK0)),
% 3.69/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f1,f32])).
% 3.69/0.99  
% 3.69/0.99  fof(f54,plain,(
% 3.69/0.99    v1_xboole_0(sK0)),
% 3.69/0.99    inference(cnf_transformation,[],[f33])).
% 3.69/0.99  
% 3.69/0.99  fof(f16,conjecture,(
% 3.69/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 3.69/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/0.99  
% 3.69/0.99  fof(f17,negated_conjecture,(
% 3.69/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 3.69/0.99    inference(negated_conjecture,[],[f16])).
% 3.69/0.99  
% 3.69/0.99  fof(f18,plain,(
% 3.69/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 3.69/0.99    inference(pure_predicate_removal,[],[f17])).
% 3.69/0.99  
% 3.69/0.99  fof(f30,plain,(
% 3.69/0.99    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.69/0.99    inference(ennf_transformation,[],[f18])).
% 3.69/0.99  
% 3.69/0.99  fof(f31,plain,(
% 3.69/0.99    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.69/0.99    inference(flattening,[],[f30])).
% 3.69/0.99  
% 3.69/0.99  fof(f52,plain,(
% 3.69/0.99    ( ! [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => (~v2_tex_2(sK7,X0) & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(sK7))) )),
% 3.69/0.99    introduced(choice_axiom,[])).
% 3.69/0.99  
% 3.69/0.99  fof(f51,plain,(
% 3.69/0.99    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (~v2_tex_2(X1,sK6) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) & v1_xboole_0(X1)) & l1_pre_topc(sK6) & v2_pre_topc(sK6))),
% 3.69/0.99    introduced(choice_axiom,[])).
% 3.69/0.99  
% 3.69/0.99  fof(f53,plain,(
% 3.69/0.99    (~v2_tex_2(sK7,sK6) & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) & v1_xboole_0(sK7)) & l1_pre_topc(sK6) & v2_pre_topc(sK6)),
% 3.69/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f31,f52,f51])).
% 3.69/0.99  
% 3.69/0.99  fof(f84,plain,(
% 3.69/0.99    v1_xboole_0(sK7)),
% 3.69/0.99    inference(cnf_transformation,[],[f53])).
% 3.69/0.99  
% 3.69/0.99  fof(f5,axiom,(
% 3.69/0.99    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 3.69/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/0.99  
% 3.69/0.99  fof(f21,plain,(
% 3.69/0.99    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 3.69/0.99    inference(ennf_transformation,[],[f5])).
% 3.69/0.99  
% 3.69/0.99  fof(f61,plain,(
% 3.69/0.99    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 3.69/0.99    inference(cnf_transformation,[],[f21])).
% 3.69/0.99  
% 3.69/0.99  fof(f85,plain,(
% 3.69/0.99    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))),
% 3.69/0.99    inference(cnf_transformation,[],[f53])).
% 3.69/0.99  
% 3.69/0.99  fof(f15,axiom,(
% 3.69/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0))) & r1_tarski(X2,X1))))))),
% 3.69/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/0.99  
% 3.69/0.99  fof(f28,plain,(
% 3.69/0.99    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((? [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.69/0.99    inference(ennf_transformation,[],[f15])).
% 3.69/0.99  
% 3.69/0.99  fof(f29,plain,(
% 3.69/0.99    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.69/0.99    inference(flattening,[],[f28])).
% 3.69/0.99  
% 3.69/0.99  fof(f46,plain,(
% 3.69/0.99    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.69/0.99    inference(nnf_transformation,[],[f29])).
% 3.69/0.99  
% 3.69/0.99  fof(f47,plain,(
% 3.69/0.99    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (? [X5] : (k9_subset_1(u1_struct_0(X0),X1,X5) = X4 & v4_pre_topc(X5,X0) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.69/0.99    inference(rectify,[],[f46])).
% 3.69/0.99  
% 3.69/0.99  fof(f49,plain,(
% 3.69/0.99    ! [X4,X1,X0] : (? [X5] : (k9_subset_1(u1_struct_0(X0),X1,X5) = X4 & v4_pre_topc(X5,X0) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) => (k9_subset_1(u1_struct_0(X0),X1,sK5(X0,X1,X4)) = X4 & v4_pre_topc(sK5(X0,X1,X4),X0) & m1_subset_1(sK5(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.69/0.99    introduced(choice_axiom,[])).
% 3.69/0.99  
% 3.69/0.99  fof(f48,plain,(
% 3.69/0.99    ! [X1,X0] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK4(X0,X1) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(sK4(X0,X1),X1) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.69/0.99    introduced(choice_axiom,[])).
% 3.69/0.99  
% 3.69/0.99  fof(f50,plain,(
% 3.69/0.99    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK4(X0,X1) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(sK4(X0,X1),X1) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : ((k9_subset_1(u1_struct_0(X0),X1,sK5(X0,X1,X4)) = X4 & v4_pre_topc(sK5(X0,X1,X4),X0) & m1_subset_1(sK5(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.69/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f47,f49,f48])).
% 3.69/0.99  
% 3.69/0.99  fof(f80,plain,(
% 3.69/0.99    ( ! [X0,X1] : (v2_tex_2(X1,X0) | r1_tarski(sK4(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.69/0.99    inference(cnf_transformation,[],[f50])).
% 3.69/0.99  
% 3.69/0.99  fof(f83,plain,(
% 3.69/0.99    l1_pre_topc(sK6)),
% 3.69/0.99    inference(cnf_transformation,[],[f53])).
% 3.69/0.99  
% 3.69/0.99  fof(f86,plain,(
% 3.69/0.99    ~v2_tex_2(sK7,sK6)),
% 3.69/0.99    inference(cnf_transformation,[],[f53])).
% 3.69/0.99  
% 3.69/0.99  fof(f3,axiom,(
% 3.69/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.69/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/0.99  
% 3.69/0.99  fof(f37,plain,(
% 3.69/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.69/0.99    inference(nnf_transformation,[],[f3])).
% 3.69/0.99  
% 3.69/0.99  fof(f38,plain,(
% 3.69/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.69/0.99    inference(flattening,[],[f37])).
% 3.69/0.99  
% 3.69/0.99  fof(f59,plain,(
% 3.69/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.69/0.99    inference(cnf_transformation,[],[f38])).
% 3.69/0.99  
% 3.69/0.99  fof(f10,axiom,(
% 3.69/0.99    ! [X0] : ? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.69/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/0.99  
% 3.69/0.99  fof(f43,plain,(
% 3.69/0.99    ! [X0] : (? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (v1_xboole_0(sK3(X0)) & m1_subset_1(sK3(X0),k1_zfmisc_1(X0))))),
% 3.69/0.99    introduced(choice_axiom,[])).
% 3.69/0.99  
% 3.69/0.99  fof(f44,plain,(
% 3.69/0.99    ! [X0] : (v1_xboole_0(sK3(X0)) & m1_subset_1(sK3(X0),k1_zfmisc_1(X0)))),
% 3.69/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f10,f43])).
% 3.69/0.99  
% 3.69/0.99  fof(f69,plain,(
% 3.69/0.99    ( ! [X0] : (m1_subset_1(sK3(X0),k1_zfmisc_1(X0))) )),
% 3.69/0.99    inference(cnf_transformation,[],[f44])).
% 3.69/0.99  
% 3.69/0.99  fof(f11,axiom,(
% 3.69/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.69/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/0.99  
% 3.69/0.99  fof(f45,plain,(
% 3.69/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.69/0.99    inference(nnf_transformation,[],[f11])).
% 3.69/0.99  
% 3.69/0.99  fof(f71,plain,(
% 3.69/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.69/0.99    inference(cnf_transformation,[],[f45])).
% 3.69/0.99  
% 3.69/0.99  fof(f70,plain,(
% 3.69/0.99    ( ! [X0] : (v1_xboole_0(sK3(X0))) )),
% 3.69/0.99    inference(cnf_transformation,[],[f44])).
% 3.69/0.99  
% 3.69/0.99  fof(f9,axiom,(
% 3.69/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X1) = X1)),
% 3.69/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/0.99  
% 3.69/0.99  fof(f23,plain,(
% 3.69/0.99    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 3.69/0.99    inference(ennf_transformation,[],[f9])).
% 3.69/0.99  
% 3.69/0.99  fof(f68,plain,(
% 3.69/0.99    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.69/0.99    inference(cnf_transformation,[],[f23])).
% 3.69/0.99  
% 3.69/0.99  fof(f72,plain,(
% 3.69/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.69/0.99    inference(cnf_transformation,[],[f45])).
% 3.69/0.99  
% 3.69/0.99  fof(f57,plain,(
% 3.69/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.69/0.99    inference(cnf_transformation,[],[f38])).
% 3.69/0.99  
% 3.69/0.99  fof(f88,plain,(
% 3.69/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.69/0.99    inference(equality_resolution,[],[f57])).
% 3.69/0.99  
% 3.69/0.99  fof(f81,plain,(
% 3.69/0.99    ( ! [X0,X3,X1] : (v2_tex_2(X1,X0) | k9_subset_1(u1_struct_0(X0),X1,X3) != sK4(X0,X1) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.69/0.99    inference(cnf_transformation,[],[f50])).
% 3.69/0.99  
% 3.69/0.99  fof(f14,axiom,(
% 3.69/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_xboole_0(X1) => v4_pre_topc(X1,X0))))),
% 3.69/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/0.99  
% 3.69/0.99  fof(f26,plain,(
% 3.69/0.99    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) | ~v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.69/0.99    inference(ennf_transformation,[],[f14])).
% 3.69/0.99  
% 3.69/0.99  fof(f27,plain,(
% 3.69/0.99    ! [X0] : (! [X1] : (v4_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.69/0.99    inference(flattening,[],[f26])).
% 3.69/0.99  
% 3.69/0.99  fof(f75,plain,(
% 3.69/0.99    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.69/0.99    inference(cnf_transformation,[],[f27])).
% 3.69/0.99  
% 3.69/0.99  fof(f82,plain,(
% 3.69/0.99    v2_pre_topc(sK6)),
% 3.69/0.99    inference(cnf_transformation,[],[f53])).
% 3.69/0.99  
% 3.69/0.99  cnf(c_0,plain,
% 3.69/0.99      ( v1_xboole_0(sK0) ),
% 3.69/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_2346,plain,
% 3.69/0.99      ( v1_xboole_0(sK0) = iProver_top ),
% 3.69/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_30,negated_conjecture,
% 3.69/0.99      ( v1_xboole_0(sK7) ),
% 3.69/0.99      inference(cnf_transformation,[],[f84]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_2326,plain,
% 3.69/0.99      ( v1_xboole_0(sK7) = iProver_top ),
% 3.69/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_7,plain,
% 3.69/0.99      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X0 = X1 ),
% 3.69/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_2340,plain,
% 3.69/0.99      ( X0 = X1
% 3.69/0.99      | v1_xboole_0(X0) != iProver_top
% 3.69/0.99      | v1_xboole_0(X1) != iProver_top ),
% 3.69/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_5504,plain,
% 3.69/0.99      ( sK7 = X0 | v1_xboole_0(X0) != iProver_top ),
% 3.69/0.99      inference(superposition,[status(thm)],[c_2326,c_2340]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_5680,plain,
% 3.69/0.99      ( sK7 = sK0 ),
% 3.69/0.99      inference(superposition,[status(thm)],[c_2346,c_5504]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_29,negated_conjecture,
% 3.69/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
% 3.69/0.99      inference(cnf_transformation,[],[f85]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_2327,plain,
% 3.69/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
% 3.69/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_23,plain,
% 3.69/0.99      ( v2_tex_2(X0,X1)
% 3.69/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.69/0.99      | r1_tarski(sK4(X1,X0),X0)
% 3.69/0.99      | ~ l1_pre_topc(X1) ),
% 3.69/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_31,negated_conjecture,
% 3.69/0.99      ( l1_pre_topc(sK6) ),
% 3.69/0.99      inference(cnf_transformation,[],[f83]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_593,plain,
% 3.69/0.99      ( v2_tex_2(X0,X1)
% 3.69/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.69/0.99      | r1_tarski(sK4(X1,X0),X0)
% 3.69/0.99      | sK6 != X1 ),
% 3.69/0.99      inference(resolution_lifted,[status(thm)],[c_23,c_31]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_594,plain,
% 3.69/0.99      ( v2_tex_2(X0,sK6)
% 3.69/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.69/0.99      | r1_tarski(sK4(sK6,X0),X0) ),
% 3.69/0.99      inference(unflattening,[status(thm)],[c_593]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_2319,plain,
% 3.69/0.99      ( v2_tex_2(X0,sK6) = iProver_top
% 3.69/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 3.69/0.99      | r1_tarski(sK4(sK6,X0),X0) = iProver_top ),
% 3.69/0.99      inference(predicate_to_equality,[status(thm)],[c_594]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_2884,plain,
% 3.69/0.99      ( v2_tex_2(sK7,sK6) = iProver_top
% 3.69/0.99      | r1_tarski(sK4(sK6,sK7),sK7) = iProver_top ),
% 3.69/0.99      inference(superposition,[status(thm)],[c_2327,c_2319]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_36,plain,
% 3.69/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
% 3.69/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_28,negated_conjecture,
% 3.69/0.99      ( ~ v2_tex_2(sK7,sK6) ),
% 3.69/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_939,plain,
% 3.69/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.69/0.99      | r1_tarski(sK4(sK6,X0),X0)
% 3.69/0.99      | sK6 != sK6
% 3.69/0.99      | sK7 != X0 ),
% 3.69/0.99      inference(resolution_lifted,[status(thm)],[c_28,c_594]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_940,plain,
% 3.69/0.99      ( ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.69/0.99      | r1_tarski(sK4(sK6,sK7),sK7) ),
% 3.69/0.99      inference(unflattening,[status(thm)],[c_939]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_941,plain,
% 3.69/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 3.69/0.99      | r1_tarski(sK4(sK6,sK7),sK7) = iProver_top ),
% 3.69/0.99      inference(predicate_to_equality,[status(thm)],[c_940]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_3247,plain,
% 3.69/0.99      ( r1_tarski(sK4(sK6,sK7),sK7) = iProver_top ),
% 3.69/0.99      inference(global_propositional_subsumption,
% 3.69/0.99                [status(thm)],
% 3.69/0.99                [c_2884,c_36,c_941]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_5882,plain,
% 3.69/0.99      ( r1_tarski(sK4(sK6,sK0),sK0) = iProver_top ),
% 3.69/0.99      inference(demodulation,[status(thm)],[c_5680,c_3247]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_3,plain,
% 3.69/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.69/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_2343,plain,
% 3.69/0.99      ( X0 = X1
% 3.69/0.99      | r1_tarski(X0,X1) != iProver_top
% 3.69/0.99      | r1_tarski(X1,X0) != iProver_top ),
% 3.69/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_6893,plain,
% 3.69/0.99      ( sK4(sK6,sK0) = sK0 | r1_tarski(sK0,sK4(sK6,sK0)) != iProver_top ),
% 3.69/0.99      inference(superposition,[status(thm)],[c_5882,c_2343]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_16,plain,
% 3.69/0.99      ( m1_subset_1(sK3(X0),k1_zfmisc_1(X0)) ),
% 3.69/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_2333,plain,
% 3.69/0.99      ( m1_subset_1(sK3(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 3.69/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_18,plain,
% 3.69/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.69/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_2331,plain,
% 3.69/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.69/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.69/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_4979,plain,
% 3.69/0.99      ( r1_tarski(sK3(X0),X0) = iProver_top ),
% 3.69/0.99      inference(superposition,[status(thm)],[c_2333,c_2331]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_15,plain,
% 3.69/0.99      ( v1_xboole_0(sK3(X0)) ),
% 3.69/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_2334,plain,
% 3.69/0.99      ( v1_xboole_0(sK3(X0)) = iProver_top ),
% 3.69/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_5681,plain,
% 3.69/0.99      ( sK3(X0) = sK7 ),
% 3.69/0.99      inference(superposition,[status(thm)],[c_2334,c_5504]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_6189,plain,
% 3.69/0.99      ( sK3(X0) = sK0 ),
% 3.69/0.99      inference(light_normalisation,[status(thm)],[c_5681,c_5680]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_7319,plain,
% 3.69/0.99      ( r1_tarski(sK0,X0) = iProver_top ),
% 3.69/0.99      inference(light_normalisation,[status(thm)],[c_4979,c_6189]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_10534,plain,
% 3.69/0.99      ( sK4(sK6,sK0) = sK0 ),
% 3.69/0.99      inference(forward_subsumption_resolution,
% 3.69/0.99                [status(thm)],
% 3.69/0.99                [c_6893,c_7319]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_14,plain,
% 3.69/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | k9_subset_1(X1,X2,X2) = X2 ),
% 3.69/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_17,plain,
% 3.69/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.69/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_251,plain,
% 3.69/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.69/0.99      inference(prop_impl,[status(thm)],[c_17]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_252,plain,
% 3.69/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.69/0.99      inference(renaming,[status(thm)],[c_251]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_305,plain,
% 3.69/0.99      ( ~ r1_tarski(X0,X1) | k9_subset_1(X1,X2,X2) = X2 ),
% 3.69/0.99      inference(bin_hyper_res,[status(thm)],[c_14,c_252]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_2325,plain,
% 3.69/0.99      ( k9_subset_1(X0,X1,X1) = X1 | r1_tarski(X2,X0) != iProver_top ),
% 3.69/0.99      inference(predicate_to_equality,[status(thm)],[c_305]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_5,plain,
% 3.69/0.99      ( r1_tarski(X0,X0) ),
% 3.69/0.99      inference(cnf_transformation,[],[f88]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_11112,plain,
% 3.69/0.99      ( k9_subset_1(X0,X1,X1) = X1 ),
% 3.69/0.99      inference(resolution,[status(thm)],[c_305,c_5]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_15120,plain,
% 3.69/0.99      ( k9_subset_1(X0,X1,X1) = X1 ),
% 3.69/0.99      inference(global_propositional_subsumption,
% 3.69/0.99                [status(thm)],
% 3.69/0.99                [c_2325,c_11112]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_22,plain,
% 3.69/0.99      ( v2_tex_2(X0,X1)
% 3.69/0.99      | ~ v4_pre_topc(X2,X1)
% 3.69/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.69/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.69/0.99      | ~ l1_pre_topc(X1)
% 3.69/0.99      | k9_subset_1(u1_struct_0(X1),X0,X2) != sK4(X1,X0) ),
% 3.69/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_608,plain,
% 3.69/0.99      ( v2_tex_2(X0,X1)
% 3.69/0.99      | ~ v4_pre_topc(X2,X1)
% 3.69/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.69/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.69/0.99      | k9_subset_1(u1_struct_0(X1),X0,X2) != sK4(X1,X0)
% 3.69/0.99      | sK6 != X1 ),
% 3.69/0.99      inference(resolution_lifted,[status(thm)],[c_22,c_31]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_609,plain,
% 3.69/0.99      ( v2_tex_2(X0,sK6)
% 3.69/0.99      | ~ v4_pre_topc(X1,sK6)
% 3.69/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.69/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.69/0.99      | k9_subset_1(u1_struct_0(sK6),X0,X1) != sK4(sK6,X0) ),
% 3.69/0.99      inference(unflattening,[status(thm)],[c_608]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_2318,plain,
% 3.69/0.99      ( k9_subset_1(u1_struct_0(sK6),X0,X1) != sK4(sK6,X0)
% 3.69/0.99      | v2_tex_2(X0,sK6) = iProver_top
% 3.69/0.99      | v4_pre_topc(X1,sK6) != iProver_top
% 3.69/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 3.69/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
% 3.69/0.99      inference(predicate_to_equality,[status(thm)],[c_609]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_15123,plain,
% 3.69/0.99      ( sK4(sK6,X0) != X0
% 3.69/0.99      | v2_tex_2(X0,sK6) = iProver_top
% 3.69/0.99      | v4_pre_topc(X0,sK6) != iProver_top
% 3.69/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
% 3.69/0.99      inference(superposition,[status(thm)],[c_15120,c_2318]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_15361,plain,
% 3.69/0.99      ( v2_tex_2(sK0,sK6) = iProver_top
% 3.69/0.99      | v4_pre_topc(sK0,sK6) != iProver_top
% 3.69/0.99      | m1_subset_1(sK0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
% 3.69/0.99      inference(superposition,[status(thm)],[c_10534,c_15123]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_2328,plain,
% 3.69/0.99      ( v2_tex_2(sK7,sK6) != iProver_top ),
% 3.69/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_5885,plain,
% 3.69/0.99      ( v2_tex_2(sK0,sK6) != iProver_top ),
% 3.69/0.99      inference(demodulation,[status(thm)],[c_5680,c_2328]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_5884,plain,
% 3.69/0.99      ( m1_subset_1(sK0,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
% 3.69/0.99      inference(demodulation,[status(thm)],[c_5680,c_2327]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_21,plain,
% 3.69/0.99      ( v4_pre_topc(X0,X1)
% 3.69/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.69/0.99      | ~ v2_pre_topc(X1)
% 3.69/0.99      | ~ l1_pre_topc(X1)
% 3.69/0.99      | ~ v1_xboole_0(X0) ),
% 3.69/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_32,negated_conjecture,
% 3.69/0.99      ( v2_pre_topc(sK6) ),
% 3.69/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_419,plain,
% 3.69/0.99      ( v4_pre_topc(X0,X1)
% 3.69/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.69/0.99      | ~ l1_pre_topc(X1)
% 3.69/0.99      | ~ v1_xboole_0(X0)
% 3.69/0.99      | sK6 != X1 ),
% 3.69/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_32]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_420,plain,
% 3.69/0.99      ( v4_pre_topc(X0,sK6)
% 3.69/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.69/0.99      | ~ l1_pre_topc(sK6)
% 3.69/0.99      | ~ v1_xboole_0(X0) ),
% 3.69/0.99      inference(unflattening,[status(thm)],[c_419]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_424,plain,
% 3.69/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.69/0.99      | v4_pre_topc(X0,sK6)
% 3.69/0.99      | ~ v1_xboole_0(X0) ),
% 3.69/0.99      inference(global_propositional_subsumption,
% 3.69/0.99                [status(thm)],
% 3.69/0.99                [c_420,c_31]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_425,plain,
% 3.69/0.99      ( v4_pre_topc(X0,sK6)
% 3.69/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.69/0.99      | ~ v1_xboole_0(X0) ),
% 3.69/0.99      inference(renaming,[status(thm)],[c_424]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_2324,plain,
% 3.69/0.99      ( v4_pre_topc(X0,sK6) = iProver_top
% 3.69/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 3.69/0.99      | v1_xboole_0(X0) != iProver_top ),
% 3.69/0.99      inference(predicate_to_equality,[status(thm)],[c_425]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_2646,plain,
% 3.69/0.99      ( v4_pre_topc(sK7,sK6) = iProver_top
% 3.69/0.99      | v1_xboole_0(sK7) != iProver_top ),
% 3.69/0.99      inference(superposition,[status(thm)],[c_2327,c_2324]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_35,plain,
% 3.69/0.99      ( v1_xboole_0(sK7) = iProver_top ),
% 3.69/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_2567,plain,
% 3.69/0.99      ( v4_pre_topc(sK7,sK6)
% 3.69/0.99      | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.69/0.99      | ~ v1_xboole_0(sK7) ),
% 3.69/0.99      inference(instantiation,[status(thm)],[c_425]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_2568,plain,
% 3.69/0.99      ( v4_pre_topc(sK7,sK6) = iProver_top
% 3.69/0.99      | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 3.69/0.99      | v1_xboole_0(sK7) != iProver_top ),
% 3.69/0.99      inference(predicate_to_equality,[status(thm)],[c_2567]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_2700,plain,
% 3.69/0.99      ( v4_pre_topc(sK7,sK6) = iProver_top ),
% 3.69/0.99      inference(global_propositional_subsumption,
% 3.69/0.99                [status(thm)],
% 3.69/0.99                [c_2646,c_35,c_36,c_2568]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_5883,plain,
% 3.69/0.99      ( v4_pre_topc(sK0,sK6) = iProver_top ),
% 3.69/0.99      inference(demodulation,[status(thm)],[c_5680,c_2700]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(contradiction,plain,
% 3.69/0.99      ( $false ),
% 3.69/0.99      inference(minisat,[status(thm)],[c_15361,c_5885,c_5884,c_5883]) ).
% 3.69/0.99  
% 3.69/0.99  
% 3.69/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.69/0.99  
% 3.69/0.99  ------                               Statistics
% 3.69/0.99  
% 3.69/0.99  ------ Selected
% 3.69/0.99  
% 3.69/0.99  total_time:                             0.424
% 3.69/0.99  
%------------------------------------------------------------------------------
