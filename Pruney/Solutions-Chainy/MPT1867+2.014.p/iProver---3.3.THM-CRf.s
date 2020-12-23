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
% DateTime   : Thu Dec  3 12:26:09 EST 2020

% Result     : Theorem 1.69s
% Output     : CNFRefutation 1.69s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 326 expanded)
%              Number of clauses        :   58 (  97 expanded)
%              Number of leaves         :   15 (  78 expanded)
%              Depth                    :   18
%              Number of atoms          :  352 (1561 expanded)
%              Number of equality atoms :   97 ( 180 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_xboole_0(X1) )
           => v2_tex_2(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f16,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_xboole_0(X1) )
           => v2_tex_2(X1,X0) ) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
     => ( ~ v2_tex_2(sK4,X0)
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0)))
        & v1_xboole_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
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

fof(f42,plain,
    ( ~ v2_tex_2(sK4,sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    & v1_xboole_0(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f27,f41,f40])).

fof(f68,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f42])).

fof(f13,axiom,(
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

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f13])).

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
    inference(flattening,[],[f24])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f25])).

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
    inference(rectify,[],[f35])).

fof(f38,plain,(
    ! [X4,X1,X0] :
      ( ? [X5] :
          ( k9_subset_1(u1_struct_0(X0),X1,X5) = X4
          & v3_pre_topc(X5,X0)
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X0),X1,sK2(X0,X1,X4)) = X4
        & v3_pre_topc(sK2(X0,X1,X4),X0)
        & m1_subset_1(sK2(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
              | ~ v3_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ! [X3] :
            ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK1(X0,X1)
            | ~ v3_pre_topc(X3,X0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & r1_tarski(sK1(X0,X1),X1)
        & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ( ! [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK1(X0,X1)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & r1_tarski(sK1(X0,X1),X1)
                & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X4] :
                  ( ( k9_subset_1(u1_struct_0(X0),X1,sK2(X0,X1,X4)) = X4
                    & v3_pre_topc(sK2(X0,X1,X4),X0)
                    & m1_subset_1(sK2(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r1_tarski(X4,X1)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f36,f38,f37])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | r1_tarski(sK1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f66,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f69,plain,(
    ~ v2_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f67,plain,(
    v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f42])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f46,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

fof(f49,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f9,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f64,plain,(
    ! [X0,X3,X1] :
      ( v2_tex_2(X1,X0)
      | k9_subset_1(u1_struct_0(X0),X1,X3) != sK1(X0,X1)
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v3_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f65,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X2) = X2 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_4844,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | k9_subset_1(u1_struct_0(sK3),X1,X1) = X1 ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_4846,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3)))
    | k9_subset_1(u1_struct_0(sK3),k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4844])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2296,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_17,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(sK1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_25,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_687,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(sK1(X1,X0),X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_25])).

cnf(c_688,plain,
    ( v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | r1_tarski(sK1(sK3,X0),X0) ),
    inference(unflattening,[status(thm)],[c_687])).

cnf(c_2287,plain,
    ( v2_tex_2(X0,sK3) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r1_tarski(sK1(sK3,X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_688])).

cnf(c_2643,plain,
    ( v2_tex_2(sK4,sK3) = iProver_top
    | r1_tarski(sK1(sK3,sK4),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2296,c_2287])).

cnf(c_30,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_22,negated_conjecture,
    ( ~ v2_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1033,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | r1_tarski(sK1(sK3,X0),X0)
    | sK3 != sK3
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_688])).

cnf(c_1034,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | r1_tarski(sK1(sK3,sK4),sK4) ),
    inference(unflattening,[status(thm)],[c_1033])).

cnf(c_1035,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r1_tarski(sK1(sK3,sK4),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1034])).

cnf(c_3062,plain,
    ( r1_tarski(sK1(sK3,sK4),sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2643,c_30,c_1035])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2303,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3598,plain,
    ( k4_xboole_0(sK1(sK3,sK4),sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3062,c_2303])).

cnf(c_24,negated_conjecture,
    ( v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_2295,plain,
    ( v1_xboole_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_2306,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3494,plain,
    ( sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2295,c_2306])).

cnf(c_3816,plain,
    ( k4_xboole_0(sK1(sK3,k1_xboole_0),k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3598,c_3494])).

cnf(c_9,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2301,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3819,plain,
    ( r1_tarski(k1_xboole_0,sK1(sK3,k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3816,c_2301])).

cnf(c_2297,plain,
    ( v2_tex_2(sK4,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3673,plain,
    ( v2_tex_2(k1_xboole_0,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3494,c_2297])).

cnf(c_3670,plain,
    ( r1_tarski(sK1(sK3,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3494,c_3062])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_3323,plain,
    ( ~ r1_tarski(X0,sK1(sK3,X1))
    | ~ r1_tarski(sK1(sK3,X1),X0)
    | sK1(sK3,X1) = X0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_3324,plain,
    ( sK1(sK3,X0) = X1
    | r1_tarski(X1,sK1(sK3,X0)) != iProver_top
    | r1_tarski(sK1(sK3,X0),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3323])).

cnf(c_3326,plain,
    ( sK1(sK3,k1_xboole_0) = k1_xboole_0
    | r1_tarski(sK1(sK3,k1_xboole_0),k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK1(sK3,k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3324])).

cnf(c_1759,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3244,plain,
    ( k9_subset_1(u1_struct_0(sK3),X0,X1) != X2
    | k9_subset_1(u1_struct_0(sK3),X0,X1) = sK1(sK3,X0)
    | sK1(sK3,X0) != X2 ),
    inference(instantiation,[status(thm)],[c_1759])).

cnf(c_3245,plain,
    ( k9_subset_1(u1_struct_0(sK3),k1_xboole_0,k1_xboole_0) = sK1(sK3,k1_xboole_0)
    | k9_subset_1(u1_struct_0(sK3),k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | sK1(sK3,k1_xboole_0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3244])).

cnf(c_12,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2476,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2480,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2476])).

cnf(c_16,plain,
    ( v2_tex_2(X0,X1)
    | ~ v3_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),X0,X2) != sK1(X1,X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_15,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_26,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_346,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_26])).

cnf(c_347,plain,
    ( v3_pre_topc(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3)
    | ~ v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_346])).

cnf(c_351,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v3_pre_topc(X0,sK3)
    | ~ v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_347,c_25])).

cnf(c_352,plain,
    ( v3_pre_topc(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_351])).

cnf(c_434,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(X3)
    | X3 != X2
    | k9_subset_1(u1_struct_0(X1),X0,X2) != sK1(X1,X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_352])).

cnf(c_435,plain,
    ( v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3)
    | ~ v1_xboole_0(X1)
    | k9_subset_1(u1_struct_0(sK3),X0,X1) != sK1(sK3,X0) ),
    inference(unflattening,[status(thm)],[c_434])).

cnf(c_439,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_tex_2(X0,sK3)
    | ~ v1_xboole_0(X1)
    | k9_subset_1(u1_struct_0(sK3),X0,X1) != sK1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_435,c_25])).

cnf(c_440,plain,
    ( v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_xboole_0(X1)
    | k9_subset_1(u1_struct_0(sK3),X0,X1) != sK1(sK3,X0) ),
    inference(renaming,[status(thm)],[c_439])).

cnf(c_441,plain,
    ( k9_subset_1(u1_struct_0(sK3),X0,X1) != sK1(sK3,X0)
    | v2_tex_2(X0,sK3) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_440])).

cnf(c_443,plain,
    ( k9_subset_1(u1_struct_0(sK3),k1_xboole_0,k1_xboole_0) != sK1(sK3,k1_xboole_0)
    | v2_tex_2(k1_xboole_0,sK3) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_441])).

cnf(c_2,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_87,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4846,c_3819,c_3673,c_3670,c_3326,c_3245,c_2480,c_2476,c_443,c_87])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:11:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 1.69/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.69/0.99  
% 1.69/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.69/0.99  
% 1.69/0.99  ------  iProver source info
% 1.69/0.99  
% 1.69/0.99  git: date: 2020-06-30 10:37:57 +0100
% 1.69/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.69/0.99  git: non_committed_changes: false
% 1.69/0.99  git: last_make_outside_of_git: false
% 1.69/0.99  
% 1.69/0.99  ------ 
% 1.69/0.99  
% 1.69/0.99  ------ Input Options
% 1.69/0.99  
% 1.69/0.99  --out_options                           all
% 1.69/0.99  --tptp_safe_out                         true
% 1.69/0.99  --problem_path                          ""
% 1.69/0.99  --include_path                          ""
% 1.69/0.99  --clausifier                            res/vclausify_rel
% 1.69/0.99  --clausifier_options                    --mode clausify
% 1.69/0.99  --stdin                                 false
% 1.69/0.99  --stats_out                             all
% 1.69/0.99  
% 1.69/0.99  ------ General Options
% 1.69/0.99  
% 1.69/0.99  --fof                                   false
% 1.69/0.99  --time_out_real                         305.
% 1.69/0.99  --time_out_virtual                      -1.
% 1.69/0.99  --symbol_type_check                     false
% 1.69/0.99  --clausify_out                          false
% 1.69/0.99  --sig_cnt_out                           false
% 1.69/0.99  --trig_cnt_out                          false
% 1.69/0.99  --trig_cnt_out_tolerance                1.
% 1.69/0.99  --trig_cnt_out_sk_spl                   false
% 1.69/0.99  --abstr_cl_out                          false
% 1.69/0.99  
% 1.69/0.99  ------ Global Options
% 1.69/0.99  
% 1.69/0.99  --schedule                              default
% 1.69/0.99  --add_important_lit                     false
% 1.69/0.99  --prop_solver_per_cl                    1000
% 1.69/0.99  --min_unsat_core                        false
% 1.69/0.99  --soft_assumptions                      false
% 1.69/0.99  --soft_lemma_size                       3
% 1.69/0.99  --prop_impl_unit_size                   0
% 1.69/0.99  --prop_impl_unit                        []
% 1.69/0.99  --share_sel_clauses                     true
% 1.69/0.99  --reset_solvers                         false
% 1.69/0.99  --bc_imp_inh                            [conj_cone]
% 1.69/0.99  --conj_cone_tolerance                   3.
% 1.69/0.99  --extra_neg_conj                        none
% 1.69/0.99  --large_theory_mode                     true
% 1.69/0.99  --prolific_symb_bound                   200
% 1.69/0.99  --lt_threshold                          2000
% 1.69/0.99  --clause_weak_htbl                      true
% 1.69/0.99  --gc_record_bc_elim                     false
% 1.69/0.99  
% 1.69/0.99  ------ Preprocessing Options
% 1.69/0.99  
% 1.69/0.99  --preprocessing_flag                    true
% 1.69/0.99  --time_out_prep_mult                    0.1
% 1.69/0.99  --splitting_mode                        input
% 1.69/0.99  --splitting_grd                         true
% 1.69/0.99  --splitting_cvd                         false
% 1.69/0.99  --splitting_cvd_svl                     false
% 1.69/0.99  --splitting_nvd                         32
% 1.69/0.99  --sub_typing                            true
% 1.69/0.99  --prep_gs_sim                           true
% 1.69/0.99  --prep_unflatten                        true
% 1.69/0.99  --prep_res_sim                          true
% 1.69/0.99  --prep_upred                            true
% 1.69/0.99  --prep_sem_filter                       exhaustive
% 1.69/0.99  --prep_sem_filter_out                   false
% 1.69/0.99  --pred_elim                             true
% 1.69/0.99  --res_sim_input                         true
% 1.69/0.99  --eq_ax_congr_red                       true
% 1.69/0.99  --pure_diseq_elim                       true
% 1.69/0.99  --brand_transform                       false
% 1.69/0.99  --non_eq_to_eq                          false
% 1.69/0.99  --prep_def_merge                        true
% 1.69/0.99  --prep_def_merge_prop_impl              false
% 1.69/0.99  --prep_def_merge_mbd                    true
% 1.69/0.99  --prep_def_merge_tr_red                 false
% 1.69/0.99  --prep_def_merge_tr_cl                  false
% 1.69/0.99  --smt_preprocessing                     true
% 1.69/0.99  --smt_ac_axioms                         fast
% 1.69/0.99  --preprocessed_out                      false
% 1.69/0.99  --preprocessed_stats                    false
% 1.69/0.99  
% 1.69/0.99  ------ Abstraction refinement Options
% 1.69/0.99  
% 1.69/0.99  --abstr_ref                             []
% 1.69/0.99  --abstr_ref_prep                        false
% 1.69/0.99  --abstr_ref_until_sat                   false
% 1.69/0.99  --abstr_ref_sig_restrict                funpre
% 1.69/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.69/0.99  --abstr_ref_under                       []
% 1.69/0.99  
% 1.69/0.99  ------ SAT Options
% 1.69/0.99  
% 1.69/0.99  --sat_mode                              false
% 1.69/0.99  --sat_fm_restart_options                ""
% 1.69/0.99  --sat_gr_def                            false
% 1.69/0.99  --sat_epr_types                         true
% 1.69/0.99  --sat_non_cyclic_types                  false
% 1.69/0.99  --sat_finite_models                     false
% 1.69/0.99  --sat_fm_lemmas                         false
% 1.69/0.99  --sat_fm_prep                           false
% 1.69/0.99  --sat_fm_uc_incr                        true
% 1.69/0.99  --sat_out_model                         small
% 1.69/0.99  --sat_out_clauses                       false
% 1.69/0.99  
% 1.69/0.99  ------ QBF Options
% 1.69/0.99  
% 1.69/0.99  --qbf_mode                              false
% 1.69/0.99  --qbf_elim_univ                         false
% 1.69/0.99  --qbf_dom_inst                          none
% 1.69/0.99  --qbf_dom_pre_inst                      false
% 1.69/0.99  --qbf_sk_in                             false
% 1.69/0.99  --qbf_pred_elim                         true
% 1.69/0.99  --qbf_split                             512
% 1.69/0.99  
% 1.69/0.99  ------ BMC1 Options
% 1.69/0.99  
% 1.69/0.99  --bmc1_incremental                      false
% 1.69/0.99  --bmc1_axioms                           reachable_all
% 1.69/0.99  --bmc1_min_bound                        0
% 1.69/0.99  --bmc1_max_bound                        -1
% 1.69/0.99  --bmc1_max_bound_default                -1
% 1.69/0.99  --bmc1_symbol_reachability              true
% 1.69/0.99  --bmc1_property_lemmas                  false
% 1.69/0.99  --bmc1_k_induction                      false
% 1.69/0.99  --bmc1_non_equiv_states                 false
% 1.69/0.99  --bmc1_deadlock                         false
% 1.69/0.99  --bmc1_ucm                              false
% 1.69/0.99  --bmc1_add_unsat_core                   none
% 1.69/0.99  --bmc1_unsat_core_children              false
% 1.69/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.69/0.99  --bmc1_out_stat                         full
% 1.69/0.99  --bmc1_ground_init                      false
% 1.69/0.99  --bmc1_pre_inst_next_state              false
% 1.69/0.99  --bmc1_pre_inst_state                   false
% 1.69/0.99  --bmc1_pre_inst_reach_state             false
% 1.69/0.99  --bmc1_out_unsat_core                   false
% 1.69/0.99  --bmc1_aig_witness_out                  false
% 1.69/0.99  --bmc1_verbose                          false
% 1.69/0.99  --bmc1_dump_clauses_tptp                false
% 1.69/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.69/0.99  --bmc1_dump_file                        -
% 1.69/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.69/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.69/0.99  --bmc1_ucm_extend_mode                  1
% 1.69/0.99  --bmc1_ucm_init_mode                    2
% 1.69/0.99  --bmc1_ucm_cone_mode                    none
% 1.69/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.69/0.99  --bmc1_ucm_relax_model                  4
% 1.69/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.69/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.69/0.99  --bmc1_ucm_layered_model                none
% 1.69/0.99  --bmc1_ucm_max_lemma_size               10
% 1.69/0.99  
% 1.69/0.99  ------ AIG Options
% 1.69/0.99  
% 1.69/0.99  --aig_mode                              false
% 1.69/0.99  
% 1.69/0.99  ------ Instantiation Options
% 1.69/0.99  
% 1.69/0.99  --instantiation_flag                    true
% 1.69/0.99  --inst_sos_flag                         false
% 1.69/0.99  --inst_sos_phase                        true
% 1.69/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.69/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.69/0.99  --inst_lit_sel_side                     num_symb
% 1.69/0.99  --inst_solver_per_active                1400
% 1.69/0.99  --inst_solver_calls_frac                1.
% 1.69/0.99  --inst_passive_queue_type               priority_queues
% 1.69/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.69/0.99  --inst_passive_queues_freq              [25;2]
% 1.69/0.99  --inst_dismatching                      true
% 1.69/0.99  --inst_eager_unprocessed_to_passive     true
% 1.69/0.99  --inst_prop_sim_given                   true
% 1.69/0.99  --inst_prop_sim_new                     false
% 1.69/0.99  --inst_subs_new                         false
% 1.69/0.99  --inst_eq_res_simp                      false
% 1.69/0.99  --inst_subs_given                       false
% 1.69/0.99  --inst_orphan_elimination               true
% 1.69/0.99  --inst_learning_loop_flag               true
% 1.69/0.99  --inst_learning_start                   3000
% 1.69/0.99  --inst_learning_factor                  2
% 1.69/0.99  --inst_start_prop_sim_after_learn       3
% 1.69/0.99  --inst_sel_renew                        solver
% 1.69/0.99  --inst_lit_activity_flag                true
% 1.69/0.99  --inst_restr_to_given                   false
% 1.69/0.99  --inst_activity_threshold               500
% 1.69/0.99  --inst_out_proof                        true
% 1.69/0.99  
% 1.69/0.99  ------ Resolution Options
% 1.69/0.99  
% 1.69/0.99  --resolution_flag                       true
% 1.69/0.99  --res_lit_sel                           adaptive
% 1.69/0.99  --res_lit_sel_side                      none
% 1.69/0.99  --res_ordering                          kbo
% 1.69/0.99  --res_to_prop_solver                    active
% 1.69/0.99  --res_prop_simpl_new                    false
% 1.69/0.99  --res_prop_simpl_given                  true
% 1.69/0.99  --res_passive_queue_type                priority_queues
% 1.69/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.69/0.99  --res_passive_queues_freq               [15;5]
% 1.69/0.99  --res_forward_subs                      full
% 1.69/0.99  --res_backward_subs                     full
% 1.69/0.99  --res_forward_subs_resolution           true
% 1.69/0.99  --res_backward_subs_resolution          true
% 1.69/0.99  --res_orphan_elimination                true
% 1.69/0.99  --res_time_limit                        2.
% 1.69/0.99  --res_out_proof                         true
% 1.69/0.99  
% 1.69/0.99  ------ Superposition Options
% 1.69/0.99  
% 1.69/0.99  --superposition_flag                    true
% 1.69/0.99  --sup_passive_queue_type                priority_queues
% 1.69/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.69/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.69/0.99  --demod_completeness_check              fast
% 1.69/0.99  --demod_use_ground                      true
% 1.69/0.99  --sup_to_prop_solver                    passive
% 1.69/0.99  --sup_prop_simpl_new                    true
% 1.69/0.99  --sup_prop_simpl_given                  true
% 1.69/0.99  --sup_fun_splitting                     false
% 1.69/0.99  --sup_smt_interval                      50000
% 1.69/0.99  
% 1.69/0.99  ------ Superposition Simplification Setup
% 1.69/0.99  
% 1.69/0.99  --sup_indices_passive                   []
% 1.69/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.69/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.69/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.69/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.69/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.69/0.99  --sup_full_bw                           [BwDemod]
% 1.69/0.99  --sup_immed_triv                        [TrivRules]
% 1.69/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.69/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.69/0.99  --sup_immed_bw_main                     []
% 1.69/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.69/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.69/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.69/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.69/0.99  
% 1.69/0.99  ------ Combination Options
% 1.69/0.99  
% 1.69/0.99  --comb_res_mult                         3
% 1.69/0.99  --comb_sup_mult                         2
% 1.69/0.99  --comb_inst_mult                        10
% 1.69/0.99  
% 1.69/0.99  ------ Debug Options
% 1.69/0.99  
% 1.69/0.99  --dbg_backtrace                         false
% 1.69/0.99  --dbg_dump_prop_clauses                 false
% 1.69/0.99  --dbg_dump_prop_clauses_file            -
% 1.69/0.99  --dbg_out_stat                          false
% 1.69/0.99  ------ Parsing...
% 1.69/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.69/0.99  
% 1.69/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 1.69/0.99  
% 1.69/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.69/0.99  
% 1.69/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.69/0.99  ------ Proving...
% 1.69/0.99  ------ Problem Properties 
% 1.69/0.99  
% 1.69/0.99  
% 1.69/0.99  clauses                                 22
% 1.69/0.99  conjectures                             3
% 1.69/0.99  EPR                                     6
% 1.69/0.99  Horn                                    18
% 1.69/0.99  unary                                   8
% 1.69/0.99  binary                                  5
% 1.69/0.99  lits                                    53
% 1.69/0.99  lits eq                                 7
% 1.69/0.99  fd_pure                                 0
% 1.69/0.99  fd_pseudo                               0
% 1.69/0.99  fd_cond                                 1
% 1.69/0.99  fd_pseudo_cond                          1
% 1.69/0.99  AC symbols                              0
% 1.69/0.99  
% 1.69/0.99  ------ Schedule dynamic 5 is on 
% 1.69/0.99  
% 1.69/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.69/0.99  
% 1.69/0.99  
% 1.69/0.99  ------ 
% 1.69/0.99  Current options:
% 1.69/0.99  ------ 
% 1.69/0.99  
% 1.69/0.99  ------ Input Options
% 1.69/0.99  
% 1.69/0.99  --out_options                           all
% 1.69/0.99  --tptp_safe_out                         true
% 1.69/0.99  --problem_path                          ""
% 1.69/0.99  --include_path                          ""
% 1.69/0.99  --clausifier                            res/vclausify_rel
% 1.69/0.99  --clausifier_options                    --mode clausify
% 1.69/0.99  --stdin                                 false
% 1.69/0.99  --stats_out                             all
% 1.69/0.99  
% 1.69/0.99  ------ General Options
% 1.69/0.99  
% 1.69/0.99  --fof                                   false
% 1.69/0.99  --time_out_real                         305.
% 1.69/0.99  --time_out_virtual                      -1.
% 1.69/0.99  --symbol_type_check                     false
% 1.69/0.99  --clausify_out                          false
% 1.69/0.99  --sig_cnt_out                           false
% 1.69/0.99  --trig_cnt_out                          false
% 1.69/0.99  --trig_cnt_out_tolerance                1.
% 1.69/0.99  --trig_cnt_out_sk_spl                   false
% 1.69/0.99  --abstr_cl_out                          false
% 1.69/0.99  
% 1.69/0.99  ------ Global Options
% 1.69/0.99  
% 1.69/0.99  --schedule                              default
% 1.69/0.99  --add_important_lit                     false
% 1.69/0.99  --prop_solver_per_cl                    1000
% 1.69/0.99  --min_unsat_core                        false
% 1.69/0.99  --soft_assumptions                      false
% 1.69/0.99  --soft_lemma_size                       3
% 1.69/0.99  --prop_impl_unit_size                   0
% 1.69/0.99  --prop_impl_unit                        []
% 1.69/0.99  --share_sel_clauses                     true
% 1.69/0.99  --reset_solvers                         false
% 1.69/0.99  --bc_imp_inh                            [conj_cone]
% 1.69/0.99  --conj_cone_tolerance                   3.
% 1.69/0.99  --extra_neg_conj                        none
% 1.69/0.99  --large_theory_mode                     true
% 1.69/0.99  --prolific_symb_bound                   200
% 1.69/0.99  --lt_threshold                          2000
% 1.69/0.99  --clause_weak_htbl                      true
% 1.69/0.99  --gc_record_bc_elim                     false
% 1.69/0.99  
% 1.69/0.99  ------ Preprocessing Options
% 1.69/0.99  
% 1.69/0.99  --preprocessing_flag                    true
% 1.69/0.99  --time_out_prep_mult                    0.1
% 1.69/0.99  --splitting_mode                        input
% 1.69/0.99  --splitting_grd                         true
% 1.69/0.99  --splitting_cvd                         false
% 1.69/0.99  --splitting_cvd_svl                     false
% 1.69/0.99  --splitting_nvd                         32
% 1.69/0.99  --sub_typing                            true
% 1.69/0.99  --prep_gs_sim                           true
% 1.69/0.99  --prep_unflatten                        true
% 1.69/0.99  --prep_res_sim                          true
% 1.69/0.99  --prep_upred                            true
% 1.69/0.99  --prep_sem_filter                       exhaustive
% 1.69/0.99  --prep_sem_filter_out                   false
% 1.69/0.99  --pred_elim                             true
% 1.69/0.99  --res_sim_input                         true
% 1.69/0.99  --eq_ax_congr_red                       true
% 1.69/0.99  --pure_diseq_elim                       true
% 1.69/0.99  --brand_transform                       false
% 1.69/0.99  --non_eq_to_eq                          false
% 1.69/0.99  --prep_def_merge                        true
% 1.69/0.99  --prep_def_merge_prop_impl              false
% 1.69/0.99  --prep_def_merge_mbd                    true
% 1.69/0.99  --prep_def_merge_tr_red                 false
% 1.69/0.99  --prep_def_merge_tr_cl                  false
% 1.69/0.99  --smt_preprocessing                     true
% 1.69/0.99  --smt_ac_axioms                         fast
% 1.69/0.99  --preprocessed_out                      false
% 1.69/0.99  --preprocessed_stats                    false
% 1.69/0.99  
% 1.69/0.99  ------ Abstraction refinement Options
% 1.69/0.99  
% 1.69/0.99  --abstr_ref                             []
% 1.69/0.99  --abstr_ref_prep                        false
% 1.69/0.99  --abstr_ref_until_sat                   false
% 1.69/0.99  --abstr_ref_sig_restrict                funpre
% 1.69/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.69/0.99  --abstr_ref_under                       []
% 1.69/0.99  
% 1.69/0.99  ------ SAT Options
% 1.69/0.99  
% 1.69/0.99  --sat_mode                              false
% 1.69/0.99  --sat_fm_restart_options                ""
% 1.69/0.99  --sat_gr_def                            false
% 1.69/0.99  --sat_epr_types                         true
% 1.69/0.99  --sat_non_cyclic_types                  false
% 1.69/0.99  --sat_finite_models                     false
% 1.69/0.99  --sat_fm_lemmas                         false
% 1.69/0.99  --sat_fm_prep                           false
% 1.69/0.99  --sat_fm_uc_incr                        true
% 1.69/0.99  --sat_out_model                         small
% 1.69/0.99  --sat_out_clauses                       false
% 1.69/0.99  
% 1.69/0.99  ------ QBF Options
% 1.69/0.99  
% 1.69/0.99  --qbf_mode                              false
% 1.69/0.99  --qbf_elim_univ                         false
% 1.69/0.99  --qbf_dom_inst                          none
% 1.69/0.99  --qbf_dom_pre_inst                      false
% 1.69/0.99  --qbf_sk_in                             false
% 1.69/0.99  --qbf_pred_elim                         true
% 1.69/0.99  --qbf_split                             512
% 1.69/0.99  
% 1.69/0.99  ------ BMC1 Options
% 1.69/0.99  
% 1.69/0.99  --bmc1_incremental                      false
% 1.69/0.99  --bmc1_axioms                           reachable_all
% 1.69/0.99  --bmc1_min_bound                        0
% 1.69/0.99  --bmc1_max_bound                        -1
% 1.69/0.99  --bmc1_max_bound_default                -1
% 1.69/0.99  --bmc1_symbol_reachability              true
% 1.69/0.99  --bmc1_property_lemmas                  false
% 1.69/0.99  --bmc1_k_induction                      false
% 1.69/0.99  --bmc1_non_equiv_states                 false
% 1.69/0.99  --bmc1_deadlock                         false
% 1.69/0.99  --bmc1_ucm                              false
% 1.69/0.99  --bmc1_add_unsat_core                   none
% 1.69/0.99  --bmc1_unsat_core_children              false
% 1.69/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.69/0.99  --bmc1_out_stat                         full
% 1.69/0.99  --bmc1_ground_init                      false
% 1.69/0.99  --bmc1_pre_inst_next_state              false
% 1.69/0.99  --bmc1_pre_inst_state                   false
% 1.69/0.99  --bmc1_pre_inst_reach_state             false
% 1.69/0.99  --bmc1_out_unsat_core                   false
% 1.69/0.99  --bmc1_aig_witness_out                  false
% 1.69/0.99  --bmc1_verbose                          false
% 1.69/0.99  --bmc1_dump_clauses_tptp                false
% 1.69/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.69/0.99  --bmc1_dump_file                        -
% 1.69/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.69/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.69/0.99  --bmc1_ucm_extend_mode                  1
% 1.69/0.99  --bmc1_ucm_init_mode                    2
% 1.69/0.99  --bmc1_ucm_cone_mode                    none
% 1.69/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.69/0.99  --bmc1_ucm_relax_model                  4
% 1.69/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.69/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.69/0.99  --bmc1_ucm_layered_model                none
% 1.69/0.99  --bmc1_ucm_max_lemma_size               10
% 1.69/0.99  
% 1.69/0.99  ------ AIG Options
% 1.69/0.99  
% 1.69/0.99  --aig_mode                              false
% 1.69/0.99  
% 1.69/0.99  ------ Instantiation Options
% 1.69/0.99  
% 1.69/0.99  --instantiation_flag                    true
% 1.69/0.99  --inst_sos_flag                         false
% 1.69/0.99  --inst_sos_phase                        true
% 1.69/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.69/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.69/0.99  --inst_lit_sel_side                     none
% 1.69/0.99  --inst_solver_per_active                1400
% 1.69/0.99  --inst_solver_calls_frac                1.
% 1.69/0.99  --inst_passive_queue_type               priority_queues
% 1.69/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.69/0.99  --inst_passive_queues_freq              [25;2]
% 1.69/0.99  --inst_dismatching                      true
% 1.69/0.99  --inst_eager_unprocessed_to_passive     true
% 1.69/0.99  --inst_prop_sim_given                   true
% 1.69/0.99  --inst_prop_sim_new                     false
% 1.69/0.99  --inst_subs_new                         false
% 1.69/0.99  --inst_eq_res_simp                      false
% 1.69/0.99  --inst_subs_given                       false
% 1.69/0.99  --inst_orphan_elimination               true
% 1.69/0.99  --inst_learning_loop_flag               true
% 1.69/0.99  --inst_learning_start                   3000
% 1.69/0.99  --inst_learning_factor                  2
% 1.69/0.99  --inst_start_prop_sim_after_learn       3
% 1.69/0.99  --inst_sel_renew                        solver
% 1.69/0.99  --inst_lit_activity_flag                true
% 1.69/0.99  --inst_restr_to_given                   false
% 1.69/0.99  --inst_activity_threshold               500
% 1.69/0.99  --inst_out_proof                        true
% 1.69/0.99  
% 1.69/0.99  ------ Resolution Options
% 1.69/0.99  
% 1.69/0.99  --resolution_flag                       false
% 1.69/0.99  --res_lit_sel                           adaptive
% 1.69/0.99  --res_lit_sel_side                      none
% 1.69/0.99  --res_ordering                          kbo
% 1.69/0.99  --res_to_prop_solver                    active
% 1.69/0.99  --res_prop_simpl_new                    false
% 1.69/0.99  --res_prop_simpl_given                  true
% 1.69/0.99  --res_passive_queue_type                priority_queues
% 1.69/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.69/0.99  --res_passive_queues_freq               [15;5]
% 1.69/0.99  --res_forward_subs                      full
% 1.69/0.99  --res_backward_subs                     full
% 1.69/0.99  --res_forward_subs_resolution           true
% 1.69/0.99  --res_backward_subs_resolution          true
% 1.69/0.99  --res_orphan_elimination                true
% 1.69/0.99  --res_time_limit                        2.
% 1.69/0.99  --res_out_proof                         true
% 1.69/0.99  
% 1.69/0.99  ------ Superposition Options
% 1.69/0.99  
% 1.69/0.99  --superposition_flag                    true
% 1.69/0.99  --sup_passive_queue_type                priority_queues
% 1.69/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.69/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.69/0.99  --demod_completeness_check              fast
% 1.69/0.99  --demod_use_ground                      true
% 1.69/0.99  --sup_to_prop_solver                    passive
% 1.69/0.99  --sup_prop_simpl_new                    true
% 1.69/0.99  --sup_prop_simpl_given                  true
% 1.69/0.99  --sup_fun_splitting                     false
% 1.69/0.99  --sup_smt_interval                      50000
% 1.69/0.99  
% 1.69/0.99  ------ Superposition Simplification Setup
% 1.69/0.99  
% 1.69/0.99  --sup_indices_passive                   []
% 1.69/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.69/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.69/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.69/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.69/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.69/0.99  --sup_full_bw                           [BwDemod]
% 1.69/0.99  --sup_immed_triv                        [TrivRules]
% 1.69/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.69/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.69/0.99  --sup_immed_bw_main                     []
% 1.69/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.69/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.69/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.69/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.69/0.99  
% 1.69/0.99  ------ Combination Options
% 1.69/0.99  
% 1.69/0.99  --comb_res_mult                         3
% 1.69/0.99  --comb_sup_mult                         2
% 1.69/0.99  --comb_inst_mult                        10
% 1.69/0.99  
% 1.69/0.99  ------ Debug Options
% 1.69/0.99  
% 1.69/0.99  --dbg_backtrace                         false
% 1.69/0.99  --dbg_dump_prop_clauses                 false
% 1.69/0.99  --dbg_dump_prop_clauses_file            -
% 1.69/0.99  --dbg_out_stat                          false
% 1.69/0.99  
% 1.69/0.99  
% 1.69/0.99  
% 1.69/0.99  
% 1.69/0.99  ------ Proving...
% 1.69/0.99  
% 1.69/0.99  
% 1.69/0.99  % SZS status Theorem for theBenchmark.p
% 1.69/0.99  
% 1.69/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 1.69/0.99  
% 1.69/0.99  fof(f8,axiom,(
% 1.69/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X1) = X1)),
% 1.69/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.69/0.99  
% 1.69/0.99  fof(f18,plain,(
% 1.69/0.99    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.69/0.99    inference(ennf_transformation,[],[f8])).
% 1.69/0.99  
% 1.69/0.99  fof(f54,plain,(
% 1.69/0.99    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 1.69/0.99    inference(cnf_transformation,[],[f18])).
% 1.69/0.99  
% 1.69/0.99  fof(f14,conjecture,(
% 1.69/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 1.69/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.69/0.99  
% 1.69/0.99  fof(f15,negated_conjecture,(
% 1.69/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 1.69/0.99    inference(negated_conjecture,[],[f14])).
% 1.69/0.99  
% 1.69/0.99  fof(f16,plain,(
% 1.69/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 1.69/0.99    inference(pure_predicate_removal,[],[f15])).
% 1.69/0.99  
% 1.69/0.99  fof(f26,plain,(
% 1.69/0.99    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.69/0.99    inference(ennf_transformation,[],[f16])).
% 1.69/0.99  
% 1.69/0.99  fof(f27,plain,(
% 1.69/0.99    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.69/0.99    inference(flattening,[],[f26])).
% 1.69/0.99  
% 1.69/0.99  fof(f41,plain,(
% 1.69/0.99    ( ! [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => (~v2_tex_2(sK4,X0) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(sK4))) )),
% 1.69/0.99    introduced(choice_axiom,[])).
% 1.69/0.99  
% 1.69/0.99  fof(f40,plain,(
% 1.69/0.99    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (~v2_tex_2(X1,sK3) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) & v1_xboole_0(X1)) & l1_pre_topc(sK3) & v2_pre_topc(sK3))),
% 1.69/0.99    introduced(choice_axiom,[])).
% 1.69/0.99  
% 1.69/0.99  fof(f42,plain,(
% 1.69/0.99    (~v2_tex_2(sK4,sK3) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) & v1_xboole_0(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3)),
% 1.69/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f27,f41,f40])).
% 1.69/0.99  
% 1.69/0.99  fof(f68,plain,(
% 1.69/0.99    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))),
% 1.69/0.99    inference(cnf_transformation,[],[f42])).
% 1.69/0.99  
% 1.69/0.99  fof(f13,axiom,(
% 1.69/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0))) & r1_tarski(X2,X1))))))),
% 1.69/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.69/0.99  
% 1.69/0.99  fof(f24,plain,(
% 1.69/0.99    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((? [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.69/0.99    inference(ennf_transformation,[],[f13])).
% 1.69/0.99  
% 1.69/0.99  fof(f25,plain,(
% 1.69/0.99    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.69/0.99    inference(flattening,[],[f24])).
% 1.69/0.99  
% 1.69/0.99  fof(f35,plain,(
% 1.69/0.99    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.69/0.99    inference(nnf_transformation,[],[f25])).
% 1.69/0.99  
% 1.69/0.99  fof(f36,plain,(
% 1.69/0.99    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (? [X5] : (k9_subset_1(u1_struct_0(X0),X1,X5) = X4 & v3_pre_topc(X5,X0) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.69/0.99    inference(rectify,[],[f35])).
% 1.69/0.99  
% 1.69/0.99  fof(f38,plain,(
% 1.69/0.99    ! [X4,X1,X0] : (? [X5] : (k9_subset_1(u1_struct_0(X0),X1,X5) = X4 & v3_pre_topc(X5,X0) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) => (k9_subset_1(u1_struct_0(X0),X1,sK2(X0,X1,X4)) = X4 & v3_pre_topc(sK2(X0,X1,X4),X0) & m1_subset_1(sK2(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.69/0.99    introduced(choice_axiom,[])).
% 1.69/0.99  
% 1.69/0.99  fof(f37,plain,(
% 1.69/0.99    ! [X1,X0] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK1(X0,X1) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(sK1(X0,X1),X1) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.69/0.99    introduced(choice_axiom,[])).
% 1.69/0.99  
% 1.69/0.99  fof(f39,plain,(
% 1.69/0.99    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK1(X0,X1) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(sK1(X0,X1),X1) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : ((k9_subset_1(u1_struct_0(X0),X1,sK2(X0,X1,X4)) = X4 & v3_pre_topc(sK2(X0,X1,X4),X0) & m1_subset_1(sK2(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.69/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f36,f38,f37])).
% 1.69/0.99  
% 1.69/0.99  fof(f63,plain,(
% 1.69/0.99    ( ! [X0,X1] : (v2_tex_2(X1,X0) | r1_tarski(sK1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.69/0.99    inference(cnf_transformation,[],[f39])).
% 1.69/0.99  
% 1.69/0.99  fof(f66,plain,(
% 1.69/0.99    l1_pre_topc(sK3)),
% 1.69/0.99    inference(cnf_transformation,[],[f42])).
% 1.69/0.99  
% 1.69/0.99  fof(f69,plain,(
% 1.69/0.99    ~v2_tex_2(sK4,sK3)),
% 1.69/0.99    inference(cnf_transformation,[],[f42])).
% 1.69/0.99  
% 1.69/0.99  fof(f5,axiom,(
% 1.69/0.99    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 1.69/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.69/0.99  
% 1.69/0.99  fof(f34,plain,(
% 1.69/0.99    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 1.69/0.99    inference(nnf_transformation,[],[f5])).
% 1.69/0.99  
% 1.69/0.99  fof(f51,plain,(
% 1.69/0.99    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 1.69/0.99    inference(cnf_transformation,[],[f34])).
% 1.69/0.99  
% 1.69/0.99  fof(f67,plain,(
% 1.69/0.99    v1_xboole_0(sK4)),
% 1.69/0.99    inference(cnf_transformation,[],[f42])).
% 1.69/0.99  
% 1.69/0.99  fof(f3,axiom,(
% 1.69/0.99    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.69/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.69/0.99  
% 1.69/0.99  fof(f17,plain,(
% 1.69/0.99    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.69/0.99    inference(ennf_transformation,[],[f3])).
% 1.69/0.99  
% 1.69/0.99  fof(f46,plain,(
% 1.69/0.99    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 1.69/0.99    inference(cnf_transformation,[],[f17])).
% 1.69/0.99  
% 1.69/0.99  fof(f6,axiom,(
% 1.69/0.99    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.69/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.69/0.99  
% 1.69/0.99  fof(f52,plain,(
% 1.69/0.99    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.69/0.99    inference(cnf_transformation,[],[f6])).
% 1.69/0.99  
% 1.69/0.99  fof(f4,axiom,(
% 1.69/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.69/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.69/0.99  
% 1.69/0.99  fof(f32,plain,(
% 1.69/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.69/0.99    inference(nnf_transformation,[],[f4])).
% 1.69/0.99  
% 1.69/0.99  fof(f33,plain,(
% 1.69/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.69/0.99    inference(flattening,[],[f32])).
% 1.69/0.99  
% 1.69/0.99  fof(f49,plain,(
% 1.69/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 1.69/0.99    inference(cnf_transformation,[],[f33])).
% 1.69/0.99  
% 1.69/0.99  fof(f9,axiom,(
% 1.69/0.99    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.69/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.69/0.99  
% 1.69/0.99  fof(f55,plain,(
% 1.69/0.99    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.69/0.99    inference(cnf_transformation,[],[f9])).
% 1.69/0.99  
% 1.69/0.99  fof(f64,plain,(
% 1.69/0.99    ( ! [X0,X3,X1] : (v2_tex_2(X1,X0) | k9_subset_1(u1_struct_0(X0),X1,X3) != sK1(X0,X1) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.69/0.99    inference(cnf_transformation,[],[f39])).
% 1.69/0.99  
% 1.69/0.99  fof(f12,axiom,(
% 1.69/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_xboole_0(X1) => v3_pre_topc(X1,X0))))),
% 1.69/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.69/0.99  
% 1.69/0.99  fof(f22,plain,(
% 1.69/0.99    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) | ~v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.69/0.99    inference(ennf_transformation,[],[f12])).
% 1.69/0.99  
% 1.69/0.99  fof(f23,plain,(
% 1.69/0.99    ! [X0] : (! [X1] : (v3_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.69/0.99    inference(flattening,[],[f22])).
% 1.69/0.99  
% 1.69/0.99  fof(f58,plain,(
% 1.69/0.99    ( ! [X0,X1] : (v3_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.69/0.99    inference(cnf_transformation,[],[f23])).
% 1.69/0.99  
% 1.69/0.99  fof(f65,plain,(
% 1.69/0.99    v2_pre_topc(sK3)),
% 1.69/0.99    inference(cnf_transformation,[],[f42])).
% 1.69/0.99  
% 1.69/0.99  fof(f2,axiom,(
% 1.69/0.99    v1_xboole_0(k1_xboole_0)),
% 1.69/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.69/0.99  
% 1.69/0.99  fof(f45,plain,(
% 1.69/0.99    v1_xboole_0(k1_xboole_0)),
% 1.69/0.99    inference(cnf_transformation,[],[f2])).
% 1.69/0.99  
% 1.69/0.99  cnf(c_11,plain,
% 1.69/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | k9_subset_1(X1,X2,X2) = X2 ),
% 1.69/0.99      inference(cnf_transformation,[],[f54]) ).
% 1.69/0.99  
% 1.69/0.99  cnf(c_4844,plain,
% 1.69/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.69/0.99      | k9_subset_1(u1_struct_0(sK3),X1,X1) = X1 ),
% 1.69/0.99      inference(instantiation,[status(thm)],[c_11]) ).
% 1.69/0.99  
% 1.69/0.99  cnf(c_4846,plain,
% 1.69/0.99      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.69/0.99      | k9_subset_1(u1_struct_0(sK3),k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 1.69/0.99      inference(instantiation,[status(thm)],[c_4844]) ).
% 1.69/0.99  
% 1.69/0.99  cnf(c_23,negated_conjecture,
% 1.69/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 1.69/0.99      inference(cnf_transformation,[],[f68]) ).
% 1.69/0.99  
% 1.69/0.99  cnf(c_2296,plain,
% 1.69/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 1.69/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 1.69/0.99  
% 1.69/0.99  cnf(c_17,plain,
% 1.69/0.99      ( v2_tex_2(X0,X1)
% 1.69/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.69/0.99      | r1_tarski(sK1(X1,X0),X0)
% 1.69/0.99      | ~ l1_pre_topc(X1) ),
% 1.69/0.99      inference(cnf_transformation,[],[f63]) ).
% 1.69/0.99  
% 1.69/0.99  cnf(c_25,negated_conjecture,
% 1.69/0.99      ( l1_pre_topc(sK3) ),
% 1.69/0.99      inference(cnf_transformation,[],[f66]) ).
% 1.69/0.99  
% 1.69/0.99  cnf(c_687,plain,
% 1.69/0.99      ( v2_tex_2(X0,X1)
% 1.69/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.69/0.99      | r1_tarski(sK1(X1,X0),X0)
% 1.69/0.99      | sK3 != X1 ),
% 1.69/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_25]) ).
% 1.69/0.99  
% 1.69/0.99  cnf(c_688,plain,
% 1.69/0.99      ( v2_tex_2(X0,sK3)
% 1.69/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.69/0.99      | r1_tarski(sK1(sK3,X0),X0) ),
% 1.69/0.99      inference(unflattening,[status(thm)],[c_687]) ).
% 1.69/0.99  
% 1.69/0.99  cnf(c_2287,plain,
% 1.69/0.99      ( v2_tex_2(X0,sK3) = iProver_top
% 1.69/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 1.69/0.99      | r1_tarski(sK1(sK3,X0),X0) = iProver_top ),
% 1.69/0.99      inference(predicate_to_equality,[status(thm)],[c_688]) ).
% 1.69/0.99  
% 1.69/0.99  cnf(c_2643,plain,
% 1.69/0.99      ( v2_tex_2(sK4,sK3) = iProver_top
% 1.69/0.99      | r1_tarski(sK1(sK3,sK4),sK4) = iProver_top ),
% 1.69/0.99      inference(superposition,[status(thm)],[c_2296,c_2287]) ).
% 1.69/0.99  
% 1.69/0.99  cnf(c_30,plain,
% 1.69/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 1.69/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 1.69/0.99  
% 1.69/0.99  cnf(c_22,negated_conjecture,
% 1.69/0.99      ( ~ v2_tex_2(sK4,sK3) ),
% 1.69/0.99      inference(cnf_transformation,[],[f69]) ).
% 1.69/1.00  
% 1.69/1.00  cnf(c_1033,plain,
% 1.69/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.69/1.00      | r1_tarski(sK1(sK3,X0),X0)
% 1.69/1.00      | sK3 != sK3
% 1.69/1.00      | sK4 != X0 ),
% 1.69/1.00      inference(resolution_lifted,[status(thm)],[c_22,c_688]) ).
% 1.69/1.00  
% 1.69/1.00  cnf(c_1034,plain,
% 1.69/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.69/1.00      | r1_tarski(sK1(sK3,sK4),sK4) ),
% 1.69/1.00      inference(unflattening,[status(thm)],[c_1033]) ).
% 1.69/1.00  
% 1.69/1.00  cnf(c_1035,plain,
% 1.69/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 1.69/1.00      | r1_tarski(sK1(sK3,sK4),sK4) = iProver_top ),
% 1.69/1.00      inference(predicate_to_equality,[status(thm)],[c_1034]) ).
% 1.69/1.00  
% 1.69/1.00  cnf(c_3062,plain,
% 1.69/1.00      ( r1_tarski(sK1(sK3,sK4),sK4) = iProver_top ),
% 1.69/1.00      inference(global_propositional_subsumption,
% 1.69/1.00                [status(thm)],
% 1.69/1.00                [c_2643,c_30,c_1035]) ).
% 1.69/1.00  
% 1.69/1.00  cnf(c_7,plain,
% 1.69/1.00      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 1.69/1.00      inference(cnf_transformation,[],[f51]) ).
% 1.69/1.00  
% 1.69/1.00  cnf(c_2303,plain,
% 1.69/1.00      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 1.69/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 1.69/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 1.69/1.00  
% 1.69/1.00  cnf(c_3598,plain,
% 1.69/1.00      ( k4_xboole_0(sK1(sK3,sK4),sK4) = k1_xboole_0 ),
% 1.69/1.00      inference(superposition,[status(thm)],[c_3062,c_2303]) ).
% 1.69/1.00  
% 1.69/1.00  cnf(c_24,negated_conjecture,
% 1.69/1.00      ( v1_xboole_0(sK4) ),
% 1.69/1.00      inference(cnf_transformation,[],[f67]) ).
% 1.69/1.00  
% 1.69/1.00  cnf(c_2295,plain,
% 1.69/1.00      ( v1_xboole_0(sK4) = iProver_top ),
% 1.69/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 1.69/1.00  
% 1.69/1.00  cnf(c_3,plain,
% 1.69/1.00      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 1.69/1.00      inference(cnf_transformation,[],[f46]) ).
% 1.69/1.00  
% 1.69/1.00  cnf(c_2306,plain,
% 1.69/1.00      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 1.69/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 1.69/1.00  
% 1.69/1.00  cnf(c_3494,plain,
% 1.69/1.00      ( sK4 = k1_xboole_0 ),
% 1.69/1.00      inference(superposition,[status(thm)],[c_2295,c_2306]) ).
% 1.69/1.00  
% 1.69/1.00  cnf(c_3816,plain,
% 1.69/1.00      ( k4_xboole_0(sK1(sK3,k1_xboole_0),k1_xboole_0) = k1_xboole_0 ),
% 1.69/1.00      inference(light_normalisation,[status(thm)],[c_3598,c_3494]) ).
% 1.69/1.00  
% 1.69/1.00  cnf(c_9,plain,
% 1.69/1.00      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 1.69/1.00      inference(cnf_transformation,[],[f52]) ).
% 1.69/1.00  
% 1.69/1.00  cnf(c_2301,plain,
% 1.69/1.00      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 1.69/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 1.69/1.00  
% 1.69/1.00  cnf(c_3819,plain,
% 1.69/1.00      ( r1_tarski(k1_xboole_0,sK1(sK3,k1_xboole_0)) = iProver_top ),
% 1.69/1.00      inference(superposition,[status(thm)],[c_3816,c_2301]) ).
% 1.69/1.00  
% 1.69/1.00  cnf(c_2297,plain,
% 1.69/1.00      ( v2_tex_2(sK4,sK3) != iProver_top ),
% 1.69/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 1.69/1.00  
% 1.69/1.00  cnf(c_3673,plain,
% 1.69/1.00      ( v2_tex_2(k1_xboole_0,sK3) != iProver_top ),
% 1.69/1.00      inference(demodulation,[status(thm)],[c_3494,c_2297]) ).
% 1.69/1.00  
% 1.69/1.00  cnf(c_3670,plain,
% 1.69/1.00      ( r1_tarski(sK1(sK3,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 1.69/1.00      inference(demodulation,[status(thm)],[c_3494,c_3062]) ).
% 1.69/1.00  
% 1.69/1.00  cnf(c_4,plain,
% 1.69/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 1.69/1.00      inference(cnf_transformation,[],[f49]) ).
% 1.69/1.00  
% 1.69/1.00  cnf(c_3323,plain,
% 1.69/1.00      ( ~ r1_tarski(X0,sK1(sK3,X1))
% 1.69/1.00      | ~ r1_tarski(sK1(sK3,X1),X0)
% 1.69/1.00      | sK1(sK3,X1) = X0 ),
% 1.69/1.00      inference(instantiation,[status(thm)],[c_4]) ).
% 1.69/1.00  
% 1.69/1.00  cnf(c_3324,plain,
% 1.69/1.00      ( sK1(sK3,X0) = X1
% 1.69/1.00      | r1_tarski(X1,sK1(sK3,X0)) != iProver_top
% 1.69/1.00      | r1_tarski(sK1(sK3,X0),X1) != iProver_top ),
% 1.69/1.00      inference(predicate_to_equality,[status(thm)],[c_3323]) ).
% 1.69/1.00  
% 1.69/1.00  cnf(c_3326,plain,
% 1.69/1.00      ( sK1(sK3,k1_xboole_0) = k1_xboole_0
% 1.69/1.00      | r1_tarski(sK1(sK3,k1_xboole_0),k1_xboole_0) != iProver_top
% 1.69/1.00      | r1_tarski(k1_xboole_0,sK1(sK3,k1_xboole_0)) != iProver_top ),
% 1.69/1.00      inference(instantiation,[status(thm)],[c_3324]) ).
% 1.69/1.00  
% 1.69/1.00  cnf(c_1759,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 1.69/1.00  
% 1.69/1.00  cnf(c_3244,plain,
% 1.69/1.00      ( k9_subset_1(u1_struct_0(sK3),X0,X1) != X2
% 1.69/1.00      | k9_subset_1(u1_struct_0(sK3),X0,X1) = sK1(sK3,X0)
% 1.69/1.00      | sK1(sK3,X0) != X2 ),
% 1.69/1.00      inference(instantiation,[status(thm)],[c_1759]) ).
% 1.69/1.00  
% 1.69/1.00  cnf(c_3245,plain,
% 1.69/1.00      ( k9_subset_1(u1_struct_0(sK3),k1_xboole_0,k1_xboole_0) = sK1(sK3,k1_xboole_0)
% 1.69/1.00      | k9_subset_1(u1_struct_0(sK3),k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 1.69/1.00      | sK1(sK3,k1_xboole_0) != k1_xboole_0 ),
% 1.69/1.00      inference(instantiation,[status(thm)],[c_3244]) ).
% 1.69/1.00  
% 1.69/1.00  cnf(c_12,plain,
% 1.69/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 1.69/1.00      inference(cnf_transformation,[],[f55]) ).
% 1.69/1.00  
% 1.69/1.00  cnf(c_2476,plain,
% 1.69/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 1.69/1.00      inference(instantiation,[status(thm)],[c_12]) ).
% 1.69/1.00  
% 1.69/1.00  cnf(c_2480,plain,
% 1.69/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 1.69/1.00      inference(predicate_to_equality,[status(thm)],[c_2476]) ).
% 1.69/1.00  
% 1.69/1.00  cnf(c_16,plain,
% 1.69/1.00      ( v2_tex_2(X0,X1)
% 1.69/1.00      | ~ v3_pre_topc(X2,X1)
% 1.69/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.69/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.69/1.00      | ~ l1_pre_topc(X1)
% 1.69/1.00      | k9_subset_1(u1_struct_0(X1),X0,X2) != sK1(X1,X0) ),
% 1.69/1.00      inference(cnf_transformation,[],[f64]) ).
% 1.69/1.00  
% 1.69/1.00  cnf(c_15,plain,
% 1.69/1.00      ( v3_pre_topc(X0,X1)
% 1.69/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.69/1.00      | ~ v2_pre_topc(X1)
% 1.69/1.00      | ~ l1_pre_topc(X1)
% 1.69/1.00      | ~ v1_xboole_0(X0) ),
% 1.69/1.00      inference(cnf_transformation,[],[f58]) ).
% 1.69/1.00  
% 1.69/1.00  cnf(c_26,negated_conjecture,
% 1.69/1.00      ( v2_pre_topc(sK3) ),
% 1.69/1.00      inference(cnf_transformation,[],[f65]) ).
% 1.69/1.00  
% 1.69/1.00  cnf(c_346,plain,
% 1.69/1.00      ( v3_pre_topc(X0,X1)
% 1.69/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.69/1.00      | ~ l1_pre_topc(X1)
% 1.69/1.00      | ~ v1_xboole_0(X0)
% 1.69/1.00      | sK3 != X1 ),
% 1.69/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_26]) ).
% 1.69/1.00  
% 1.69/1.00  cnf(c_347,plain,
% 1.69/1.00      ( v3_pre_topc(X0,sK3)
% 1.69/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.69/1.00      | ~ l1_pre_topc(sK3)
% 1.69/1.00      | ~ v1_xboole_0(X0) ),
% 1.69/1.00      inference(unflattening,[status(thm)],[c_346]) ).
% 1.69/1.00  
% 1.69/1.00  cnf(c_351,plain,
% 1.69/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.69/1.00      | v3_pre_topc(X0,sK3)
% 1.69/1.00      | ~ v1_xboole_0(X0) ),
% 1.69/1.00      inference(global_propositional_subsumption,
% 1.69/1.00                [status(thm)],
% 1.69/1.00                [c_347,c_25]) ).
% 1.69/1.00  
% 1.69/1.00  cnf(c_352,plain,
% 1.69/1.00      ( v3_pre_topc(X0,sK3)
% 1.69/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.69/1.00      | ~ v1_xboole_0(X0) ),
% 1.69/1.00      inference(renaming,[status(thm)],[c_351]) ).
% 1.69/1.00  
% 1.69/1.00  cnf(c_434,plain,
% 1.69/1.00      ( v2_tex_2(X0,X1)
% 1.69/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.69/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.69/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.69/1.00      | ~ l1_pre_topc(X1)
% 1.69/1.00      | ~ v1_xboole_0(X3)
% 1.69/1.00      | X3 != X2
% 1.69/1.00      | k9_subset_1(u1_struct_0(X1),X0,X2) != sK1(X1,X0)
% 1.69/1.00      | sK3 != X1 ),
% 1.69/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_352]) ).
% 1.69/1.00  
% 1.69/1.00  cnf(c_435,plain,
% 1.69/1.00      ( v2_tex_2(X0,sK3)
% 1.69/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.69/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.69/1.00      | ~ l1_pre_topc(sK3)
% 1.69/1.00      | ~ v1_xboole_0(X1)
% 1.69/1.00      | k9_subset_1(u1_struct_0(sK3),X0,X1) != sK1(sK3,X0) ),
% 1.69/1.00      inference(unflattening,[status(thm)],[c_434]) ).
% 1.69/1.00  
% 1.69/1.00  cnf(c_439,plain,
% 1.69/1.00      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.69/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.69/1.00      | v2_tex_2(X0,sK3)
% 1.69/1.00      | ~ v1_xboole_0(X1)
% 1.69/1.00      | k9_subset_1(u1_struct_0(sK3),X0,X1) != sK1(sK3,X0) ),
% 1.69/1.00      inference(global_propositional_subsumption,
% 1.69/1.00                [status(thm)],
% 1.69/1.00                [c_435,c_25]) ).
% 1.69/1.00  
% 1.69/1.00  cnf(c_440,plain,
% 1.69/1.00      ( v2_tex_2(X0,sK3)
% 1.69/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.69/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.69/1.00      | ~ v1_xboole_0(X1)
% 1.69/1.00      | k9_subset_1(u1_struct_0(sK3),X0,X1) != sK1(sK3,X0) ),
% 1.69/1.00      inference(renaming,[status(thm)],[c_439]) ).
% 1.69/1.00  
% 1.69/1.00  cnf(c_441,plain,
% 1.69/1.00      ( k9_subset_1(u1_struct_0(sK3),X0,X1) != sK1(sK3,X0)
% 1.69/1.00      | v2_tex_2(X0,sK3) = iProver_top
% 1.69/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 1.69/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 1.69/1.00      | v1_xboole_0(X1) != iProver_top ),
% 1.69/1.00      inference(predicate_to_equality,[status(thm)],[c_440]) ).
% 1.69/1.00  
% 1.69/1.00  cnf(c_443,plain,
% 1.69/1.00      ( k9_subset_1(u1_struct_0(sK3),k1_xboole_0,k1_xboole_0) != sK1(sK3,k1_xboole_0)
% 1.69/1.00      | v2_tex_2(k1_xboole_0,sK3) = iProver_top
% 1.69/1.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 1.69/1.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 1.69/1.00      inference(instantiation,[status(thm)],[c_441]) ).
% 1.69/1.00  
% 1.69/1.00  cnf(c_2,plain,
% 1.69/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 1.69/1.00      inference(cnf_transformation,[],[f45]) ).
% 1.69/1.00  
% 1.69/1.00  cnf(c_87,plain,
% 1.69/1.00      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 1.69/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 1.69/1.00  
% 1.69/1.00  cnf(contradiction,plain,
% 1.69/1.00      ( $false ),
% 1.69/1.00      inference(minisat,
% 1.69/1.00                [status(thm)],
% 1.69/1.00                [c_4846,c_3819,c_3673,c_3670,c_3326,c_3245,c_2480,c_2476,
% 1.69/1.00                 c_443,c_87]) ).
% 1.69/1.00  
% 1.69/1.00  
% 1.69/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 1.69/1.00  
% 1.69/1.00  ------                               Statistics
% 1.69/1.00  
% 1.69/1.00  ------ General
% 1.69/1.00  
% 1.69/1.00  abstr_ref_over_cycles:                  0
% 1.69/1.00  abstr_ref_under_cycles:                 0
% 1.69/1.00  gc_basic_clause_elim:                   0
% 1.69/1.00  forced_gc_time:                         0
% 1.69/1.00  parsing_time:                           0.015
% 1.69/1.00  unif_index_cands_time:                  0.
% 1.69/1.00  unif_index_add_time:                    0.
% 1.69/1.00  orderings_time:                         0.
% 1.69/1.00  out_proof_time:                         0.009
% 1.69/1.00  total_time:                             0.154
% 1.69/1.00  num_of_symbols:                         49
% 1.69/1.00  num_of_terms:                           3498
% 1.69/1.00  
% 1.69/1.00  ------ Preprocessing
% 1.69/1.00  
% 1.69/1.00  num_of_splits:                          0
% 1.69/1.00  num_of_split_atoms:                     0
% 1.69/1.00  num_of_reused_defs:                     0
% 1.69/1.00  num_eq_ax_congr_red:                    28
% 1.69/1.00  num_of_sem_filtered_clauses:            1
% 1.69/1.00  num_of_subtypes:                        0
% 1.69/1.00  monotx_restored_types:                  0
% 1.69/1.00  sat_num_of_epr_types:                   0
% 1.69/1.00  sat_num_of_non_cyclic_types:            0
% 1.69/1.00  sat_guarded_non_collapsed_types:        0
% 1.69/1.00  num_pure_diseq_elim:                    0
% 1.69/1.00  simp_replaced_by:                       0
% 1.69/1.00  res_preprocessed:                       117
% 1.69/1.00  prep_upred:                             0
% 1.69/1.00  prep_unflattend:                        39
% 1.69/1.00  smt_new_axioms:                         0
% 1.69/1.00  pred_elim_cands:                        5
% 1.69/1.00  pred_elim:                              3
% 1.69/1.00  pred_elim_cl:                           4
% 1.69/1.00  pred_elim_cycles:                       10
% 1.69/1.00  merged_defs:                            8
% 1.69/1.00  merged_defs_ncl:                        0
% 1.69/1.00  bin_hyper_res:                          8
% 1.69/1.00  prep_cycles:                            4
% 1.69/1.00  pred_elim_time:                         0.023
% 1.69/1.00  splitting_time:                         0.
% 1.69/1.00  sem_filter_time:                        0.
% 1.69/1.00  monotx_time:                            0.
% 1.69/1.00  subtype_inf_time:                       0.
% 1.69/1.00  
% 1.69/1.00  ------ Problem properties
% 1.69/1.00  
% 1.69/1.00  clauses:                                22
% 1.69/1.00  conjectures:                            3
% 1.69/1.00  epr:                                    6
% 1.69/1.00  horn:                                   18
% 1.69/1.00  ground:                                 4
% 1.69/1.00  unary:                                  8
% 1.69/1.00  binary:                                 5
% 1.69/1.00  lits:                                   53
% 1.69/1.00  lits_eq:                                7
% 1.69/1.00  fd_pure:                                0
% 1.69/1.00  fd_pseudo:                              0
% 1.69/1.00  fd_cond:                                1
% 1.69/1.00  fd_pseudo_cond:                         1
% 1.69/1.00  ac_symbols:                             0
% 1.69/1.00  
% 1.69/1.00  ------ Propositional Solver
% 1.69/1.00  
% 1.69/1.00  prop_solver_calls:                      28
% 1.69/1.00  prop_fast_solver_calls:                 1001
% 1.69/1.00  smt_solver_calls:                       0
% 1.69/1.00  smt_fast_solver_calls:                  0
% 1.69/1.00  prop_num_of_clauses:                    1326
% 1.69/1.00  prop_preprocess_simplified:             5007
% 1.69/1.00  prop_fo_subsumed:                       20
% 1.69/1.00  prop_solver_time:                       0.
% 1.69/1.00  smt_solver_time:                        0.
% 1.69/1.00  smt_fast_solver_time:                   0.
% 1.69/1.00  prop_fast_solver_time:                  0.
% 1.69/1.00  prop_unsat_core_time:                   0.
% 1.69/1.00  
% 1.69/1.00  ------ QBF
% 1.69/1.00  
% 1.69/1.00  qbf_q_res:                              0
% 1.69/1.00  qbf_num_tautologies:                    0
% 1.69/1.00  qbf_prep_cycles:                        0
% 1.69/1.00  
% 1.69/1.00  ------ BMC1
% 1.69/1.00  
% 1.69/1.00  bmc1_current_bound:                     -1
% 1.69/1.00  bmc1_last_solved_bound:                 -1
% 1.69/1.00  bmc1_unsat_core_size:                   -1
% 1.69/1.00  bmc1_unsat_core_parents_size:           -1
% 1.69/1.00  bmc1_merge_next_fun:                    0
% 1.69/1.00  bmc1_unsat_core_clauses_time:           0.
% 1.69/1.00  
% 1.69/1.00  ------ Instantiation
% 1.69/1.00  
% 1.69/1.00  inst_num_of_clauses:                    364
% 1.69/1.00  inst_num_in_passive:                    149
% 1.69/1.00  inst_num_in_active:                     175
% 1.69/1.00  inst_num_in_unprocessed:                40
% 1.69/1.00  inst_num_of_loops:                      227
% 1.69/1.00  inst_num_of_learning_restarts:          0
% 1.69/1.00  inst_num_moves_active_passive:          48
% 1.69/1.00  inst_lit_activity:                      0
% 1.69/1.00  inst_lit_activity_moves:                0
% 1.69/1.00  inst_num_tautologies:                   0
% 1.69/1.00  inst_num_prop_implied:                  0
% 1.69/1.00  inst_num_existing_simplified:           0
% 1.69/1.00  inst_num_eq_res_simplified:             0
% 1.69/1.00  inst_num_child_elim:                    0
% 1.69/1.00  inst_num_of_dismatching_blockings:      111
% 1.69/1.00  inst_num_of_non_proper_insts:           366
% 1.69/1.00  inst_num_of_duplicates:                 0
% 1.69/1.00  inst_inst_num_from_inst_to_res:         0
% 1.69/1.00  inst_dismatching_checking_time:         0.
% 1.69/1.00  
% 1.69/1.00  ------ Resolution
% 1.69/1.00  
% 1.69/1.00  res_num_of_clauses:                     0
% 1.69/1.00  res_num_in_passive:                     0
% 1.69/1.00  res_num_in_active:                      0
% 1.69/1.00  res_num_of_loops:                       121
% 1.69/1.00  res_forward_subset_subsumed:            34
% 1.69/1.00  res_backward_subset_subsumed:           2
% 1.69/1.00  res_forward_subsumed:                   0
% 1.69/1.00  res_backward_subsumed:                  0
% 1.69/1.00  res_forward_subsumption_resolution:     3
% 1.69/1.00  res_backward_subsumption_resolution:    0
% 1.69/1.00  res_clause_to_clause_subsumption:       407
% 1.69/1.00  res_orphan_elimination:                 0
% 1.69/1.00  res_tautology_del:                      46
% 1.69/1.00  res_num_eq_res_simplified:              0
% 1.69/1.00  res_num_sel_changes:                    0
% 1.69/1.00  res_moves_from_active_to_pass:          0
% 1.69/1.00  
% 1.69/1.00  ------ Superposition
% 1.69/1.00  
% 1.69/1.00  sup_time_total:                         0.
% 1.69/1.00  sup_time_generating:                    0.
% 1.69/1.00  sup_time_sim_full:                      0.
% 1.69/1.00  sup_time_sim_immed:                     0.
% 1.69/1.00  
% 1.69/1.00  sup_num_of_clauses:                     56
% 1.69/1.00  sup_num_in_active:                      37
% 1.69/1.00  sup_num_in_passive:                     19
% 1.69/1.00  sup_num_of_loops:                       44
% 1.69/1.00  sup_fw_superposition:                   27
% 1.69/1.00  sup_bw_superposition:                   27
% 1.69/1.00  sup_immediate_simplified:               10
% 1.69/1.00  sup_given_eliminated:                   0
% 1.69/1.00  comparisons_done:                       0
% 1.69/1.00  comparisons_avoided:                    0
% 1.69/1.00  
% 1.69/1.00  ------ Simplifications
% 1.69/1.00  
% 1.69/1.00  
% 1.69/1.00  sim_fw_subset_subsumed:                 5
% 1.69/1.00  sim_bw_subset_subsumed:                 3
% 1.69/1.00  sim_fw_subsumed:                        3
% 1.69/1.00  sim_bw_subsumed:                        0
% 1.69/1.00  sim_fw_subsumption_res:                 3
% 1.69/1.00  sim_bw_subsumption_res:                 0
% 1.69/1.00  sim_tautology_del:                      0
% 1.69/1.00  sim_eq_tautology_del:                   2
% 1.69/1.00  sim_eq_res_simp:                        0
% 1.69/1.00  sim_fw_demodulated:                     0
% 1.69/1.00  sim_bw_demodulated:                     6
% 1.69/1.00  sim_light_normalised:                   1
% 1.69/1.00  sim_joinable_taut:                      0
% 1.69/1.00  sim_joinable_simp:                      0
% 1.69/1.00  sim_ac_normalised:                      0
% 1.69/1.00  sim_smt_subsumption:                    0
% 1.69/1.00  
%------------------------------------------------------------------------------
