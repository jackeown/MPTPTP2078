%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:26:09 EST 2020

% Result     : Theorem 2.43s
% Output     : CNFRefutation 2.43s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 276 expanded)
%              Number of clauses        :   76 ( 108 expanded)
%              Number of leaves         :   16 (  61 expanded)
%              Depth                    :   18
%              Number of atoms          :  392 (1078 expanded)
%              Number of equality atoms :  117 ( 176 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

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

fof(f48,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f8,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

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
    inference(ennf_transformation,[],[f13])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

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
    inference(nnf_transformation,[],[f27])).

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

fof(f62,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | r1_tarski(sK1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

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

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f29,f41,f40])).

fof(f65,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f68,plain,(
    ~ v2_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f44,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f66,plain,(
    v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f42])).

fof(f63,plain,(
    ! [X0,X3,X1] :
      ( v2_tex_2(X1,X0)
      | k9_subset_1(u1_struct_0(X0),X1,X3) != sK1(X0,X1)
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v3_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f64,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1564,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_4456,plain,
    ( X0 != X1
    | k9_subset_1(u1_struct_0(sK3),X2,X3) != X1
    | k9_subset_1(u1_struct_0(sK3),X2,X3) = X0 ),
    inference(instantiation,[status(thm)],[c_1564])).

cnf(c_4909,plain,
    ( X0 != k3_xboole_0(X1,X2)
    | k9_subset_1(u1_struct_0(sK3),X1,X2) = X0
    | k9_subset_1(u1_struct_0(sK3),X1,X2) != k3_xboole_0(X1,X2) ),
    inference(instantiation,[status(thm)],[c_4456])).

cnf(c_11160,plain,
    ( k9_subset_1(X0,X1,X2) != k3_xboole_0(X1,X2)
    | k9_subset_1(u1_struct_0(sK3),X1,X2) = k9_subset_1(X0,X1,X2)
    | k9_subset_1(u1_struct_0(sK3),X1,X2) != k3_xboole_0(X1,X2) ),
    inference(instantiation,[status(thm)],[c_4909])).

cnf(c_11161,plain,
    ( k9_subset_1(u1_struct_0(sK3),k1_xboole_0,k1_xboole_0) = k9_subset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | k9_subset_1(u1_struct_0(sK3),k1_xboole_0,k1_xboole_0) != k3_xboole_0(k1_xboole_0,k1_xboole_0)
    | k9_subset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) != k3_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_11160])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_10,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_200,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_10])).

cnf(c_201,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_200])).

cnf(c_241,plain,
    ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
    | ~ r1_tarski(X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_7,c_201])).

cnf(c_2051,plain,
    ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) = iProver_top
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_241])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2054,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_4329,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k9_subset_1(X1,X2,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2051,c_2054])).

cnf(c_6,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_2057,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_2059,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3109,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2057,c_2059])).

cnf(c_5253,plain,
    ( k9_subset_1(k1_xboole_0,X0,X1) = k1_xboole_0
    | r1_tarski(X1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4329,c_3109])).

cnf(c_5307,plain,
    ( k9_subset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5253])).

cnf(c_2579,plain,
    ( X0 != X1
    | sK1(sK3,X2) != X1
    | sK1(sK3,X2) = X0 ),
    inference(instantiation,[status(thm)],[c_1564])).

cnf(c_5038,plain,
    ( k9_subset_1(X0,X1,X2) != X3
    | sK1(sK3,X1) != X3
    | sK1(sK3,X1) = k9_subset_1(X0,X1,X2) ),
    inference(instantiation,[status(thm)],[c_2579])).

cnf(c_5039,plain,
    ( k9_subset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | sK1(sK3,k1_xboole_0) = k9_subset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | sK1(sK3,k1_xboole_0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5038])).

cnf(c_2337,plain,
    ( k9_subset_1(u1_struct_0(sK3),X0,X1) != X2
    | k9_subset_1(u1_struct_0(sK3),X0,X1) = sK1(sK3,X0)
    | sK1(sK3,X0) != X2 ),
    inference(instantiation,[status(thm)],[c_1564])).

cnf(c_4457,plain,
    ( k9_subset_1(u1_struct_0(sK3),X0,X1) != k9_subset_1(X2,X0,X3)
    | k9_subset_1(u1_struct_0(sK3),X0,X1) = sK1(sK3,X0)
    | sK1(sK3,X0) != k9_subset_1(X2,X0,X3) ),
    inference(instantiation,[status(thm)],[c_2337])).

cnf(c_4459,plain,
    ( k9_subset_1(u1_struct_0(sK3),k1_xboole_0,k1_xboole_0) != k9_subset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | k9_subset_1(u1_struct_0(sK3),k1_xboole_0,k1_xboole_0) = sK1(sK3,k1_xboole_0)
    | sK1(sK3,k1_xboole_0) != k9_subset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_4457])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_242,plain,
    ( ~ r1_tarski(X0,X1)
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_8,c_201])).

cnf(c_4446,plain,
    ( ~ r1_tarski(X0,u1_struct_0(sK3))
    | k9_subset_1(u1_struct_0(sK3),X1,X0) = k3_xboole_0(X1,X0) ),
    inference(instantiation,[status(thm)],[c_242])).

cnf(c_4449,plain,
    ( ~ r1_tarski(k1_xboole_0,u1_struct_0(sK3))
    | k9_subset_1(u1_struct_0(sK3),k1_xboole_0,k1_xboole_0) = k3_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_4446])).

cnf(c_9,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2056,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_16,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(sK1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_24,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_598,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(sK1(X1,X0),X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_24])).

cnf(c_599,plain,
    ( v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | r1_tarski(sK1(sK3,X0),X0) ),
    inference(unflattening,[status(thm)],[c_598])).

cnf(c_2042,plain,
    ( v2_tex_2(X0,sK3) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r1_tarski(sK1(sK3,X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_599])).

cnf(c_2566,plain,
    ( v2_tex_2(k1_xboole_0,sK3) = iProver_top
    | r1_tarski(sK1(sK3,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2056,c_2042])).

cnf(c_600,plain,
    ( v2_tex_2(X0,sK3) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r1_tarski(sK1(sK3,X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_599])).

cnf(c_602,plain,
    ( v2_tex_2(k1_xboole_0,sK3) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r1_tarski(sK1(sK3,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_600])).

cnf(c_21,negated_conjecture,
    ( ~ v2_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2053,plain,
    ( v2_tex_2(sK4,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_23,negated_conjecture,
    ( v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_420,plain,
    ( sK4 != X0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_23])).

cnf(c_421,plain,
    ( k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_420])).

cnf(c_2069,plain,
    ( v2_tex_2(k1_xboole_0,sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2053,c_421])).

cnf(c_2213,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2217,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2213])).

cnf(c_2913,plain,
    ( r1_tarski(sK1(sK3,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2566,c_602,c_2069,c_2217])).

cnf(c_3178,plain,
    ( sK1(sK3,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2913,c_3109])).

cnf(c_2343,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | r1_tarski(X0,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2345,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3)))
    | r1_tarski(k1_xboole_0,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_2343])).

cnf(c_2160,plain,
    ( ~ v2_tex_2(k1_xboole_0,sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2069])).

cnf(c_15,plain,
    ( v2_tex_2(X0,X1)
    | ~ v3_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),X0,X2) != sK1(X1,X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_14,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_25,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_338,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_25])).

cnf(c_339,plain,
    ( v3_pre_topc(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3)
    | ~ v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_338])).

cnf(c_343,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v3_pre_topc(X0,sK3)
    | ~ v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_339,c_24])).

cnf(c_344,plain,
    ( v3_pre_topc(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_343])).

cnf(c_397,plain,
    ( v3_pre_topc(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | k1_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_344])).

cnf(c_398,plain,
    ( v3_pre_topc(k1_xboole_0,sK3)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(unflattening,[status(thm)],[c_397])).

cnf(c_404,plain,
    ( v3_pre_topc(k1_xboole_0,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_398,c_9])).

cnf(c_461,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),X0,X2) != sK1(X1,X0)
    | sK3 != X1
    | k1_xboole_0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_404])).

cnf(c_462,plain,
    ( v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3)
    | k9_subset_1(u1_struct_0(sK3),X0,k1_xboole_0) != sK1(sK3,X0) ),
    inference(unflattening,[status(thm)],[c_461])).

cnf(c_464,plain,
    ( v2_tex_2(k1_xboole_0,sK3)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3)
    | k9_subset_1(u1_struct_0(sK3),k1_xboole_0,k1_xboole_0) != sK1(sK3,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_462])).

cnf(c_68,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | k9_subset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k3_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_64,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_66,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_64])).

cnf(c_65,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_58,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_60,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_58])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11161,c_5307,c_5039,c_4459,c_4449,c_3178,c_2345,c_2213,c_2160,c_464,c_68,c_66,c_65,c_60,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:36:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.43/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.43/1.00  
% 2.43/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.43/1.00  
% 2.43/1.00  ------  iProver source info
% 2.43/1.00  
% 2.43/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.43/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.43/1.00  git: non_committed_changes: false
% 2.43/1.00  git: last_make_outside_of_git: false
% 2.43/1.00  
% 2.43/1.00  ------ 
% 2.43/1.00  
% 2.43/1.00  ------ Input Options
% 2.43/1.00  
% 2.43/1.00  --out_options                           all
% 2.43/1.00  --tptp_safe_out                         true
% 2.43/1.00  --problem_path                          ""
% 2.43/1.00  --include_path                          ""
% 2.43/1.00  --clausifier                            res/vclausify_rel
% 2.43/1.00  --clausifier_options                    --mode clausify
% 2.43/1.00  --stdin                                 false
% 2.43/1.00  --stats_out                             all
% 2.43/1.00  
% 2.43/1.00  ------ General Options
% 2.43/1.00  
% 2.43/1.00  --fof                                   false
% 2.43/1.00  --time_out_real                         305.
% 2.43/1.00  --time_out_virtual                      -1.
% 2.43/1.00  --symbol_type_check                     false
% 2.43/1.00  --clausify_out                          false
% 2.43/1.00  --sig_cnt_out                           false
% 2.43/1.00  --trig_cnt_out                          false
% 2.43/1.00  --trig_cnt_out_tolerance                1.
% 2.43/1.00  --trig_cnt_out_sk_spl                   false
% 2.43/1.00  --abstr_cl_out                          false
% 2.43/1.00  
% 2.43/1.00  ------ Global Options
% 2.43/1.00  
% 2.43/1.00  --schedule                              default
% 2.43/1.00  --add_important_lit                     false
% 2.43/1.00  --prop_solver_per_cl                    1000
% 2.43/1.00  --min_unsat_core                        false
% 2.43/1.00  --soft_assumptions                      false
% 2.43/1.00  --soft_lemma_size                       3
% 2.43/1.00  --prop_impl_unit_size                   0
% 2.43/1.00  --prop_impl_unit                        []
% 2.43/1.00  --share_sel_clauses                     true
% 2.43/1.00  --reset_solvers                         false
% 2.43/1.00  --bc_imp_inh                            [conj_cone]
% 2.43/1.00  --conj_cone_tolerance                   3.
% 2.43/1.00  --extra_neg_conj                        none
% 2.43/1.00  --large_theory_mode                     true
% 2.43/1.00  --prolific_symb_bound                   200
% 2.43/1.00  --lt_threshold                          2000
% 2.43/1.00  --clause_weak_htbl                      true
% 2.43/1.00  --gc_record_bc_elim                     false
% 2.43/1.00  
% 2.43/1.00  ------ Preprocessing Options
% 2.43/1.00  
% 2.43/1.00  --preprocessing_flag                    true
% 2.43/1.00  --time_out_prep_mult                    0.1
% 2.43/1.00  --splitting_mode                        input
% 2.43/1.00  --splitting_grd                         true
% 2.43/1.00  --splitting_cvd                         false
% 2.43/1.00  --splitting_cvd_svl                     false
% 2.43/1.00  --splitting_nvd                         32
% 2.43/1.00  --sub_typing                            true
% 2.43/1.00  --prep_gs_sim                           true
% 2.43/1.00  --prep_unflatten                        true
% 2.43/1.00  --prep_res_sim                          true
% 2.43/1.00  --prep_upred                            true
% 2.43/1.00  --prep_sem_filter                       exhaustive
% 2.43/1.00  --prep_sem_filter_out                   false
% 2.43/1.00  --pred_elim                             true
% 2.43/1.00  --res_sim_input                         true
% 2.43/1.00  --eq_ax_congr_red                       true
% 2.43/1.00  --pure_diseq_elim                       true
% 2.43/1.00  --brand_transform                       false
% 2.43/1.00  --non_eq_to_eq                          false
% 2.43/1.00  --prep_def_merge                        true
% 2.43/1.00  --prep_def_merge_prop_impl              false
% 2.43/1.00  --prep_def_merge_mbd                    true
% 2.43/1.00  --prep_def_merge_tr_red                 false
% 2.43/1.00  --prep_def_merge_tr_cl                  false
% 2.43/1.00  --smt_preprocessing                     true
% 2.43/1.00  --smt_ac_axioms                         fast
% 2.43/1.00  --preprocessed_out                      false
% 2.43/1.00  --preprocessed_stats                    false
% 2.43/1.00  
% 2.43/1.00  ------ Abstraction refinement Options
% 2.43/1.00  
% 2.43/1.00  --abstr_ref                             []
% 2.43/1.00  --abstr_ref_prep                        false
% 2.43/1.00  --abstr_ref_until_sat                   false
% 2.43/1.00  --abstr_ref_sig_restrict                funpre
% 2.43/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.43/1.00  --abstr_ref_under                       []
% 2.43/1.00  
% 2.43/1.00  ------ SAT Options
% 2.43/1.00  
% 2.43/1.00  --sat_mode                              false
% 2.43/1.00  --sat_fm_restart_options                ""
% 2.43/1.00  --sat_gr_def                            false
% 2.43/1.00  --sat_epr_types                         true
% 2.43/1.00  --sat_non_cyclic_types                  false
% 2.43/1.00  --sat_finite_models                     false
% 2.43/1.00  --sat_fm_lemmas                         false
% 2.43/1.00  --sat_fm_prep                           false
% 2.43/1.00  --sat_fm_uc_incr                        true
% 2.43/1.00  --sat_out_model                         small
% 2.43/1.00  --sat_out_clauses                       false
% 2.43/1.00  
% 2.43/1.00  ------ QBF Options
% 2.43/1.00  
% 2.43/1.00  --qbf_mode                              false
% 2.43/1.00  --qbf_elim_univ                         false
% 2.43/1.00  --qbf_dom_inst                          none
% 2.43/1.00  --qbf_dom_pre_inst                      false
% 2.43/1.00  --qbf_sk_in                             false
% 2.43/1.00  --qbf_pred_elim                         true
% 2.43/1.00  --qbf_split                             512
% 2.43/1.00  
% 2.43/1.00  ------ BMC1 Options
% 2.43/1.00  
% 2.43/1.00  --bmc1_incremental                      false
% 2.43/1.00  --bmc1_axioms                           reachable_all
% 2.43/1.00  --bmc1_min_bound                        0
% 2.43/1.00  --bmc1_max_bound                        -1
% 2.43/1.00  --bmc1_max_bound_default                -1
% 2.43/1.00  --bmc1_symbol_reachability              true
% 2.43/1.00  --bmc1_property_lemmas                  false
% 2.43/1.00  --bmc1_k_induction                      false
% 2.43/1.00  --bmc1_non_equiv_states                 false
% 2.43/1.00  --bmc1_deadlock                         false
% 2.43/1.00  --bmc1_ucm                              false
% 2.43/1.00  --bmc1_add_unsat_core                   none
% 2.43/1.00  --bmc1_unsat_core_children              false
% 2.43/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.43/1.00  --bmc1_out_stat                         full
% 2.43/1.00  --bmc1_ground_init                      false
% 2.43/1.00  --bmc1_pre_inst_next_state              false
% 2.43/1.00  --bmc1_pre_inst_state                   false
% 2.43/1.00  --bmc1_pre_inst_reach_state             false
% 2.43/1.00  --bmc1_out_unsat_core                   false
% 2.43/1.00  --bmc1_aig_witness_out                  false
% 2.43/1.00  --bmc1_verbose                          false
% 2.43/1.00  --bmc1_dump_clauses_tptp                false
% 2.43/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.43/1.00  --bmc1_dump_file                        -
% 2.43/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.43/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.43/1.00  --bmc1_ucm_extend_mode                  1
% 2.43/1.00  --bmc1_ucm_init_mode                    2
% 2.43/1.00  --bmc1_ucm_cone_mode                    none
% 2.43/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.43/1.00  --bmc1_ucm_relax_model                  4
% 2.43/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.43/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.43/1.00  --bmc1_ucm_layered_model                none
% 2.43/1.00  --bmc1_ucm_max_lemma_size               10
% 2.43/1.00  
% 2.43/1.00  ------ AIG Options
% 2.43/1.00  
% 2.43/1.00  --aig_mode                              false
% 2.43/1.00  
% 2.43/1.00  ------ Instantiation Options
% 2.43/1.00  
% 2.43/1.00  --instantiation_flag                    true
% 2.43/1.00  --inst_sos_flag                         false
% 2.43/1.00  --inst_sos_phase                        true
% 2.43/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.43/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.43/1.00  --inst_lit_sel_side                     num_symb
% 2.43/1.00  --inst_solver_per_active                1400
% 2.43/1.00  --inst_solver_calls_frac                1.
% 2.43/1.00  --inst_passive_queue_type               priority_queues
% 2.43/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.43/1.00  --inst_passive_queues_freq              [25;2]
% 2.43/1.00  --inst_dismatching                      true
% 2.43/1.00  --inst_eager_unprocessed_to_passive     true
% 2.43/1.00  --inst_prop_sim_given                   true
% 2.43/1.00  --inst_prop_sim_new                     false
% 2.43/1.00  --inst_subs_new                         false
% 2.43/1.00  --inst_eq_res_simp                      false
% 2.43/1.00  --inst_subs_given                       false
% 2.43/1.00  --inst_orphan_elimination               true
% 2.43/1.00  --inst_learning_loop_flag               true
% 2.43/1.00  --inst_learning_start                   3000
% 2.43/1.00  --inst_learning_factor                  2
% 2.43/1.00  --inst_start_prop_sim_after_learn       3
% 2.43/1.00  --inst_sel_renew                        solver
% 2.43/1.00  --inst_lit_activity_flag                true
% 2.43/1.00  --inst_restr_to_given                   false
% 2.43/1.00  --inst_activity_threshold               500
% 2.43/1.00  --inst_out_proof                        true
% 2.43/1.00  
% 2.43/1.00  ------ Resolution Options
% 2.43/1.00  
% 2.43/1.00  --resolution_flag                       true
% 2.43/1.00  --res_lit_sel                           adaptive
% 2.43/1.00  --res_lit_sel_side                      none
% 2.43/1.00  --res_ordering                          kbo
% 2.43/1.00  --res_to_prop_solver                    active
% 2.43/1.00  --res_prop_simpl_new                    false
% 2.43/1.00  --res_prop_simpl_given                  true
% 2.43/1.00  --res_passive_queue_type                priority_queues
% 2.43/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.43/1.00  --res_passive_queues_freq               [15;5]
% 2.43/1.00  --res_forward_subs                      full
% 2.43/1.00  --res_backward_subs                     full
% 2.43/1.00  --res_forward_subs_resolution           true
% 2.43/1.00  --res_backward_subs_resolution          true
% 2.43/1.00  --res_orphan_elimination                true
% 2.43/1.00  --res_time_limit                        2.
% 2.43/1.00  --res_out_proof                         true
% 2.43/1.00  
% 2.43/1.00  ------ Superposition Options
% 2.43/1.00  
% 2.43/1.00  --superposition_flag                    true
% 2.43/1.00  --sup_passive_queue_type                priority_queues
% 2.43/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.43/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.43/1.00  --demod_completeness_check              fast
% 2.43/1.00  --demod_use_ground                      true
% 2.43/1.00  --sup_to_prop_solver                    passive
% 2.43/1.00  --sup_prop_simpl_new                    true
% 2.43/1.00  --sup_prop_simpl_given                  true
% 2.43/1.00  --sup_fun_splitting                     false
% 2.43/1.00  --sup_smt_interval                      50000
% 2.43/1.00  
% 2.43/1.00  ------ Superposition Simplification Setup
% 2.43/1.00  
% 2.43/1.00  --sup_indices_passive                   []
% 2.43/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.43/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.43/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.43/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.43/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.43/1.00  --sup_full_bw                           [BwDemod]
% 2.43/1.00  --sup_immed_triv                        [TrivRules]
% 2.43/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.43/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.43/1.00  --sup_immed_bw_main                     []
% 2.43/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.43/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.43/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.43/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.43/1.00  
% 2.43/1.00  ------ Combination Options
% 2.43/1.00  
% 2.43/1.00  --comb_res_mult                         3
% 2.43/1.00  --comb_sup_mult                         2
% 2.43/1.00  --comb_inst_mult                        10
% 2.43/1.00  
% 2.43/1.00  ------ Debug Options
% 2.43/1.00  
% 2.43/1.00  --dbg_backtrace                         false
% 2.43/1.00  --dbg_dump_prop_clauses                 false
% 2.43/1.00  --dbg_dump_prop_clauses_file            -
% 2.43/1.00  --dbg_out_stat                          false
% 2.43/1.00  ------ Parsing...
% 2.43/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.43/1.00  
% 2.43/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 2.43/1.00  
% 2.43/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.43/1.00  
% 2.43/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.43/1.00  ------ Proving...
% 2.43/1.00  ------ Problem Properties 
% 2.43/1.00  
% 2.43/1.00  
% 2.43/1.00  clauses                                 21
% 2.43/1.00  conjectures                             2
% 2.43/1.00  EPR                                     7
% 2.43/1.00  Horn                                    18
% 2.43/1.00  unary                                   8
% 2.43/1.00  binary                                  5
% 2.43/1.00  lits                                    50
% 2.43/1.00  lits eq                                 7
% 2.43/1.00  fd_pure                                 0
% 2.43/1.00  fd_pseudo                               0
% 2.43/1.00  fd_cond                                 2
% 2.43/1.00  fd_pseudo_cond                          1
% 2.43/1.00  AC symbols                              0
% 2.43/1.00  
% 2.43/1.00  ------ Schedule dynamic 5 is on 
% 2.43/1.00  
% 2.43/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.43/1.00  
% 2.43/1.00  
% 2.43/1.00  ------ 
% 2.43/1.00  Current options:
% 2.43/1.00  ------ 
% 2.43/1.00  
% 2.43/1.00  ------ Input Options
% 2.43/1.00  
% 2.43/1.00  --out_options                           all
% 2.43/1.00  --tptp_safe_out                         true
% 2.43/1.00  --problem_path                          ""
% 2.43/1.00  --include_path                          ""
% 2.43/1.00  --clausifier                            res/vclausify_rel
% 2.43/1.00  --clausifier_options                    --mode clausify
% 2.43/1.00  --stdin                                 false
% 2.43/1.00  --stats_out                             all
% 2.43/1.00  
% 2.43/1.00  ------ General Options
% 2.43/1.00  
% 2.43/1.00  --fof                                   false
% 2.43/1.00  --time_out_real                         305.
% 2.43/1.00  --time_out_virtual                      -1.
% 2.43/1.00  --symbol_type_check                     false
% 2.43/1.00  --clausify_out                          false
% 2.43/1.00  --sig_cnt_out                           false
% 2.43/1.00  --trig_cnt_out                          false
% 2.43/1.00  --trig_cnt_out_tolerance                1.
% 2.43/1.00  --trig_cnt_out_sk_spl                   false
% 2.43/1.00  --abstr_cl_out                          false
% 2.43/1.00  
% 2.43/1.00  ------ Global Options
% 2.43/1.00  
% 2.43/1.00  --schedule                              default
% 2.43/1.00  --add_important_lit                     false
% 2.43/1.00  --prop_solver_per_cl                    1000
% 2.43/1.00  --min_unsat_core                        false
% 2.43/1.00  --soft_assumptions                      false
% 2.43/1.00  --soft_lemma_size                       3
% 2.43/1.00  --prop_impl_unit_size                   0
% 2.43/1.00  --prop_impl_unit                        []
% 2.43/1.00  --share_sel_clauses                     true
% 2.43/1.00  --reset_solvers                         false
% 2.43/1.00  --bc_imp_inh                            [conj_cone]
% 2.43/1.00  --conj_cone_tolerance                   3.
% 2.43/1.00  --extra_neg_conj                        none
% 2.43/1.00  --large_theory_mode                     true
% 2.43/1.00  --prolific_symb_bound                   200
% 2.43/1.00  --lt_threshold                          2000
% 2.43/1.00  --clause_weak_htbl                      true
% 2.43/1.00  --gc_record_bc_elim                     false
% 2.43/1.00  
% 2.43/1.00  ------ Preprocessing Options
% 2.43/1.00  
% 2.43/1.00  --preprocessing_flag                    true
% 2.43/1.00  --time_out_prep_mult                    0.1
% 2.43/1.00  --splitting_mode                        input
% 2.43/1.00  --splitting_grd                         true
% 2.43/1.00  --splitting_cvd                         false
% 2.43/1.00  --splitting_cvd_svl                     false
% 2.43/1.00  --splitting_nvd                         32
% 2.43/1.00  --sub_typing                            true
% 2.43/1.00  --prep_gs_sim                           true
% 2.43/1.00  --prep_unflatten                        true
% 2.43/1.00  --prep_res_sim                          true
% 2.43/1.00  --prep_upred                            true
% 2.43/1.00  --prep_sem_filter                       exhaustive
% 2.43/1.00  --prep_sem_filter_out                   false
% 2.43/1.00  --pred_elim                             true
% 2.43/1.00  --res_sim_input                         true
% 2.43/1.01  --eq_ax_congr_red                       true
% 2.43/1.01  --pure_diseq_elim                       true
% 2.43/1.01  --brand_transform                       false
% 2.43/1.01  --non_eq_to_eq                          false
% 2.43/1.01  --prep_def_merge                        true
% 2.43/1.01  --prep_def_merge_prop_impl              false
% 2.43/1.01  --prep_def_merge_mbd                    true
% 2.43/1.01  --prep_def_merge_tr_red                 false
% 2.43/1.01  --prep_def_merge_tr_cl                  false
% 2.43/1.01  --smt_preprocessing                     true
% 2.43/1.01  --smt_ac_axioms                         fast
% 2.43/1.01  --preprocessed_out                      false
% 2.43/1.01  --preprocessed_stats                    false
% 2.43/1.01  
% 2.43/1.01  ------ Abstraction refinement Options
% 2.43/1.01  
% 2.43/1.01  --abstr_ref                             []
% 2.43/1.01  --abstr_ref_prep                        false
% 2.43/1.01  --abstr_ref_until_sat                   false
% 2.43/1.01  --abstr_ref_sig_restrict                funpre
% 2.43/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.43/1.01  --abstr_ref_under                       []
% 2.43/1.01  
% 2.43/1.01  ------ SAT Options
% 2.43/1.01  
% 2.43/1.01  --sat_mode                              false
% 2.43/1.01  --sat_fm_restart_options                ""
% 2.43/1.01  --sat_gr_def                            false
% 2.43/1.01  --sat_epr_types                         true
% 2.43/1.01  --sat_non_cyclic_types                  false
% 2.43/1.01  --sat_finite_models                     false
% 2.43/1.01  --sat_fm_lemmas                         false
% 2.43/1.01  --sat_fm_prep                           false
% 2.43/1.01  --sat_fm_uc_incr                        true
% 2.43/1.01  --sat_out_model                         small
% 2.43/1.01  --sat_out_clauses                       false
% 2.43/1.01  
% 2.43/1.01  ------ QBF Options
% 2.43/1.01  
% 2.43/1.01  --qbf_mode                              false
% 2.43/1.01  --qbf_elim_univ                         false
% 2.43/1.01  --qbf_dom_inst                          none
% 2.43/1.01  --qbf_dom_pre_inst                      false
% 2.43/1.01  --qbf_sk_in                             false
% 2.43/1.01  --qbf_pred_elim                         true
% 2.43/1.01  --qbf_split                             512
% 2.43/1.01  
% 2.43/1.01  ------ BMC1 Options
% 2.43/1.01  
% 2.43/1.01  --bmc1_incremental                      false
% 2.43/1.01  --bmc1_axioms                           reachable_all
% 2.43/1.01  --bmc1_min_bound                        0
% 2.43/1.01  --bmc1_max_bound                        -1
% 2.43/1.01  --bmc1_max_bound_default                -1
% 2.43/1.01  --bmc1_symbol_reachability              true
% 2.43/1.01  --bmc1_property_lemmas                  false
% 2.43/1.01  --bmc1_k_induction                      false
% 2.43/1.01  --bmc1_non_equiv_states                 false
% 2.43/1.01  --bmc1_deadlock                         false
% 2.43/1.01  --bmc1_ucm                              false
% 2.43/1.01  --bmc1_add_unsat_core                   none
% 2.43/1.01  --bmc1_unsat_core_children              false
% 2.43/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.43/1.01  --bmc1_out_stat                         full
% 2.43/1.01  --bmc1_ground_init                      false
% 2.43/1.01  --bmc1_pre_inst_next_state              false
% 2.43/1.01  --bmc1_pre_inst_state                   false
% 2.43/1.01  --bmc1_pre_inst_reach_state             false
% 2.43/1.01  --bmc1_out_unsat_core                   false
% 2.43/1.01  --bmc1_aig_witness_out                  false
% 2.43/1.01  --bmc1_verbose                          false
% 2.43/1.01  --bmc1_dump_clauses_tptp                false
% 2.43/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.43/1.01  --bmc1_dump_file                        -
% 2.43/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.43/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.43/1.01  --bmc1_ucm_extend_mode                  1
% 2.43/1.01  --bmc1_ucm_init_mode                    2
% 2.43/1.01  --bmc1_ucm_cone_mode                    none
% 2.43/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.43/1.01  --bmc1_ucm_relax_model                  4
% 2.43/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.43/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.43/1.01  --bmc1_ucm_layered_model                none
% 2.43/1.01  --bmc1_ucm_max_lemma_size               10
% 2.43/1.01  
% 2.43/1.01  ------ AIG Options
% 2.43/1.01  
% 2.43/1.01  --aig_mode                              false
% 2.43/1.01  
% 2.43/1.01  ------ Instantiation Options
% 2.43/1.01  
% 2.43/1.01  --instantiation_flag                    true
% 2.43/1.01  --inst_sos_flag                         false
% 2.43/1.01  --inst_sos_phase                        true
% 2.43/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.43/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.43/1.01  --inst_lit_sel_side                     none
% 2.43/1.01  --inst_solver_per_active                1400
% 2.43/1.01  --inst_solver_calls_frac                1.
% 2.43/1.01  --inst_passive_queue_type               priority_queues
% 2.43/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.43/1.01  --inst_passive_queues_freq              [25;2]
% 2.43/1.01  --inst_dismatching                      true
% 2.43/1.01  --inst_eager_unprocessed_to_passive     true
% 2.43/1.01  --inst_prop_sim_given                   true
% 2.43/1.01  --inst_prop_sim_new                     false
% 2.43/1.01  --inst_subs_new                         false
% 2.43/1.01  --inst_eq_res_simp                      false
% 2.43/1.01  --inst_subs_given                       false
% 2.43/1.01  --inst_orphan_elimination               true
% 2.43/1.01  --inst_learning_loop_flag               true
% 2.43/1.01  --inst_learning_start                   3000
% 2.43/1.01  --inst_learning_factor                  2
% 2.43/1.01  --inst_start_prop_sim_after_learn       3
% 2.43/1.01  --inst_sel_renew                        solver
% 2.43/1.01  --inst_lit_activity_flag                true
% 2.43/1.01  --inst_restr_to_given                   false
% 2.43/1.01  --inst_activity_threshold               500
% 2.43/1.01  --inst_out_proof                        true
% 2.43/1.01  
% 2.43/1.01  ------ Resolution Options
% 2.43/1.01  
% 2.43/1.01  --resolution_flag                       false
% 2.43/1.01  --res_lit_sel                           adaptive
% 2.43/1.01  --res_lit_sel_side                      none
% 2.43/1.01  --res_ordering                          kbo
% 2.43/1.01  --res_to_prop_solver                    active
% 2.43/1.01  --res_prop_simpl_new                    false
% 2.43/1.01  --res_prop_simpl_given                  true
% 2.43/1.01  --res_passive_queue_type                priority_queues
% 2.43/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.43/1.01  --res_passive_queues_freq               [15;5]
% 2.43/1.01  --res_forward_subs                      full
% 2.43/1.01  --res_backward_subs                     full
% 2.43/1.01  --res_forward_subs_resolution           true
% 2.43/1.01  --res_backward_subs_resolution          true
% 2.43/1.01  --res_orphan_elimination                true
% 2.43/1.01  --res_time_limit                        2.
% 2.43/1.01  --res_out_proof                         true
% 2.43/1.01  
% 2.43/1.01  ------ Superposition Options
% 2.43/1.01  
% 2.43/1.01  --superposition_flag                    true
% 2.43/1.01  --sup_passive_queue_type                priority_queues
% 2.43/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.43/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.43/1.01  --demod_completeness_check              fast
% 2.43/1.01  --demod_use_ground                      true
% 2.43/1.01  --sup_to_prop_solver                    passive
% 2.43/1.01  --sup_prop_simpl_new                    true
% 2.43/1.01  --sup_prop_simpl_given                  true
% 2.43/1.01  --sup_fun_splitting                     false
% 2.43/1.01  --sup_smt_interval                      50000
% 2.43/1.01  
% 2.43/1.01  ------ Superposition Simplification Setup
% 2.43/1.01  
% 2.43/1.01  --sup_indices_passive                   []
% 2.43/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.43/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.43/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.43/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.43/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.43/1.01  --sup_full_bw                           [BwDemod]
% 2.43/1.01  --sup_immed_triv                        [TrivRules]
% 2.43/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.43/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.43/1.01  --sup_immed_bw_main                     []
% 2.43/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.43/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.43/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.43/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.43/1.01  
% 2.43/1.01  ------ Combination Options
% 2.43/1.01  
% 2.43/1.01  --comb_res_mult                         3
% 2.43/1.01  --comb_sup_mult                         2
% 2.43/1.01  --comb_inst_mult                        10
% 2.43/1.01  
% 2.43/1.01  ------ Debug Options
% 2.43/1.01  
% 2.43/1.01  --dbg_backtrace                         false
% 2.43/1.01  --dbg_dump_prop_clauses                 false
% 2.43/1.01  --dbg_dump_prop_clauses_file            -
% 2.43/1.01  --dbg_out_stat                          false
% 2.43/1.01  
% 2.43/1.01  
% 2.43/1.01  
% 2.43/1.01  
% 2.43/1.01  ------ Proving...
% 2.43/1.01  
% 2.43/1.01  
% 2.43/1.01  % SZS status Theorem for theBenchmark.p
% 2.43/1.01  
% 2.43/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.43/1.01  
% 2.43/1.01  fof(f6,axiom,(
% 2.43/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 2.43/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/1.01  
% 2.43/1.01  fof(f19,plain,(
% 2.43/1.01    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 2.43/1.01    inference(ennf_transformation,[],[f6])).
% 2.43/1.01  
% 2.43/1.01  fof(f50,plain,(
% 2.43/1.01    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 2.43/1.01    inference(cnf_transformation,[],[f19])).
% 2.43/1.01  
% 2.43/1.01  fof(f9,axiom,(
% 2.43/1.01    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.43/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/1.01  
% 2.43/1.01  fof(f34,plain,(
% 2.43/1.01    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.43/1.01    inference(nnf_transformation,[],[f9])).
% 2.43/1.01  
% 2.43/1.01  fof(f54,plain,(
% 2.43/1.01    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.43/1.01    inference(cnf_transformation,[],[f34])).
% 2.43/1.01  
% 2.43/1.01  fof(f53,plain,(
% 2.43/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.43/1.01    inference(cnf_transformation,[],[f34])).
% 2.43/1.01  
% 2.43/1.01  fof(f5,axiom,(
% 2.43/1.01    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.43/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/1.01  
% 2.43/1.01  fof(f49,plain,(
% 2.43/1.01    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.43/1.01    inference(cnf_transformation,[],[f5])).
% 2.43/1.01  
% 2.43/1.01  fof(f4,axiom,(
% 2.43/1.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.43/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/1.01  
% 2.43/1.01  fof(f32,plain,(
% 2.43/1.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.43/1.01    inference(nnf_transformation,[],[f4])).
% 2.43/1.01  
% 2.43/1.01  fof(f33,plain,(
% 2.43/1.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.43/1.01    inference(flattening,[],[f32])).
% 2.43/1.01  
% 2.43/1.01  fof(f48,plain,(
% 2.43/1.01    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.43/1.01    inference(cnf_transformation,[],[f33])).
% 2.43/1.01  
% 2.43/1.01  fof(f7,axiom,(
% 2.43/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 2.43/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/1.01  
% 2.43/1.01  fof(f20,plain,(
% 2.43/1.01    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 2.43/1.01    inference(ennf_transformation,[],[f7])).
% 2.43/1.01  
% 2.43/1.01  fof(f51,plain,(
% 2.43/1.01    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 2.43/1.01    inference(cnf_transformation,[],[f20])).
% 2.43/1.01  
% 2.43/1.01  fof(f8,axiom,(
% 2.43/1.01    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.43/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/1.01  
% 2.43/1.01  fof(f52,plain,(
% 2.43/1.01    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.43/1.01    inference(cnf_transformation,[],[f8])).
% 2.43/1.01  
% 2.43/1.01  fof(f13,axiom,(
% 2.43/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0))) & r1_tarski(X2,X1))))))),
% 2.43/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/1.01  
% 2.43/1.01  fof(f26,plain,(
% 2.43/1.01    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((? [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.43/1.01    inference(ennf_transformation,[],[f13])).
% 2.43/1.01  
% 2.43/1.01  fof(f27,plain,(
% 2.43/1.01    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.43/1.01    inference(flattening,[],[f26])).
% 2.43/1.01  
% 2.43/1.01  fof(f35,plain,(
% 2.43/1.01    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.43/1.01    inference(nnf_transformation,[],[f27])).
% 2.43/1.01  
% 2.43/1.01  fof(f36,plain,(
% 2.43/1.01    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (? [X5] : (k9_subset_1(u1_struct_0(X0),X1,X5) = X4 & v3_pre_topc(X5,X0) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.43/1.01    inference(rectify,[],[f35])).
% 2.43/1.01  
% 2.43/1.01  fof(f38,plain,(
% 2.43/1.01    ! [X4,X1,X0] : (? [X5] : (k9_subset_1(u1_struct_0(X0),X1,X5) = X4 & v3_pre_topc(X5,X0) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) => (k9_subset_1(u1_struct_0(X0),X1,sK2(X0,X1,X4)) = X4 & v3_pre_topc(sK2(X0,X1,X4),X0) & m1_subset_1(sK2(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.43/1.01    introduced(choice_axiom,[])).
% 2.43/1.01  
% 2.43/1.01  fof(f37,plain,(
% 2.43/1.01    ! [X1,X0] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK1(X0,X1) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(sK1(X0,X1),X1) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.43/1.01    introduced(choice_axiom,[])).
% 2.43/1.01  
% 2.43/1.01  fof(f39,plain,(
% 2.43/1.01    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK1(X0,X1) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(sK1(X0,X1),X1) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : ((k9_subset_1(u1_struct_0(X0),X1,sK2(X0,X1,X4)) = X4 & v3_pre_topc(sK2(X0,X1,X4),X0) & m1_subset_1(sK2(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.43/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f36,f38,f37])).
% 2.43/1.01  
% 2.43/1.01  fof(f62,plain,(
% 2.43/1.01    ( ! [X0,X1] : (v2_tex_2(X1,X0) | r1_tarski(sK1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.43/1.01    inference(cnf_transformation,[],[f39])).
% 2.43/1.01  
% 2.43/1.01  fof(f14,conjecture,(
% 2.43/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 2.43/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/1.01  
% 2.43/1.01  fof(f15,negated_conjecture,(
% 2.43/1.01    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 2.43/1.01    inference(negated_conjecture,[],[f14])).
% 2.43/1.01  
% 2.43/1.01  fof(f16,plain,(
% 2.43/1.01    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 2.43/1.01    inference(pure_predicate_removal,[],[f15])).
% 2.43/1.01  
% 2.43/1.01  fof(f28,plain,(
% 2.43/1.01    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.43/1.01    inference(ennf_transformation,[],[f16])).
% 2.43/1.01  
% 2.43/1.01  fof(f29,plain,(
% 2.43/1.01    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.43/1.01    inference(flattening,[],[f28])).
% 2.43/1.01  
% 2.43/1.01  fof(f41,plain,(
% 2.43/1.01    ( ! [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => (~v2_tex_2(sK4,X0) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(sK4))) )),
% 2.43/1.01    introduced(choice_axiom,[])).
% 2.43/1.01  
% 2.43/1.01  fof(f40,plain,(
% 2.43/1.01    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (~v2_tex_2(X1,sK3) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) & v1_xboole_0(X1)) & l1_pre_topc(sK3) & v2_pre_topc(sK3))),
% 2.43/1.01    introduced(choice_axiom,[])).
% 2.43/1.01  
% 2.43/1.01  fof(f42,plain,(
% 2.43/1.01    (~v2_tex_2(sK4,sK3) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) & v1_xboole_0(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3)),
% 2.43/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f29,f41,f40])).
% 2.43/1.01  
% 2.43/1.01  fof(f65,plain,(
% 2.43/1.01    l1_pre_topc(sK3)),
% 2.43/1.01    inference(cnf_transformation,[],[f42])).
% 2.43/1.01  
% 2.43/1.01  fof(f68,plain,(
% 2.43/1.01    ~v2_tex_2(sK4,sK3)),
% 2.43/1.01    inference(cnf_transformation,[],[f42])).
% 2.43/1.01  
% 2.43/1.01  fof(f2,axiom,(
% 2.43/1.01    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 2.43/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/1.01  
% 2.43/1.01  fof(f17,plain,(
% 2.43/1.01    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 2.43/1.01    inference(ennf_transformation,[],[f2])).
% 2.43/1.01  
% 2.43/1.01  fof(f44,plain,(
% 2.43/1.01    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 2.43/1.01    inference(cnf_transformation,[],[f17])).
% 2.43/1.01  
% 2.43/1.01  fof(f66,plain,(
% 2.43/1.01    v1_xboole_0(sK4)),
% 2.43/1.01    inference(cnf_transformation,[],[f42])).
% 2.43/1.01  
% 2.43/1.01  fof(f63,plain,(
% 2.43/1.01    ( ! [X0,X3,X1] : (v2_tex_2(X1,X0) | k9_subset_1(u1_struct_0(X0),X1,X3) != sK1(X0,X1) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.43/1.01    inference(cnf_transformation,[],[f39])).
% 2.43/1.01  
% 2.43/1.01  fof(f1,axiom,(
% 2.43/1.01    v1_xboole_0(k1_xboole_0)),
% 2.43/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/1.01  
% 2.43/1.01  fof(f43,plain,(
% 2.43/1.01    v1_xboole_0(k1_xboole_0)),
% 2.43/1.01    inference(cnf_transformation,[],[f1])).
% 2.43/1.01  
% 2.43/1.01  fof(f12,axiom,(
% 2.43/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_xboole_0(X1) => v3_pre_topc(X1,X0))))),
% 2.43/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/1.01  
% 2.43/1.01  fof(f24,plain,(
% 2.43/1.01    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) | ~v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.43/1.01    inference(ennf_transformation,[],[f12])).
% 2.43/1.01  
% 2.43/1.01  fof(f25,plain,(
% 2.43/1.01    ! [X0] : (! [X1] : (v3_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.43/1.01    inference(flattening,[],[f24])).
% 2.43/1.01  
% 2.43/1.01  fof(f57,plain,(
% 2.43/1.01    ( ! [X0,X1] : (v3_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.43/1.01    inference(cnf_transformation,[],[f25])).
% 2.43/1.01  
% 2.43/1.01  fof(f64,plain,(
% 2.43/1.01    v2_pre_topc(sK3)),
% 2.43/1.01    inference(cnf_transformation,[],[f42])).
% 2.43/1.01  
% 2.43/1.01  cnf(c_1564,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_4456,plain,
% 2.43/1.01      ( X0 != X1
% 2.43/1.01      | k9_subset_1(u1_struct_0(sK3),X2,X3) != X1
% 2.43/1.01      | k9_subset_1(u1_struct_0(sK3),X2,X3) = X0 ),
% 2.43/1.01      inference(instantiation,[status(thm)],[c_1564]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_4909,plain,
% 2.43/1.01      ( X0 != k3_xboole_0(X1,X2)
% 2.43/1.01      | k9_subset_1(u1_struct_0(sK3),X1,X2) = X0
% 2.43/1.01      | k9_subset_1(u1_struct_0(sK3),X1,X2) != k3_xboole_0(X1,X2) ),
% 2.43/1.01      inference(instantiation,[status(thm)],[c_4456]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_11160,plain,
% 2.43/1.01      ( k9_subset_1(X0,X1,X2) != k3_xboole_0(X1,X2)
% 2.43/1.01      | k9_subset_1(u1_struct_0(sK3),X1,X2) = k9_subset_1(X0,X1,X2)
% 2.43/1.01      | k9_subset_1(u1_struct_0(sK3),X1,X2) != k3_xboole_0(X1,X2) ),
% 2.43/1.01      inference(instantiation,[status(thm)],[c_4909]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_11161,plain,
% 2.43/1.01      ( k9_subset_1(u1_struct_0(sK3),k1_xboole_0,k1_xboole_0) = k9_subset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
% 2.43/1.01      | k9_subset_1(u1_struct_0(sK3),k1_xboole_0,k1_xboole_0) != k3_xboole_0(k1_xboole_0,k1_xboole_0)
% 2.43/1.01      | k9_subset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) != k3_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 2.43/1.01      inference(instantiation,[status(thm)],[c_11160]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_7,plain,
% 2.43/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.43/1.01      | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 2.43/1.01      inference(cnf_transformation,[],[f50]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_10,plain,
% 2.43/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.43/1.01      inference(cnf_transformation,[],[f54]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_200,plain,
% 2.43/1.01      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.43/1.01      inference(prop_impl,[status(thm)],[c_10]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_201,plain,
% 2.43/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.43/1.01      inference(renaming,[status(thm)],[c_200]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_241,plain,
% 2.43/1.01      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
% 2.43/1.01      | ~ r1_tarski(X2,X0) ),
% 2.43/1.01      inference(bin_hyper_res,[status(thm)],[c_7,c_201]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_2051,plain,
% 2.43/1.01      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) = iProver_top
% 2.43/1.01      | r1_tarski(X2,X0) != iProver_top ),
% 2.43/1.01      inference(predicate_to_equality,[status(thm)],[c_241]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_11,plain,
% 2.43/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.43/1.01      inference(cnf_transformation,[],[f53]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_2054,plain,
% 2.43/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.43/1.01      | r1_tarski(X0,X1) = iProver_top ),
% 2.43/1.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_4329,plain,
% 2.43/1.01      ( r1_tarski(X0,X1) != iProver_top
% 2.43/1.01      | r1_tarski(k9_subset_1(X1,X2,X0),X1) = iProver_top ),
% 2.43/1.01      inference(superposition,[status(thm)],[c_2051,c_2054]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_6,plain,
% 2.43/1.01      ( r1_tarski(k1_xboole_0,X0) ),
% 2.43/1.01      inference(cnf_transformation,[],[f49]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_2057,plain,
% 2.43/1.01      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.43/1.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_3,plain,
% 2.43/1.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 2.43/1.01      inference(cnf_transformation,[],[f48]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_2059,plain,
% 2.43/1.01      ( X0 = X1
% 2.43/1.01      | r1_tarski(X0,X1) != iProver_top
% 2.43/1.01      | r1_tarski(X1,X0) != iProver_top ),
% 2.43/1.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_3109,plain,
% 2.43/1.01      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 2.43/1.01      inference(superposition,[status(thm)],[c_2057,c_2059]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_5253,plain,
% 2.43/1.01      ( k9_subset_1(k1_xboole_0,X0,X1) = k1_xboole_0
% 2.43/1.01      | r1_tarski(X1,k1_xboole_0) != iProver_top ),
% 2.43/1.01      inference(superposition,[status(thm)],[c_4329,c_3109]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_5307,plain,
% 2.43/1.01      ( k9_subset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0
% 2.43/1.01      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 2.43/1.01      inference(instantiation,[status(thm)],[c_5253]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_2579,plain,
% 2.43/1.01      ( X0 != X1 | sK1(sK3,X2) != X1 | sK1(sK3,X2) = X0 ),
% 2.43/1.01      inference(instantiation,[status(thm)],[c_1564]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_5038,plain,
% 2.43/1.01      ( k9_subset_1(X0,X1,X2) != X3
% 2.43/1.01      | sK1(sK3,X1) != X3
% 2.43/1.01      | sK1(sK3,X1) = k9_subset_1(X0,X1,X2) ),
% 2.43/1.01      inference(instantiation,[status(thm)],[c_2579]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_5039,plain,
% 2.43/1.01      ( k9_subset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 2.43/1.01      | sK1(sK3,k1_xboole_0) = k9_subset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
% 2.43/1.01      | sK1(sK3,k1_xboole_0) != k1_xboole_0 ),
% 2.43/1.01      inference(instantiation,[status(thm)],[c_5038]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_2337,plain,
% 2.43/1.01      ( k9_subset_1(u1_struct_0(sK3),X0,X1) != X2
% 2.43/1.01      | k9_subset_1(u1_struct_0(sK3),X0,X1) = sK1(sK3,X0)
% 2.43/1.01      | sK1(sK3,X0) != X2 ),
% 2.43/1.01      inference(instantiation,[status(thm)],[c_1564]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_4457,plain,
% 2.43/1.01      ( k9_subset_1(u1_struct_0(sK3),X0,X1) != k9_subset_1(X2,X0,X3)
% 2.43/1.01      | k9_subset_1(u1_struct_0(sK3),X0,X1) = sK1(sK3,X0)
% 2.43/1.01      | sK1(sK3,X0) != k9_subset_1(X2,X0,X3) ),
% 2.43/1.01      inference(instantiation,[status(thm)],[c_2337]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_4459,plain,
% 2.43/1.01      ( k9_subset_1(u1_struct_0(sK3),k1_xboole_0,k1_xboole_0) != k9_subset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
% 2.43/1.01      | k9_subset_1(u1_struct_0(sK3),k1_xboole_0,k1_xboole_0) = sK1(sK3,k1_xboole_0)
% 2.43/1.01      | sK1(sK3,k1_xboole_0) != k9_subset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
% 2.43/1.01      inference(instantiation,[status(thm)],[c_4457]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_8,plain,
% 2.43/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.43/1.01      | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 2.43/1.01      inference(cnf_transformation,[],[f51]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_242,plain,
% 2.43/1.01      ( ~ r1_tarski(X0,X1) | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 2.43/1.01      inference(bin_hyper_res,[status(thm)],[c_8,c_201]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_4446,plain,
% 2.43/1.01      ( ~ r1_tarski(X0,u1_struct_0(sK3))
% 2.43/1.01      | k9_subset_1(u1_struct_0(sK3),X1,X0) = k3_xboole_0(X1,X0) ),
% 2.43/1.01      inference(instantiation,[status(thm)],[c_242]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_4449,plain,
% 2.43/1.01      ( ~ r1_tarski(k1_xboole_0,u1_struct_0(sK3))
% 2.43/1.01      | k9_subset_1(u1_struct_0(sK3),k1_xboole_0,k1_xboole_0) = k3_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 2.43/1.01      inference(instantiation,[status(thm)],[c_4446]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_9,plain,
% 2.43/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 2.43/1.01      inference(cnf_transformation,[],[f52]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_2056,plain,
% 2.43/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.43/1.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_16,plain,
% 2.43/1.01      ( v2_tex_2(X0,X1)
% 2.43/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.43/1.01      | r1_tarski(sK1(X1,X0),X0)
% 2.43/1.01      | ~ l1_pre_topc(X1) ),
% 2.43/1.01      inference(cnf_transformation,[],[f62]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_24,negated_conjecture,
% 2.43/1.01      ( l1_pre_topc(sK3) ),
% 2.43/1.01      inference(cnf_transformation,[],[f65]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_598,plain,
% 2.43/1.01      ( v2_tex_2(X0,X1)
% 2.43/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.43/1.01      | r1_tarski(sK1(X1,X0),X0)
% 2.43/1.01      | sK3 != X1 ),
% 2.43/1.01      inference(resolution_lifted,[status(thm)],[c_16,c_24]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_599,plain,
% 2.43/1.01      ( v2_tex_2(X0,sK3)
% 2.43/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.43/1.01      | r1_tarski(sK1(sK3,X0),X0) ),
% 2.43/1.01      inference(unflattening,[status(thm)],[c_598]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_2042,plain,
% 2.43/1.01      ( v2_tex_2(X0,sK3) = iProver_top
% 2.43/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.43/1.01      | r1_tarski(sK1(sK3,X0),X0) = iProver_top ),
% 2.43/1.01      inference(predicate_to_equality,[status(thm)],[c_599]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_2566,plain,
% 2.43/1.01      ( v2_tex_2(k1_xboole_0,sK3) = iProver_top
% 2.43/1.01      | r1_tarski(sK1(sK3,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 2.43/1.01      inference(superposition,[status(thm)],[c_2056,c_2042]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_600,plain,
% 2.43/1.01      ( v2_tex_2(X0,sK3) = iProver_top
% 2.43/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.43/1.01      | r1_tarski(sK1(sK3,X0),X0) = iProver_top ),
% 2.43/1.01      inference(predicate_to_equality,[status(thm)],[c_599]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_602,plain,
% 2.43/1.01      ( v2_tex_2(k1_xboole_0,sK3) = iProver_top
% 2.43/1.01      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.43/1.01      | r1_tarski(sK1(sK3,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 2.43/1.01      inference(instantiation,[status(thm)],[c_600]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_21,negated_conjecture,
% 2.43/1.01      ( ~ v2_tex_2(sK4,sK3) ),
% 2.43/1.01      inference(cnf_transformation,[],[f68]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_2053,plain,
% 2.43/1.01      ( v2_tex_2(sK4,sK3) != iProver_top ),
% 2.43/1.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_1,plain,
% 2.43/1.01      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 2.43/1.01      inference(cnf_transformation,[],[f44]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_23,negated_conjecture,
% 2.43/1.01      ( v1_xboole_0(sK4) ),
% 2.43/1.01      inference(cnf_transformation,[],[f66]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_420,plain,
% 2.43/1.01      ( sK4 != X0 | k1_xboole_0 = X0 ),
% 2.43/1.01      inference(resolution_lifted,[status(thm)],[c_1,c_23]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_421,plain,
% 2.43/1.01      ( k1_xboole_0 = sK4 ),
% 2.43/1.01      inference(unflattening,[status(thm)],[c_420]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_2069,plain,
% 2.43/1.01      ( v2_tex_2(k1_xboole_0,sK3) != iProver_top ),
% 2.43/1.01      inference(light_normalisation,[status(thm)],[c_2053,c_421]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_2213,plain,
% 2.43/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.43/1.01      inference(instantiation,[status(thm)],[c_9]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_2217,plain,
% 2.43/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 2.43/1.01      inference(predicate_to_equality,[status(thm)],[c_2213]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_2913,plain,
% 2.43/1.01      ( r1_tarski(sK1(sK3,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 2.43/1.01      inference(global_propositional_subsumption,
% 2.43/1.01                [status(thm)],
% 2.43/1.01                [c_2566,c_602,c_2069,c_2217]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_3178,plain,
% 2.43/1.01      ( sK1(sK3,k1_xboole_0) = k1_xboole_0 ),
% 2.43/1.01      inference(superposition,[status(thm)],[c_2913,c_3109]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_2343,plain,
% 2.43/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.43/1.01      | r1_tarski(X0,u1_struct_0(sK3)) ),
% 2.43/1.01      inference(instantiation,[status(thm)],[c_11]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_2345,plain,
% 2.43/1.01      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.43/1.01      | r1_tarski(k1_xboole_0,u1_struct_0(sK3)) ),
% 2.43/1.01      inference(instantiation,[status(thm)],[c_2343]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_2160,plain,
% 2.43/1.01      ( ~ v2_tex_2(k1_xboole_0,sK3) ),
% 2.43/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_2069]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_15,plain,
% 2.43/1.01      ( v2_tex_2(X0,X1)
% 2.43/1.01      | ~ v3_pre_topc(X2,X1)
% 2.43/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.43/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.43/1.01      | ~ l1_pre_topc(X1)
% 2.43/1.01      | k9_subset_1(u1_struct_0(X1),X0,X2) != sK1(X1,X0) ),
% 2.43/1.01      inference(cnf_transformation,[],[f63]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_0,plain,
% 2.43/1.01      ( v1_xboole_0(k1_xboole_0) ),
% 2.43/1.01      inference(cnf_transformation,[],[f43]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_14,plain,
% 2.43/1.01      ( v3_pre_topc(X0,X1)
% 2.43/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.43/1.01      | ~ v2_pre_topc(X1)
% 2.43/1.01      | ~ l1_pre_topc(X1)
% 2.43/1.01      | ~ v1_xboole_0(X0) ),
% 2.43/1.01      inference(cnf_transformation,[],[f57]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_25,negated_conjecture,
% 2.43/1.01      ( v2_pre_topc(sK3) ),
% 2.43/1.01      inference(cnf_transformation,[],[f64]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_338,plain,
% 2.43/1.01      ( v3_pre_topc(X0,X1)
% 2.43/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.43/1.01      | ~ l1_pre_topc(X1)
% 2.43/1.01      | ~ v1_xboole_0(X0)
% 2.43/1.01      | sK3 != X1 ),
% 2.43/1.01      inference(resolution_lifted,[status(thm)],[c_14,c_25]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_339,plain,
% 2.43/1.01      ( v3_pre_topc(X0,sK3)
% 2.43/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.43/1.01      | ~ l1_pre_topc(sK3)
% 2.43/1.01      | ~ v1_xboole_0(X0) ),
% 2.43/1.01      inference(unflattening,[status(thm)],[c_338]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_343,plain,
% 2.43/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.43/1.01      | v3_pre_topc(X0,sK3)
% 2.43/1.01      | ~ v1_xboole_0(X0) ),
% 2.43/1.01      inference(global_propositional_subsumption,
% 2.43/1.01                [status(thm)],
% 2.43/1.01                [c_339,c_24]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_344,plain,
% 2.43/1.01      ( v3_pre_topc(X0,sK3)
% 2.43/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.43/1.01      | ~ v1_xboole_0(X0) ),
% 2.43/1.01      inference(renaming,[status(thm)],[c_343]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_397,plain,
% 2.43/1.01      ( v3_pre_topc(X0,sK3)
% 2.43/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.43/1.01      | k1_xboole_0 != X0 ),
% 2.43/1.01      inference(resolution_lifted,[status(thm)],[c_0,c_344]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_398,plain,
% 2.43/1.01      ( v3_pre_topc(k1_xboole_0,sK3)
% 2.43/1.01      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.43/1.01      inference(unflattening,[status(thm)],[c_397]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_404,plain,
% 2.43/1.01      ( v3_pre_topc(k1_xboole_0,sK3) ),
% 2.43/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_398,c_9]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_461,plain,
% 2.43/1.01      ( v2_tex_2(X0,X1)
% 2.43/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.43/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.43/1.01      | ~ l1_pre_topc(X1)
% 2.43/1.01      | k9_subset_1(u1_struct_0(X1),X0,X2) != sK1(X1,X0)
% 2.43/1.01      | sK3 != X1
% 2.43/1.01      | k1_xboole_0 != X2 ),
% 2.43/1.01      inference(resolution_lifted,[status(thm)],[c_15,c_404]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_462,plain,
% 2.43/1.01      ( v2_tex_2(X0,sK3)
% 2.43/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.43/1.01      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.43/1.01      | ~ l1_pre_topc(sK3)
% 2.43/1.01      | k9_subset_1(u1_struct_0(sK3),X0,k1_xboole_0) != sK1(sK3,X0) ),
% 2.43/1.01      inference(unflattening,[status(thm)],[c_461]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_464,plain,
% 2.43/1.01      ( v2_tex_2(k1_xboole_0,sK3)
% 2.43/1.01      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.43/1.01      | ~ l1_pre_topc(sK3)
% 2.43/1.01      | k9_subset_1(u1_struct_0(sK3),k1_xboole_0,k1_xboole_0) != sK1(sK3,k1_xboole_0) ),
% 2.43/1.01      inference(instantiation,[status(thm)],[c_462]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_68,plain,
% 2.43/1.01      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
% 2.43/1.01      | k9_subset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k3_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 2.43/1.01      inference(instantiation,[status(thm)],[c_8]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_64,plain,
% 2.43/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.43/1.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_66,plain,
% 2.43/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.43/1.01      inference(instantiation,[status(thm)],[c_64]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_65,plain,
% 2.43/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
% 2.43/1.01      inference(instantiation,[status(thm)],[c_9]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_58,plain,
% 2.43/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.43/1.01      | r1_tarski(X0,X1) = iProver_top ),
% 2.43/1.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_60,plain,
% 2.43/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.43/1.01      | r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 2.43/1.01      inference(instantiation,[status(thm)],[c_58]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(contradiction,plain,
% 2.43/1.01      ( $false ),
% 2.43/1.01      inference(minisat,
% 2.43/1.01                [status(thm)],
% 2.43/1.01                [c_11161,c_5307,c_5039,c_4459,c_4449,c_3178,c_2345,
% 2.43/1.01                 c_2213,c_2160,c_464,c_68,c_66,c_65,c_60,c_24]) ).
% 2.43/1.01  
% 2.43/1.01  
% 2.43/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.43/1.01  
% 2.43/1.01  ------                               Statistics
% 2.43/1.01  
% 2.43/1.01  ------ General
% 2.43/1.01  
% 2.43/1.01  abstr_ref_over_cycles:                  0
% 2.43/1.01  abstr_ref_under_cycles:                 0
% 2.43/1.01  gc_basic_clause_elim:                   0
% 2.43/1.01  forced_gc_time:                         0
% 2.43/1.01  parsing_time:                           0.009
% 2.43/1.01  unif_index_cands_time:                  0.
% 2.43/1.01  unif_index_add_time:                    0.
% 2.43/1.01  orderings_time:                         0.
% 2.43/1.01  out_proof_time:                         0.009
% 2.43/1.01  total_time:                             0.29
% 2.43/1.01  num_of_symbols:                         49
% 2.43/1.01  num_of_terms:                           8178
% 2.43/1.01  
% 2.43/1.01  ------ Preprocessing
% 2.43/1.01  
% 2.43/1.01  num_of_splits:                          0
% 2.43/1.01  num_of_split_atoms:                     0
% 2.43/1.01  num_of_reused_defs:                     0
% 2.43/1.01  num_eq_ax_congr_red:                    26
% 2.43/1.01  num_of_sem_filtered_clauses:            1
% 2.43/1.01  num_of_subtypes:                        0
% 2.43/1.01  monotx_restored_types:                  0
% 2.43/1.01  sat_num_of_epr_types:                   0
% 2.43/1.01  sat_num_of_non_cyclic_types:            0
% 2.43/1.01  sat_guarded_non_collapsed_types:        0
% 2.43/1.01  num_pure_diseq_elim:                    0
% 2.43/1.01  simp_replaced_by:                       0
% 2.43/1.01  res_preprocessed:                       111
% 2.43/1.01  prep_upred:                             0
% 2.43/1.01  prep_unflattend:                        33
% 2.43/1.01  smt_new_axioms:                         0
% 2.43/1.01  pred_elim_cands:                        4
% 2.43/1.01  pred_elim:                              4
% 2.43/1.01  pred_elim_cl:                           4
% 2.43/1.01  pred_elim_cycles:                       9
% 2.43/1.01  merged_defs:                            8
% 2.43/1.01  merged_defs_ncl:                        0
% 2.43/1.01  bin_hyper_res:                          11
% 2.43/1.01  prep_cycles:                            4
% 2.43/1.01  pred_elim_time:                         0.012
% 2.43/1.01  splitting_time:                         0.
% 2.43/1.01  sem_filter_time:                        0.
% 2.43/1.01  monotx_time:                            0.
% 2.43/1.01  subtype_inf_time:                       0.
% 2.43/1.01  
% 2.43/1.01  ------ Problem properties
% 2.43/1.01  
% 2.43/1.01  clauses:                                21
% 2.43/1.01  conjectures:                            2
% 2.43/1.01  epr:                                    7
% 2.43/1.01  horn:                                   18
% 2.43/1.01  ground:                                 5
% 2.43/1.01  unary:                                  8
% 2.43/1.01  binary:                                 5
% 2.43/1.01  lits:                                   50
% 2.43/1.01  lits_eq:                                7
% 2.43/1.01  fd_pure:                                0
% 2.43/1.01  fd_pseudo:                              0
% 2.43/1.01  fd_cond:                                2
% 2.43/1.01  fd_pseudo_cond:                         1
% 2.43/1.01  ac_symbols:                             0
% 2.43/1.01  
% 2.43/1.01  ------ Propositional Solver
% 2.43/1.01  
% 2.43/1.01  prop_solver_calls:                      30
% 2.43/1.01  prop_fast_solver_calls:                 1364
% 2.43/1.01  smt_solver_calls:                       0
% 2.43/1.01  smt_fast_solver_calls:                  0
% 2.43/1.01  prop_num_of_clauses:                    3121
% 2.43/1.01  prop_preprocess_simplified:             6851
% 2.43/1.01  prop_fo_subsumed:                       26
% 2.43/1.01  prop_solver_time:                       0.
% 2.43/1.01  smt_solver_time:                        0.
% 2.43/1.01  smt_fast_solver_time:                   0.
% 2.43/1.01  prop_fast_solver_time:                  0.
% 2.43/1.01  prop_unsat_core_time:                   0.
% 2.43/1.01  
% 2.43/1.01  ------ QBF
% 2.43/1.01  
% 2.43/1.01  qbf_q_res:                              0
% 2.43/1.01  qbf_num_tautologies:                    0
% 2.43/1.01  qbf_prep_cycles:                        0
% 2.43/1.01  
% 2.43/1.01  ------ BMC1
% 2.43/1.01  
% 2.43/1.01  bmc1_current_bound:                     -1
% 2.43/1.01  bmc1_last_solved_bound:                 -1
% 2.43/1.01  bmc1_unsat_core_size:                   -1
% 2.43/1.01  bmc1_unsat_core_parents_size:           -1
% 2.43/1.01  bmc1_merge_next_fun:                    0
% 2.43/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.43/1.01  
% 2.43/1.01  ------ Instantiation
% 2.43/1.01  
% 2.43/1.01  inst_num_of_clauses:                    783
% 2.43/1.01  inst_num_in_passive:                    154
% 2.43/1.01  inst_num_in_active:                     436
% 2.43/1.01  inst_num_in_unprocessed:                195
% 2.43/1.01  inst_num_of_loops:                      531
% 2.43/1.01  inst_num_of_learning_restarts:          0
% 2.43/1.01  inst_num_moves_active_passive:          90
% 2.43/1.01  inst_lit_activity:                      0
% 2.43/1.01  inst_lit_activity_moves:                0
% 2.43/1.01  inst_num_tautologies:                   0
% 2.43/1.01  inst_num_prop_implied:                  0
% 2.43/1.01  inst_num_existing_simplified:           0
% 2.43/1.01  inst_num_eq_res_simplified:             0
% 2.43/1.01  inst_num_child_elim:                    0
% 2.43/1.01  inst_num_of_dismatching_blockings:      399
% 2.43/1.01  inst_num_of_non_proper_insts:           1243
% 2.43/1.01  inst_num_of_duplicates:                 0
% 2.43/1.01  inst_inst_num_from_inst_to_res:         0
% 2.43/1.01  inst_dismatching_checking_time:         0.
% 2.43/1.01  
% 2.43/1.01  ------ Resolution
% 2.43/1.01  
% 2.43/1.01  res_num_of_clauses:                     0
% 2.43/1.01  res_num_in_passive:                     0
% 2.43/1.01  res_num_in_active:                      0
% 2.43/1.01  res_num_of_loops:                       115
% 2.43/1.01  res_forward_subset_subsumed:            134
% 2.43/1.01  res_backward_subset_subsumed:           10
% 2.43/1.01  res_forward_subsumed:                   0
% 2.43/1.01  res_backward_subsumed:                  0
% 2.43/1.01  res_forward_subsumption_resolution:     4
% 2.43/1.01  res_backward_subsumption_resolution:    0
% 2.43/1.01  res_clause_to_clause_subsumption:       2904
% 2.43/1.01  res_orphan_elimination:                 0
% 2.43/1.01  res_tautology_del:                      90
% 2.43/1.01  res_num_eq_res_simplified:              0
% 2.43/1.01  res_num_sel_changes:                    0
% 2.43/1.01  res_moves_from_active_to_pass:          0
% 2.43/1.01  
% 2.43/1.01  ------ Superposition
% 2.43/1.01  
% 2.43/1.01  sup_time_total:                         0.
% 2.43/1.01  sup_time_generating:                    0.
% 2.43/1.01  sup_time_sim_full:                      0.
% 2.43/1.01  sup_time_sim_immed:                     0.
% 2.43/1.01  
% 2.43/1.01  sup_num_of_clauses:                     234
% 2.43/1.01  sup_num_in_active:                      105
% 2.43/1.01  sup_num_in_passive:                     129
% 2.43/1.01  sup_num_of_loops:                       106
% 2.43/1.01  sup_fw_superposition:                   251
% 2.43/1.01  sup_bw_superposition:                   60
% 2.43/1.01  sup_immediate_simplified:               47
% 2.43/1.01  sup_given_eliminated:                   0
% 2.43/1.01  comparisons_done:                       0
% 2.43/1.01  comparisons_avoided:                    9
% 2.43/1.01  
% 2.43/1.01  ------ Simplifications
% 2.43/1.01  
% 2.43/1.01  
% 2.43/1.01  sim_fw_subset_subsumed:                 13
% 2.43/1.01  sim_bw_subset_subsumed:                 4
% 2.43/1.01  sim_fw_subsumed:                        13
% 2.43/1.01  sim_bw_subsumed:                        0
% 2.43/1.01  sim_fw_subsumption_res:                 3
% 2.43/1.01  sim_bw_subsumption_res:                 0
% 2.43/1.01  sim_tautology_del:                      30
% 2.43/1.01  sim_eq_tautology_del:                   12
% 2.43/1.01  sim_eq_res_simp:                        0
% 2.43/1.01  sim_fw_demodulated:                     12
% 2.43/1.01  sim_bw_demodulated:                     1
% 2.43/1.01  sim_light_normalised:                   28
% 2.43/1.01  sim_joinable_taut:                      0
% 2.43/1.01  sim_joinable_simp:                      0
% 2.43/1.01  sim_ac_normalised:                      0
% 2.43/1.01  sim_smt_subsumption:                    0
% 2.43/1.01  
%------------------------------------------------------------------------------
