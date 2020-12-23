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
% DateTime   : Thu Dec  3 12:26:16 EST 2020

% Result     : Theorem 1.94s
% Output     : CNFRefutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 280 expanded)
%              Number of clauses        :   61 (  98 expanded)
%              Number of leaves         :   16 (  63 expanded)
%              Depth                    :   19
%              Number of atoms          :  373 (1119 expanded)
%              Number of equality atoms :   96 ( 157 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

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

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
     => ( ~ v2_tex_2(sK4,X0)
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0)))
        & v1_xboole_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
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

fof(f40,plain,
    ( ~ v2_tex_2(sK4,sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    & v1_xboole_0(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f28,f39,f38])).

fof(f61,plain,(
    v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f45,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f4,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f46,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

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
                            & v4_pre_topc(X3,X0) ) )
                    & r1_tarski(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f34,plain,(
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
    inference(rectify,[],[f33])).

fof(f36,plain,(
    ! [X4,X1,X0] :
      ( ? [X5] :
          ( k9_subset_1(u1_struct_0(X0),X1,X5) = X4
          & v4_pre_topc(X5,X0)
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X0),X1,sK2(X0,X1,X4)) = X4
        & v4_pre_topc(sK2(X0,X1,X4),X0)
        & m1_subset_1(sK2(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
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

fof(f37,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f34,f36,f35])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | r1_tarski(sK1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f60,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f63,plain,(
    ~ v2_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f58,plain,(
    ! [X0,X3,X1] :
      ( v2_tex_2(X1,X0)
      | k9_subset_1(u1_struct_0(X0),X1,X3) != sK1(X0,X1)
      | ~ v4_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f59,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_8,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_2342,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_2347,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_2344,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_20,negated_conjecture,
    ( v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_324,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_20])).

cnf(c_325,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK4))
    | ~ r2_hidden(X1,X0) ),
    inference(unflattening,[status(thm)],[c_324])).

cnf(c_2335,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK4)) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_325])).

cnf(c_4,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_319,plain,
    ( sK4 != X0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_20])).

cnf(c_320,plain,
    ( k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_319])).

cnf(c_2368,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2335,c_320])).

cnf(c_3461,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r2_hidden(X1,k9_subset_1(k1_xboole_0,X2,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2344,c_2368])).

cnf(c_3672,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k9_subset_1(k1_xboole_0,X1,X0),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2347,c_3461])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_2345,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4272,plain,
    ( k9_subset_1(k1_xboole_0,X0,X1) = k1_xboole_0
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3672,c_2345])).

cnf(c_5093,plain,
    ( k9_subset_1(k1_xboole_0,X0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2342,c_4272])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_2343,plain,
    ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3428,plain,
    ( k9_subset_1(X0,X1,k1_xboole_0) = k3_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2342,c_2343])).

cnf(c_5137,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5093,c_3428])).

cnf(c_5142,plain,
    ( k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5137])).

cnf(c_13,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(sK1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_21,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_515,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(sK1(X1,X0),X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_21])).

cnf(c_516,plain,
    ( v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | r1_tarski(sK1(sK3,X0),X0) ),
    inference(unflattening,[status(thm)],[c_515])).

cnf(c_2330,plain,
    ( v2_tex_2(X0,sK3) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r1_tarski(sK1(sK3,X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_516])).

cnf(c_2706,plain,
    ( v2_tex_2(k1_xboole_0,sK3) = iProver_top
    | r1_tarski(sK1(sK3,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2342,c_2330])).

cnf(c_517,plain,
    ( v2_tex_2(X0,sK3) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r1_tarski(sK1(sK3,X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_516])).

cnf(c_519,plain,
    ( v2_tex_2(k1_xboole_0,sK3) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r1_tarski(sK1(sK3,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_517])).

cnf(c_18,negated_conjecture,
    ( ~ v2_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2340,plain,
    ( v2_tex_2(sK4,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2354,plain,
    ( v2_tex_2(k1_xboole_0,sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2340,c_320])).

cnf(c_2503,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2507,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2503])).

cnf(c_3105,plain,
    ( r1_tarski(sK1(sK3,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2706,c_519,c_2354,c_2507])).

cnf(c_3110,plain,
    ( sK1(sK3,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3105,c_2345])).

cnf(c_12,plain,
    ( v2_tex_2(X0,X1)
    | ~ v4_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),X0,X2) != sK1(X1,X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_530,plain,
    ( v2_tex_2(X0,X1)
    | ~ v4_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | k9_subset_1(u1_struct_0(X1),X0,X2) != sK1(X1,X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_21])).

cnf(c_531,plain,
    ( v2_tex_2(X0,sK3)
    | ~ v4_pre_topc(X1,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | k9_subset_1(u1_struct_0(sK3),X0,X1) != sK1(sK3,X0) ),
    inference(unflattening,[status(thm)],[c_530])).

cnf(c_2329,plain,
    ( k9_subset_1(u1_struct_0(sK3),X0,X1) != sK1(sK3,X0)
    | v2_tex_2(X0,sK3) = iProver_top
    | v4_pre_topc(X1,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_531])).

cnf(c_4215,plain,
    ( sK1(sK3,X0) != k3_xboole_0(X0,k1_xboole_0)
    | v2_tex_2(X0,sK3) = iProver_top
    | v4_pre_topc(k1_xboole_0,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3428,c_2329])).

cnf(c_3,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_11,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_22,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_259,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_22])).

cnf(c_260,plain,
    ( v4_pre_topc(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3)
    | ~ v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_259])).

cnf(c_264,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v4_pre_topc(X0,sK3)
    | ~ v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_260,c_21])).

cnf(c_265,plain,
    ( v4_pre_topc(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_264])).

cnf(c_284,plain,
    ( v4_pre_topc(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | k1_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_265])).

cnf(c_285,plain,
    ( v4_pre_topc(k1_xboole_0,sK3)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(unflattening,[status(thm)],[c_284])).

cnf(c_291,plain,
    ( v4_pre_topc(k1_xboole_0,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_285,c_8])).

cnf(c_293,plain,
    ( v4_pre_topc(k1_xboole_0,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_291])).

cnf(c_4370,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | sK1(sK3,X0) != k3_xboole_0(X0,k1_xboole_0)
    | v2_tex_2(X0,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4215,c_293,c_2507])).

cnf(c_4371,plain,
    ( sK1(sK3,X0) != k3_xboole_0(X0,k1_xboole_0)
    | v2_tex_2(X0,sK3) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_4370])).

cnf(c_4379,plain,
    ( k3_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | v2_tex_2(k1_xboole_0,sK3) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3110,c_4371])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5142,c_4379,c_2507,c_2354])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:41:44 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 1.94/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/0.99  
% 1.94/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.94/0.99  
% 1.94/0.99  ------  iProver source info
% 1.94/0.99  
% 1.94/0.99  git: date: 2020-06-30 10:37:57 +0100
% 1.94/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.94/0.99  git: non_committed_changes: false
% 1.94/0.99  git: last_make_outside_of_git: false
% 1.94/0.99  
% 1.94/0.99  ------ 
% 1.94/0.99  
% 1.94/0.99  ------ Input Options
% 1.94/0.99  
% 1.94/0.99  --out_options                           all
% 1.94/0.99  --tptp_safe_out                         true
% 1.94/0.99  --problem_path                          ""
% 1.94/0.99  --include_path                          ""
% 1.94/0.99  --clausifier                            res/vclausify_rel
% 1.94/0.99  --clausifier_options                    --mode clausify
% 1.94/0.99  --stdin                                 false
% 1.94/0.99  --stats_out                             all
% 1.94/0.99  
% 1.94/0.99  ------ General Options
% 1.94/0.99  
% 1.94/0.99  --fof                                   false
% 1.94/0.99  --time_out_real                         305.
% 1.94/0.99  --time_out_virtual                      -1.
% 1.94/0.99  --symbol_type_check                     false
% 1.94/0.99  --clausify_out                          false
% 1.94/0.99  --sig_cnt_out                           false
% 1.94/0.99  --trig_cnt_out                          false
% 1.94/0.99  --trig_cnt_out_tolerance                1.
% 1.94/0.99  --trig_cnt_out_sk_spl                   false
% 1.94/0.99  --abstr_cl_out                          false
% 1.94/0.99  
% 1.94/0.99  ------ Global Options
% 1.94/0.99  
% 1.94/0.99  --schedule                              default
% 1.94/0.99  --add_important_lit                     false
% 1.94/0.99  --prop_solver_per_cl                    1000
% 1.94/0.99  --min_unsat_core                        false
% 1.94/0.99  --soft_assumptions                      false
% 1.94/0.99  --soft_lemma_size                       3
% 1.94/0.99  --prop_impl_unit_size                   0
% 1.94/0.99  --prop_impl_unit                        []
% 1.94/0.99  --share_sel_clauses                     true
% 1.94/0.99  --reset_solvers                         false
% 1.94/0.99  --bc_imp_inh                            [conj_cone]
% 1.94/0.99  --conj_cone_tolerance                   3.
% 1.94/0.99  --extra_neg_conj                        none
% 1.94/0.99  --large_theory_mode                     true
% 1.94/0.99  --prolific_symb_bound                   200
% 1.94/0.99  --lt_threshold                          2000
% 1.94/0.99  --clause_weak_htbl                      true
% 1.94/0.99  --gc_record_bc_elim                     false
% 1.94/0.99  
% 1.94/0.99  ------ Preprocessing Options
% 1.94/0.99  
% 1.94/0.99  --preprocessing_flag                    true
% 1.94/0.99  --time_out_prep_mult                    0.1
% 1.94/0.99  --splitting_mode                        input
% 1.94/0.99  --splitting_grd                         true
% 1.94/0.99  --splitting_cvd                         false
% 1.94/0.99  --splitting_cvd_svl                     false
% 1.94/0.99  --splitting_nvd                         32
% 1.94/0.99  --sub_typing                            true
% 1.94/0.99  --prep_gs_sim                           true
% 1.94/0.99  --prep_unflatten                        true
% 1.94/0.99  --prep_res_sim                          true
% 1.94/0.99  --prep_upred                            true
% 1.94/0.99  --prep_sem_filter                       exhaustive
% 1.94/0.99  --prep_sem_filter_out                   false
% 1.94/0.99  --pred_elim                             true
% 1.94/0.99  --res_sim_input                         true
% 1.94/0.99  --eq_ax_congr_red                       true
% 1.94/0.99  --pure_diseq_elim                       true
% 1.94/0.99  --brand_transform                       false
% 1.94/0.99  --non_eq_to_eq                          false
% 1.94/0.99  --prep_def_merge                        true
% 1.94/0.99  --prep_def_merge_prop_impl              false
% 1.94/0.99  --prep_def_merge_mbd                    true
% 1.94/0.99  --prep_def_merge_tr_red                 false
% 1.94/0.99  --prep_def_merge_tr_cl                  false
% 1.94/0.99  --smt_preprocessing                     true
% 1.94/0.99  --smt_ac_axioms                         fast
% 1.94/0.99  --preprocessed_out                      false
% 1.94/0.99  --preprocessed_stats                    false
% 1.94/0.99  
% 1.94/0.99  ------ Abstraction refinement Options
% 1.94/0.99  
% 1.94/0.99  --abstr_ref                             []
% 1.94/0.99  --abstr_ref_prep                        false
% 1.94/0.99  --abstr_ref_until_sat                   false
% 1.94/0.99  --abstr_ref_sig_restrict                funpre
% 1.94/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.94/0.99  --abstr_ref_under                       []
% 1.94/0.99  
% 1.94/0.99  ------ SAT Options
% 1.94/0.99  
% 1.94/0.99  --sat_mode                              false
% 1.94/0.99  --sat_fm_restart_options                ""
% 1.94/0.99  --sat_gr_def                            false
% 1.94/0.99  --sat_epr_types                         true
% 1.94/0.99  --sat_non_cyclic_types                  false
% 1.94/0.99  --sat_finite_models                     false
% 1.94/0.99  --sat_fm_lemmas                         false
% 1.94/0.99  --sat_fm_prep                           false
% 1.94/0.99  --sat_fm_uc_incr                        true
% 1.94/0.99  --sat_out_model                         small
% 1.94/0.99  --sat_out_clauses                       false
% 1.94/0.99  
% 1.94/0.99  ------ QBF Options
% 1.94/0.99  
% 1.94/0.99  --qbf_mode                              false
% 1.94/0.99  --qbf_elim_univ                         false
% 1.94/0.99  --qbf_dom_inst                          none
% 1.94/0.99  --qbf_dom_pre_inst                      false
% 1.94/0.99  --qbf_sk_in                             false
% 1.94/0.99  --qbf_pred_elim                         true
% 1.94/0.99  --qbf_split                             512
% 1.94/0.99  
% 1.94/0.99  ------ BMC1 Options
% 1.94/0.99  
% 1.94/0.99  --bmc1_incremental                      false
% 1.94/0.99  --bmc1_axioms                           reachable_all
% 1.94/0.99  --bmc1_min_bound                        0
% 1.94/0.99  --bmc1_max_bound                        -1
% 1.94/0.99  --bmc1_max_bound_default                -1
% 1.94/0.99  --bmc1_symbol_reachability              true
% 1.94/0.99  --bmc1_property_lemmas                  false
% 1.94/0.99  --bmc1_k_induction                      false
% 1.94/0.99  --bmc1_non_equiv_states                 false
% 1.94/0.99  --bmc1_deadlock                         false
% 1.94/0.99  --bmc1_ucm                              false
% 1.94/0.99  --bmc1_add_unsat_core                   none
% 1.94/0.99  --bmc1_unsat_core_children              false
% 1.94/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.94/0.99  --bmc1_out_stat                         full
% 1.94/0.99  --bmc1_ground_init                      false
% 1.94/0.99  --bmc1_pre_inst_next_state              false
% 1.94/0.99  --bmc1_pre_inst_state                   false
% 1.94/0.99  --bmc1_pre_inst_reach_state             false
% 1.94/0.99  --bmc1_out_unsat_core                   false
% 1.94/0.99  --bmc1_aig_witness_out                  false
% 1.94/0.99  --bmc1_verbose                          false
% 1.94/0.99  --bmc1_dump_clauses_tptp                false
% 1.94/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.94/0.99  --bmc1_dump_file                        -
% 1.94/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.94/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.94/0.99  --bmc1_ucm_extend_mode                  1
% 1.94/0.99  --bmc1_ucm_init_mode                    2
% 1.94/0.99  --bmc1_ucm_cone_mode                    none
% 1.94/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.94/0.99  --bmc1_ucm_relax_model                  4
% 1.94/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.94/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.94/0.99  --bmc1_ucm_layered_model                none
% 1.94/0.99  --bmc1_ucm_max_lemma_size               10
% 1.94/0.99  
% 1.94/0.99  ------ AIG Options
% 1.94/0.99  
% 1.94/0.99  --aig_mode                              false
% 1.94/0.99  
% 1.94/0.99  ------ Instantiation Options
% 1.94/0.99  
% 1.94/0.99  --instantiation_flag                    true
% 1.94/0.99  --inst_sos_flag                         false
% 1.94/0.99  --inst_sos_phase                        true
% 1.94/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.94/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.94/0.99  --inst_lit_sel_side                     num_symb
% 1.94/0.99  --inst_solver_per_active                1400
% 1.94/0.99  --inst_solver_calls_frac                1.
% 1.94/0.99  --inst_passive_queue_type               priority_queues
% 1.94/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.94/0.99  --inst_passive_queues_freq              [25;2]
% 1.94/0.99  --inst_dismatching                      true
% 1.94/0.99  --inst_eager_unprocessed_to_passive     true
% 1.94/0.99  --inst_prop_sim_given                   true
% 1.94/0.99  --inst_prop_sim_new                     false
% 1.94/0.99  --inst_subs_new                         false
% 1.94/0.99  --inst_eq_res_simp                      false
% 1.94/0.99  --inst_subs_given                       false
% 1.94/0.99  --inst_orphan_elimination               true
% 1.94/0.99  --inst_learning_loop_flag               true
% 1.94/0.99  --inst_learning_start                   3000
% 1.94/0.99  --inst_learning_factor                  2
% 1.94/0.99  --inst_start_prop_sim_after_learn       3
% 1.94/0.99  --inst_sel_renew                        solver
% 1.94/0.99  --inst_lit_activity_flag                true
% 1.94/0.99  --inst_restr_to_given                   false
% 1.94/0.99  --inst_activity_threshold               500
% 1.94/0.99  --inst_out_proof                        true
% 1.94/0.99  
% 1.94/0.99  ------ Resolution Options
% 1.94/0.99  
% 1.94/0.99  --resolution_flag                       true
% 1.94/0.99  --res_lit_sel                           adaptive
% 1.94/0.99  --res_lit_sel_side                      none
% 1.94/0.99  --res_ordering                          kbo
% 1.94/0.99  --res_to_prop_solver                    active
% 1.94/0.99  --res_prop_simpl_new                    false
% 1.94/0.99  --res_prop_simpl_given                  true
% 1.94/0.99  --res_passive_queue_type                priority_queues
% 1.94/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.94/0.99  --res_passive_queues_freq               [15;5]
% 1.94/0.99  --res_forward_subs                      full
% 1.94/0.99  --res_backward_subs                     full
% 1.94/0.99  --res_forward_subs_resolution           true
% 1.94/0.99  --res_backward_subs_resolution          true
% 1.94/0.99  --res_orphan_elimination                true
% 1.94/0.99  --res_time_limit                        2.
% 1.94/0.99  --res_out_proof                         true
% 1.94/0.99  
% 1.94/0.99  ------ Superposition Options
% 1.94/0.99  
% 1.94/0.99  --superposition_flag                    true
% 1.94/0.99  --sup_passive_queue_type                priority_queues
% 1.94/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.94/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.94/0.99  --demod_completeness_check              fast
% 1.94/0.99  --demod_use_ground                      true
% 1.94/0.99  --sup_to_prop_solver                    passive
% 1.94/0.99  --sup_prop_simpl_new                    true
% 1.94/0.99  --sup_prop_simpl_given                  true
% 1.94/0.99  --sup_fun_splitting                     false
% 1.94/0.99  --sup_smt_interval                      50000
% 1.94/0.99  
% 1.94/0.99  ------ Superposition Simplification Setup
% 1.94/0.99  
% 1.94/0.99  --sup_indices_passive                   []
% 1.94/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.94/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.94/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.94/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.94/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.94/0.99  --sup_full_bw                           [BwDemod]
% 1.94/0.99  --sup_immed_triv                        [TrivRules]
% 1.94/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.94/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.94/0.99  --sup_immed_bw_main                     []
% 1.94/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.94/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.94/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.94/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.94/0.99  
% 1.94/0.99  ------ Combination Options
% 1.94/0.99  
% 1.94/0.99  --comb_res_mult                         3
% 1.94/0.99  --comb_sup_mult                         2
% 1.94/0.99  --comb_inst_mult                        10
% 1.94/0.99  
% 1.94/0.99  ------ Debug Options
% 1.94/0.99  
% 1.94/0.99  --dbg_backtrace                         false
% 1.94/0.99  --dbg_dump_prop_clauses                 false
% 1.94/0.99  --dbg_dump_prop_clauses_file            -
% 1.94/0.99  --dbg_out_stat                          false
% 1.94/0.99  ------ Parsing...
% 1.94/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.94/0.99  
% 1.94/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 1.94/0.99  
% 1.94/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.94/0.99  
% 1.94/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.94/0.99  ------ Proving...
% 1.94/0.99  ------ Problem Properties 
% 1.94/0.99  
% 1.94/0.99  
% 1.94/0.99  clauses                                 21
% 1.94/0.99  conjectures                             2
% 1.94/0.99  EPR                                     6
% 1.94/0.99  Horn                                    18
% 1.94/0.99  unary                                   6
% 1.94/0.99  binary                                  7
% 1.94/0.99  lits                                    52
% 1.94/0.99  lits eq                                 5
% 1.94/0.99  fd_pure                                 0
% 1.94/0.99  fd_pseudo                               0
% 1.94/0.99  fd_cond                                 1
% 1.94/0.99  fd_pseudo_cond                          0
% 1.94/0.99  AC symbols                              0
% 1.94/0.99  
% 1.94/0.99  ------ Schedule dynamic 5 is on 
% 1.94/0.99  
% 1.94/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.94/0.99  
% 1.94/0.99  
% 1.94/0.99  ------ 
% 1.94/0.99  Current options:
% 1.94/0.99  ------ 
% 1.94/0.99  
% 1.94/0.99  ------ Input Options
% 1.94/0.99  
% 1.94/0.99  --out_options                           all
% 1.94/0.99  --tptp_safe_out                         true
% 1.94/0.99  --problem_path                          ""
% 1.94/0.99  --include_path                          ""
% 1.94/0.99  --clausifier                            res/vclausify_rel
% 1.94/0.99  --clausifier_options                    --mode clausify
% 1.94/0.99  --stdin                                 false
% 1.94/0.99  --stats_out                             all
% 1.94/0.99  
% 1.94/0.99  ------ General Options
% 1.94/0.99  
% 1.94/0.99  --fof                                   false
% 1.94/0.99  --time_out_real                         305.
% 1.94/0.99  --time_out_virtual                      -1.
% 1.94/0.99  --symbol_type_check                     false
% 1.94/0.99  --clausify_out                          false
% 1.94/0.99  --sig_cnt_out                           false
% 1.94/0.99  --trig_cnt_out                          false
% 1.94/0.99  --trig_cnt_out_tolerance                1.
% 1.94/0.99  --trig_cnt_out_sk_spl                   false
% 1.94/0.99  --abstr_cl_out                          false
% 1.94/0.99  
% 1.94/0.99  ------ Global Options
% 1.94/0.99  
% 1.94/0.99  --schedule                              default
% 1.94/0.99  --add_important_lit                     false
% 1.94/0.99  --prop_solver_per_cl                    1000
% 1.94/0.99  --min_unsat_core                        false
% 1.94/0.99  --soft_assumptions                      false
% 1.94/0.99  --soft_lemma_size                       3
% 1.94/0.99  --prop_impl_unit_size                   0
% 1.94/0.99  --prop_impl_unit                        []
% 1.94/0.99  --share_sel_clauses                     true
% 1.94/0.99  --reset_solvers                         false
% 1.94/0.99  --bc_imp_inh                            [conj_cone]
% 1.94/0.99  --conj_cone_tolerance                   3.
% 1.94/0.99  --extra_neg_conj                        none
% 1.94/0.99  --large_theory_mode                     true
% 1.94/0.99  --prolific_symb_bound                   200
% 1.94/0.99  --lt_threshold                          2000
% 1.94/0.99  --clause_weak_htbl                      true
% 1.94/0.99  --gc_record_bc_elim                     false
% 1.94/0.99  
% 1.94/0.99  ------ Preprocessing Options
% 1.94/0.99  
% 1.94/0.99  --preprocessing_flag                    true
% 1.94/0.99  --time_out_prep_mult                    0.1
% 1.94/0.99  --splitting_mode                        input
% 1.94/0.99  --splitting_grd                         true
% 1.94/0.99  --splitting_cvd                         false
% 1.94/0.99  --splitting_cvd_svl                     false
% 1.94/0.99  --splitting_nvd                         32
% 1.94/0.99  --sub_typing                            true
% 1.94/0.99  --prep_gs_sim                           true
% 1.94/0.99  --prep_unflatten                        true
% 1.94/0.99  --prep_res_sim                          true
% 1.94/0.99  --prep_upred                            true
% 1.94/0.99  --prep_sem_filter                       exhaustive
% 1.94/0.99  --prep_sem_filter_out                   false
% 1.94/0.99  --pred_elim                             true
% 1.94/0.99  --res_sim_input                         true
% 1.94/0.99  --eq_ax_congr_red                       true
% 1.94/0.99  --pure_diseq_elim                       true
% 1.94/0.99  --brand_transform                       false
% 1.94/0.99  --non_eq_to_eq                          false
% 1.94/0.99  --prep_def_merge                        true
% 1.94/0.99  --prep_def_merge_prop_impl              false
% 1.94/0.99  --prep_def_merge_mbd                    true
% 1.94/0.99  --prep_def_merge_tr_red                 false
% 1.94/0.99  --prep_def_merge_tr_cl                  false
% 1.94/0.99  --smt_preprocessing                     true
% 1.94/0.99  --smt_ac_axioms                         fast
% 1.94/0.99  --preprocessed_out                      false
% 1.94/0.99  --preprocessed_stats                    false
% 1.94/0.99  
% 1.94/0.99  ------ Abstraction refinement Options
% 1.94/0.99  
% 1.94/0.99  --abstr_ref                             []
% 1.94/0.99  --abstr_ref_prep                        false
% 1.94/0.99  --abstr_ref_until_sat                   false
% 1.94/0.99  --abstr_ref_sig_restrict                funpre
% 1.94/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.94/0.99  --abstr_ref_under                       []
% 1.94/0.99  
% 1.94/0.99  ------ SAT Options
% 1.94/0.99  
% 1.94/0.99  --sat_mode                              false
% 1.94/0.99  --sat_fm_restart_options                ""
% 1.94/0.99  --sat_gr_def                            false
% 1.94/0.99  --sat_epr_types                         true
% 1.94/0.99  --sat_non_cyclic_types                  false
% 1.94/0.99  --sat_finite_models                     false
% 1.94/0.99  --sat_fm_lemmas                         false
% 1.94/0.99  --sat_fm_prep                           false
% 1.94/0.99  --sat_fm_uc_incr                        true
% 1.94/0.99  --sat_out_model                         small
% 1.94/0.99  --sat_out_clauses                       false
% 1.94/0.99  
% 1.94/0.99  ------ QBF Options
% 1.94/0.99  
% 1.94/0.99  --qbf_mode                              false
% 1.94/0.99  --qbf_elim_univ                         false
% 1.94/0.99  --qbf_dom_inst                          none
% 1.94/0.99  --qbf_dom_pre_inst                      false
% 1.94/0.99  --qbf_sk_in                             false
% 1.94/0.99  --qbf_pred_elim                         true
% 1.94/0.99  --qbf_split                             512
% 1.94/0.99  
% 1.94/0.99  ------ BMC1 Options
% 1.94/0.99  
% 1.94/0.99  --bmc1_incremental                      false
% 1.94/0.99  --bmc1_axioms                           reachable_all
% 1.94/0.99  --bmc1_min_bound                        0
% 1.94/0.99  --bmc1_max_bound                        -1
% 1.94/0.99  --bmc1_max_bound_default                -1
% 1.94/0.99  --bmc1_symbol_reachability              true
% 1.94/0.99  --bmc1_property_lemmas                  false
% 1.94/0.99  --bmc1_k_induction                      false
% 1.94/0.99  --bmc1_non_equiv_states                 false
% 1.94/0.99  --bmc1_deadlock                         false
% 1.94/0.99  --bmc1_ucm                              false
% 1.94/0.99  --bmc1_add_unsat_core                   none
% 1.94/0.99  --bmc1_unsat_core_children              false
% 1.94/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.94/0.99  --bmc1_out_stat                         full
% 1.94/0.99  --bmc1_ground_init                      false
% 1.94/0.99  --bmc1_pre_inst_next_state              false
% 1.94/0.99  --bmc1_pre_inst_state                   false
% 1.94/0.99  --bmc1_pre_inst_reach_state             false
% 1.94/0.99  --bmc1_out_unsat_core                   false
% 1.94/0.99  --bmc1_aig_witness_out                  false
% 1.94/0.99  --bmc1_verbose                          false
% 1.94/0.99  --bmc1_dump_clauses_tptp                false
% 1.94/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.94/0.99  --bmc1_dump_file                        -
% 1.94/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.94/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.94/0.99  --bmc1_ucm_extend_mode                  1
% 1.94/0.99  --bmc1_ucm_init_mode                    2
% 1.94/0.99  --bmc1_ucm_cone_mode                    none
% 1.94/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.94/0.99  --bmc1_ucm_relax_model                  4
% 1.94/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.94/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.94/0.99  --bmc1_ucm_layered_model                none
% 1.94/0.99  --bmc1_ucm_max_lemma_size               10
% 1.94/0.99  
% 1.94/0.99  ------ AIG Options
% 1.94/0.99  
% 1.94/0.99  --aig_mode                              false
% 1.94/0.99  
% 1.94/0.99  ------ Instantiation Options
% 1.94/0.99  
% 1.94/0.99  --instantiation_flag                    true
% 1.94/0.99  --inst_sos_flag                         false
% 1.94/0.99  --inst_sos_phase                        true
% 1.94/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.94/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.94/0.99  --inst_lit_sel_side                     none
% 1.94/0.99  --inst_solver_per_active                1400
% 1.94/0.99  --inst_solver_calls_frac                1.
% 1.94/0.99  --inst_passive_queue_type               priority_queues
% 1.94/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.94/0.99  --inst_passive_queues_freq              [25;2]
% 1.94/0.99  --inst_dismatching                      true
% 1.94/0.99  --inst_eager_unprocessed_to_passive     true
% 1.94/0.99  --inst_prop_sim_given                   true
% 1.94/0.99  --inst_prop_sim_new                     false
% 1.94/0.99  --inst_subs_new                         false
% 1.94/0.99  --inst_eq_res_simp                      false
% 1.94/0.99  --inst_subs_given                       false
% 1.94/0.99  --inst_orphan_elimination               true
% 1.94/0.99  --inst_learning_loop_flag               true
% 1.94/0.99  --inst_learning_start                   3000
% 1.94/0.99  --inst_learning_factor                  2
% 1.94/0.99  --inst_start_prop_sim_after_learn       3
% 1.94/0.99  --inst_sel_renew                        solver
% 1.94/0.99  --inst_lit_activity_flag                true
% 1.94/0.99  --inst_restr_to_given                   false
% 1.94/0.99  --inst_activity_threshold               500
% 1.94/0.99  --inst_out_proof                        true
% 1.94/0.99  
% 1.94/0.99  ------ Resolution Options
% 1.94/0.99  
% 1.94/0.99  --resolution_flag                       false
% 1.94/0.99  --res_lit_sel                           adaptive
% 1.94/0.99  --res_lit_sel_side                      none
% 1.94/0.99  --res_ordering                          kbo
% 1.94/0.99  --res_to_prop_solver                    active
% 1.94/0.99  --res_prop_simpl_new                    false
% 1.94/0.99  --res_prop_simpl_given                  true
% 1.94/0.99  --res_passive_queue_type                priority_queues
% 1.94/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.94/0.99  --res_passive_queues_freq               [15;5]
% 1.94/0.99  --res_forward_subs                      full
% 1.94/0.99  --res_backward_subs                     full
% 1.94/0.99  --res_forward_subs_resolution           true
% 1.94/0.99  --res_backward_subs_resolution          true
% 1.94/0.99  --res_orphan_elimination                true
% 1.94/0.99  --res_time_limit                        2.
% 1.94/0.99  --res_out_proof                         true
% 1.94/0.99  
% 1.94/0.99  ------ Superposition Options
% 1.94/0.99  
% 1.94/0.99  --superposition_flag                    true
% 1.94/0.99  --sup_passive_queue_type                priority_queues
% 1.94/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.94/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.94/0.99  --demod_completeness_check              fast
% 1.94/0.99  --demod_use_ground                      true
% 1.94/0.99  --sup_to_prop_solver                    passive
% 1.94/0.99  --sup_prop_simpl_new                    true
% 1.94/0.99  --sup_prop_simpl_given                  true
% 1.94/0.99  --sup_fun_splitting                     false
% 1.94/0.99  --sup_smt_interval                      50000
% 1.94/0.99  
% 1.94/0.99  ------ Superposition Simplification Setup
% 1.94/0.99  
% 1.94/0.99  --sup_indices_passive                   []
% 1.94/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.94/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.94/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.94/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.94/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.94/0.99  --sup_full_bw                           [BwDemod]
% 1.94/0.99  --sup_immed_triv                        [TrivRules]
% 1.94/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.94/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.94/0.99  --sup_immed_bw_main                     []
% 1.94/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.94/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.94/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.94/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.94/0.99  
% 1.94/0.99  ------ Combination Options
% 1.94/0.99  
% 1.94/0.99  --comb_res_mult                         3
% 1.94/0.99  --comb_sup_mult                         2
% 1.94/0.99  --comb_inst_mult                        10
% 1.94/0.99  
% 1.94/0.99  ------ Debug Options
% 1.94/0.99  
% 1.94/0.99  --dbg_backtrace                         false
% 1.94/0.99  --dbg_dump_prop_clauses                 false
% 1.94/0.99  --dbg_dump_prop_clauses_file            -
% 1.94/0.99  --dbg_out_stat                          false
% 1.94/0.99  
% 1.94/0.99  
% 1.94/0.99  
% 1.94/0.99  
% 1.94/0.99  ------ Proving...
% 1.94/0.99  
% 1.94/0.99  
% 1.94/0.99  % SZS status Theorem for theBenchmark.p
% 1.94/0.99  
% 1.94/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 1.94/0.99  
% 1.94/0.99  fof(f7,axiom,(
% 1.94/0.99    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.94/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.94/0.99  
% 1.94/0.99  fof(f49,plain,(
% 1.94/0.99    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.94/0.99    inference(cnf_transformation,[],[f7])).
% 1.94/0.99  
% 1.94/0.99  fof(f1,axiom,(
% 1.94/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.94/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.94/0.99  
% 1.94/0.99  fof(f15,plain,(
% 1.94/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.94/0.99    inference(ennf_transformation,[],[f1])).
% 1.94/0.99  
% 1.94/0.99  fof(f29,plain,(
% 1.94/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.94/0.99    inference(nnf_transformation,[],[f15])).
% 1.94/0.99  
% 1.94/0.99  fof(f30,plain,(
% 1.94/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.94/0.99    inference(rectify,[],[f29])).
% 1.94/0.99  
% 1.94/0.99  fof(f31,plain,(
% 1.94/0.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 1.94/0.99    introduced(choice_axiom,[])).
% 1.94/0.99  
% 1.94/0.99  fof(f32,plain,(
% 1.94/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.94/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).
% 1.94/0.99  
% 1.94/0.99  fof(f42,plain,(
% 1.94/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 1.94/0.99    inference(cnf_transformation,[],[f32])).
% 1.94/0.99  
% 1.94/0.99  fof(f5,axiom,(
% 1.94/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 1.94/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.94/0.99  
% 1.94/0.99  fof(f18,plain,(
% 1.94/0.99    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.94/0.99    inference(ennf_transformation,[],[f5])).
% 1.94/0.99  
% 1.94/0.99  fof(f47,plain,(
% 1.94/0.99    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 1.94/0.99    inference(cnf_transformation,[],[f18])).
% 1.94/0.99  
% 1.94/0.99  fof(f9,axiom,(
% 1.94/0.99    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.94/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.94/0.99  
% 1.94/0.99  fof(f22,plain,(
% 1.94/0.99    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.94/0.99    inference(ennf_transformation,[],[f9])).
% 1.94/0.99  
% 1.94/0.99  fof(f51,plain,(
% 1.94/0.99    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.94/0.99    inference(cnf_transformation,[],[f22])).
% 1.94/0.99  
% 1.94/0.99  fof(f12,conjecture,(
% 1.94/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 1.94/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.94/0.99  
% 1.94/0.99  fof(f13,negated_conjecture,(
% 1.94/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 1.94/0.99    inference(negated_conjecture,[],[f12])).
% 1.94/0.99  
% 1.94/0.99  fof(f14,plain,(
% 1.94/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 1.94/0.99    inference(pure_predicate_removal,[],[f13])).
% 1.94/0.99  
% 1.94/0.99  fof(f27,plain,(
% 1.94/0.99    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.94/0.99    inference(ennf_transformation,[],[f14])).
% 1.94/0.99  
% 1.94/0.99  fof(f28,plain,(
% 1.94/0.99    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.94/0.99    inference(flattening,[],[f27])).
% 1.94/0.99  
% 1.94/0.99  fof(f39,plain,(
% 1.94/0.99    ( ! [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => (~v2_tex_2(sK4,X0) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(sK4))) )),
% 1.94/0.99    introduced(choice_axiom,[])).
% 1.94/0.99  
% 1.94/0.99  fof(f38,plain,(
% 1.94/0.99    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (~v2_tex_2(X1,sK3) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) & v1_xboole_0(X1)) & l1_pre_topc(sK3) & v2_pre_topc(sK3))),
% 1.94/0.99    introduced(choice_axiom,[])).
% 1.94/0.99  
% 1.94/0.99  fof(f40,plain,(
% 1.94/0.99    (~v2_tex_2(sK4,sK3) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) & v1_xboole_0(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3)),
% 1.94/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f28,f39,f38])).
% 1.94/0.99  
% 1.94/0.99  fof(f61,plain,(
% 1.94/0.99    v1_xboole_0(sK4)),
% 1.94/0.99    inference(cnf_transformation,[],[f40])).
% 1.94/0.99  
% 1.94/0.99  fof(f3,axiom,(
% 1.94/0.99    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.94/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.94/0.99  
% 1.94/0.99  fof(f16,plain,(
% 1.94/0.99    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.94/0.99    inference(ennf_transformation,[],[f3])).
% 1.94/0.99  
% 1.94/0.99  fof(f45,plain,(
% 1.94/0.99    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 1.94/0.99    inference(cnf_transformation,[],[f16])).
% 1.94/0.99  
% 1.94/0.99  fof(f4,axiom,(
% 1.94/0.99    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 1.94/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.94/0.99  
% 1.94/0.99  fof(f17,plain,(
% 1.94/0.99    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 1.94/0.99    inference(ennf_transformation,[],[f4])).
% 1.94/0.99  
% 1.94/0.99  fof(f46,plain,(
% 1.94/0.99    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 1.94/0.99    inference(cnf_transformation,[],[f17])).
% 1.94/0.99  
% 1.94/0.99  fof(f6,axiom,(
% 1.94/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 1.94/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.94/0.99  
% 1.94/0.99  fof(f19,plain,(
% 1.94/0.99    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.94/0.99    inference(ennf_transformation,[],[f6])).
% 1.94/0.99  
% 1.94/0.99  fof(f48,plain,(
% 1.94/0.99    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 1.94/0.99    inference(cnf_transformation,[],[f19])).
% 1.94/0.99  
% 1.94/0.99  fof(f11,axiom,(
% 1.94/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0))) & r1_tarski(X2,X1))))))),
% 1.94/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.94/0.99  
% 1.94/0.99  fof(f25,plain,(
% 1.94/0.99    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((? [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.94/0.99    inference(ennf_transformation,[],[f11])).
% 1.94/0.99  
% 1.94/0.99  fof(f26,plain,(
% 1.94/0.99    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.94/0.99    inference(flattening,[],[f25])).
% 1.94/0.99  
% 1.94/0.99  fof(f33,plain,(
% 1.94/0.99    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.94/0.99    inference(nnf_transformation,[],[f26])).
% 1.94/0.99  
% 1.94/0.99  fof(f34,plain,(
% 1.94/0.99    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (? [X5] : (k9_subset_1(u1_struct_0(X0),X1,X5) = X4 & v4_pre_topc(X5,X0) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.94/0.99    inference(rectify,[],[f33])).
% 1.94/0.99  
% 1.94/0.99  fof(f36,plain,(
% 1.94/0.99    ! [X4,X1,X0] : (? [X5] : (k9_subset_1(u1_struct_0(X0),X1,X5) = X4 & v4_pre_topc(X5,X0) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) => (k9_subset_1(u1_struct_0(X0),X1,sK2(X0,X1,X4)) = X4 & v4_pre_topc(sK2(X0,X1,X4),X0) & m1_subset_1(sK2(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.94/0.99    introduced(choice_axiom,[])).
% 1.94/0.99  
% 1.94/0.99  fof(f35,plain,(
% 1.94/0.99    ! [X1,X0] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK1(X0,X1) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(sK1(X0,X1),X1) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.94/0.99    introduced(choice_axiom,[])).
% 1.94/0.99  
% 1.94/0.99  fof(f37,plain,(
% 1.94/0.99    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK1(X0,X1) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(sK1(X0,X1),X1) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : ((k9_subset_1(u1_struct_0(X0),X1,sK2(X0,X1,X4)) = X4 & v4_pre_topc(sK2(X0,X1,X4),X0) & m1_subset_1(sK2(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.94/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f34,f36,f35])).
% 1.94/0.99  
% 1.94/0.99  fof(f57,plain,(
% 1.94/0.99    ( ! [X0,X1] : (v2_tex_2(X1,X0) | r1_tarski(sK1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.94/0.99    inference(cnf_transformation,[],[f37])).
% 1.94/0.99  
% 1.94/0.99  fof(f60,plain,(
% 1.94/0.99    l1_pre_topc(sK3)),
% 1.94/0.99    inference(cnf_transformation,[],[f40])).
% 1.94/0.99  
% 1.94/0.99  fof(f63,plain,(
% 1.94/0.99    ~v2_tex_2(sK4,sK3)),
% 1.94/0.99    inference(cnf_transformation,[],[f40])).
% 1.94/0.99  
% 1.94/0.99  fof(f58,plain,(
% 1.94/0.99    ( ! [X0,X3,X1] : (v2_tex_2(X1,X0) | k9_subset_1(u1_struct_0(X0),X1,X3) != sK1(X0,X1) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.94/0.99    inference(cnf_transformation,[],[f37])).
% 1.94/0.99  
% 1.94/0.99  fof(f2,axiom,(
% 1.94/0.99    v1_xboole_0(k1_xboole_0)),
% 1.94/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.94/0.99  
% 1.94/0.99  fof(f44,plain,(
% 1.94/0.99    v1_xboole_0(k1_xboole_0)),
% 1.94/0.99    inference(cnf_transformation,[],[f2])).
% 1.94/0.99  
% 1.94/0.99  fof(f10,axiom,(
% 1.94/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_xboole_0(X1) => v4_pre_topc(X1,X0))))),
% 1.94/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.94/0.99  
% 1.94/0.99  fof(f23,plain,(
% 1.94/0.99    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) | ~v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.94/0.99    inference(ennf_transformation,[],[f10])).
% 1.94/0.99  
% 1.94/0.99  fof(f24,plain,(
% 1.94/0.99    ! [X0] : (! [X1] : (v4_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.94/0.99    inference(flattening,[],[f23])).
% 1.94/0.99  
% 1.94/0.99  fof(f52,plain,(
% 1.94/0.99    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.94/0.99    inference(cnf_transformation,[],[f24])).
% 1.94/0.99  
% 1.94/0.99  fof(f59,plain,(
% 1.94/0.99    v2_pre_topc(sK3)),
% 1.94/0.99    inference(cnf_transformation,[],[f40])).
% 1.94/0.99  
% 1.94/0.99  cnf(c_8,plain,
% 1.94/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 1.94/0.99      inference(cnf_transformation,[],[f49]) ).
% 1.94/0.99  
% 1.94/0.99  cnf(c_2342,plain,
% 1.94/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 1.94/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 1.94/0.99  
% 1.94/0.99  cnf(c_1,plain,
% 1.94/0.99      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 1.94/0.99      inference(cnf_transformation,[],[f42]) ).
% 1.94/0.99  
% 1.94/0.99  cnf(c_2347,plain,
% 1.94/0.99      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 1.94/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 1.94/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 1.94/0.99  
% 1.94/0.99  cnf(c_6,plain,
% 1.94/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.94/0.99      | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 1.94/0.99      inference(cnf_transformation,[],[f47]) ).
% 1.94/0.99  
% 1.94/0.99  cnf(c_2344,plain,
% 1.94/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 1.94/0.99      | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 1.94/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 1.94/0.99  
% 1.94/0.99  cnf(c_10,plain,
% 1.94/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.94/0.99      | ~ r2_hidden(X2,X0)
% 1.94/0.99      | ~ v1_xboole_0(X1) ),
% 1.94/0.99      inference(cnf_transformation,[],[f51]) ).
% 1.94/0.99  
% 1.94/0.99  cnf(c_20,negated_conjecture,
% 1.94/0.99      ( v1_xboole_0(sK4) ),
% 1.94/0.99      inference(cnf_transformation,[],[f61]) ).
% 1.94/0.99  
% 1.94/0.99  cnf(c_324,plain,
% 1.94/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.94/0.99      | ~ r2_hidden(X2,X0)
% 1.94/0.99      | sK4 != X1 ),
% 1.94/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_20]) ).
% 1.94/0.99  
% 1.94/0.99  cnf(c_325,plain,
% 1.94/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK4)) | ~ r2_hidden(X1,X0) ),
% 1.94/0.99      inference(unflattening,[status(thm)],[c_324]) ).
% 1.94/0.99  
% 1.94/0.99  cnf(c_2335,plain,
% 1.94/0.99      ( m1_subset_1(X0,k1_zfmisc_1(sK4)) != iProver_top
% 1.94/0.99      | r2_hidden(X1,X0) != iProver_top ),
% 1.94/0.99      inference(predicate_to_equality,[status(thm)],[c_325]) ).
% 1.94/0.99  
% 1.94/0.99  cnf(c_4,plain,
% 1.94/0.99      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 1.94/0.99      inference(cnf_transformation,[],[f45]) ).
% 1.94/0.99  
% 1.94/0.99  cnf(c_319,plain,
% 1.94/0.99      ( sK4 != X0 | k1_xboole_0 = X0 ),
% 1.94/0.99      inference(resolution_lifted,[status(thm)],[c_4,c_20]) ).
% 1.94/0.99  
% 1.94/0.99  cnf(c_320,plain,
% 1.94/0.99      ( k1_xboole_0 = sK4 ),
% 1.94/0.99      inference(unflattening,[status(thm)],[c_319]) ).
% 1.94/0.99  
% 1.94/0.99  cnf(c_2368,plain,
% 1.94/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 1.94/0.99      | r2_hidden(X1,X0) != iProver_top ),
% 1.94/0.99      inference(light_normalisation,[status(thm)],[c_2335,c_320]) ).
% 1.94/0.99  
% 1.94/0.99  cnf(c_3461,plain,
% 1.94/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 1.94/0.99      | r2_hidden(X1,k9_subset_1(k1_xboole_0,X2,X0)) != iProver_top ),
% 1.94/0.99      inference(superposition,[status(thm)],[c_2344,c_2368]) ).
% 1.94/0.99  
% 1.94/0.99  cnf(c_3672,plain,
% 1.94/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 1.94/0.99      | r1_tarski(k9_subset_1(k1_xboole_0,X1,X0),X2) = iProver_top ),
% 1.94/0.99      inference(superposition,[status(thm)],[c_2347,c_3461]) ).
% 1.94/0.99  
% 1.94/0.99  cnf(c_5,plain,
% 1.94/0.99      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 1.94/0.99      inference(cnf_transformation,[],[f46]) ).
% 1.94/0.99  
% 1.94/0.99  cnf(c_2345,plain,
% 1.94/0.99      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 1.94/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 1.94/0.99  
% 1.94/0.99  cnf(c_4272,plain,
% 1.94/0.99      ( k9_subset_1(k1_xboole_0,X0,X1) = k1_xboole_0
% 1.94/0.99      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 1.94/0.99      inference(superposition,[status(thm)],[c_3672,c_2345]) ).
% 1.94/0.99  
% 1.94/0.99  cnf(c_5093,plain,
% 1.94/0.99      ( k9_subset_1(k1_xboole_0,X0,k1_xboole_0) = k1_xboole_0 ),
% 1.94/0.99      inference(superposition,[status(thm)],[c_2342,c_4272]) ).
% 1.94/0.99  
% 1.94/0.99  cnf(c_7,plain,
% 1.94/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.94/0.99      | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 1.94/0.99      inference(cnf_transformation,[],[f48]) ).
% 1.94/0.99  
% 1.94/0.99  cnf(c_2343,plain,
% 1.94/0.99      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
% 1.94/0.99      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 1.94/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 1.94/0.99  
% 1.94/0.99  cnf(c_3428,plain,
% 1.94/0.99      ( k9_subset_1(X0,X1,k1_xboole_0) = k3_xboole_0(X1,k1_xboole_0) ),
% 1.94/0.99      inference(superposition,[status(thm)],[c_2342,c_2343]) ).
% 1.94/0.99  
% 1.94/0.99  cnf(c_5137,plain,
% 1.94/0.99      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 1.94/0.99      inference(superposition,[status(thm)],[c_5093,c_3428]) ).
% 1.94/0.99  
% 1.94/0.99  cnf(c_5142,plain,
% 1.94/0.99      ( k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 1.94/0.99      inference(instantiation,[status(thm)],[c_5137]) ).
% 1.94/0.99  
% 1.94/0.99  cnf(c_13,plain,
% 1.94/0.99      ( v2_tex_2(X0,X1)
% 1.94/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.94/0.99      | r1_tarski(sK1(X1,X0),X0)
% 1.94/0.99      | ~ l1_pre_topc(X1) ),
% 1.94/0.99      inference(cnf_transformation,[],[f57]) ).
% 1.94/0.99  
% 1.94/0.99  cnf(c_21,negated_conjecture,
% 1.94/0.99      ( l1_pre_topc(sK3) ),
% 1.94/0.99      inference(cnf_transformation,[],[f60]) ).
% 1.94/0.99  
% 1.94/0.99  cnf(c_515,plain,
% 1.94/0.99      ( v2_tex_2(X0,X1)
% 1.94/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.94/0.99      | r1_tarski(sK1(X1,X0),X0)
% 1.94/0.99      | sK3 != X1 ),
% 1.94/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_21]) ).
% 1.94/0.99  
% 1.94/0.99  cnf(c_516,plain,
% 1.94/0.99      ( v2_tex_2(X0,sK3)
% 1.94/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.94/0.99      | r1_tarski(sK1(sK3,X0),X0) ),
% 1.94/0.99      inference(unflattening,[status(thm)],[c_515]) ).
% 1.94/0.99  
% 1.94/0.99  cnf(c_2330,plain,
% 1.94/0.99      ( v2_tex_2(X0,sK3) = iProver_top
% 1.94/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 1.94/0.99      | r1_tarski(sK1(sK3,X0),X0) = iProver_top ),
% 1.94/0.99      inference(predicate_to_equality,[status(thm)],[c_516]) ).
% 1.94/0.99  
% 1.94/0.99  cnf(c_2706,plain,
% 1.94/0.99      ( v2_tex_2(k1_xboole_0,sK3) = iProver_top
% 1.94/0.99      | r1_tarski(sK1(sK3,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 1.94/0.99      inference(superposition,[status(thm)],[c_2342,c_2330]) ).
% 1.94/0.99  
% 1.94/0.99  cnf(c_517,plain,
% 1.94/0.99      ( v2_tex_2(X0,sK3) = iProver_top
% 1.94/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 1.94/0.99      | r1_tarski(sK1(sK3,X0),X0) = iProver_top ),
% 1.94/0.99      inference(predicate_to_equality,[status(thm)],[c_516]) ).
% 1.94/0.99  
% 1.94/0.99  cnf(c_519,plain,
% 1.94/0.99      ( v2_tex_2(k1_xboole_0,sK3) = iProver_top
% 1.94/0.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 1.94/0.99      | r1_tarski(sK1(sK3,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 1.94/0.99      inference(instantiation,[status(thm)],[c_517]) ).
% 1.94/0.99  
% 1.94/0.99  cnf(c_18,negated_conjecture,
% 1.94/0.99      ( ~ v2_tex_2(sK4,sK3) ),
% 1.94/0.99      inference(cnf_transformation,[],[f63]) ).
% 1.94/0.99  
% 1.94/0.99  cnf(c_2340,plain,
% 1.94/0.99      ( v2_tex_2(sK4,sK3) != iProver_top ),
% 1.94/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 1.94/0.99  
% 1.94/0.99  cnf(c_2354,plain,
% 1.94/0.99      ( v2_tex_2(k1_xboole_0,sK3) != iProver_top ),
% 1.94/0.99      inference(light_normalisation,[status(thm)],[c_2340,c_320]) ).
% 1.94/0.99  
% 1.94/0.99  cnf(c_2503,plain,
% 1.94/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 1.94/0.99      inference(instantiation,[status(thm)],[c_8]) ).
% 1.94/0.99  
% 1.94/0.99  cnf(c_2507,plain,
% 1.94/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 1.94/0.99      inference(predicate_to_equality,[status(thm)],[c_2503]) ).
% 1.94/0.99  
% 1.94/0.99  cnf(c_3105,plain,
% 1.94/0.99      ( r1_tarski(sK1(sK3,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 1.94/0.99      inference(global_propositional_subsumption,
% 1.94/0.99                [status(thm)],
% 1.94/0.99                [c_2706,c_519,c_2354,c_2507]) ).
% 1.94/0.99  
% 1.94/0.99  cnf(c_3110,plain,
% 1.94/0.99      ( sK1(sK3,k1_xboole_0) = k1_xboole_0 ),
% 1.94/0.99      inference(superposition,[status(thm)],[c_3105,c_2345]) ).
% 1.94/0.99  
% 1.94/0.99  cnf(c_12,plain,
% 1.94/0.99      ( v2_tex_2(X0,X1)
% 1.94/0.99      | ~ v4_pre_topc(X2,X1)
% 1.94/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.94/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.94/0.99      | ~ l1_pre_topc(X1)
% 1.94/0.99      | k9_subset_1(u1_struct_0(X1),X0,X2) != sK1(X1,X0) ),
% 1.94/0.99      inference(cnf_transformation,[],[f58]) ).
% 1.94/0.99  
% 1.94/0.99  cnf(c_530,plain,
% 1.94/0.99      ( v2_tex_2(X0,X1)
% 1.94/0.99      | ~ v4_pre_topc(X2,X1)
% 1.94/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.94/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.94/0.99      | k9_subset_1(u1_struct_0(X1),X0,X2) != sK1(X1,X0)
% 1.94/0.99      | sK3 != X1 ),
% 1.94/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_21]) ).
% 1.94/0.99  
% 1.94/0.99  cnf(c_531,plain,
% 1.94/0.99      ( v2_tex_2(X0,sK3)
% 1.94/0.99      | ~ v4_pre_topc(X1,sK3)
% 1.94/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.94/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.94/0.99      | k9_subset_1(u1_struct_0(sK3),X0,X1) != sK1(sK3,X0) ),
% 1.94/0.99      inference(unflattening,[status(thm)],[c_530]) ).
% 1.94/0.99  
% 1.94/0.99  cnf(c_2329,plain,
% 1.94/0.99      ( k9_subset_1(u1_struct_0(sK3),X0,X1) != sK1(sK3,X0)
% 1.94/0.99      | v2_tex_2(X0,sK3) = iProver_top
% 1.94/0.99      | v4_pre_topc(X1,sK3) != iProver_top
% 1.94/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 1.94/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 1.94/0.99      inference(predicate_to_equality,[status(thm)],[c_531]) ).
% 1.94/0.99  
% 1.94/0.99  cnf(c_4215,plain,
% 1.94/0.99      ( sK1(sK3,X0) != k3_xboole_0(X0,k1_xboole_0)
% 1.94/0.99      | v2_tex_2(X0,sK3) = iProver_top
% 1.94/0.99      | v4_pre_topc(k1_xboole_0,sK3) != iProver_top
% 1.94/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 1.94/0.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 1.94/0.99      inference(superposition,[status(thm)],[c_3428,c_2329]) ).
% 1.94/0.99  
% 1.94/0.99  cnf(c_3,plain,
% 1.94/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 1.94/0.99      inference(cnf_transformation,[],[f44]) ).
% 1.94/0.99  
% 1.94/0.99  cnf(c_11,plain,
% 1.94/0.99      ( v4_pre_topc(X0,X1)
% 1.94/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.94/0.99      | ~ v2_pre_topc(X1)
% 1.94/0.99      | ~ l1_pre_topc(X1)
% 1.94/0.99      | ~ v1_xboole_0(X0) ),
% 1.94/0.99      inference(cnf_transformation,[],[f52]) ).
% 1.94/0.99  
% 1.94/0.99  cnf(c_22,negated_conjecture,
% 1.94/0.99      ( v2_pre_topc(sK3) ),
% 1.94/0.99      inference(cnf_transformation,[],[f59]) ).
% 1.94/0.99  
% 1.94/0.99  cnf(c_259,plain,
% 1.94/0.99      ( v4_pre_topc(X0,X1)
% 1.94/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.94/0.99      | ~ l1_pre_topc(X1)
% 1.94/0.99      | ~ v1_xboole_0(X0)
% 1.94/0.99      | sK3 != X1 ),
% 1.94/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_22]) ).
% 1.94/0.99  
% 1.94/0.99  cnf(c_260,plain,
% 1.94/0.99      ( v4_pre_topc(X0,sK3)
% 1.94/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.94/0.99      | ~ l1_pre_topc(sK3)
% 1.94/0.99      | ~ v1_xboole_0(X0) ),
% 1.94/0.99      inference(unflattening,[status(thm)],[c_259]) ).
% 1.94/0.99  
% 1.94/0.99  cnf(c_264,plain,
% 1.94/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.94/0.99      | v4_pre_topc(X0,sK3)
% 1.94/0.99      | ~ v1_xboole_0(X0) ),
% 1.94/0.99      inference(global_propositional_subsumption,
% 1.94/0.99                [status(thm)],
% 1.94/0.99                [c_260,c_21]) ).
% 1.94/0.99  
% 1.94/0.99  cnf(c_265,plain,
% 1.94/0.99      ( v4_pre_topc(X0,sK3)
% 1.94/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.94/0.99      | ~ v1_xboole_0(X0) ),
% 1.94/0.99      inference(renaming,[status(thm)],[c_264]) ).
% 1.94/0.99  
% 1.94/0.99  cnf(c_284,plain,
% 1.94/0.99      ( v4_pre_topc(X0,sK3)
% 1.94/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.94/0.99      | k1_xboole_0 != X0 ),
% 1.94/0.99      inference(resolution_lifted,[status(thm)],[c_3,c_265]) ).
% 1.94/0.99  
% 1.94/0.99  cnf(c_285,plain,
% 1.94/0.99      ( v4_pre_topc(k1_xboole_0,sK3)
% 1.94/0.99      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 1.94/0.99      inference(unflattening,[status(thm)],[c_284]) ).
% 1.94/0.99  
% 1.94/0.99  cnf(c_291,plain,
% 1.94/0.99      ( v4_pre_topc(k1_xboole_0,sK3) ),
% 1.94/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_285,c_8]) ).
% 1.94/0.99  
% 1.94/0.99  cnf(c_293,plain,
% 1.94/0.99      ( v4_pre_topc(k1_xboole_0,sK3) = iProver_top ),
% 1.94/0.99      inference(predicate_to_equality,[status(thm)],[c_291]) ).
% 1.94/0.99  
% 1.94/0.99  cnf(c_4370,plain,
% 1.94/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 1.94/0.99      | sK1(sK3,X0) != k3_xboole_0(X0,k1_xboole_0)
% 1.94/0.99      | v2_tex_2(X0,sK3) = iProver_top ),
% 1.94/0.99      inference(global_propositional_subsumption,
% 1.94/0.99                [status(thm)],
% 1.94/0.99                [c_4215,c_293,c_2507]) ).
% 1.94/0.99  
% 1.94/0.99  cnf(c_4371,plain,
% 1.94/0.99      ( sK1(sK3,X0) != k3_xboole_0(X0,k1_xboole_0)
% 1.94/0.99      | v2_tex_2(X0,sK3) = iProver_top
% 1.94/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 1.94/0.99      inference(renaming,[status(thm)],[c_4370]) ).
% 1.94/0.99  
% 1.94/0.99  cnf(c_4379,plain,
% 1.94/0.99      ( k3_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 1.94/0.99      | v2_tex_2(k1_xboole_0,sK3) = iProver_top
% 1.94/0.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 1.94/0.99      inference(superposition,[status(thm)],[c_3110,c_4371]) ).
% 1.94/0.99  
% 1.94/0.99  cnf(contradiction,plain,
% 1.94/0.99      ( $false ),
% 1.94/0.99      inference(minisat,[status(thm)],[c_5142,c_4379,c_2507,c_2354]) ).
% 1.94/0.99  
% 1.94/0.99  
% 1.94/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 1.94/0.99  
% 1.94/0.99  ------                               Statistics
% 1.94/0.99  
% 1.94/0.99  ------ General
% 1.94/0.99  
% 1.94/0.99  abstr_ref_over_cycles:                  0
% 1.94/0.99  abstr_ref_under_cycles:                 0
% 1.94/0.99  gc_basic_clause_elim:                   0
% 1.94/0.99  forced_gc_time:                         0
% 1.94/0.99  parsing_time:                           0.008
% 1.94/0.99  unif_index_cands_time:                  0.
% 1.94/0.99  unif_index_add_time:                    0.
% 1.94/0.99  orderings_time:                         0.
% 1.94/0.99  out_proof_time:                         0.006
% 1.94/0.99  total_time:                             0.164
% 1.94/0.99  num_of_symbols:                         49
% 1.94/0.99  num_of_terms:                           3405
% 1.94/0.99  
% 1.94/0.99  ------ Preprocessing
% 1.94/0.99  
% 1.94/0.99  num_of_splits:                          0
% 1.94/0.99  num_of_split_atoms:                     0
% 1.94/0.99  num_of_reused_defs:                     0
% 1.94/0.99  num_eq_ax_congr_red:                    30
% 1.94/0.99  num_of_sem_filtered_clauses:            1
% 1.94/0.99  num_of_subtypes:                        0
% 1.94/0.99  monotx_restored_types:                  0
% 1.94/0.99  sat_num_of_epr_types:                   0
% 1.94/0.99  sat_num_of_non_cyclic_types:            0
% 1.94/0.99  sat_guarded_non_collapsed_types:        0
% 1.94/0.99  num_pure_diseq_elim:                    0
% 1.94/0.99  simp_replaced_by:                       0
% 1.94/0.99  res_preprocessed:                       111
% 1.94/0.99  prep_upred:                             0
% 1.94/0.99  prep_unflattend:                        91
% 1.94/0.99  smt_new_axioms:                         0
% 1.94/0.99  pred_elim_cands:                        5
% 1.94/0.99  pred_elim:                              3
% 1.94/0.99  pred_elim_cl:                           2
% 1.94/0.99  pred_elim_cycles:                       10
% 1.94/0.99  merged_defs:                            0
% 1.94/0.99  merged_defs_ncl:                        0
% 1.94/0.99  bin_hyper_res:                          0
% 1.94/0.99  prep_cycles:                            4
% 1.94/0.99  pred_elim_time:                         0.026
% 1.94/0.99  splitting_time:                         0.
% 1.94/0.99  sem_filter_time:                        0.
% 1.94/0.99  monotx_time:                            0.001
% 1.94/0.99  subtype_inf_time:                       0.
% 1.94/0.99  
% 1.94/0.99  ------ Problem properties
% 1.94/0.99  
% 1.94/0.99  clauses:                                21
% 1.94/0.99  conjectures:                            2
% 1.94/0.99  epr:                                    6
% 1.94/0.99  horn:                                   18
% 1.94/0.99  ground:                                 5
% 1.94/0.99  unary:                                  6
% 1.94/0.99  binary:                                 7
% 1.94/0.99  lits:                                   52
% 1.94/0.99  lits_eq:                                5
% 1.94/0.99  fd_pure:                                0
% 1.94/0.99  fd_pseudo:                              0
% 1.94/0.99  fd_cond:                                1
% 1.94/0.99  fd_pseudo_cond:                         0
% 1.94/0.99  ac_symbols:                             0
% 1.94/0.99  
% 1.94/0.99  ------ Propositional Solver
% 1.94/0.99  
% 1.94/0.99  prop_solver_calls:                      28
% 1.94/0.99  prop_fast_solver_calls:                 1109
% 1.94/0.99  smt_solver_calls:                       0
% 1.94/0.99  smt_fast_solver_calls:                  0
% 1.94/0.99  prop_num_of_clauses:                    1326
% 1.94/0.99  prop_preprocess_simplified:             4773
% 1.94/0.99  prop_fo_subsumed:                       20
% 1.94/0.99  prop_solver_time:                       0.
% 1.94/0.99  smt_solver_time:                        0.
% 1.94/0.99  smt_fast_solver_time:                   0.
% 1.94/0.99  prop_fast_solver_time:                  0.
% 1.94/0.99  prop_unsat_core_time:                   0.
% 1.94/0.99  
% 1.94/0.99  ------ QBF
% 1.94/0.99  
% 1.94/0.99  qbf_q_res:                              0
% 1.94/0.99  qbf_num_tautologies:                    0
% 1.94/0.99  qbf_prep_cycles:                        0
% 1.94/0.99  
% 1.94/0.99  ------ BMC1
% 1.94/0.99  
% 1.94/0.99  bmc1_current_bound:                     -1
% 1.94/0.99  bmc1_last_solved_bound:                 -1
% 1.94/0.99  bmc1_unsat_core_size:                   -1
% 1.94/0.99  bmc1_unsat_core_parents_size:           -1
% 1.94/0.99  bmc1_merge_next_fun:                    0
% 1.94/0.99  bmc1_unsat_core_clauses_time:           0.
% 1.94/0.99  
% 1.94/0.99  ------ Instantiation
% 1.94/0.99  
% 1.94/0.99  inst_num_of_clauses:                    374
% 1.94/0.99  inst_num_in_passive:                    80
% 1.94/0.99  inst_num_in_active:                     202
% 1.94/0.99  inst_num_in_unprocessed:                94
% 1.94/0.99  inst_num_of_loops:                      250
% 1.94/0.99  inst_num_of_learning_restarts:          0
% 1.94/0.99  inst_num_moves_active_passive:          45
% 1.94/0.99  inst_lit_activity:                      0
% 1.94/0.99  inst_lit_activity_moves:                0
% 1.94/0.99  inst_num_tautologies:                   0
% 1.94/0.99  inst_num_prop_implied:                  0
% 1.94/0.99  inst_num_existing_simplified:           0
% 1.94/0.99  inst_num_eq_res_simplified:             0
% 1.94/0.99  inst_num_child_elim:                    0
% 1.94/0.99  inst_num_of_dismatching_blockings:      97
% 1.94/0.99  inst_num_of_non_proper_insts:           310
% 1.94/0.99  inst_num_of_duplicates:                 0
% 1.94/0.99  inst_inst_num_from_inst_to_res:         0
% 1.94/0.99  inst_dismatching_checking_time:         0.
% 1.94/0.99  
% 1.94/0.99  ------ Resolution
% 1.94/0.99  
% 1.94/0.99  res_num_of_clauses:                     0
% 1.94/0.99  res_num_in_passive:                     0
% 1.94/0.99  res_num_in_active:                      0
% 1.94/0.99  res_num_of_loops:                       115
% 1.94/0.99  res_forward_subset_subsumed:            19
% 1.94/0.99  res_backward_subset_subsumed:           4
% 1.94/0.99  res_forward_subsumed:                   0
% 1.94/0.99  res_backward_subsumed:                  0
% 1.94/0.99  res_forward_subsumption_resolution:     5
% 1.94/0.99  res_backward_subsumption_resolution:    0
% 1.94/0.99  res_clause_to_clause_subsumption:       535
% 1.94/0.99  res_orphan_elimination:                 0
% 1.94/0.99  res_tautology_del:                      48
% 1.94/0.99  res_num_eq_res_simplified:              0
% 1.94/0.99  res_num_sel_changes:                    0
% 1.94/0.99  res_moves_from_active_to_pass:          0
% 1.94/0.99  
% 1.94/0.99  ------ Superposition
% 1.94/0.99  
% 1.94/0.99  sup_time_total:                         0.
% 1.94/0.99  sup_time_generating:                    0.
% 1.94/0.99  sup_time_sim_full:                      0.
% 1.94/0.99  sup_time_sim_immed:                     0.
% 1.94/0.99  
% 1.94/0.99  sup_num_of_clauses:                     81
% 1.94/0.99  sup_num_in_active:                      48
% 1.94/0.99  sup_num_in_passive:                     33
% 1.94/0.99  sup_num_of_loops:                       48
% 1.94/0.99  sup_fw_superposition:                   51
% 1.94/0.99  sup_bw_superposition:                   34
% 1.94/0.99  sup_immediate_simplified:               14
% 1.94/0.99  sup_given_eliminated:                   0
% 1.94/0.99  comparisons_done:                       0
% 1.94/0.99  comparisons_avoided:                    0
% 1.94/0.99  
% 1.94/0.99  ------ Simplifications
% 1.94/0.99  
% 1.94/0.99  
% 1.94/0.99  sim_fw_subset_subsumed:                 5
% 1.94/0.99  sim_bw_subset_subsumed:                 0
% 1.94/0.99  sim_fw_subsumed:                        6
% 1.94/0.99  sim_bw_subsumed:                        0
% 1.94/0.99  sim_fw_subsumption_res:                 1
% 1.94/0.99  sim_bw_subsumption_res:                 0
% 1.94/0.99  sim_tautology_del:                      6
% 1.94/0.99  sim_eq_tautology_del:                   4
% 1.94/0.99  sim_eq_res_simp:                        0
% 1.94/0.99  sim_fw_demodulated:                     4
% 1.94/0.99  sim_bw_demodulated:                     1
% 1.94/0.99  sim_light_normalised:                   12
% 1.94/0.99  sim_joinable_taut:                      0
% 1.94/0.99  sim_joinable_simp:                      0
% 1.94/0.99  sim_ac_normalised:                      0
% 1.94/0.99  sim_smt_subsumption:                    0
% 1.94/0.99  
%------------------------------------------------------------------------------
