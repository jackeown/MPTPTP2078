%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:26:14 EST 2020

% Result     : Theorem 39.68s
% Output     : CNFRefutation 39.68s
% Verified   : 
% Statistics : Number of formulae       :  269 (15237 expanded)
%              Number of clauses        :  202 (5450 expanded)
%              Number of leaves         :   23 (3173 expanded)
%              Depth                    :   47
%              Number of atoms          :  819 (51844 expanded)
%              Number of equality atoms :  435 (9926 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f28,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f27])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).

fof(f47,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

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
    inference(ennf_transformation,[],[f11])).

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

fof(f38,plain,(
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

fof(f39,plain,(
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
    inference(rectify,[],[f38])).

fof(f41,plain,(
    ! [X4,X1,X0] :
      ( ? [X5] :
          ( k9_subset_1(u1_struct_0(X0),X1,X5) = X4
          & v4_pre_topc(X5,X0)
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X0),X1,sK3(X0,X1,X4)) = X4
        & v4_pre_topc(sK3(X0,X1,X4),X0)
        & m1_subset_1(sK3(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
              | ~ v4_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ! [X3] :
            ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1)
            | ~ v4_pre_topc(X3,X0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & r1_tarski(sK2(X0,X1),X1)
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ( ! [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1)
                    | ~ v4_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & r1_tarski(sK2(X0,X1),X1)
                & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X4] :
                  ( ( k9_subset_1(u1_struct_0(X0),X1,sK3(X0,X1,X4)) = X4
                    & v4_pre_topc(sK3(X0,X1,X4),X0)
                    & m1_subset_1(sK3(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r1_tarski(X4,X1)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f39,f41,f40])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | r1_tarski(sK2(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f2,axiom,(
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
    inference(ennf_transformation,[],[f2])).

fof(f31,plain,(
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

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f31])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f32,f33])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

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

fof(f51,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

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

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
     => ( ~ v2_tex_2(sK5,X0)
        & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
        & v1_xboole_0(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
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

fof(f45,plain,
    ( ~ v2_tex_2(sK5,sK4)
    & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    & v1_xboole_0(sK5)
    & l1_pre_topc(sK4)
    & v2_pre_topc(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f26,f44,f43])).

fof(f70,plain,(
    v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f45])).

fof(f46,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f35])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f74,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f52])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f54,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f71,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f45])).

fof(f72,plain,(
    ~ v2_tex_2(sK5,sK4) ),
    inference(cnf_transformation,[],[f45])).

fof(f69,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f45])).

fof(f68,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f45])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f67,plain,(
    ! [X0,X3,X1] :
      ( v2_tex_2(X1,X0)
      | k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1)
      | ~ v4_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1123,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_11,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1115,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_17,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(sK2(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1109,plain,
    ( v2_tex_2(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(sK2(X1,X0),X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2869,plain,
    ( v2_tex_2(k1_xboole_0,X0) = iProver_top
    | r1_tarski(sK2(X0,k1_xboole_0),k1_xboole_0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1115,c_1109])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1119,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_9229,plain,
    ( v2_tex_2(k1_xboole_0,X0) = iProver_top
    | r2_hidden(X1,sK2(X0,k1_xboole_0)) != iProver_top
    | r2_hidden(X1,k1_xboole_0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2869,c_1119])).

cnf(c_51099,plain,
    ( v2_tex_2(k1_xboole_0,X0) = iProver_top
    | r2_hidden(sK0(sK2(X0,k1_xboole_0)),k1_xboole_0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(sK2(X0,k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1123,c_9229])).

cnf(c_479,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_5,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1475,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_479,c_5])).

cnf(c_24,negated_conjecture,
    ( v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1485,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1475,c_24])).

cnf(c_1486,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1485])).

cnf(c_3178,plain,
    ( v2_tex_2(k1_xboole_0,X0)
    | r1_tarski(sK2(X0,k1_xboole_0),k1_xboole_0)
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_17,c_11])).

cnf(c_2163,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_hidden(sK0(X0),X1)
    | v1_xboole_0(X0) ),
    inference(resolution,[status(thm)],[c_4,c_0])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_2383,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(resolution,[status(thm)],[c_2163,c_1])).

cnf(c_3596,plain,
    ( v2_tex_2(k1_xboole_0,X0)
    | ~ l1_pre_topc(X0)
    | v1_xboole_0(sK2(X0,k1_xboole_0))
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_3178,c_2383])).

cnf(c_3597,plain,
    ( v2_tex_2(k1_xboole_0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(sK2(X0,k1_xboole_0)) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3596])).

cnf(c_66034,plain,
    ( v2_tex_2(k1_xboole_0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(sK2(X0,k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_51099,c_1486,c_3597])).

cnf(c_1102,plain,
    ( v1_xboole_0(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_1118,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1460,plain,
    ( sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1102,c_1118])).

cnf(c_1820,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1460,c_1102])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1120,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_8,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1116,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_12,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1114,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_14,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1112,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2823,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1114,c_1112])).

cnf(c_4054,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1116,c_2823])).

cnf(c_4261,plain,
    ( m1_subset_1(sK1(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1120,c_4054])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1113,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_5302,plain,
    ( r1_tarski(sK1(k1_zfmisc_1(X0),X1),X0) = iProver_top
    | r1_tarski(k1_zfmisc_1(X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_4261,c_1113])).

cnf(c_6580,plain,
    ( r1_tarski(k1_zfmisc_1(X0),X1) = iProver_top
    | r2_hidden(X2,X0) = iProver_top
    | r2_hidden(X2,sK1(k1_zfmisc_1(X0),X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5302,c_1119])).

cnf(c_15029,plain,
    ( r1_tarski(k1_zfmisc_1(X0),X1) = iProver_top
    | r2_hidden(sK0(sK1(k1_zfmisc_1(X0),X1)),X0) = iProver_top
    | v1_xboole_0(sK1(k1_zfmisc_1(X0),X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1123,c_6580])).

cnf(c_1122,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_44884,plain,
    ( r1_tarski(k1_zfmisc_1(X0),X1) = iProver_top
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK1(k1_zfmisc_1(X0),X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_15029,c_1122])).

cnf(c_45135,plain,
    ( sK1(k1_zfmisc_1(X0),X1) = k1_xboole_0
    | r1_tarski(k1_zfmisc_1(X0),X1) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_44884,c_1118])).

cnf(c_45696,plain,
    ( sK1(k1_zfmisc_1(X0),X1) = k1_xboole_0
    | r2_hidden(X2,X1) = iProver_top
    | r2_hidden(X2,k1_zfmisc_1(X0)) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_45135,c_1119])).

cnf(c_54748,plain,
    ( sK1(k1_zfmisc_1(X0),X1) = k1_xboole_0
    | r1_tarski(k1_zfmisc_1(X0),X2) = iProver_top
    | r2_hidden(sK1(k1_zfmisc_1(X0),X2),X1) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1120,c_45696])).

cnf(c_69611,plain,
    ( sK1(k1_zfmisc_1(X0),X1) = k1_xboole_0
    | r1_tarski(k1_zfmisc_1(X0),X2) = iProver_top
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_54748,c_1122])).

cnf(c_72664,plain,
    ( sK1(k1_zfmisc_1(X0),k1_xboole_0) = k1_xboole_0
    | r1_tarski(k1_zfmisc_1(X0),X1) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1820,c_69611])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1117,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_73004,plain,
    ( sK1(k1_zfmisc_1(X0),k1_xboole_0) = k1_xboole_0
    | k1_zfmisc_1(X0) = X1
    | r1_tarski(X1,k1_zfmisc_1(X0)) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_72664,c_1117])).

cnf(c_73297,plain,
    ( sK1(k1_zfmisc_1(X0),k1_xboole_0) = k1_xboole_0
    | sK1(k1_zfmisc_1(X1),k1_xboole_0) = k1_xboole_0
    | k1_zfmisc_1(X1) = k1_zfmisc_1(X0)
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_72664,c_73004])).

cnf(c_2032,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1120,c_1122])).

cnf(c_2349,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2032,c_1117])).

cnf(c_4028,plain,
    ( X0 = X1
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2032,c_2349])).

cnf(c_478,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_477,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3161,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_478,c_477])).

cnf(c_483,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_5844,plain,
    ( X0 != X1
    | k1_zfmisc_1(X1) = k1_zfmisc_1(X0) ),
    inference(resolution,[status(thm)],[c_3161,c_483])).

cnf(c_80602,plain,
    ( k1_zfmisc_1(X1) = k1_zfmisc_1(X0)
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_73297,c_4028,c_5844])).

cnf(c_80603,plain,
    ( k1_zfmisc_1(X0) = k1_zfmisc_1(X1)
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_80602])).

cnf(c_80609,plain,
    ( k1_zfmisc_1(X0) = k1_zfmisc_1(k1_xboole_0)
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1820,c_80603])).

cnf(c_4260,plain,
    ( m1_subset_1(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1123,c_4054])).

cnf(c_5117,plain,
    ( r1_tarski(sK0(k1_zfmisc_1(X0)),X0) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4260,c_1113])).

cnf(c_5366,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,sK0(k1_zfmisc_1(X1))) != iProver_top
    | v1_xboole_0(k1_zfmisc_1(X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5117,c_1119])).

cnf(c_9583,plain,
    ( r2_hidden(sK0(sK0(k1_zfmisc_1(X0))),X0) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(X0)) = iProver_top
    | v1_xboole_0(sK0(k1_zfmisc_1(X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1123,c_5366])).

cnf(c_12073,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k1_zfmisc_1(X0)) = iProver_top
    | v1_xboole_0(sK0(k1_zfmisc_1(X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_9583,c_1122])).

cnf(c_12379,plain,
    ( sK0(k1_zfmisc_1(X0)) = k1_xboole_0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k1_zfmisc_1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_12073,c_1118])).

cnf(c_12709,plain,
    ( k1_zfmisc_1(X0) = k1_xboole_0
    | sK0(k1_zfmisc_1(X0)) = k1_xboole_0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_12379,c_1118])).

cnf(c_13254,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_xboole_0
    | sK0(k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1820,c_12709])).

cnf(c_9584,plain,
    ( r1_tarski(sK0(k1_zfmisc_1(X0)),X1) = iProver_top
    | r2_hidden(sK1(sK0(k1_zfmisc_1(X0)),X1),X0) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1120,c_5366])).

cnf(c_27064,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_xboole_0
    | r1_tarski(sK0(k1_zfmisc_1(k1_xboole_0)),X0) = iProver_top
    | r2_hidden(sK1(k1_xboole_0,X0),k1_xboole_0) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_13254,c_9584])).

cnf(c_27393,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_xboole_0
    | m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,sK0(k1_zfmisc_1(k1_xboole_0))) != iProver_top
    | r2_hidden(sK1(k1_xboole_0,X1),k1_xboole_0) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_27064,c_2823])).

cnf(c_2046,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_14,c_11])).

cnf(c_2047,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2046])).

cnf(c_27390,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_xboole_0
    | sK0(k1_zfmisc_1(k1_xboole_0)) = X0
    | r1_tarski(X0,sK0(k1_zfmisc_1(k1_xboole_0))) != iProver_top
    | r2_hidden(sK1(k1_xboole_0,X0),k1_xboole_0) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_27064,c_1117])).

cnf(c_35947,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_xboole_0
    | sK0(k1_zfmisc_1(k1_xboole_0)) = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top
    | r2_hidden(sK1(k1_xboole_0,X0),k1_xboole_0) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_13254,c_27390])).

cnf(c_13298,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_xboole_0
    | r2_hidden(sK0(k1_xboole_0),k1_xboole_0) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | v1_xboole_0(sK0(k1_zfmisc_1(k1_xboole_0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_13254,c_9583])).

cnf(c_1684,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1115,c_1113])).

cnf(c_2223,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1684,c_1119])).

cnf(c_13518,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_xboole_0
    | r2_hidden(sK0(k1_xboole_0),X0) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | v1_xboole_0(sK0(k1_zfmisc_1(k1_xboole_0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_13298,c_2223])).

cnf(c_13956,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_xboole_0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | v1_xboole_0(sK0(k1_zfmisc_1(k1_xboole_0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_13518,c_1122])).

cnf(c_14009,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_xboole_0
    | v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | v1_xboole_0(sK0(k1_zfmisc_1(k1_xboole_0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1820,c_13956])).

cnf(c_14207,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_xboole_0
    | sK0(k1_zfmisc_1(k1_xboole_0)) = X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_14009,c_4028])).

cnf(c_2070,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2046,c_13])).

cnf(c_484,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3279,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_484,c_477])).

cnf(c_3802,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k1_xboole_0,X1)
    | ~ v1_xboole_0(X0) ),
    inference(resolution,[status(thm)],[c_3279,c_5])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2050,plain,
    ( m1_subset_1(X0,u1_struct_0(sK4))
    | ~ r2_hidden(X0,sK5) ),
    inference(resolution,[status(thm)],[c_14,c_23])).

cnf(c_3830,plain,
    ( m1_subset_1(k1_xboole_0,u1_struct_0(sK4))
    | ~ r2_hidden(X0,sK5)
    | ~ v1_xboole_0(X0) ),
    inference(resolution,[status(thm)],[c_3802,c_2050])).

cnf(c_4088,plain,
    ( m1_subset_1(k1_xboole_0,u1_struct_0(sK4))
    | ~ r1_tarski(X0,sK5)
    | v1_xboole_0(X0)
    | ~ v1_xboole_0(sK0(X0)) ),
    inference(resolution,[status(thm)],[c_3830,c_2163])).

cnf(c_1653,plain,
    ( ~ r1_tarski(X0,sK5)
    | ~ r1_tarski(sK5,X0)
    | X0 = sK5 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1749,plain,
    ( r1_tarski(sK5,X0)
    | r2_hidden(sK1(sK5,X0),sK5) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2430,plain,
    ( v1_xboole_0(X0)
    | ~ v1_xboole_0(sK5)
    | X0 != sK5 ),
    inference(instantiation,[status(thm)],[c_479])).

cnf(c_5735,plain,
    ( ~ r2_hidden(sK1(sK5,X0),sK5)
    | ~ v1_xboole_0(sK5) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_15110,plain,
    ( v1_xboole_0(X0)
    | ~ r1_tarski(X0,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4088,c_24,c_1653,c_1749,c_2430,c_5735])).

cnf(c_15111,plain,
    ( ~ r1_tarski(X0,sK5)
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_15110])).

cnf(c_19514,plain,
    ( ~ r2_hidden(X0,k1_xboole_0)
    | v1_xboole_0(X0) ),
    inference(resolution,[status(thm)],[c_2070,c_15111])).

cnf(c_19623,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | v1_xboole_0(X0)
    | v1_xboole_0(sK0(X0)) ),
    inference(resolution,[status(thm)],[c_19514,c_2163])).

cnf(c_1445,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[status(thm)],[c_13,c_11])).

cnf(c_1651,plain,
    ( X0 != X1
    | X0 = sK5
    | sK5 != X1 ),
    inference(instantiation,[status(thm)],[c_478])).

cnf(c_5689,plain,
    ( X0 = sK5
    | X0 != k1_xboole_0
    | sK5 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1651])).

cnf(c_11222,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,X0)
    | X0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_21206,plain,
    ( v1_xboole_0(X0)
    | ~ r1_tarski(X0,k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_19623,c_24,c_1445,c_1460,c_2430,c_5689,c_11222])).

cnf(c_21207,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_21206])).

cnf(c_21208,plain,
    ( r1_tarski(X0,k1_xboole_0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21207])).

cnf(c_36031,plain,
    ( r1_tarski(X0,k1_xboole_0) != iProver_top
    | sK0(k1_zfmisc_1(k1_xboole_0)) = X0
    | k1_zfmisc_1(k1_xboole_0) = k1_xboole_0
    | v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_35947,c_14207,c_21208])).

cnf(c_36032,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_xboole_0
    | sK0(k1_zfmisc_1(k1_xboole_0)) = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top
    | v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_36031])).

cnf(c_36046,plain,
    ( sK2(X0,k1_xboole_0) = sK0(k1_zfmisc_1(k1_xboole_0))
    | k1_zfmisc_1(k1_xboole_0) = k1_xboole_0
    | v2_tex_2(k1_xboole_0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2869,c_36032])).

cnf(c_22,negated_conjecture,
    ( ~ v2_tex_2(sK5,sK4) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1104,plain,
    ( v2_tex_2(sK5,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1819,plain,
    ( v2_tex_2(k1_xboole_0,sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1460,c_1104])).

cnf(c_37920,plain,
    ( sK2(sK4,k1_xboole_0) = sK0(k1_zfmisc_1(k1_xboole_0))
    | k1_zfmisc_1(k1_xboole_0) = k1_xboole_0
    | l1_pre_topc(sK4) != iProver_top
    | v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_36046,c_1819])).

cnf(c_25,negated_conjecture,
    ( l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_28,plain,
    ( l1_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_39394,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_xboole_0
    | sK2(sK4,k1_xboole_0) = sK0(k1_zfmisc_1(k1_xboole_0))
    | v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_37920,c_28])).

cnf(c_39395,plain,
    ( sK2(sK4,k1_xboole_0) = sK0(k1_zfmisc_1(k1_xboole_0))
    | k1_zfmisc_1(k1_xboole_0) = k1_xboole_0
    | v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_39394])).

cnf(c_39408,plain,
    ( sK2(sK4,k1_xboole_0) = sK0(k1_zfmisc_1(k1_xboole_0))
    | k1_zfmisc_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_39395,c_1118])).

cnf(c_39634,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_xboole_0
    | v2_tex_2(k1_xboole_0,sK4) = iProver_top
    | r1_tarski(sK0(k1_zfmisc_1(k1_xboole_0)),k1_xboole_0) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_39408,c_2869])).

cnf(c_39775,plain,
    ( r1_tarski(sK0(k1_zfmisc_1(k1_xboole_0)),k1_xboole_0) = iProver_top
    | k1_zfmisc_1(k1_xboole_0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_39634,c_28,c_1819])).

cnf(c_39776,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_xboole_0
    | r1_tarski(sK0(k1_zfmisc_1(k1_xboole_0)),k1_xboole_0) = iProver_top ),
    inference(renaming,[status(thm)],[c_39775])).

cnf(c_39783,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_xboole_0
    | r2_hidden(X0,sK0(k1_zfmisc_1(k1_xboole_0))) != iProver_top
    | r2_hidden(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_39776,c_1119])).

cnf(c_41315,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_xboole_0
    | m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,sK0(k1_zfmisc_1(k1_xboole_0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_27393,c_2047,c_39783])).

cnf(c_41325,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_xboole_0
    | m1_subset_1(sK1(sK0(k1_zfmisc_1(k1_xboole_0)),X0),X1) = iProver_top
    | r1_tarski(sK0(k1_zfmisc_1(k1_xboole_0)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1120,c_41315])).

cnf(c_43380,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_xboole_0
    | m1_subset_1(sK1(k1_xboole_0,X0),X1) = iProver_top
    | r1_tarski(sK0(k1_zfmisc_1(k1_xboole_0)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_13254,c_41325])).

cnf(c_41618,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_xboole_0
    | r1_tarski(sK0(k1_zfmisc_1(k1_xboole_0)),X0) = iProver_top
    | r2_hidden(sK1(sK0(k1_zfmisc_1(k1_xboole_0)),X0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1120,c_39783])).

cnf(c_43564,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_xboole_0
    | r1_tarski(sK0(k1_zfmisc_1(k1_xboole_0)),X0) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_41618,c_1122])).

cnf(c_43960,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_xboole_0
    | r1_tarski(sK0(k1_zfmisc_1(k1_xboole_0)),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_43380,c_1486,c_43564])).

cnf(c_5367,plain,
    ( sK0(k1_zfmisc_1(X0)) = X0
    | r1_tarski(X0,sK0(k1_zfmisc_1(X0))) != iProver_top
    | v1_xboole_0(k1_zfmisc_1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5117,c_1117])).

cnf(c_43984,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_xboole_0
    | sK0(k1_zfmisc_1(sK0(k1_zfmisc_1(k1_xboole_0)))) = sK0(k1_zfmisc_1(k1_xboole_0))
    | v1_xboole_0(k1_zfmisc_1(sK0(k1_zfmisc_1(k1_xboole_0)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_43960,c_5367])).

cnf(c_46450,plain,
    ( k1_zfmisc_1(sK0(k1_zfmisc_1(k1_xboole_0))) = k1_xboole_0
    | k1_zfmisc_1(k1_xboole_0) = k1_xboole_0
    | sK0(k1_zfmisc_1(sK0(k1_zfmisc_1(k1_xboole_0)))) = sK0(k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_43984,c_1118])).

cnf(c_26,negated_conjecture,
    ( v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_27,plain,
    ( v2_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_15,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1359,plain,
    ( v4_pre_topc(k1_xboole_0,X0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1361,plain,
    ( v4_pre_topc(k1_xboole_0,X0) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1359])).

cnf(c_1363,plain,
    ( v4_pre_topc(k1_xboole_0,sK4) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1361])).

cnf(c_1360,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1365,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1360])).

cnf(c_1367,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1365])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_181,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_12])).

cnf(c_182,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_181])).

cnf(c_226,plain,
    ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
    | ~ r1_tarski(X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_9,c_182])).

cnf(c_1099,plain,
    ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) = iProver_top
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_226])).

cnf(c_1686,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k9_subset_1(X1,X2,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1099,c_1113])).

cnf(c_2111,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1684,c_1117])).

cnf(c_3355,plain,
    ( k9_subset_1(k1_xboole_0,X0,X1) = k1_xboole_0
    | r1_tarski(X1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1686,c_2111])).

cnf(c_3408,plain,
    ( k9_subset_1(k1_xboole_0,X0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1684,c_3355])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_227,plain,
    ( ~ r1_tarski(X0,X1)
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_10,c_182])).

cnf(c_1098,plain,
    ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_227])).

cnf(c_2615,plain,
    ( k9_subset_1(X0,X1,X0) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_1116,c_1098])).

cnf(c_3501,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3408,c_2615])).

cnf(c_2616,plain,
    ( k9_subset_1(X0,X1,k1_xboole_0) = k3_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1684,c_1098])).

cnf(c_3509,plain,
    ( k9_subset_1(X0,X1,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3501,c_2616])).

cnf(c_16,plain,
    ( v2_tex_2(X0,X1)
    | ~ v4_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),X0,X2) != sK2(X1,X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1110,plain,
    ( k9_subset_1(u1_struct_0(X0),X1,X2) != sK2(X0,X1)
    | v2_tex_2(X1,X0) = iProver_top
    | v4_pre_topc(X2,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3760,plain,
    ( sK2(X0,X1) != k1_xboole_0
    | v2_tex_2(X1,X0) = iProver_top
    | v4_pre_topc(k1_xboole_0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3509,c_1110])).

cnf(c_48433,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v4_pre_topc(k1_xboole_0,X0) != iProver_top
    | v2_tex_2(X1,X0) = iProver_top
    | sK2(X0,X1) != k1_xboole_0
    | l1_pre_topc(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3760,c_1365])).

cnf(c_48434,plain,
    ( sK2(X0,X1) != k1_xboole_0
    | v2_tex_2(X1,X0) = iProver_top
    | v4_pre_topc(k1_xboole_0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_48433])).

cnf(c_48444,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_xboole_0
    | sK0(k1_zfmisc_1(k1_xboole_0)) != k1_xboole_0
    | v2_tex_2(k1_xboole_0,sK4) = iProver_top
    | v4_pre_topc(k1_xboole_0,sK4) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_39408,c_48434])).

cnf(c_48766,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_46450,c_27,c_28,c_1363,c_1367,c_1486,c_1819,c_13254,c_48444])).

cnf(c_80722,plain,
    ( k1_zfmisc_1(X0) = k1_xboole_0
    | v1_xboole_0(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_80609,c_48766])).

cnf(c_81087,plain,
    ( k1_zfmisc_1(sK2(X0,k1_xboole_0)) = k1_xboole_0
    | v2_tex_2(k1_xboole_0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_66034,c_80722])).

cnf(c_117223,plain,
    ( k1_zfmisc_1(sK2(sK4,k1_xboole_0)) = k1_xboole_0
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_81087,c_1819])).

cnf(c_81180,plain,
    ( k1_zfmisc_1(sK2(sK4,k1_xboole_0)) = k1_xboole_0
    | v2_tex_2(k1_xboole_0,sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_81087])).

cnf(c_117386,plain,
    ( k1_zfmisc_1(sK2(sK4,k1_xboole_0)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_117223,c_28,c_1819,c_81180])).

cnf(c_6582,plain,
    ( k9_subset_1(X0,X1,sK1(k1_zfmisc_1(X0),X2)) = k3_xboole_0(X1,sK1(k1_zfmisc_1(X0),X2))
    | r1_tarski(k1_zfmisc_1(X0),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_5302,c_1098])).

cnf(c_127445,plain,
    ( k9_subset_1(X0,X1,sK1(k1_zfmisc_1(X0),X2)) = k3_xboole_0(X1,sK1(k1_zfmisc_1(X0),X2))
    | r2_hidden(X3,X2) = iProver_top
    | r2_hidden(X3,k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6582,c_1119])).

cnf(c_128446,plain,
    ( k9_subset_1(X0,X1,sK1(k1_zfmisc_1(X0),X2)) = k3_xboole_0(X1,sK1(k1_zfmisc_1(X0),X2))
    | r1_tarski(k1_zfmisc_1(X0),X3) = iProver_top
    | r2_hidden(sK1(k1_zfmisc_1(X0),X3),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1120,c_127445])).

cnf(c_134129,plain,
    ( k9_subset_1(X0,X1,sK1(k1_zfmisc_1(X0),X2)) = k3_xboole_0(X1,sK1(k1_zfmisc_1(X0),X2))
    | r1_tarski(k1_zfmisc_1(X0),X3) = iProver_top
    | v1_xboole_0(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_128446,c_1122])).

cnf(c_142051,plain,
    ( k9_subset_1(X0,X1,sK1(k1_zfmisc_1(X0),k1_xboole_0)) = k3_xboole_0(X1,sK1(k1_zfmisc_1(X0),k1_xboole_0))
    | r1_tarski(k1_zfmisc_1(X0),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1820,c_134129])).

cnf(c_51100,plain,
    ( v2_tex_2(k1_xboole_0,X0) = iProver_top
    | r1_tarski(sK2(X0,k1_xboole_0),X1) = iProver_top
    | r2_hidden(sK1(sK2(X0,k1_xboole_0),X1),k1_xboole_0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1120,c_9229])).

cnf(c_2165,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,X2)
    | r2_hidden(sK1(X0,X2),X1) ),
    inference(resolution,[status(thm)],[c_4,c_3])).

cnf(c_5854,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,X2)
    | ~ v1_xboole_0(X1) ),
    inference(resolution,[status(thm)],[c_2165,c_1])).

cnf(c_24631,plain,
    ( v2_tex_2(k1_xboole_0,X0)
    | r1_tarski(sK2(X0,k1_xboole_0),X1)
    | ~ l1_pre_topc(X0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_5854,c_3178])).

cnf(c_24632,plain,
    ( v2_tex_2(k1_xboole_0,X0) = iProver_top
    | r1_tarski(sK2(X0,k1_xboole_0),X1) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24631])).

cnf(c_86163,plain,
    ( r1_tarski(sK2(X0,k1_xboole_0),X1) = iProver_top
    | v2_tex_2(k1_xboole_0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_51100,c_1486,c_24632])).

cnf(c_86164,plain,
    ( v2_tex_2(k1_xboole_0,X0) = iProver_top
    | r1_tarski(sK2(X0,k1_xboole_0),X1) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_86163])).

cnf(c_86174,plain,
    ( sK2(X0,k1_xboole_0) = X1
    | v2_tex_2(k1_xboole_0,X0) = iProver_top
    | r1_tarski(X1,sK2(X0,k1_xboole_0)) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_86164,c_1117])).

cnf(c_143701,plain,
    ( k9_subset_1(X0,X1,sK1(k1_zfmisc_1(X0),k1_xboole_0)) = k3_xboole_0(X1,sK1(k1_zfmisc_1(X0),k1_xboole_0))
    | sK2(X2,k1_xboole_0) = k1_zfmisc_1(X0)
    | v2_tex_2(k1_xboole_0,X2) = iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_142051,c_86174])).

cnf(c_194287,plain,
    ( k9_subset_1(X0,X1,sK1(k1_zfmisc_1(X0),k1_xboole_0)) = k3_xboole_0(X1,sK1(k1_zfmisc_1(X0),k1_xboole_0))
    | sK2(sK4,k1_xboole_0) = k1_zfmisc_1(X0)
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_143701,c_1819])).

cnf(c_194305,plain,
    ( ~ l1_pre_topc(sK4)
    | k9_subset_1(X0,X1,sK1(k1_zfmisc_1(X0),k1_xboole_0)) = k3_xboole_0(X1,sK1(k1_zfmisc_1(X0),k1_xboole_0))
    | sK2(sK4,k1_xboole_0) = k1_zfmisc_1(X0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_194287])).

cnf(c_194528,plain,
    ( sK2(sK4,k1_xboole_0) = k1_zfmisc_1(X0)
    | k9_subset_1(X0,X1,sK1(k1_zfmisc_1(X0),k1_xboole_0)) = k3_xboole_0(X1,sK1(k1_zfmisc_1(X0),k1_xboole_0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_194287,c_25,c_194305])).

cnf(c_194529,plain,
    ( k9_subset_1(X0,X1,sK1(k1_zfmisc_1(X0),k1_xboole_0)) = k3_xboole_0(X1,sK1(k1_zfmisc_1(X0),k1_xboole_0))
    | sK2(sK4,k1_xboole_0) = k1_zfmisc_1(X0) ),
    inference(renaming,[status(thm)],[c_194528])).

cnf(c_194534,plain,
    ( k3_xboole_0(X0,sK1(k1_zfmisc_1(sK2(sK4,k1_xboole_0)),k1_xboole_0)) = k9_subset_1(sK2(sK4,k1_xboole_0),X0,sK1(k1_xboole_0,k1_xboole_0))
    | k1_zfmisc_1(sK2(sK4,k1_xboole_0)) = sK2(sK4,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_117386,c_194529])).

cnf(c_194835,plain,
    ( k9_subset_1(sK2(sK4,k1_xboole_0),X0,sK1(k1_xboole_0,k1_xboole_0)) = k3_xboole_0(X0,sK1(k1_xboole_0,k1_xboole_0))
    | sK2(sK4,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_194534,c_117386])).

cnf(c_1103,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1685,plain,
    ( r1_tarski(sK5,u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1103,c_1113])).

cnf(c_1885,plain,
    ( r1_tarski(k1_xboole_0,u1_struct_0(sK4)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1685,c_1460])).

cnf(c_2868,plain,
    ( v2_tex_2(X0,X1) = iProver_top
    | r1_tarski(X0,u1_struct_0(X1)) != iProver_top
    | r1_tarski(sK2(X1,X0),X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1114,c_1109])).

cnf(c_9112,plain,
    ( sK2(X0,k1_xboole_0) = k1_xboole_0
    | v2_tex_2(k1_xboole_0,X0) = iProver_top
    | r1_tarski(k1_xboole_0,u1_struct_0(X0)) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2868,c_2111])).

cnf(c_9216,plain,
    ( sK2(sK4,k1_xboole_0) = k1_xboole_0
    | v2_tex_2(k1_xboole_0,sK4) = iProver_top
    | r1_tarski(k1_xboole_0,u1_struct_0(sK4)) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_9112])).

cnf(c_194927,plain,
    ( sK2(sK4,k1_xboole_0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_194835,c_28,c_1819,c_1885,c_9216])).

cnf(c_195017,plain,
    ( v2_tex_2(k1_xboole_0,sK4) = iProver_top
    | v4_pre_topc(k1_xboole_0,sK4) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_194927,c_48434])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_195017,c_1819,c_1486,c_1367,c_1363,c_28,c_27])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 15:01:09 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 39.68/5.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 39.68/5.49  
% 39.68/5.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 39.68/5.49  
% 39.68/5.49  ------  iProver source info
% 39.68/5.49  
% 39.68/5.49  git: date: 2020-06-30 10:37:57 +0100
% 39.68/5.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 39.68/5.49  git: non_committed_changes: false
% 39.68/5.49  git: last_make_outside_of_git: false
% 39.68/5.49  
% 39.68/5.49  ------ 
% 39.68/5.49  ------ Parsing...
% 39.68/5.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 39.68/5.49  
% 39.68/5.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 39.68/5.49  
% 39.68/5.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 39.68/5.49  
% 39.68/5.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 39.68/5.49  ------ Proving...
% 39.68/5.49  ------ Problem Properties 
% 39.68/5.49  
% 39.68/5.49  
% 39.68/5.49  clauses                                 26
% 39.68/5.49  conjectures                             5
% 39.68/5.49  EPR                                     9
% 39.68/5.49  Horn                                    22
% 39.68/5.49  unary                                   7
% 39.68/5.49  binary                                  9
% 39.68/5.49  lits                                    71
% 39.68/5.49  lits eq                                 5
% 39.68/5.49  fd_pure                                 0
% 39.68/5.49  fd_pseudo                               0
% 39.68/5.49  fd_cond                                 1
% 39.68/5.49  fd_pseudo_cond                          1
% 39.68/5.49  AC symbols                              0
% 39.68/5.49  
% 39.68/5.49  ------ Input Options Time Limit: Unbounded
% 39.68/5.49  
% 39.68/5.49  
% 39.68/5.49  ------ 
% 39.68/5.49  Current options:
% 39.68/5.49  ------ 
% 39.68/5.49  
% 39.68/5.49  
% 39.68/5.49  
% 39.68/5.49  
% 39.68/5.49  ------ Proving...
% 39.68/5.49  
% 39.68/5.49  
% 39.68/5.49  % SZS status Theorem for theBenchmark.p
% 39.68/5.49  
% 39.68/5.49  % SZS output start CNFRefutation for theBenchmark.p
% 39.68/5.49  
% 39.68/5.49  fof(f1,axiom,(
% 39.68/5.49    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 39.68/5.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.68/5.49  
% 39.68/5.49  fof(f27,plain,(
% 39.68/5.49    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 39.68/5.49    inference(nnf_transformation,[],[f1])).
% 39.68/5.49  
% 39.68/5.49  fof(f28,plain,(
% 39.68/5.49    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 39.68/5.49    inference(rectify,[],[f27])).
% 39.68/5.49  
% 39.68/5.49  fof(f29,plain,(
% 39.68/5.49    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 39.68/5.49    introduced(choice_axiom,[])).
% 39.68/5.49  
% 39.68/5.49  fof(f30,plain,(
% 39.68/5.49    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 39.68/5.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).
% 39.68/5.49  
% 39.68/5.49  fof(f47,plain,(
% 39.68/5.49    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 39.68/5.49    inference(cnf_transformation,[],[f30])).
% 39.68/5.49  
% 39.68/5.49  fof(f7,axiom,(
% 39.68/5.49    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 39.68/5.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.68/5.49  
% 39.68/5.49  fof(f57,plain,(
% 39.68/5.49    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 39.68/5.49    inference(cnf_transformation,[],[f7])).
% 39.68/5.49  
% 39.68/5.49  fof(f11,axiom,(
% 39.68/5.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0))) & r1_tarski(X2,X1))))))),
% 39.68/5.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.68/5.49  
% 39.68/5.49  fof(f23,plain,(
% 39.68/5.49    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((? [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 39.68/5.49    inference(ennf_transformation,[],[f11])).
% 39.68/5.49  
% 39.68/5.49  fof(f24,plain,(
% 39.68/5.49    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 39.68/5.49    inference(flattening,[],[f23])).
% 39.68/5.49  
% 39.68/5.49  fof(f38,plain,(
% 39.68/5.49    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 39.68/5.49    inference(nnf_transformation,[],[f24])).
% 39.68/5.49  
% 39.68/5.49  fof(f39,plain,(
% 39.68/5.49    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (? [X5] : (k9_subset_1(u1_struct_0(X0),X1,X5) = X4 & v4_pre_topc(X5,X0) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 39.68/5.49    inference(rectify,[],[f38])).
% 39.68/5.49  
% 39.68/5.49  fof(f41,plain,(
% 39.68/5.49    ! [X4,X1,X0] : (? [X5] : (k9_subset_1(u1_struct_0(X0),X1,X5) = X4 & v4_pre_topc(X5,X0) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) => (k9_subset_1(u1_struct_0(X0),X1,sK3(X0,X1,X4)) = X4 & v4_pre_topc(sK3(X0,X1,X4),X0) & m1_subset_1(sK3(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))))),
% 39.68/5.49    introduced(choice_axiom,[])).
% 39.68/5.49  
% 39.68/5.49  fof(f40,plain,(
% 39.68/5.49    ! [X1,X0] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(sK2(X0,X1),X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 39.68/5.49    introduced(choice_axiom,[])).
% 39.68/5.49  
% 39.68/5.49  fof(f42,plain,(
% 39.68/5.49    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(sK2(X0,X1),X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : ((k9_subset_1(u1_struct_0(X0),X1,sK3(X0,X1,X4)) = X4 & v4_pre_topc(sK3(X0,X1,X4),X0) & m1_subset_1(sK3(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 39.68/5.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f39,f41,f40])).
% 39.68/5.49  
% 39.68/5.49  fof(f66,plain,(
% 39.68/5.49    ( ! [X0,X1] : (v2_tex_2(X1,X0) | r1_tarski(sK2(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 39.68/5.49    inference(cnf_transformation,[],[f42])).
% 39.68/5.49  
% 39.68/5.49  fof(f2,axiom,(
% 39.68/5.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 39.68/5.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.68/5.49  
% 39.68/5.49  fof(f15,plain,(
% 39.68/5.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 39.68/5.49    inference(ennf_transformation,[],[f2])).
% 39.68/5.49  
% 39.68/5.49  fof(f31,plain,(
% 39.68/5.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 39.68/5.49    inference(nnf_transformation,[],[f15])).
% 39.68/5.49  
% 39.68/5.49  fof(f32,plain,(
% 39.68/5.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 39.68/5.49    inference(rectify,[],[f31])).
% 39.68/5.49  
% 39.68/5.49  fof(f33,plain,(
% 39.68/5.49    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 39.68/5.49    introduced(choice_axiom,[])).
% 39.68/5.49  
% 39.68/5.49  fof(f34,plain,(
% 39.68/5.49    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 39.68/5.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f32,f33])).
% 39.68/5.49  
% 39.68/5.49  fof(f48,plain,(
% 39.68/5.49    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 39.68/5.49    inference(cnf_transformation,[],[f34])).
% 39.68/5.49  
% 39.68/5.49  fof(f3,axiom,(
% 39.68/5.49    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 39.68/5.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.68/5.49  
% 39.68/5.49  fof(f16,plain,(
% 39.68/5.49    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 39.68/5.49    inference(ennf_transformation,[],[f3])).
% 39.68/5.49  
% 39.68/5.49  fof(f51,plain,(
% 39.68/5.49    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 39.68/5.49    inference(cnf_transformation,[],[f16])).
% 39.68/5.49  
% 39.68/5.49  fof(f12,conjecture,(
% 39.68/5.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 39.68/5.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.68/5.49  
% 39.68/5.49  fof(f13,negated_conjecture,(
% 39.68/5.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 39.68/5.49    inference(negated_conjecture,[],[f12])).
% 39.68/5.49  
% 39.68/5.49  fof(f14,plain,(
% 39.68/5.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 39.68/5.49    inference(pure_predicate_removal,[],[f13])).
% 39.68/5.49  
% 39.68/5.49  fof(f25,plain,(
% 39.68/5.49    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 39.68/5.49    inference(ennf_transformation,[],[f14])).
% 39.68/5.49  
% 39.68/5.49  fof(f26,plain,(
% 39.68/5.49    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 39.68/5.49    inference(flattening,[],[f25])).
% 39.68/5.49  
% 39.68/5.49  fof(f44,plain,(
% 39.68/5.49    ( ! [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => (~v2_tex_2(sK5,X0) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(sK5))) )),
% 39.68/5.49    introduced(choice_axiom,[])).
% 39.68/5.49  
% 39.68/5.49  fof(f43,plain,(
% 39.68/5.49    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (~v2_tex_2(X1,sK4) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) & v1_xboole_0(X1)) & l1_pre_topc(sK4) & v2_pre_topc(sK4))),
% 39.68/5.49    introduced(choice_axiom,[])).
% 39.68/5.49  
% 39.68/5.49  fof(f45,plain,(
% 39.68/5.49    (~v2_tex_2(sK5,sK4) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) & v1_xboole_0(sK5)) & l1_pre_topc(sK4) & v2_pre_topc(sK4)),
% 39.68/5.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f26,f44,f43])).
% 39.68/5.49  
% 39.68/5.49  fof(f70,plain,(
% 39.68/5.49    v1_xboole_0(sK5)),
% 39.68/5.49    inference(cnf_transformation,[],[f45])).
% 39.68/5.49  
% 39.68/5.49  fof(f46,plain,(
% 39.68/5.49    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 39.68/5.49    inference(cnf_transformation,[],[f30])).
% 39.68/5.49  
% 39.68/5.49  fof(f49,plain,(
% 39.68/5.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 39.68/5.49    inference(cnf_transformation,[],[f34])).
% 39.68/5.49  
% 39.68/5.49  fof(f4,axiom,(
% 39.68/5.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 39.68/5.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.68/5.49  
% 39.68/5.49  fof(f35,plain,(
% 39.68/5.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 39.68/5.49    inference(nnf_transformation,[],[f4])).
% 39.68/5.49  
% 39.68/5.49  fof(f36,plain,(
% 39.68/5.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 39.68/5.49    inference(flattening,[],[f35])).
% 39.68/5.49  
% 39.68/5.49  fof(f52,plain,(
% 39.68/5.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 39.68/5.49    inference(cnf_transformation,[],[f36])).
% 39.68/5.49  
% 39.68/5.49  fof(f74,plain,(
% 39.68/5.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 39.68/5.49    inference(equality_resolution,[],[f52])).
% 39.68/5.49  
% 39.68/5.49  fof(f8,axiom,(
% 39.68/5.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 39.68/5.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.68/5.49  
% 39.68/5.49  fof(f37,plain,(
% 39.68/5.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 39.68/5.49    inference(nnf_transformation,[],[f8])).
% 39.68/5.49  
% 39.68/5.49  fof(f59,plain,(
% 39.68/5.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 39.68/5.49    inference(cnf_transformation,[],[f37])).
% 39.68/5.49  
% 39.68/5.49  fof(f9,axiom,(
% 39.68/5.49    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 39.68/5.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.68/5.49  
% 39.68/5.49  fof(f19,plain,(
% 39.68/5.49    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 39.68/5.49    inference(ennf_transformation,[],[f9])).
% 39.68/5.49  
% 39.68/5.49  fof(f20,plain,(
% 39.68/5.49    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 39.68/5.49    inference(flattening,[],[f19])).
% 39.68/5.49  
% 39.68/5.49  fof(f60,plain,(
% 39.68/5.49    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 39.68/5.49    inference(cnf_transformation,[],[f20])).
% 39.68/5.49  
% 39.68/5.49  fof(f58,plain,(
% 39.68/5.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 39.68/5.49    inference(cnf_transformation,[],[f37])).
% 39.68/5.49  
% 39.68/5.49  fof(f54,plain,(
% 39.68/5.49    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 39.68/5.49    inference(cnf_transformation,[],[f36])).
% 39.68/5.49  
% 39.68/5.49  fof(f71,plain,(
% 39.68/5.49    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))),
% 39.68/5.49    inference(cnf_transformation,[],[f45])).
% 39.68/5.49  
% 39.68/5.49  fof(f72,plain,(
% 39.68/5.49    ~v2_tex_2(sK5,sK4)),
% 39.68/5.49    inference(cnf_transformation,[],[f45])).
% 39.68/5.49  
% 39.68/5.49  fof(f69,plain,(
% 39.68/5.49    l1_pre_topc(sK4)),
% 39.68/5.49    inference(cnf_transformation,[],[f45])).
% 39.68/5.49  
% 39.68/5.49  fof(f68,plain,(
% 39.68/5.49    v2_pre_topc(sK4)),
% 39.68/5.49    inference(cnf_transformation,[],[f45])).
% 39.68/5.49  
% 39.68/5.49  fof(f10,axiom,(
% 39.68/5.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_xboole_0(X1) => v4_pre_topc(X1,X0))))),
% 39.68/5.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.68/5.49  
% 39.68/5.49  fof(f21,plain,(
% 39.68/5.49    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) | ~v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 39.68/5.49    inference(ennf_transformation,[],[f10])).
% 39.68/5.49  
% 39.68/5.49  fof(f22,plain,(
% 39.68/5.49    ! [X0] : (! [X1] : (v4_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 39.68/5.49    inference(flattening,[],[f21])).
% 39.68/5.49  
% 39.68/5.49  fof(f61,plain,(
% 39.68/5.49    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 39.68/5.49    inference(cnf_transformation,[],[f22])).
% 39.68/5.49  
% 39.68/5.49  fof(f5,axiom,(
% 39.68/5.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 39.68/5.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.68/5.49  
% 39.68/5.49  fof(f17,plain,(
% 39.68/5.49    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 39.68/5.49    inference(ennf_transformation,[],[f5])).
% 39.68/5.49  
% 39.68/5.49  fof(f55,plain,(
% 39.68/5.49    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 39.68/5.49    inference(cnf_transformation,[],[f17])).
% 39.68/5.49  
% 39.68/5.49  fof(f6,axiom,(
% 39.68/5.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 39.68/5.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.68/5.49  
% 39.68/5.49  fof(f18,plain,(
% 39.68/5.49    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 39.68/5.49    inference(ennf_transformation,[],[f6])).
% 39.68/5.49  
% 39.68/5.49  fof(f56,plain,(
% 39.68/5.49    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 39.68/5.49    inference(cnf_transformation,[],[f18])).
% 39.68/5.49  
% 39.68/5.49  fof(f67,plain,(
% 39.68/5.49    ( ! [X0,X3,X1] : (v2_tex_2(X1,X0) | k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 39.68/5.49    inference(cnf_transformation,[],[f42])).
% 39.68/5.49  
% 39.68/5.49  cnf(c_0,plain,
% 39.68/5.49      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 39.68/5.49      inference(cnf_transformation,[],[f47]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_1123,plain,
% 39.68/5.49      ( r2_hidden(sK0(X0),X0) = iProver_top
% 39.68/5.49      | v1_xboole_0(X0) = iProver_top ),
% 39.68/5.49      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_11,plain,
% 39.68/5.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 39.68/5.49      inference(cnf_transformation,[],[f57]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_1115,plain,
% 39.68/5.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 39.68/5.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_17,plain,
% 39.68/5.49      ( v2_tex_2(X0,X1)
% 39.68/5.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 39.68/5.49      | r1_tarski(sK2(X1,X0),X0)
% 39.68/5.49      | ~ l1_pre_topc(X1) ),
% 39.68/5.49      inference(cnf_transformation,[],[f66]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_1109,plain,
% 39.68/5.49      ( v2_tex_2(X0,X1) = iProver_top
% 39.68/5.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 39.68/5.49      | r1_tarski(sK2(X1,X0),X0) = iProver_top
% 39.68/5.49      | l1_pre_topc(X1) != iProver_top ),
% 39.68/5.49      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_2869,plain,
% 39.68/5.49      ( v2_tex_2(k1_xboole_0,X0) = iProver_top
% 39.68/5.49      | r1_tarski(sK2(X0,k1_xboole_0),k1_xboole_0) = iProver_top
% 39.68/5.49      | l1_pre_topc(X0) != iProver_top ),
% 39.68/5.49      inference(superposition,[status(thm)],[c_1115,c_1109]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_4,plain,
% 39.68/5.49      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 39.68/5.49      inference(cnf_transformation,[],[f48]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_1119,plain,
% 39.68/5.49      ( r1_tarski(X0,X1) != iProver_top
% 39.68/5.49      | r2_hidden(X2,X0) != iProver_top
% 39.68/5.49      | r2_hidden(X2,X1) = iProver_top ),
% 39.68/5.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_9229,plain,
% 39.68/5.49      ( v2_tex_2(k1_xboole_0,X0) = iProver_top
% 39.68/5.49      | r2_hidden(X1,sK2(X0,k1_xboole_0)) != iProver_top
% 39.68/5.49      | r2_hidden(X1,k1_xboole_0) = iProver_top
% 39.68/5.49      | l1_pre_topc(X0) != iProver_top ),
% 39.68/5.49      inference(superposition,[status(thm)],[c_2869,c_1119]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_51099,plain,
% 39.68/5.49      ( v2_tex_2(k1_xboole_0,X0) = iProver_top
% 39.68/5.49      | r2_hidden(sK0(sK2(X0,k1_xboole_0)),k1_xboole_0) = iProver_top
% 39.68/5.49      | l1_pre_topc(X0) != iProver_top
% 39.68/5.49      | v1_xboole_0(sK2(X0,k1_xboole_0)) = iProver_top ),
% 39.68/5.49      inference(superposition,[status(thm)],[c_1123,c_9229]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_479,plain,
% 39.68/5.49      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 39.68/5.49      theory(equality) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_5,plain,
% 39.68/5.49      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 39.68/5.49      inference(cnf_transformation,[],[f51]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_1475,plain,
% 39.68/5.49      ( ~ v1_xboole_0(X0) | v1_xboole_0(k1_xboole_0) ),
% 39.68/5.49      inference(resolution,[status(thm)],[c_479,c_5]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_24,negated_conjecture,
% 39.68/5.49      ( v1_xboole_0(sK5) ),
% 39.68/5.49      inference(cnf_transformation,[],[f70]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_1485,plain,
% 39.68/5.49      ( v1_xboole_0(k1_xboole_0) ),
% 39.68/5.49      inference(resolution,[status(thm)],[c_1475,c_24]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_1486,plain,
% 39.68/5.49      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 39.68/5.49      inference(predicate_to_equality,[status(thm)],[c_1485]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_3178,plain,
% 39.68/5.49      ( v2_tex_2(k1_xboole_0,X0)
% 39.68/5.49      | r1_tarski(sK2(X0,k1_xboole_0),k1_xboole_0)
% 39.68/5.49      | ~ l1_pre_topc(X0) ),
% 39.68/5.49      inference(resolution,[status(thm)],[c_17,c_11]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_2163,plain,
% 39.68/5.49      ( ~ r1_tarski(X0,X1) | r2_hidden(sK0(X0),X1) | v1_xboole_0(X0) ),
% 39.68/5.49      inference(resolution,[status(thm)],[c_4,c_0]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_1,plain,
% 39.68/5.49      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 39.68/5.49      inference(cnf_transformation,[],[f46]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_2383,plain,
% 39.68/5.49      ( ~ r1_tarski(X0,X1) | ~ v1_xboole_0(X1) | v1_xboole_0(X0) ),
% 39.68/5.49      inference(resolution,[status(thm)],[c_2163,c_1]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_3596,plain,
% 39.68/5.49      ( v2_tex_2(k1_xboole_0,X0)
% 39.68/5.49      | ~ l1_pre_topc(X0)
% 39.68/5.49      | v1_xboole_0(sK2(X0,k1_xboole_0))
% 39.68/5.49      | ~ v1_xboole_0(k1_xboole_0) ),
% 39.68/5.49      inference(resolution,[status(thm)],[c_3178,c_2383]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_3597,plain,
% 39.68/5.49      ( v2_tex_2(k1_xboole_0,X0) = iProver_top
% 39.68/5.49      | l1_pre_topc(X0) != iProver_top
% 39.68/5.49      | v1_xboole_0(sK2(X0,k1_xboole_0)) = iProver_top
% 39.68/5.49      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 39.68/5.49      inference(predicate_to_equality,[status(thm)],[c_3596]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_66034,plain,
% 39.68/5.49      ( v2_tex_2(k1_xboole_0,X0) = iProver_top
% 39.68/5.49      | l1_pre_topc(X0) != iProver_top
% 39.68/5.49      | v1_xboole_0(sK2(X0,k1_xboole_0)) = iProver_top ),
% 39.68/5.49      inference(global_propositional_subsumption,
% 39.68/5.49                [status(thm)],
% 39.68/5.49                [c_51099,c_1486,c_3597]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_1102,plain,
% 39.68/5.49      ( v1_xboole_0(sK5) = iProver_top ),
% 39.68/5.49      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_1118,plain,
% 39.68/5.49      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 39.68/5.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_1460,plain,
% 39.68/5.49      ( sK5 = k1_xboole_0 ),
% 39.68/5.49      inference(superposition,[status(thm)],[c_1102,c_1118]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_1820,plain,
% 39.68/5.49      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 39.68/5.49      inference(demodulation,[status(thm)],[c_1460,c_1102]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_3,plain,
% 39.68/5.49      ( r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 39.68/5.49      inference(cnf_transformation,[],[f49]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_1120,plain,
% 39.68/5.49      ( r1_tarski(X0,X1) = iProver_top
% 39.68/5.49      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 39.68/5.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_8,plain,
% 39.68/5.49      ( r1_tarski(X0,X0) ),
% 39.68/5.49      inference(cnf_transformation,[],[f74]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_1116,plain,
% 39.68/5.49      ( r1_tarski(X0,X0) = iProver_top ),
% 39.68/5.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_12,plain,
% 39.68/5.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 39.68/5.49      inference(cnf_transformation,[],[f59]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_1114,plain,
% 39.68/5.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 39.68/5.49      | r1_tarski(X0,X1) != iProver_top ),
% 39.68/5.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_14,plain,
% 39.68/5.49      ( m1_subset_1(X0,X1)
% 39.68/5.49      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 39.68/5.49      | ~ r2_hidden(X0,X2) ),
% 39.68/5.49      inference(cnf_transformation,[],[f60]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_1112,plain,
% 39.68/5.49      ( m1_subset_1(X0,X1) = iProver_top
% 39.68/5.49      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 39.68/5.49      | r2_hidden(X0,X2) != iProver_top ),
% 39.68/5.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_2823,plain,
% 39.68/5.49      ( m1_subset_1(X0,X1) = iProver_top
% 39.68/5.49      | r1_tarski(X2,X1) != iProver_top
% 39.68/5.49      | r2_hidden(X0,X2) != iProver_top ),
% 39.68/5.49      inference(superposition,[status(thm)],[c_1114,c_1112]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_4054,plain,
% 39.68/5.49      ( m1_subset_1(X0,X1) = iProver_top
% 39.68/5.49      | r2_hidden(X0,X1) != iProver_top ),
% 39.68/5.49      inference(superposition,[status(thm)],[c_1116,c_2823]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_4261,plain,
% 39.68/5.49      ( m1_subset_1(sK1(X0,X1),X0) = iProver_top
% 39.68/5.49      | r1_tarski(X0,X1) = iProver_top ),
% 39.68/5.49      inference(superposition,[status(thm)],[c_1120,c_4054]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_13,plain,
% 39.68/5.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 39.68/5.49      inference(cnf_transformation,[],[f58]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_1113,plain,
% 39.68/5.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 39.68/5.49      | r1_tarski(X0,X1) = iProver_top ),
% 39.68/5.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_5302,plain,
% 39.68/5.49      ( r1_tarski(sK1(k1_zfmisc_1(X0),X1),X0) = iProver_top
% 39.68/5.49      | r1_tarski(k1_zfmisc_1(X0),X1) = iProver_top ),
% 39.68/5.49      inference(superposition,[status(thm)],[c_4261,c_1113]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_6580,plain,
% 39.68/5.49      ( r1_tarski(k1_zfmisc_1(X0),X1) = iProver_top
% 39.68/5.49      | r2_hidden(X2,X0) = iProver_top
% 39.68/5.49      | r2_hidden(X2,sK1(k1_zfmisc_1(X0),X1)) != iProver_top ),
% 39.68/5.49      inference(superposition,[status(thm)],[c_5302,c_1119]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_15029,plain,
% 39.68/5.49      ( r1_tarski(k1_zfmisc_1(X0),X1) = iProver_top
% 39.68/5.49      | r2_hidden(sK0(sK1(k1_zfmisc_1(X0),X1)),X0) = iProver_top
% 39.68/5.49      | v1_xboole_0(sK1(k1_zfmisc_1(X0),X1)) = iProver_top ),
% 39.68/5.49      inference(superposition,[status(thm)],[c_1123,c_6580]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_1122,plain,
% 39.68/5.49      ( r2_hidden(X0,X1) != iProver_top
% 39.68/5.49      | v1_xboole_0(X1) != iProver_top ),
% 39.68/5.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_44884,plain,
% 39.68/5.49      ( r1_tarski(k1_zfmisc_1(X0),X1) = iProver_top
% 39.68/5.49      | v1_xboole_0(X0) != iProver_top
% 39.68/5.49      | v1_xboole_0(sK1(k1_zfmisc_1(X0),X1)) = iProver_top ),
% 39.68/5.49      inference(superposition,[status(thm)],[c_15029,c_1122]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_45135,plain,
% 39.68/5.49      ( sK1(k1_zfmisc_1(X0),X1) = k1_xboole_0
% 39.68/5.49      | r1_tarski(k1_zfmisc_1(X0),X1) = iProver_top
% 39.68/5.49      | v1_xboole_0(X0) != iProver_top ),
% 39.68/5.49      inference(superposition,[status(thm)],[c_44884,c_1118]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_45696,plain,
% 39.68/5.49      ( sK1(k1_zfmisc_1(X0),X1) = k1_xboole_0
% 39.68/5.49      | r2_hidden(X2,X1) = iProver_top
% 39.68/5.49      | r2_hidden(X2,k1_zfmisc_1(X0)) != iProver_top
% 39.68/5.49      | v1_xboole_0(X0) != iProver_top ),
% 39.68/5.49      inference(superposition,[status(thm)],[c_45135,c_1119]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_54748,plain,
% 39.68/5.49      ( sK1(k1_zfmisc_1(X0),X1) = k1_xboole_0
% 39.68/5.49      | r1_tarski(k1_zfmisc_1(X0),X2) = iProver_top
% 39.68/5.49      | r2_hidden(sK1(k1_zfmisc_1(X0),X2),X1) = iProver_top
% 39.68/5.49      | v1_xboole_0(X0) != iProver_top ),
% 39.68/5.49      inference(superposition,[status(thm)],[c_1120,c_45696]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_69611,plain,
% 39.68/5.49      ( sK1(k1_zfmisc_1(X0),X1) = k1_xboole_0
% 39.68/5.49      | r1_tarski(k1_zfmisc_1(X0),X2) = iProver_top
% 39.68/5.49      | v1_xboole_0(X0) != iProver_top
% 39.68/5.49      | v1_xboole_0(X1) != iProver_top ),
% 39.68/5.49      inference(superposition,[status(thm)],[c_54748,c_1122]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_72664,plain,
% 39.68/5.49      ( sK1(k1_zfmisc_1(X0),k1_xboole_0) = k1_xboole_0
% 39.68/5.49      | r1_tarski(k1_zfmisc_1(X0),X1) = iProver_top
% 39.68/5.49      | v1_xboole_0(X0) != iProver_top ),
% 39.68/5.49      inference(superposition,[status(thm)],[c_1820,c_69611]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_6,plain,
% 39.68/5.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 39.68/5.49      inference(cnf_transformation,[],[f54]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_1117,plain,
% 39.68/5.49      ( X0 = X1
% 39.68/5.49      | r1_tarski(X1,X0) != iProver_top
% 39.68/5.49      | r1_tarski(X0,X1) != iProver_top ),
% 39.68/5.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_73004,plain,
% 39.68/5.49      ( sK1(k1_zfmisc_1(X0),k1_xboole_0) = k1_xboole_0
% 39.68/5.49      | k1_zfmisc_1(X0) = X1
% 39.68/5.49      | r1_tarski(X1,k1_zfmisc_1(X0)) != iProver_top
% 39.68/5.49      | v1_xboole_0(X0) != iProver_top ),
% 39.68/5.49      inference(superposition,[status(thm)],[c_72664,c_1117]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_73297,plain,
% 39.68/5.49      ( sK1(k1_zfmisc_1(X0),k1_xboole_0) = k1_xboole_0
% 39.68/5.49      | sK1(k1_zfmisc_1(X1),k1_xboole_0) = k1_xboole_0
% 39.68/5.49      | k1_zfmisc_1(X1) = k1_zfmisc_1(X0)
% 39.68/5.49      | v1_xboole_0(X0) != iProver_top
% 39.68/5.49      | v1_xboole_0(X1) != iProver_top ),
% 39.68/5.49      inference(superposition,[status(thm)],[c_72664,c_73004]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_2032,plain,
% 39.68/5.49      ( r1_tarski(X0,X1) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 39.68/5.49      inference(superposition,[status(thm)],[c_1120,c_1122]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_2349,plain,
% 39.68/5.49      ( X0 = X1
% 39.68/5.49      | r1_tarski(X0,X1) != iProver_top
% 39.68/5.49      | v1_xboole_0(X1) != iProver_top ),
% 39.68/5.49      inference(superposition,[status(thm)],[c_2032,c_1117]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_4028,plain,
% 39.68/5.49      ( X0 = X1
% 39.68/5.49      | v1_xboole_0(X1) != iProver_top
% 39.68/5.49      | v1_xboole_0(X0) != iProver_top ),
% 39.68/5.49      inference(superposition,[status(thm)],[c_2032,c_2349]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_478,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_477,plain,( X0 = X0 ),theory(equality) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_3161,plain,
% 39.68/5.49      ( X0 != X1 | X1 = X0 ),
% 39.68/5.49      inference(resolution,[status(thm)],[c_478,c_477]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_483,plain,
% 39.68/5.49      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 39.68/5.49      theory(equality) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_5844,plain,
% 39.68/5.49      ( X0 != X1 | k1_zfmisc_1(X1) = k1_zfmisc_1(X0) ),
% 39.68/5.49      inference(resolution,[status(thm)],[c_3161,c_483]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_80602,plain,
% 39.68/5.49      ( k1_zfmisc_1(X1) = k1_zfmisc_1(X0)
% 39.68/5.49      | v1_xboole_0(X0) != iProver_top
% 39.68/5.49      | v1_xboole_0(X1) != iProver_top ),
% 39.68/5.49      inference(global_propositional_subsumption,
% 39.68/5.49                [status(thm)],
% 39.68/5.49                [c_73297,c_4028,c_5844]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_80603,plain,
% 39.68/5.49      ( k1_zfmisc_1(X0) = k1_zfmisc_1(X1)
% 39.68/5.49      | v1_xboole_0(X1) != iProver_top
% 39.68/5.49      | v1_xboole_0(X0) != iProver_top ),
% 39.68/5.49      inference(renaming,[status(thm)],[c_80602]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_80609,plain,
% 39.68/5.49      ( k1_zfmisc_1(X0) = k1_zfmisc_1(k1_xboole_0)
% 39.68/5.49      | v1_xboole_0(X0) != iProver_top ),
% 39.68/5.49      inference(superposition,[status(thm)],[c_1820,c_80603]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_4260,plain,
% 39.68/5.49      ( m1_subset_1(sK0(X0),X0) = iProver_top
% 39.68/5.49      | v1_xboole_0(X0) = iProver_top ),
% 39.68/5.49      inference(superposition,[status(thm)],[c_1123,c_4054]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_5117,plain,
% 39.68/5.49      ( r1_tarski(sK0(k1_zfmisc_1(X0)),X0) = iProver_top
% 39.68/5.49      | v1_xboole_0(k1_zfmisc_1(X0)) = iProver_top ),
% 39.68/5.49      inference(superposition,[status(thm)],[c_4260,c_1113]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_5366,plain,
% 39.68/5.49      ( r2_hidden(X0,X1) = iProver_top
% 39.68/5.49      | r2_hidden(X0,sK0(k1_zfmisc_1(X1))) != iProver_top
% 39.68/5.49      | v1_xboole_0(k1_zfmisc_1(X1)) = iProver_top ),
% 39.68/5.49      inference(superposition,[status(thm)],[c_5117,c_1119]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_9583,plain,
% 39.68/5.49      ( r2_hidden(sK0(sK0(k1_zfmisc_1(X0))),X0) = iProver_top
% 39.68/5.49      | v1_xboole_0(k1_zfmisc_1(X0)) = iProver_top
% 39.68/5.49      | v1_xboole_0(sK0(k1_zfmisc_1(X0))) = iProver_top ),
% 39.68/5.49      inference(superposition,[status(thm)],[c_1123,c_5366]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_12073,plain,
% 39.68/5.49      ( v1_xboole_0(X0) != iProver_top
% 39.68/5.49      | v1_xboole_0(k1_zfmisc_1(X0)) = iProver_top
% 39.68/5.49      | v1_xboole_0(sK0(k1_zfmisc_1(X0))) = iProver_top ),
% 39.68/5.49      inference(superposition,[status(thm)],[c_9583,c_1122]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_12379,plain,
% 39.68/5.49      ( sK0(k1_zfmisc_1(X0)) = k1_xboole_0
% 39.68/5.49      | v1_xboole_0(X0) != iProver_top
% 39.68/5.49      | v1_xboole_0(k1_zfmisc_1(X0)) = iProver_top ),
% 39.68/5.49      inference(superposition,[status(thm)],[c_12073,c_1118]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_12709,plain,
% 39.68/5.49      ( k1_zfmisc_1(X0) = k1_xboole_0
% 39.68/5.49      | sK0(k1_zfmisc_1(X0)) = k1_xboole_0
% 39.68/5.49      | v1_xboole_0(X0) != iProver_top ),
% 39.68/5.49      inference(superposition,[status(thm)],[c_12379,c_1118]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_13254,plain,
% 39.68/5.49      ( k1_zfmisc_1(k1_xboole_0) = k1_xboole_0
% 39.68/5.49      | sK0(k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0 ),
% 39.68/5.49      inference(superposition,[status(thm)],[c_1820,c_12709]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_9584,plain,
% 39.68/5.49      ( r1_tarski(sK0(k1_zfmisc_1(X0)),X1) = iProver_top
% 39.68/5.49      | r2_hidden(sK1(sK0(k1_zfmisc_1(X0)),X1),X0) = iProver_top
% 39.68/5.49      | v1_xboole_0(k1_zfmisc_1(X0)) = iProver_top ),
% 39.68/5.49      inference(superposition,[status(thm)],[c_1120,c_5366]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_27064,plain,
% 39.68/5.49      ( k1_zfmisc_1(k1_xboole_0) = k1_xboole_0
% 39.68/5.49      | r1_tarski(sK0(k1_zfmisc_1(k1_xboole_0)),X0) = iProver_top
% 39.68/5.49      | r2_hidden(sK1(k1_xboole_0,X0),k1_xboole_0) = iProver_top
% 39.68/5.49      | v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 39.68/5.49      inference(superposition,[status(thm)],[c_13254,c_9584]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_27393,plain,
% 39.68/5.49      ( k1_zfmisc_1(k1_xboole_0) = k1_xboole_0
% 39.68/5.49      | m1_subset_1(X0,X1) = iProver_top
% 39.68/5.49      | r2_hidden(X0,sK0(k1_zfmisc_1(k1_xboole_0))) != iProver_top
% 39.68/5.49      | r2_hidden(sK1(k1_xboole_0,X1),k1_xboole_0) = iProver_top
% 39.68/5.49      | v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 39.68/5.49      inference(superposition,[status(thm)],[c_27064,c_2823]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_2046,plain,
% 39.68/5.49      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,k1_xboole_0) ),
% 39.68/5.49      inference(resolution,[status(thm)],[c_14,c_11]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_2047,plain,
% 39.68/5.49      ( m1_subset_1(X0,X1) = iProver_top
% 39.68/5.49      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 39.68/5.49      inference(predicate_to_equality,[status(thm)],[c_2046]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_27390,plain,
% 39.68/5.49      ( k1_zfmisc_1(k1_xboole_0) = k1_xboole_0
% 39.68/5.49      | sK0(k1_zfmisc_1(k1_xboole_0)) = X0
% 39.68/5.49      | r1_tarski(X0,sK0(k1_zfmisc_1(k1_xboole_0))) != iProver_top
% 39.68/5.49      | r2_hidden(sK1(k1_xboole_0,X0),k1_xboole_0) = iProver_top
% 39.68/5.49      | v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 39.68/5.49      inference(superposition,[status(thm)],[c_27064,c_1117]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_35947,plain,
% 39.68/5.49      ( k1_zfmisc_1(k1_xboole_0) = k1_xboole_0
% 39.68/5.49      | sK0(k1_zfmisc_1(k1_xboole_0)) = X0
% 39.68/5.49      | r1_tarski(X0,k1_xboole_0) != iProver_top
% 39.68/5.49      | r2_hidden(sK1(k1_xboole_0,X0),k1_xboole_0) = iProver_top
% 39.68/5.49      | v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 39.68/5.49      inference(superposition,[status(thm)],[c_13254,c_27390]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_13298,plain,
% 39.68/5.49      ( k1_zfmisc_1(k1_xboole_0) = k1_xboole_0
% 39.68/5.49      | r2_hidden(sK0(k1_xboole_0),k1_xboole_0) = iProver_top
% 39.68/5.49      | v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 39.68/5.49      | v1_xboole_0(sK0(k1_zfmisc_1(k1_xboole_0))) = iProver_top ),
% 39.68/5.49      inference(superposition,[status(thm)],[c_13254,c_9583]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_1684,plain,
% 39.68/5.49      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 39.68/5.49      inference(superposition,[status(thm)],[c_1115,c_1113]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_2223,plain,
% 39.68/5.49      ( r2_hidden(X0,X1) = iProver_top
% 39.68/5.49      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 39.68/5.49      inference(superposition,[status(thm)],[c_1684,c_1119]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_13518,plain,
% 39.68/5.49      ( k1_zfmisc_1(k1_xboole_0) = k1_xboole_0
% 39.68/5.49      | r2_hidden(sK0(k1_xboole_0),X0) = iProver_top
% 39.68/5.49      | v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 39.68/5.49      | v1_xboole_0(sK0(k1_zfmisc_1(k1_xboole_0))) = iProver_top ),
% 39.68/5.49      inference(superposition,[status(thm)],[c_13298,c_2223]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_13956,plain,
% 39.68/5.49      ( k1_zfmisc_1(k1_xboole_0) = k1_xboole_0
% 39.68/5.49      | v1_xboole_0(X0) != iProver_top
% 39.68/5.49      | v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 39.68/5.49      | v1_xboole_0(sK0(k1_zfmisc_1(k1_xboole_0))) = iProver_top ),
% 39.68/5.49      inference(superposition,[status(thm)],[c_13518,c_1122]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_14009,plain,
% 39.68/5.49      ( k1_zfmisc_1(k1_xboole_0) = k1_xboole_0
% 39.68/5.49      | v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 39.68/5.49      | v1_xboole_0(sK0(k1_zfmisc_1(k1_xboole_0))) = iProver_top ),
% 39.68/5.49      inference(superposition,[status(thm)],[c_1820,c_13956]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_14207,plain,
% 39.68/5.49      ( k1_zfmisc_1(k1_xboole_0) = k1_xboole_0
% 39.68/5.49      | sK0(k1_zfmisc_1(k1_xboole_0)) = X0
% 39.68/5.49      | v1_xboole_0(X0) != iProver_top
% 39.68/5.49      | v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 39.68/5.49      inference(superposition,[status(thm)],[c_14009,c_4028]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_2070,plain,
% 39.68/5.49      ( r1_tarski(X0,X1) | ~ r2_hidden(X0,k1_xboole_0) ),
% 39.68/5.49      inference(resolution,[status(thm)],[c_2046,c_13]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_484,plain,
% 39.68/5.49      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 39.68/5.49      theory(equality) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_3279,plain,
% 39.68/5.49      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X1) | X2 != X0 ),
% 39.68/5.49      inference(resolution,[status(thm)],[c_484,c_477]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_3802,plain,
% 39.68/5.49      ( ~ m1_subset_1(X0,X1)
% 39.68/5.49      | m1_subset_1(k1_xboole_0,X1)
% 39.68/5.49      | ~ v1_xboole_0(X0) ),
% 39.68/5.49      inference(resolution,[status(thm)],[c_3279,c_5]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_23,negated_conjecture,
% 39.68/5.49      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 39.68/5.49      inference(cnf_transformation,[],[f71]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_2050,plain,
% 39.68/5.49      ( m1_subset_1(X0,u1_struct_0(sK4)) | ~ r2_hidden(X0,sK5) ),
% 39.68/5.49      inference(resolution,[status(thm)],[c_14,c_23]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_3830,plain,
% 39.68/5.49      ( m1_subset_1(k1_xboole_0,u1_struct_0(sK4))
% 39.68/5.49      | ~ r2_hidden(X0,sK5)
% 39.68/5.49      | ~ v1_xboole_0(X0) ),
% 39.68/5.49      inference(resolution,[status(thm)],[c_3802,c_2050]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_4088,plain,
% 39.68/5.49      ( m1_subset_1(k1_xboole_0,u1_struct_0(sK4))
% 39.68/5.49      | ~ r1_tarski(X0,sK5)
% 39.68/5.49      | v1_xboole_0(X0)
% 39.68/5.49      | ~ v1_xboole_0(sK0(X0)) ),
% 39.68/5.49      inference(resolution,[status(thm)],[c_3830,c_2163]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_1653,plain,
% 39.68/5.49      ( ~ r1_tarski(X0,sK5) | ~ r1_tarski(sK5,X0) | X0 = sK5 ),
% 39.68/5.49      inference(instantiation,[status(thm)],[c_6]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_1749,plain,
% 39.68/5.49      ( r1_tarski(sK5,X0) | r2_hidden(sK1(sK5,X0),sK5) ),
% 39.68/5.49      inference(instantiation,[status(thm)],[c_3]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_2430,plain,
% 39.68/5.49      ( v1_xboole_0(X0) | ~ v1_xboole_0(sK5) | X0 != sK5 ),
% 39.68/5.49      inference(instantiation,[status(thm)],[c_479]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_5735,plain,
% 39.68/5.49      ( ~ r2_hidden(sK1(sK5,X0),sK5) | ~ v1_xboole_0(sK5) ),
% 39.68/5.49      inference(instantiation,[status(thm)],[c_1]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_15110,plain,
% 39.68/5.49      ( v1_xboole_0(X0) | ~ r1_tarski(X0,sK5) ),
% 39.68/5.49      inference(global_propositional_subsumption,
% 39.68/5.49                [status(thm)],
% 39.68/5.49                [c_4088,c_24,c_1653,c_1749,c_2430,c_5735]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_15111,plain,
% 39.68/5.49      ( ~ r1_tarski(X0,sK5) | v1_xboole_0(X0) ),
% 39.68/5.49      inference(renaming,[status(thm)],[c_15110]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_19514,plain,
% 39.68/5.49      ( ~ r2_hidden(X0,k1_xboole_0) | v1_xboole_0(X0) ),
% 39.68/5.49      inference(resolution,[status(thm)],[c_2070,c_15111]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_19623,plain,
% 39.68/5.49      ( ~ r1_tarski(X0,k1_xboole_0)
% 39.68/5.49      | v1_xboole_0(X0)
% 39.68/5.49      | v1_xboole_0(sK0(X0)) ),
% 39.68/5.49      inference(resolution,[status(thm)],[c_19514,c_2163]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_1445,plain,
% 39.68/5.49      ( r1_tarski(k1_xboole_0,X0) ),
% 39.68/5.49      inference(resolution,[status(thm)],[c_13,c_11]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_1651,plain,
% 39.68/5.49      ( X0 != X1 | X0 = sK5 | sK5 != X1 ),
% 39.68/5.49      inference(instantiation,[status(thm)],[c_478]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_5689,plain,
% 39.68/5.49      ( X0 = sK5 | X0 != k1_xboole_0 | sK5 != k1_xboole_0 ),
% 39.68/5.49      inference(instantiation,[status(thm)],[c_1651]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_11222,plain,
% 39.68/5.49      ( ~ r1_tarski(X0,k1_xboole_0)
% 39.68/5.49      | ~ r1_tarski(k1_xboole_0,X0)
% 39.68/5.49      | X0 = k1_xboole_0 ),
% 39.68/5.49      inference(instantiation,[status(thm)],[c_6]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_21206,plain,
% 39.68/5.49      ( v1_xboole_0(X0) | ~ r1_tarski(X0,k1_xboole_0) ),
% 39.68/5.49      inference(global_propositional_subsumption,
% 39.68/5.49                [status(thm)],
% 39.68/5.49                [c_19623,c_24,c_1445,c_1460,c_2430,c_5689,c_11222]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_21207,plain,
% 39.68/5.49      ( ~ r1_tarski(X0,k1_xboole_0) | v1_xboole_0(X0) ),
% 39.68/5.49      inference(renaming,[status(thm)],[c_21206]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_21208,plain,
% 39.68/5.49      ( r1_tarski(X0,k1_xboole_0) != iProver_top
% 39.68/5.49      | v1_xboole_0(X0) = iProver_top ),
% 39.68/5.49      inference(predicate_to_equality,[status(thm)],[c_21207]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_36031,plain,
% 39.68/5.49      ( r1_tarski(X0,k1_xboole_0) != iProver_top
% 39.68/5.49      | sK0(k1_zfmisc_1(k1_xboole_0)) = X0
% 39.68/5.49      | k1_zfmisc_1(k1_xboole_0) = k1_xboole_0
% 39.68/5.49      | v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 39.68/5.49      inference(global_propositional_subsumption,
% 39.68/5.49                [status(thm)],
% 39.68/5.49                [c_35947,c_14207,c_21208]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_36032,plain,
% 39.68/5.49      ( k1_zfmisc_1(k1_xboole_0) = k1_xboole_0
% 39.68/5.49      | sK0(k1_zfmisc_1(k1_xboole_0)) = X0
% 39.68/5.49      | r1_tarski(X0,k1_xboole_0) != iProver_top
% 39.68/5.49      | v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 39.68/5.49      inference(renaming,[status(thm)],[c_36031]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_36046,plain,
% 39.68/5.49      ( sK2(X0,k1_xboole_0) = sK0(k1_zfmisc_1(k1_xboole_0))
% 39.68/5.49      | k1_zfmisc_1(k1_xboole_0) = k1_xboole_0
% 39.68/5.49      | v2_tex_2(k1_xboole_0,X0) = iProver_top
% 39.68/5.49      | l1_pre_topc(X0) != iProver_top
% 39.68/5.49      | v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 39.68/5.49      inference(superposition,[status(thm)],[c_2869,c_36032]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_22,negated_conjecture,
% 39.68/5.49      ( ~ v2_tex_2(sK5,sK4) ),
% 39.68/5.49      inference(cnf_transformation,[],[f72]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_1104,plain,
% 39.68/5.49      ( v2_tex_2(sK5,sK4) != iProver_top ),
% 39.68/5.49      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_1819,plain,
% 39.68/5.49      ( v2_tex_2(k1_xboole_0,sK4) != iProver_top ),
% 39.68/5.49      inference(demodulation,[status(thm)],[c_1460,c_1104]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_37920,plain,
% 39.68/5.49      ( sK2(sK4,k1_xboole_0) = sK0(k1_zfmisc_1(k1_xboole_0))
% 39.68/5.49      | k1_zfmisc_1(k1_xboole_0) = k1_xboole_0
% 39.68/5.49      | l1_pre_topc(sK4) != iProver_top
% 39.68/5.49      | v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 39.68/5.49      inference(superposition,[status(thm)],[c_36046,c_1819]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_25,negated_conjecture,
% 39.68/5.49      ( l1_pre_topc(sK4) ),
% 39.68/5.49      inference(cnf_transformation,[],[f69]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_28,plain,
% 39.68/5.49      ( l1_pre_topc(sK4) = iProver_top ),
% 39.68/5.49      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_39394,plain,
% 39.68/5.49      ( k1_zfmisc_1(k1_xboole_0) = k1_xboole_0
% 39.68/5.49      | sK2(sK4,k1_xboole_0) = sK0(k1_zfmisc_1(k1_xboole_0))
% 39.68/5.49      | v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 39.68/5.49      inference(global_propositional_subsumption,
% 39.68/5.49                [status(thm)],
% 39.68/5.49                [c_37920,c_28]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_39395,plain,
% 39.68/5.49      ( sK2(sK4,k1_xboole_0) = sK0(k1_zfmisc_1(k1_xboole_0))
% 39.68/5.49      | k1_zfmisc_1(k1_xboole_0) = k1_xboole_0
% 39.68/5.49      | v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 39.68/5.49      inference(renaming,[status(thm)],[c_39394]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_39408,plain,
% 39.68/5.49      ( sK2(sK4,k1_xboole_0) = sK0(k1_zfmisc_1(k1_xboole_0))
% 39.68/5.49      | k1_zfmisc_1(k1_xboole_0) = k1_xboole_0 ),
% 39.68/5.49      inference(superposition,[status(thm)],[c_39395,c_1118]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_39634,plain,
% 39.68/5.49      ( k1_zfmisc_1(k1_xboole_0) = k1_xboole_0
% 39.68/5.49      | v2_tex_2(k1_xboole_0,sK4) = iProver_top
% 39.68/5.49      | r1_tarski(sK0(k1_zfmisc_1(k1_xboole_0)),k1_xboole_0) = iProver_top
% 39.68/5.49      | l1_pre_topc(sK4) != iProver_top ),
% 39.68/5.49      inference(superposition,[status(thm)],[c_39408,c_2869]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_39775,plain,
% 39.68/5.49      ( r1_tarski(sK0(k1_zfmisc_1(k1_xboole_0)),k1_xboole_0) = iProver_top
% 39.68/5.49      | k1_zfmisc_1(k1_xboole_0) = k1_xboole_0 ),
% 39.68/5.49      inference(global_propositional_subsumption,
% 39.68/5.49                [status(thm)],
% 39.68/5.49                [c_39634,c_28,c_1819]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_39776,plain,
% 39.68/5.49      ( k1_zfmisc_1(k1_xboole_0) = k1_xboole_0
% 39.68/5.49      | r1_tarski(sK0(k1_zfmisc_1(k1_xboole_0)),k1_xboole_0) = iProver_top ),
% 39.68/5.49      inference(renaming,[status(thm)],[c_39775]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_39783,plain,
% 39.68/5.49      ( k1_zfmisc_1(k1_xboole_0) = k1_xboole_0
% 39.68/5.49      | r2_hidden(X0,sK0(k1_zfmisc_1(k1_xboole_0))) != iProver_top
% 39.68/5.49      | r2_hidden(X0,k1_xboole_0) = iProver_top ),
% 39.68/5.49      inference(superposition,[status(thm)],[c_39776,c_1119]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_41315,plain,
% 39.68/5.49      ( k1_zfmisc_1(k1_xboole_0) = k1_xboole_0
% 39.68/5.49      | m1_subset_1(X0,X1) = iProver_top
% 39.68/5.49      | r2_hidden(X0,sK0(k1_zfmisc_1(k1_xboole_0))) != iProver_top ),
% 39.68/5.49      inference(global_propositional_subsumption,
% 39.68/5.49                [status(thm)],
% 39.68/5.49                [c_27393,c_2047,c_39783]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_41325,plain,
% 39.68/5.49      ( k1_zfmisc_1(k1_xboole_0) = k1_xboole_0
% 39.68/5.49      | m1_subset_1(sK1(sK0(k1_zfmisc_1(k1_xboole_0)),X0),X1) = iProver_top
% 39.68/5.49      | r1_tarski(sK0(k1_zfmisc_1(k1_xboole_0)),X0) = iProver_top ),
% 39.68/5.49      inference(superposition,[status(thm)],[c_1120,c_41315]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_43380,plain,
% 39.68/5.49      ( k1_zfmisc_1(k1_xboole_0) = k1_xboole_0
% 39.68/5.49      | m1_subset_1(sK1(k1_xboole_0,X0),X1) = iProver_top
% 39.68/5.49      | r1_tarski(sK0(k1_zfmisc_1(k1_xboole_0)),X0) = iProver_top ),
% 39.68/5.49      inference(superposition,[status(thm)],[c_13254,c_41325]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_41618,plain,
% 39.68/5.49      ( k1_zfmisc_1(k1_xboole_0) = k1_xboole_0
% 39.68/5.49      | r1_tarski(sK0(k1_zfmisc_1(k1_xboole_0)),X0) = iProver_top
% 39.68/5.49      | r2_hidden(sK1(sK0(k1_zfmisc_1(k1_xboole_0)),X0),k1_xboole_0) = iProver_top ),
% 39.68/5.49      inference(superposition,[status(thm)],[c_1120,c_39783]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_43564,plain,
% 39.68/5.49      ( k1_zfmisc_1(k1_xboole_0) = k1_xboole_0
% 39.68/5.49      | r1_tarski(sK0(k1_zfmisc_1(k1_xboole_0)),X0) = iProver_top
% 39.68/5.49      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 39.68/5.49      inference(superposition,[status(thm)],[c_41618,c_1122]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_43960,plain,
% 39.68/5.49      ( k1_zfmisc_1(k1_xboole_0) = k1_xboole_0
% 39.68/5.49      | r1_tarski(sK0(k1_zfmisc_1(k1_xboole_0)),X0) = iProver_top ),
% 39.68/5.49      inference(global_propositional_subsumption,
% 39.68/5.49                [status(thm)],
% 39.68/5.49                [c_43380,c_1486,c_43564]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_5367,plain,
% 39.68/5.49      ( sK0(k1_zfmisc_1(X0)) = X0
% 39.68/5.49      | r1_tarski(X0,sK0(k1_zfmisc_1(X0))) != iProver_top
% 39.68/5.49      | v1_xboole_0(k1_zfmisc_1(X0)) = iProver_top ),
% 39.68/5.49      inference(superposition,[status(thm)],[c_5117,c_1117]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_43984,plain,
% 39.68/5.49      ( k1_zfmisc_1(k1_xboole_0) = k1_xboole_0
% 39.68/5.49      | sK0(k1_zfmisc_1(sK0(k1_zfmisc_1(k1_xboole_0)))) = sK0(k1_zfmisc_1(k1_xboole_0))
% 39.68/5.49      | v1_xboole_0(k1_zfmisc_1(sK0(k1_zfmisc_1(k1_xboole_0)))) = iProver_top ),
% 39.68/5.49      inference(superposition,[status(thm)],[c_43960,c_5367]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_46450,plain,
% 39.68/5.49      ( k1_zfmisc_1(sK0(k1_zfmisc_1(k1_xboole_0))) = k1_xboole_0
% 39.68/5.49      | k1_zfmisc_1(k1_xboole_0) = k1_xboole_0
% 39.68/5.49      | sK0(k1_zfmisc_1(sK0(k1_zfmisc_1(k1_xboole_0)))) = sK0(k1_zfmisc_1(k1_xboole_0)) ),
% 39.68/5.49      inference(superposition,[status(thm)],[c_43984,c_1118]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_26,negated_conjecture,
% 39.68/5.49      ( v2_pre_topc(sK4) ),
% 39.68/5.49      inference(cnf_transformation,[],[f68]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_27,plain,
% 39.68/5.49      ( v2_pre_topc(sK4) = iProver_top ),
% 39.68/5.49      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_15,plain,
% 39.68/5.49      ( v4_pre_topc(X0,X1)
% 39.68/5.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 39.68/5.49      | ~ v2_pre_topc(X1)
% 39.68/5.49      | ~ l1_pre_topc(X1)
% 39.68/5.49      | ~ v1_xboole_0(X0) ),
% 39.68/5.49      inference(cnf_transformation,[],[f61]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_1359,plain,
% 39.68/5.49      ( v4_pre_topc(k1_xboole_0,X0)
% 39.68/5.49      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
% 39.68/5.49      | ~ v2_pre_topc(X0)
% 39.68/5.49      | ~ l1_pre_topc(X0)
% 39.68/5.49      | ~ v1_xboole_0(k1_xboole_0) ),
% 39.68/5.49      inference(instantiation,[status(thm)],[c_15]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_1361,plain,
% 39.68/5.49      ( v4_pre_topc(k1_xboole_0,X0) = iProver_top
% 39.68/5.49      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 39.68/5.49      | v2_pre_topc(X0) != iProver_top
% 39.68/5.49      | l1_pre_topc(X0) != iProver_top
% 39.68/5.49      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 39.68/5.49      inference(predicate_to_equality,[status(thm)],[c_1359]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_1363,plain,
% 39.68/5.49      ( v4_pre_topc(k1_xboole_0,sK4) = iProver_top
% 39.68/5.49      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 39.68/5.49      | v2_pre_topc(sK4) != iProver_top
% 39.68/5.49      | l1_pre_topc(sK4) != iProver_top
% 39.68/5.49      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 39.68/5.49      inference(instantiation,[status(thm)],[c_1361]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_1360,plain,
% 39.68/5.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) ),
% 39.68/5.49      inference(instantiation,[status(thm)],[c_11]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_1365,plain,
% 39.68/5.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top ),
% 39.68/5.49      inference(predicate_to_equality,[status(thm)],[c_1360]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_1367,plain,
% 39.68/5.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 39.68/5.49      inference(instantiation,[status(thm)],[c_1365]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_9,plain,
% 39.68/5.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 39.68/5.49      | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 39.68/5.49      inference(cnf_transformation,[],[f55]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_181,plain,
% 39.68/5.49      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 39.68/5.49      inference(prop_impl,[status(thm)],[c_12]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_182,plain,
% 39.68/5.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 39.68/5.49      inference(renaming,[status(thm)],[c_181]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_226,plain,
% 39.68/5.49      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
% 39.68/5.49      | ~ r1_tarski(X2,X0) ),
% 39.68/5.49      inference(bin_hyper_res,[status(thm)],[c_9,c_182]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_1099,plain,
% 39.68/5.49      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) = iProver_top
% 39.68/5.49      | r1_tarski(X2,X0) != iProver_top ),
% 39.68/5.49      inference(predicate_to_equality,[status(thm)],[c_226]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_1686,plain,
% 39.68/5.49      ( r1_tarski(X0,X1) != iProver_top
% 39.68/5.49      | r1_tarski(k9_subset_1(X1,X2,X0),X1) = iProver_top ),
% 39.68/5.49      inference(superposition,[status(thm)],[c_1099,c_1113]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_2111,plain,
% 39.68/5.49      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 39.68/5.49      inference(superposition,[status(thm)],[c_1684,c_1117]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_3355,plain,
% 39.68/5.49      ( k9_subset_1(k1_xboole_0,X0,X1) = k1_xboole_0
% 39.68/5.49      | r1_tarski(X1,k1_xboole_0) != iProver_top ),
% 39.68/5.49      inference(superposition,[status(thm)],[c_1686,c_2111]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_3408,plain,
% 39.68/5.49      ( k9_subset_1(k1_xboole_0,X0,k1_xboole_0) = k1_xboole_0 ),
% 39.68/5.49      inference(superposition,[status(thm)],[c_1684,c_3355]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_10,plain,
% 39.68/5.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 39.68/5.49      | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 39.68/5.49      inference(cnf_transformation,[],[f56]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_227,plain,
% 39.68/5.49      ( ~ r1_tarski(X0,X1) | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 39.68/5.49      inference(bin_hyper_res,[status(thm)],[c_10,c_182]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_1098,plain,
% 39.68/5.49      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
% 39.68/5.49      | r1_tarski(X2,X0) != iProver_top ),
% 39.68/5.49      inference(predicate_to_equality,[status(thm)],[c_227]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_2615,plain,
% 39.68/5.49      ( k9_subset_1(X0,X1,X0) = k3_xboole_0(X1,X0) ),
% 39.68/5.49      inference(superposition,[status(thm)],[c_1116,c_1098]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_3501,plain,
% 39.68/5.49      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 39.68/5.49      inference(superposition,[status(thm)],[c_3408,c_2615]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_2616,plain,
% 39.68/5.49      ( k9_subset_1(X0,X1,k1_xboole_0) = k3_xboole_0(X1,k1_xboole_0) ),
% 39.68/5.49      inference(superposition,[status(thm)],[c_1684,c_1098]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_3509,plain,
% 39.68/5.49      ( k9_subset_1(X0,X1,k1_xboole_0) = k1_xboole_0 ),
% 39.68/5.49      inference(demodulation,[status(thm)],[c_3501,c_2616]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_16,plain,
% 39.68/5.49      ( v2_tex_2(X0,X1)
% 39.68/5.49      | ~ v4_pre_topc(X2,X1)
% 39.68/5.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 39.68/5.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 39.68/5.49      | ~ l1_pre_topc(X1)
% 39.68/5.49      | k9_subset_1(u1_struct_0(X1),X0,X2) != sK2(X1,X0) ),
% 39.68/5.49      inference(cnf_transformation,[],[f67]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_1110,plain,
% 39.68/5.49      ( k9_subset_1(u1_struct_0(X0),X1,X2) != sK2(X0,X1)
% 39.68/5.49      | v2_tex_2(X1,X0) = iProver_top
% 39.68/5.49      | v4_pre_topc(X2,X0) != iProver_top
% 39.68/5.49      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 39.68/5.49      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 39.68/5.49      | l1_pre_topc(X0) != iProver_top ),
% 39.68/5.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_3760,plain,
% 39.68/5.49      ( sK2(X0,X1) != k1_xboole_0
% 39.68/5.49      | v2_tex_2(X1,X0) = iProver_top
% 39.68/5.49      | v4_pre_topc(k1_xboole_0,X0) != iProver_top
% 39.68/5.49      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 39.68/5.49      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 39.68/5.49      | l1_pre_topc(X0) != iProver_top ),
% 39.68/5.49      inference(superposition,[status(thm)],[c_3509,c_1110]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_48433,plain,
% 39.68/5.49      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 39.68/5.49      | v4_pre_topc(k1_xboole_0,X0) != iProver_top
% 39.68/5.49      | v2_tex_2(X1,X0) = iProver_top
% 39.68/5.49      | sK2(X0,X1) != k1_xboole_0
% 39.68/5.49      | l1_pre_topc(X0) != iProver_top ),
% 39.68/5.49      inference(global_propositional_subsumption,
% 39.68/5.49                [status(thm)],
% 39.68/5.49                [c_3760,c_1365]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_48434,plain,
% 39.68/5.49      ( sK2(X0,X1) != k1_xboole_0
% 39.68/5.49      | v2_tex_2(X1,X0) = iProver_top
% 39.68/5.49      | v4_pre_topc(k1_xboole_0,X0) != iProver_top
% 39.68/5.49      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 39.68/5.49      | l1_pre_topc(X0) != iProver_top ),
% 39.68/5.49      inference(renaming,[status(thm)],[c_48433]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_48444,plain,
% 39.68/5.49      ( k1_zfmisc_1(k1_xboole_0) = k1_xboole_0
% 39.68/5.49      | sK0(k1_zfmisc_1(k1_xboole_0)) != k1_xboole_0
% 39.68/5.49      | v2_tex_2(k1_xboole_0,sK4) = iProver_top
% 39.68/5.49      | v4_pre_topc(k1_xboole_0,sK4) != iProver_top
% 39.68/5.49      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 39.68/5.49      | l1_pre_topc(sK4) != iProver_top ),
% 39.68/5.49      inference(superposition,[status(thm)],[c_39408,c_48434]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_48766,plain,
% 39.68/5.49      ( k1_zfmisc_1(k1_xboole_0) = k1_xboole_0 ),
% 39.68/5.49      inference(global_propositional_subsumption,
% 39.68/5.49                [status(thm)],
% 39.68/5.49                [c_46450,c_27,c_28,c_1363,c_1367,c_1486,c_1819,c_13254,
% 39.68/5.49                 c_48444]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_80722,plain,
% 39.68/5.49      ( k1_zfmisc_1(X0) = k1_xboole_0 | v1_xboole_0(X0) != iProver_top ),
% 39.68/5.49      inference(light_normalisation,[status(thm)],[c_80609,c_48766]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_81087,plain,
% 39.68/5.49      ( k1_zfmisc_1(sK2(X0,k1_xboole_0)) = k1_xboole_0
% 39.68/5.49      | v2_tex_2(k1_xboole_0,X0) = iProver_top
% 39.68/5.49      | l1_pre_topc(X0) != iProver_top ),
% 39.68/5.49      inference(superposition,[status(thm)],[c_66034,c_80722]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_117223,plain,
% 39.68/5.49      ( k1_zfmisc_1(sK2(sK4,k1_xboole_0)) = k1_xboole_0
% 39.68/5.49      | l1_pre_topc(sK4) != iProver_top ),
% 39.68/5.49      inference(superposition,[status(thm)],[c_81087,c_1819]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_81180,plain,
% 39.68/5.49      ( k1_zfmisc_1(sK2(sK4,k1_xboole_0)) = k1_xboole_0
% 39.68/5.49      | v2_tex_2(k1_xboole_0,sK4) = iProver_top
% 39.68/5.49      | l1_pre_topc(sK4) != iProver_top ),
% 39.68/5.49      inference(instantiation,[status(thm)],[c_81087]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_117386,plain,
% 39.68/5.49      ( k1_zfmisc_1(sK2(sK4,k1_xboole_0)) = k1_xboole_0 ),
% 39.68/5.49      inference(global_propositional_subsumption,
% 39.68/5.49                [status(thm)],
% 39.68/5.49                [c_117223,c_28,c_1819,c_81180]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_6582,plain,
% 39.68/5.49      ( k9_subset_1(X0,X1,sK1(k1_zfmisc_1(X0),X2)) = k3_xboole_0(X1,sK1(k1_zfmisc_1(X0),X2))
% 39.68/5.49      | r1_tarski(k1_zfmisc_1(X0),X2) = iProver_top ),
% 39.68/5.49      inference(superposition,[status(thm)],[c_5302,c_1098]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_127445,plain,
% 39.68/5.49      ( k9_subset_1(X0,X1,sK1(k1_zfmisc_1(X0),X2)) = k3_xboole_0(X1,sK1(k1_zfmisc_1(X0),X2))
% 39.68/5.49      | r2_hidden(X3,X2) = iProver_top
% 39.68/5.49      | r2_hidden(X3,k1_zfmisc_1(X0)) != iProver_top ),
% 39.68/5.49      inference(superposition,[status(thm)],[c_6582,c_1119]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_128446,plain,
% 39.68/5.49      ( k9_subset_1(X0,X1,sK1(k1_zfmisc_1(X0),X2)) = k3_xboole_0(X1,sK1(k1_zfmisc_1(X0),X2))
% 39.68/5.49      | r1_tarski(k1_zfmisc_1(X0),X3) = iProver_top
% 39.68/5.49      | r2_hidden(sK1(k1_zfmisc_1(X0),X3),X2) = iProver_top ),
% 39.68/5.49      inference(superposition,[status(thm)],[c_1120,c_127445]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_134129,plain,
% 39.68/5.49      ( k9_subset_1(X0,X1,sK1(k1_zfmisc_1(X0),X2)) = k3_xboole_0(X1,sK1(k1_zfmisc_1(X0),X2))
% 39.68/5.49      | r1_tarski(k1_zfmisc_1(X0),X3) = iProver_top
% 39.68/5.49      | v1_xboole_0(X2) != iProver_top ),
% 39.68/5.49      inference(superposition,[status(thm)],[c_128446,c_1122]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_142051,plain,
% 39.68/5.49      ( k9_subset_1(X0,X1,sK1(k1_zfmisc_1(X0),k1_xboole_0)) = k3_xboole_0(X1,sK1(k1_zfmisc_1(X0),k1_xboole_0))
% 39.68/5.49      | r1_tarski(k1_zfmisc_1(X0),X2) = iProver_top ),
% 39.68/5.49      inference(superposition,[status(thm)],[c_1820,c_134129]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_51100,plain,
% 39.68/5.49      ( v2_tex_2(k1_xboole_0,X0) = iProver_top
% 39.68/5.49      | r1_tarski(sK2(X0,k1_xboole_0),X1) = iProver_top
% 39.68/5.49      | r2_hidden(sK1(sK2(X0,k1_xboole_0),X1),k1_xboole_0) = iProver_top
% 39.68/5.49      | l1_pre_topc(X0) != iProver_top ),
% 39.68/5.49      inference(superposition,[status(thm)],[c_1120,c_9229]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_2165,plain,
% 39.68/5.49      ( ~ r1_tarski(X0,X1)
% 39.68/5.49      | r1_tarski(X0,X2)
% 39.68/5.49      | r2_hidden(sK1(X0,X2),X1) ),
% 39.68/5.49      inference(resolution,[status(thm)],[c_4,c_3]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_5854,plain,
% 39.68/5.49      ( ~ r1_tarski(X0,X1) | r1_tarski(X0,X2) | ~ v1_xboole_0(X1) ),
% 39.68/5.49      inference(resolution,[status(thm)],[c_2165,c_1]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_24631,plain,
% 39.68/5.49      ( v2_tex_2(k1_xboole_0,X0)
% 39.68/5.49      | r1_tarski(sK2(X0,k1_xboole_0),X1)
% 39.68/5.49      | ~ l1_pre_topc(X0)
% 39.68/5.49      | ~ v1_xboole_0(k1_xboole_0) ),
% 39.68/5.49      inference(resolution,[status(thm)],[c_5854,c_3178]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_24632,plain,
% 39.68/5.49      ( v2_tex_2(k1_xboole_0,X0) = iProver_top
% 39.68/5.49      | r1_tarski(sK2(X0,k1_xboole_0),X1) = iProver_top
% 39.68/5.49      | l1_pre_topc(X0) != iProver_top
% 39.68/5.49      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 39.68/5.49      inference(predicate_to_equality,[status(thm)],[c_24631]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_86163,plain,
% 39.68/5.49      ( r1_tarski(sK2(X0,k1_xboole_0),X1) = iProver_top
% 39.68/5.49      | v2_tex_2(k1_xboole_0,X0) = iProver_top
% 39.68/5.49      | l1_pre_topc(X0) != iProver_top ),
% 39.68/5.49      inference(global_propositional_subsumption,
% 39.68/5.49                [status(thm)],
% 39.68/5.49                [c_51100,c_1486,c_24632]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_86164,plain,
% 39.68/5.49      ( v2_tex_2(k1_xboole_0,X0) = iProver_top
% 39.68/5.49      | r1_tarski(sK2(X0,k1_xboole_0),X1) = iProver_top
% 39.68/5.49      | l1_pre_topc(X0) != iProver_top ),
% 39.68/5.49      inference(renaming,[status(thm)],[c_86163]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_86174,plain,
% 39.68/5.49      ( sK2(X0,k1_xboole_0) = X1
% 39.68/5.49      | v2_tex_2(k1_xboole_0,X0) = iProver_top
% 39.68/5.49      | r1_tarski(X1,sK2(X0,k1_xboole_0)) != iProver_top
% 39.68/5.49      | l1_pre_topc(X0) != iProver_top ),
% 39.68/5.49      inference(superposition,[status(thm)],[c_86164,c_1117]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_143701,plain,
% 39.68/5.49      ( k9_subset_1(X0,X1,sK1(k1_zfmisc_1(X0),k1_xboole_0)) = k3_xboole_0(X1,sK1(k1_zfmisc_1(X0),k1_xboole_0))
% 39.68/5.49      | sK2(X2,k1_xboole_0) = k1_zfmisc_1(X0)
% 39.68/5.49      | v2_tex_2(k1_xboole_0,X2) = iProver_top
% 39.68/5.49      | l1_pre_topc(X2) != iProver_top ),
% 39.68/5.49      inference(superposition,[status(thm)],[c_142051,c_86174]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_194287,plain,
% 39.68/5.49      ( k9_subset_1(X0,X1,sK1(k1_zfmisc_1(X0),k1_xboole_0)) = k3_xboole_0(X1,sK1(k1_zfmisc_1(X0),k1_xboole_0))
% 39.68/5.49      | sK2(sK4,k1_xboole_0) = k1_zfmisc_1(X0)
% 39.68/5.49      | l1_pre_topc(sK4) != iProver_top ),
% 39.68/5.49      inference(superposition,[status(thm)],[c_143701,c_1819]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_194305,plain,
% 39.68/5.49      ( ~ l1_pre_topc(sK4)
% 39.68/5.49      | k9_subset_1(X0,X1,sK1(k1_zfmisc_1(X0),k1_xboole_0)) = k3_xboole_0(X1,sK1(k1_zfmisc_1(X0),k1_xboole_0))
% 39.68/5.49      | sK2(sK4,k1_xboole_0) = k1_zfmisc_1(X0) ),
% 39.68/5.49      inference(predicate_to_equality_rev,[status(thm)],[c_194287]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_194528,plain,
% 39.68/5.49      ( sK2(sK4,k1_xboole_0) = k1_zfmisc_1(X0)
% 39.68/5.49      | k9_subset_1(X0,X1,sK1(k1_zfmisc_1(X0),k1_xboole_0)) = k3_xboole_0(X1,sK1(k1_zfmisc_1(X0),k1_xboole_0)) ),
% 39.68/5.49      inference(global_propositional_subsumption,
% 39.68/5.49                [status(thm)],
% 39.68/5.49                [c_194287,c_25,c_194305]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_194529,plain,
% 39.68/5.49      ( k9_subset_1(X0,X1,sK1(k1_zfmisc_1(X0),k1_xboole_0)) = k3_xboole_0(X1,sK1(k1_zfmisc_1(X0),k1_xboole_0))
% 39.68/5.49      | sK2(sK4,k1_xboole_0) = k1_zfmisc_1(X0) ),
% 39.68/5.49      inference(renaming,[status(thm)],[c_194528]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_194534,plain,
% 39.68/5.49      ( k3_xboole_0(X0,sK1(k1_zfmisc_1(sK2(sK4,k1_xboole_0)),k1_xboole_0)) = k9_subset_1(sK2(sK4,k1_xboole_0),X0,sK1(k1_xboole_0,k1_xboole_0))
% 39.68/5.49      | k1_zfmisc_1(sK2(sK4,k1_xboole_0)) = sK2(sK4,k1_xboole_0) ),
% 39.68/5.49      inference(superposition,[status(thm)],[c_117386,c_194529]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_194835,plain,
% 39.68/5.49      ( k9_subset_1(sK2(sK4,k1_xboole_0),X0,sK1(k1_xboole_0,k1_xboole_0)) = k3_xboole_0(X0,sK1(k1_xboole_0,k1_xboole_0))
% 39.68/5.49      | sK2(sK4,k1_xboole_0) = k1_xboole_0 ),
% 39.68/5.49      inference(light_normalisation,[status(thm)],[c_194534,c_117386]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_1103,plain,
% 39.68/5.49      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 39.68/5.49      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_1685,plain,
% 39.68/5.49      ( r1_tarski(sK5,u1_struct_0(sK4)) = iProver_top ),
% 39.68/5.49      inference(superposition,[status(thm)],[c_1103,c_1113]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_1885,plain,
% 39.68/5.49      ( r1_tarski(k1_xboole_0,u1_struct_0(sK4)) = iProver_top ),
% 39.68/5.49      inference(light_normalisation,[status(thm)],[c_1685,c_1460]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_2868,plain,
% 39.68/5.49      ( v2_tex_2(X0,X1) = iProver_top
% 39.68/5.49      | r1_tarski(X0,u1_struct_0(X1)) != iProver_top
% 39.68/5.49      | r1_tarski(sK2(X1,X0),X0) = iProver_top
% 39.68/5.49      | l1_pre_topc(X1) != iProver_top ),
% 39.68/5.49      inference(superposition,[status(thm)],[c_1114,c_1109]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_9112,plain,
% 39.68/5.49      ( sK2(X0,k1_xboole_0) = k1_xboole_0
% 39.68/5.49      | v2_tex_2(k1_xboole_0,X0) = iProver_top
% 39.68/5.49      | r1_tarski(k1_xboole_0,u1_struct_0(X0)) != iProver_top
% 39.68/5.49      | l1_pre_topc(X0) != iProver_top ),
% 39.68/5.49      inference(superposition,[status(thm)],[c_2868,c_2111]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_9216,plain,
% 39.68/5.49      ( sK2(sK4,k1_xboole_0) = k1_xboole_0
% 39.68/5.49      | v2_tex_2(k1_xboole_0,sK4) = iProver_top
% 39.68/5.49      | r1_tarski(k1_xboole_0,u1_struct_0(sK4)) != iProver_top
% 39.68/5.49      | l1_pre_topc(sK4) != iProver_top ),
% 39.68/5.49      inference(instantiation,[status(thm)],[c_9112]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_194927,plain,
% 39.68/5.49      ( sK2(sK4,k1_xboole_0) = k1_xboole_0 ),
% 39.68/5.49      inference(global_propositional_subsumption,
% 39.68/5.49                [status(thm)],
% 39.68/5.49                [c_194835,c_28,c_1819,c_1885,c_9216]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(c_195017,plain,
% 39.68/5.49      ( v2_tex_2(k1_xboole_0,sK4) = iProver_top
% 39.68/5.49      | v4_pre_topc(k1_xboole_0,sK4) != iProver_top
% 39.68/5.49      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 39.68/5.49      | l1_pre_topc(sK4) != iProver_top ),
% 39.68/5.49      inference(superposition,[status(thm)],[c_194927,c_48434]) ).
% 39.68/5.49  
% 39.68/5.49  cnf(contradiction,plain,
% 39.68/5.49      ( $false ),
% 39.68/5.49      inference(minisat,
% 39.68/5.49                [status(thm)],
% 39.68/5.49                [c_195017,c_1819,c_1486,c_1367,c_1363,c_28,c_27]) ).
% 39.68/5.49  
% 39.68/5.49  
% 39.68/5.49  % SZS output end CNFRefutation for theBenchmark.p
% 39.68/5.49  
% 39.68/5.49  ------                               Statistics
% 39.68/5.49  
% 39.68/5.49  ------ Selected
% 39.68/5.49  
% 39.68/5.49  total_time:                             4.721
% 39.68/5.49  
%------------------------------------------------------------------------------
