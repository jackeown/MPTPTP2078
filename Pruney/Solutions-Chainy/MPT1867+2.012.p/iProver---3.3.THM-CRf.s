%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:26:08 EST 2020

% Result     : Theorem 3.76s
% Output     : CNFRefutation 3.76s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 395 expanded)
%              Number of clauses        :   80 ( 131 expanded)
%              Number of leaves         :   18 (  89 expanded)
%              Depth                    :   19
%              Number of atoms          :  448 (1609 expanded)
%              Number of equality atoms :  132 ( 223 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f27,f44,f43])).

fof(f70,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f45])).

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
    inference(ennf_transformation,[],[f11])).

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

fof(f38,plain,(
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

fof(f39,plain,(
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
    inference(rectify,[],[f38])).

fof(f41,plain,(
    ! [X4,X1,X0] :
      ( ? [X5] :
          ( k9_subset_1(u1_struct_0(X0),X1,X5) = X4
          & v3_pre_topc(X5,X0)
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X0),X1,sK3(X0,X1,X4)) = X4
        & v3_pre_topc(sK3(X0,X1,X4),X0)
        & m1_subset_1(sK3(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
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

fof(f42,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f39,f41,f40])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | r1_tarski(sK2(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f68,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f45])).

fof(f71,plain,(
    ~ v2_tex_2(sK5,sK4) ),
    inference(cnf_transformation,[],[f45])).

fof(f69,plain,(
    v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f45])).

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

fof(f32,plain,(
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

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f32])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f33,f34])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f36])).

fof(f54,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).

fof(f47,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f31])).

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

fof(f66,plain,(
    ! [X0,X3,X1] :
      ( v2_tex_2(X1,X0)
      | k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1)
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f73,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f52])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v3_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f67,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2022,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_16,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(sK2(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_24,negated_conjecture,
    ( l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_563,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(sK2(X1,X0),X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_24])).

cnf(c_564,plain,
    ( v2_tex_2(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | r1_tarski(sK2(sK4,X0),X0) ),
    inference(unflattening,[status(thm)],[c_563])).

cnf(c_2015,plain,
    ( v2_tex_2(X0,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r1_tarski(sK2(sK4,X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_564])).

cnf(c_2480,plain,
    ( v2_tex_2(sK5,sK4) = iProver_top
    | r1_tarski(sK2(sK4,sK5),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2022,c_2015])).

cnf(c_29,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_21,negated_conjecture,
    ( ~ v2_tex_2(sK5,sK4) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_909,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | r1_tarski(sK2(sK4,X0),X0)
    | sK4 != sK4
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_564])).

cnf(c_910,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | r1_tarski(sK2(sK4,sK5),sK5) ),
    inference(unflattening,[status(thm)],[c_909])).

cnf(c_911,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r1_tarski(sK2(sK4,sK5),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_910])).

cnf(c_3089,plain,
    ( r1_tarski(sK2(sK4,sK5),sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2480,c_29,c_911])).

cnf(c_23,negated_conjecture,
    ( v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_2021,plain,
    ( v1_xboole_0(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_5,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2031,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2657,plain,
    ( sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2021,c_2031])).

cnf(c_3093,plain,
    ( r1_tarski(sK2(sK4,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3089,c_2657])).

cnf(c_2800,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2657,c_2021])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_2033,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_11,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2026,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2024,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3479,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2026,c_2024])).

cnf(c_5860,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2033,c_3479])).

cnf(c_5950,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2800,c_5860])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2030,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_5956,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5950,c_2030])).

cnf(c_6691,plain,
    ( sK2(sK4,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3093,c_5956])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_2036,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2027,plain,
    ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3609,plain,
    ( k9_subset_1(X0,X1,k1_xboole_0) = k3_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2026,c_2027])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2028,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4605,plain,
    ( m1_subset_1(k3_xboole_0(X0,k1_xboole_0),k1_zfmisc_1(X1)) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3609,c_2028])).

cnf(c_7108,plain,
    ( m1_subset_1(k3_xboole_0(X0,k1_xboole_0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4605,c_2026])).

cnf(c_7112,plain,
    ( r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) != iProver_top
    | v1_xboole_0(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_7108,c_2024])).

cnf(c_8699,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k3_xboole_0(X1,k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2036,c_7112])).

cnf(c_8718,plain,
    ( v1_xboole_0(k3_xboole_0(X0,k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2800,c_8699])).

cnf(c_8831,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8718,c_2031])).

cnf(c_15,plain,
    ( v2_tex_2(X0,X1)
    | ~ v3_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),X0,X2) != sK2(X1,X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_578,plain,
    ( v2_tex_2(X0,X1)
    | ~ v3_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | k9_subset_1(u1_struct_0(X1),X0,X2) != sK2(X1,X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_24])).

cnf(c_579,plain,
    ( v2_tex_2(X0,sK4)
    | ~ v3_pre_topc(X1,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | k9_subset_1(u1_struct_0(sK4),X0,X1) != sK2(sK4,X0) ),
    inference(unflattening,[status(thm)],[c_578])).

cnf(c_2014,plain,
    ( k9_subset_1(u1_struct_0(sK4),X0,X1) != sK2(sK4,X0)
    | v2_tex_2(X0,sK4) = iProver_top
    | v3_pre_topc(X1,sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_579])).

cnf(c_4606,plain,
    ( sK2(sK4,X0) != k3_xboole_0(X0,k1_xboole_0)
    | v2_tex_2(X0,sK4) = iProver_top
    | v3_pre_topc(k1_xboole_0,sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3609,c_2014])).

cnf(c_8,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_68,plain,
    ( r1_tarski(sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_72,plain,
    ( ~ r1_tarski(sK4,sK4)
    | sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_14,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_25,negated_conjecture,
    ( v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_285,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_25])).

cnf(c_286,plain,
    ( v3_pre_topc(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_pre_topc(sK4)
    | ~ v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_285])).

cnf(c_290,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | v3_pre_topc(X0,sK4)
    | ~ v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_286,c_24])).

cnf(c_291,plain,
    ( v3_pre_topc(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_290])).

cnf(c_362,plain,
    ( v3_pre_topc(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_291,c_23])).

cnf(c_363,plain,
    ( v3_pre_topc(sK5,sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(unflattening,[status(thm)],[c_362])).

cnf(c_364,plain,
    ( v3_pre_topc(sK5,sK4) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_363])).

cnf(c_373,plain,
    ( sK5 != X0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_23])).

cnf(c_374,plain,
    ( k1_xboole_0 = sK5 ),
    inference(unflattening,[status(thm)],[c_373])).

cnf(c_2222,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2226,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2222])).

cnf(c_1582,plain,
    ( ~ v3_pre_topc(X0,X1)
    | v3_pre_topc(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2284,plain,
    ( v3_pre_topc(X0,X1)
    | ~ v3_pre_topc(sK5,sK4)
    | X1 != sK4
    | X0 != sK5 ),
    inference(instantiation,[status(thm)],[c_1582])).

cnf(c_2715,plain,
    ( ~ v3_pre_topc(sK5,sK4)
    | v3_pre_topc(k1_xboole_0,X0)
    | X0 != sK4
    | k1_xboole_0 != sK5 ),
    inference(instantiation,[status(thm)],[c_2284])).

cnf(c_2716,plain,
    ( X0 != sK4
    | k1_xboole_0 != sK5
    | v3_pre_topc(sK5,sK4) != iProver_top
    | v3_pre_topc(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2715])).

cnf(c_2718,plain,
    ( sK4 != sK4
    | k1_xboole_0 != sK5
    | v3_pre_topc(sK5,sK4) != iProver_top
    | v3_pre_topc(k1_xboole_0,sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2716])).

cnf(c_4962,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | sK2(sK4,X0) != k3_xboole_0(X0,k1_xboole_0)
    | v2_tex_2(X0,sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4606,c_29,c_68,c_72,c_364,c_374,c_2226,c_2718])).

cnf(c_4963,plain,
    ( sK2(sK4,X0) != k3_xboole_0(X0,k1_xboole_0)
    | v2_tex_2(X0,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(renaming,[status(thm)],[c_4962])).

cnf(c_9916,plain,
    ( sK2(sK4,X0) != k1_xboole_0
    | v2_tex_2(X0,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8831,c_4963])).

cnf(c_10322,plain,
    ( v2_tex_2(k1_xboole_0,sK4) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6691,c_9916])).

cnf(c_2023,plain,
    ( v2_tex_2(sK5,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2799,plain,
    ( v2_tex_2(k1_xboole_0,sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2657,c_2023])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10322,c_2799,c_2226])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:57:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.76/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.76/0.99  
% 3.76/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.76/0.99  
% 3.76/0.99  ------  iProver source info
% 3.76/0.99  
% 3.76/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.76/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.76/0.99  git: non_committed_changes: false
% 3.76/0.99  git: last_make_outside_of_git: false
% 3.76/0.99  
% 3.76/0.99  ------ 
% 3.76/0.99  
% 3.76/0.99  ------ Input Options
% 3.76/0.99  
% 3.76/0.99  --out_options                           all
% 3.76/0.99  --tptp_safe_out                         true
% 3.76/0.99  --problem_path                          ""
% 3.76/0.99  --include_path                          ""
% 3.76/0.99  --clausifier                            res/vclausify_rel
% 3.76/0.99  --clausifier_options                    --mode clausify
% 3.76/0.99  --stdin                                 false
% 3.76/0.99  --stats_out                             all
% 3.76/0.99  
% 3.76/0.99  ------ General Options
% 3.76/0.99  
% 3.76/0.99  --fof                                   false
% 3.76/0.99  --time_out_real                         305.
% 3.76/0.99  --time_out_virtual                      -1.
% 3.76/0.99  --symbol_type_check                     false
% 3.76/0.99  --clausify_out                          false
% 3.76/0.99  --sig_cnt_out                           false
% 3.76/0.99  --trig_cnt_out                          false
% 3.76/0.99  --trig_cnt_out_tolerance                1.
% 3.76/0.99  --trig_cnt_out_sk_spl                   false
% 3.76/0.99  --abstr_cl_out                          false
% 3.76/0.99  
% 3.76/0.99  ------ Global Options
% 3.76/0.99  
% 3.76/0.99  --schedule                              default
% 3.76/0.99  --add_important_lit                     false
% 3.76/0.99  --prop_solver_per_cl                    1000
% 3.76/0.99  --min_unsat_core                        false
% 3.76/0.99  --soft_assumptions                      false
% 3.76/0.99  --soft_lemma_size                       3
% 3.76/0.99  --prop_impl_unit_size                   0
% 3.76/0.99  --prop_impl_unit                        []
% 3.76/0.99  --share_sel_clauses                     true
% 3.76/0.99  --reset_solvers                         false
% 3.76/0.99  --bc_imp_inh                            [conj_cone]
% 3.76/0.99  --conj_cone_tolerance                   3.
% 3.76/0.99  --extra_neg_conj                        none
% 3.76/0.99  --large_theory_mode                     true
% 3.76/0.99  --prolific_symb_bound                   200
% 3.76/0.99  --lt_threshold                          2000
% 3.76/0.99  --clause_weak_htbl                      true
% 3.76/0.99  --gc_record_bc_elim                     false
% 3.76/0.99  
% 3.76/0.99  ------ Preprocessing Options
% 3.76/0.99  
% 3.76/0.99  --preprocessing_flag                    true
% 3.76/0.99  --time_out_prep_mult                    0.1
% 3.76/0.99  --splitting_mode                        input
% 3.76/0.99  --splitting_grd                         true
% 3.76/0.99  --splitting_cvd                         false
% 3.76/0.99  --splitting_cvd_svl                     false
% 3.76/0.99  --splitting_nvd                         32
% 3.76/0.99  --sub_typing                            true
% 3.76/0.99  --prep_gs_sim                           true
% 3.76/0.99  --prep_unflatten                        true
% 3.76/0.99  --prep_res_sim                          true
% 3.76/0.99  --prep_upred                            true
% 3.76/0.99  --prep_sem_filter                       exhaustive
% 3.76/0.99  --prep_sem_filter_out                   false
% 3.76/0.99  --pred_elim                             true
% 3.76/0.99  --res_sim_input                         true
% 3.76/0.99  --eq_ax_congr_red                       true
% 3.76/0.99  --pure_diseq_elim                       true
% 3.76/0.99  --brand_transform                       false
% 3.76/0.99  --non_eq_to_eq                          false
% 3.76/0.99  --prep_def_merge                        true
% 3.76/0.99  --prep_def_merge_prop_impl              false
% 3.76/0.99  --prep_def_merge_mbd                    true
% 3.76/0.99  --prep_def_merge_tr_red                 false
% 3.76/0.99  --prep_def_merge_tr_cl                  false
% 3.76/0.99  --smt_preprocessing                     true
% 3.76/0.99  --smt_ac_axioms                         fast
% 3.76/0.99  --preprocessed_out                      false
% 3.76/0.99  --preprocessed_stats                    false
% 3.76/0.99  
% 3.76/0.99  ------ Abstraction refinement Options
% 3.76/0.99  
% 3.76/0.99  --abstr_ref                             []
% 3.76/0.99  --abstr_ref_prep                        false
% 3.76/0.99  --abstr_ref_until_sat                   false
% 3.76/0.99  --abstr_ref_sig_restrict                funpre
% 3.76/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.76/0.99  --abstr_ref_under                       []
% 3.76/0.99  
% 3.76/0.99  ------ SAT Options
% 3.76/0.99  
% 3.76/0.99  --sat_mode                              false
% 3.76/0.99  --sat_fm_restart_options                ""
% 3.76/0.99  --sat_gr_def                            false
% 3.76/0.99  --sat_epr_types                         true
% 3.76/0.99  --sat_non_cyclic_types                  false
% 3.76/0.99  --sat_finite_models                     false
% 3.76/0.99  --sat_fm_lemmas                         false
% 3.76/0.99  --sat_fm_prep                           false
% 3.76/0.99  --sat_fm_uc_incr                        true
% 3.76/0.99  --sat_out_model                         small
% 3.76/0.99  --sat_out_clauses                       false
% 3.76/0.99  
% 3.76/0.99  ------ QBF Options
% 3.76/0.99  
% 3.76/0.99  --qbf_mode                              false
% 3.76/0.99  --qbf_elim_univ                         false
% 3.76/0.99  --qbf_dom_inst                          none
% 3.76/0.99  --qbf_dom_pre_inst                      false
% 3.76/0.99  --qbf_sk_in                             false
% 3.76/0.99  --qbf_pred_elim                         true
% 3.76/0.99  --qbf_split                             512
% 3.76/0.99  
% 3.76/0.99  ------ BMC1 Options
% 3.76/0.99  
% 3.76/0.99  --bmc1_incremental                      false
% 3.76/0.99  --bmc1_axioms                           reachable_all
% 3.76/0.99  --bmc1_min_bound                        0
% 3.76/0.99  --bmc1_max_bound                        -1
% 3.76/0.99  --bmc1_max_bound_default                -1
% 3.76/0.99  --bmc1_symbol_reachability              true
% 3.76/0.99  --bmc1_property_lemmas                  false
% 3.76/0.99  --bmc1_k_induction                      false
% 3.76/0.99  --bmc1_non_equiv_states                 false
% 3.76/0.99  --bmc1_deadlock                         false
% 3.76/0.99  --bmc1_ucm                              false
% 3.76/0.99  --bmc1_add_unsat_core                   none
% 3.76/0.99  --bmc1_unsat_core_children              false
% 3.76/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.76/0.99  --bmc1_out_stat                         full
% 3.76/0.99  --bmc1_ground_init                      false
% 3.76/0.99  --bmc1_pre_inst_next_state              false
% 3.76/0.99  --bmc1_pre_inst_state                   false
% 3.76/0.99  --bmc1_pre_inst_reach_state             false
% 3.76/0.99  --bmc1_out_unsat_core                   false
% 3.76/0.99  --bmc1_aig_witness_out                  false
% 3.76/0.99  --bmc1_verbose                          false
% 3.76/0.99  --bmc1_dump_clauses_tptp                false
% 3.76/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.76/0.99  --bmc1_dump_file                        -
% 3.76/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.76/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.76/0.99  --bmc1_ucm_extend_mode                  1
% 3.76/0.99  --bmc1_ucm_init_mode                    2
% 3.76/0.99  --bmc1_ucm_cone_mode                    none
% 3.76/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.76/0.99  --bmc1_ucm_relax_model                  4
% 3.76/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.76/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.76/0.99  --bmc1_ucm_layered_model                none
% 3.76/0.99  --bmc1_ucm_max_lemma_size               10
% 3.76/0.99  
% 3.76/0.99  ------ AIG Options
% 3.76/0.99  
% 3.76/0.99  --aig_mode                              false
% 3.76/0.99  
% 3.76/0.99  ------ Instantiation Options
% 3.76/0.99  
% 3.76/0.99  --instantiation_flag                    true
% 3.76/0.99  --inst_sos_flag                         false
% 3.76/0.99  --inst_sos_phase                        true
% 3.76/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.76/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.76/0.99  --inst_lit_sel_side                     num_symb
% 3.76/0.99  --inst_solver_per_active                1400
% 3.76/0.99  --inst_solver_calls_frac                1.
% 3.76/0.99  --inst_passive_queue_type               priority_queues
% 3.76/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.76/0.99  --inst_passive_queues_freq              [25;2]
% 3.76/0.99  --inst_dismatching                      true
% 3.76/0.99  --inst_eager_unprocessed_to_passive     true
% 3.76/0.99  --inst_prop_sim_given                   true
% 3.76/0.99  --inst_prop_sim_new                     false
% 3.76/0.99  --inst_subs_new                         false
% 3.76/0.99  --inst_eq_res_simp                      false
% 3.76/0.99  --inst_subs_given                       false
% 3.76/0.99  --inst_orphan_elimination               true
% 3.76/0.99  --inst_learning_loop_flag               true
% 3.76/0.99  --inst_learning_start                   3000
% 3.76/0.99  --inst_learning_factor                  2
% 3.76/0.99  --inst_start_prop_sim_after_learn       3
% 3.76/0.99  --inst_sel_renew                        solver
% 3.76/0.99  --inst_lit_activity_flag                true
% 3.76/0.99  --inst_restr_to_given                   false
% 3.76/0.99  --inst_activity_threshold               500
% 3.76/0.99  --inst_out_proof                        true
% 3.76/0.99  
% 3.76/0.99  ------ Resolution Options
% 3.76/0.99  
% 3.76/0.99  --resolution_flag                       true
% 3.76/0.99  --res_lit_sel                           adaptive
% 3.76/0.99  --res_lit_sel_side                      none
% 3.76/0.99  --res_ordering                          kbo
% 3.76/0.99  --res_to_prop_solver                    active
% 3.76/0.99  --res_prop_simpl_new                    false
% 3.76/0.99  --res_prop_simpl_given                  true
% 3.76/0.99  --res_passive_queue_type                priority_queues
% 3.76/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.76/0.99  --res_passive_queues_freq               [15;5]
% 3.76/0.99  --res_forward_subs                      full
% 3.76/0.99  --res_backward_subs                     full
% 3.76/0.99  --res_forward_subs_resolution           true
% 3.76/0.99  --res_backward_subs_resolution          true
% 3.76/0.99  --res_orphan_elimination                true
% 3.76/0.99  --res_time_limit                        2.
% 3.76/0.99  --res_out_proof                         true
% 3.76/0.99  
% 3.76/0.99  ------ Superposition Options
% 3.76/0.99  
% 3.76/0.99  --superposition_flag                    true
% 3.76/0.99  --sup_passive_queue_type                priority_queues
% 3.76/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.76/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.76/0.99  --demod_completeness_check              fast
% 3.76/0.99  --demod_use_ground                      true
% 3.76/0.99  --sup_to_prop_solver                    passive
% 3.76/0.99  --sup_prop_simpl_new                    true
% 3.76/0.99  --sup_prop_simpl_given                  true
% 3.76/0.99  --sup_fun_splitting                     false
% 3.76/0.99  --sup_smt_interval                      50000
% 3.76/0.99  
% 3.76/0.99  ------ Superposition Simplification Setup
% 3.76/0.99  
% 3.76/0.99  --sup_indices_passive                   []
% 3.76/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.76/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.76/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.76/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.76/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.76/0.99  --sup_full_bw                           [BwDemod]
% 3.76/0.99  --sup_immed_triv                        [TrivRules]
% 3.76/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.76/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.76/0.99  --sup_immed_bw_main                     []
% 3.76/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.76/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.76/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.76/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.76/0.99  
% 3.76/0.99  ------ Combination Options
% 3.76/0.99  
% 3.76/0.99  --comb_res_mult                         3
% 3.76/0.99  --comb_sup_mult                         2
% 3.76/0.99  --comb_inst_mult                        10
% 3.76/0.99  
% 3.76/0.99  ------ Debug Options
% 3.76/0.99  
% 3.76/0.99  --dbg_backtrace                         false
% 3.76/0.99  --dbg_dump_prop_clauses                 false
% 3.76/0.99  --dbg_dump_prop_clauses_file            -
% 3.76/0.99  --dbg_out_stat                          false
% 3.76/0.99  ------ Parsing...
% 3.76/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.76/0.99  
% 3.76/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.76/0.99  
% 3.76/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.76/0.99  
% 3.76/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.76/0.99  ------ Proving...
% 3.76/0.99  ------ Problem Properties 
% 3.76/0.99  
% 3.76/0.99  
% 3.76/0.99  clauses                                 23
% 3.76/0.99  conjectures                             3
% 3.76/0.99  EPR                                     7
% 3.76/0.99  Horn                                    19
% 3.76/0.99  unary                                   5
% 3.76/0.99  binary                                  7
% 3.76/0.99  lits                                    60
% 3.76/0.99  lits eq                                 5
% 3.76/0.99  fd_pure                                 0
% 3.76/0.99  fd_pseudo                               0
% 3.76/0.99  fd_cond                                 1
% 3.76/0.99  fd_pseudo_cond                          1
% 3.76/0.99  AC symbols                              0
% 3.76/0.99  
% 3.76/0.99  ------ Schedule dynamic 5 is on 
% 3.76/0.99  
% 3.76/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.76/0.99  
% 3.76/0.99  
% 3.76/0.99  ------ 
% 3.76/0.99  Current options:
% 3.76/0.99  ------ 
% 3.76/0.99  
% 3.76/0.99  ------ Input Options
% 3.76/0.99  
% 3.76/0.99  --out_options                           all
% 3.76/0.99  --tptp_safe_out                         true
% 3.76/0.99  --problem_path                          ""
% 3.76/0.99  --include_path                          ""
% 3.76/0.99  --clausifier                            res/vclausify_rel
% 3.76/0.99  --clausifier_options                    --mode clausify
% 3.76/0.99  --stdin                                 false
% 3.76/0.99  --stats_out                             all
% 3.76/0.99  
% 3.76/0.99  ------ General Options
% 3.76/0.99  
% 3.76/0.99  --fof                                   false
% 3.76/0.99  --time_out_real                         305.
% 3.76/0.99  --time_out_virtual                      -1.
% 3.76/0.99  --symbol_type_check                     false
% 3.76/0.99  --clausify_out                          false
% 3.76/0.99  --sig_cnt_out                           false
% 3.76/0.99  --trig_cnt_out                          false
% 3.76/0.99  --trig_cnt_out_tolerance                1.
% 3.76/0.99  --trig_cnt_out_sk_spl                   false
% 3.76/0.99  --abstr_cl_out                          false
% 3.76/0.99  
% 3.76/0.99  ------ Global Options
% 3.76/0.99  
% 3.76/0.99  --schedule                              default
% 3.76/0.99  --add_important_lit                     false
% 3.76/0.99  --prop_solver_per_cl                    1000
% 3.76/0.99  --min_unsat_core                        false
% 3.76/0.99  --soft_assumptions                      false
% 3.76/0.99  --soft_lemma_size                       3
% 3.76/0.99  --prop_impl_unit_size                   0
% 3.76/0.99  --prop_impl_unit                        []
% 3.76/0.99  --share_sel_clauses                     true
% 3.76/0.99  --reset_solvers                         false
% 3.76/0.99  --bc_imp_inh                            [conj_cone]
% 3.76/0.99  --conj_cone_tolerance                   3.
% 3.76/0.99  --extra_neg_conj                        none
% 3.76/0.99  --large_theory_mode                     true
% 3.76/0.99  --prolific_symb_bound                   200
% 3.76/0.99  --lt_threshold                          2000
% 3.76/0.99  --clause_weak_htbl                      true
% 3.76/0.99  --gc_record_bc_elim                     false
% 3.76/0.99  
% 3.76/0.99  ------ Preprocessing Options
% 3.76/0.99  
% 3.76/0.99  --preprocessing_flag                    true
% 3.76/0.99  --time_out_prep_mult                    0.1
% 3.76/0.99  --splitting_mode                        input
% 3.76/0.99  --splitting_grd                         true
% 3.76/0.99  --splitting_cvd                         false
% 3.76/0.99  --splitting_cvd_svl                     false
% 3.76/0.99  --splitting_nvd                         32
% 3.76/0.99  --sub_typing                            true
% 3.76/0.99  --prep_gs_sim                           true
% 3.76/0.99  --prep_unflatten                        true
% 3.76/0.99  --prep_res_sim                          true
% 3.76/0.99  --prep_upred                            true
% 3.76/0.99  --prep_sem_filter                       exhaustive
% 3.76/0.99  --prep_sem_filter_out                   false
% 3.76/0.99  --pred_elim                             true
% 3.76/0.99  --res_sim_input                         true
% 3.76/0.99  --eq_ax_congr_red                       true
% 3.76/0.99  --pure_diseq_elim                       true
% 3.76/0.99  --brand_transform                       false
% 3.76/0.99  --non_eq_to_eq                          false
% 3.76/0.99  --prep_def_merge                        true
% 3.76/0.99  --prep_def_merge_prop_impl              false
% 3.76/0.99  --prep_def_merge_mbd                    true
% 3.76/0.99  --prep_def_merge_tr_red                 false
% 3.76/0.99  --prep_def_merge_tr_cl                  false
% 3.76/0.99  --smt_preprocessing                     true
% 3.76/0.99  --smt_ac_axioms                         fast
% 3.76/0.99  --preprocessed_out                      false
% 3.76/0.99  --preprocessed_stats                    false
% 3.76/0.99  
% 3.76/0.99  ------ Abstraction refinement Options
% 3.76/0.99  
% 3.76/0.99  --abstr_ref                             []
% 3.76/0.99  --abstr_ref_prep                        false
% 3.76/0.99  --abstr_ref_until_sat                   false
% 3.76/0.99  --abstr_ref_sig_restrict                funpre
% 3.76/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.76/0.99  --abstr_ref_under                       []
% 3.76/0.99  
% 3.76/0.99  ------ SAT Options
% 3.76/0.99  
% 3.76/0.99  --sat_mode                              false
% 3.76/0.99  --sat_fm_restart_options                ""
% 3.76/0.99  --sat_gr_def                            false
% 3.76/0.99  --sat_epr_types                         true
% 3.76/0.99  --sat_non_cyclic_types                  false
% 3.76/0.99  --sat_finite_models                     false
% 3.76/0.99  --sat_fm_lemmas                         false
% 3.76/0.99  --sat_fm_prep                           false
% 3.76/0.99  --sat_fm_uc_incr                        true
% 3.76/0.99  --sat_out_model                         small
% 3.76/0.99  --sat_out_clauses                       false
% 3.76/0.99  
% 3.76/0.99  ------ QBF Options
% 3.76/0.99  
% 3.76/0.99  --qbf_mode                              false
% 3.76/0.99  --qbf_elim_univ                         false
% 3.76/0.99  --qbf_dom_inst                          none
% 3.76/0.99  --qbf_dom_pre_inst                      false
% 3.76/0.99  --qbf_sk_in                             false
% 3.76/0.99  --qbf_pred_elim                         true
% 3.76/0.99  --qbf_split                             512
% 3.76/0.99  
% 3.76/0.99  ------ BMC1 Options
% 3.76/0.99  
% 3.76/0.99  --bmc1_incremental                      false
% 3.76/0.99  --bmc1_axioms                           reachable_all
% 3.76/0.99  --bmc1_min_bound                        0
% 3.76/0.99  --bmc1_max_bound                        -1
% 3.76/0.99  --bmc1_max_bound_default                -1
% 3.76/0.99  --bmc1_symbol_reachability              true
% 3.76/0.99  --bmc1_property_lemmas                  false
% 3.76/0.99  --bmc1_k_induction                      false
% 3.76/0.99  --bmc1_non_equiv_states                 false
% 3.76/0.99  --bmc1_deadlock                         false
% 3.76/0.99  --bmc1_ucm                              false
% 3.76/0.99  --bmc1_add_unsat_core                   none
% 3.76/0.99  --bmc1_unsat_core_children              false
% 3.76/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.76/0.99  --bmc1_out_stat                         full
% 3.76/0.99  --bmc1_ground_init                      false
% 3.76/0.99  --bmc1_pre_inst_next_state              false
% 3.76/0.99  --bmc1_pre_inst_state                   false
% 3.76/0.99  --bmc1_pre_inst_reach_state             false
% 3.76/0.99  --bmc1_out_unsat_core                   false
% 3.76/0.99  --bmc1_aig_witness_out                  false
% 3.76/0.99  --bmc1_verbose                          false
% 3.76/0.99  --bmc1_dump_clauses_tptp                false
% 3.76/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.76/0.99  --bmc1_dump_file                        -
% 3.76/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.76/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.76/0.99  --bmc1_ucm_extend_mode                  1
% 3.76/0.99  --bmc1_ucm_init_mode                    2
% 3.76/0.99  --bmc1_ucm_cone_mode                    none
% 3.76/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.76/0.99  --bmc1_ucm_relax_model                  4
% 3.76/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.76/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.76/0.99  --bmc1_ucm_layered_model                none
% 3.76/0.99  --bmc1_ucm_max_lemma_size               10
% 3.76/0.99  
% 3.76/0.99  ------ AIG Options
% 3.76/0.99  
% 3.76/0.99  --aig_mode                              false
% 3.76/0.99  
% 3.76/0.99  ------ Instantiation Options
% 3.76/0.99  
% 3.76/0.99  --instantiation_flag                    true
% 3.76/0.99  --inst_sos_flag                         false
% 3.76/0.99  --inst_sos_phase                        true
% 3.76/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.76/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.76/0.99  --inst_lit_sel_side                     none
% 3.76/0.99  --inst_solver_per_active                1400
% 3.76/0.99  --inst_solver_calls_frac                1.
% 3.76/0.99  --inst_passive_queue_type               priority_queues
% 3.76/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.76/0.99  --inst_passive_queues_freq              [25;2]
% 3.76/0.99  --inst_dismatching                      true
% 3.76/0.99  --inst_eager_unprocessed_to_passive     true
% 3.76/0.99  --inst_prop_sim_given                   true
% 3.76/0.99  --inst_prop_sim_new                     false
% 3.76/0.99  --inst_subs_new                         false
% 3.76/0.99  --inst_eq_res_simp                      false
% 3.76/0.99  --inst_subs_given                       false
% 3.76/0.99  --inst_orphan_elimination               true
% 3.76/0.99  --inst_learning_loop_flag               true
% 3.76/0.99  --inst_learning_start                   3000
% 3.76/0.99  --inst_learning_factor                  2
% 3.76/0.99  --inst_start_prop_sim_after_learn       3
% 3.76/0.99  --inst_sel_renew                        solver
% 3.76/0.99  --inst_lit_activity_flag                true
% 3.76/0.99  --inst_restr_to_given                   false
% 3.76/0.99  --inst_activity_threshold               500
% 3.76/0.99  --inst_out_proof                        true
% 3.76/0.99  
% 3.76/0.99  ------ Resolution Options
% 3.76/0.99  
% 3.76/0.99  --resolution_flag                       false
% 3.76/0.99  --res_lit_sel                           adaptive
% 3.76/0.99  --res_lit_sel_side                      none
% 3.76/0.99  --res_ordering                          kbo
% 3.76/0.99  --res_to_prop_solver                    active
% 3.76/0.99  --res_prop_simpl_new                    false
% 3.76/0.99  --res_prop_simpl_given                  true
% 3.76/0.99  --res_passive_queue_type                priority_queues
% 3.76/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.76/0.99  --res_passive_queues_freq               [15;5]
% 3.76/0.99  --res_forward_subs                      full
% 3.76/0.99  --res_backward_subs                     full
% 3.76/0.99  --res_forward_subs_resolution           true
% 3.76/0.99  --res_backward_subs_resolution          true
% 3.76/0.99  --res_orphan_elimination                true
% 3.76/0.99  --res_time_limit                        2.
% 3.76/0.99  --res_out_proof                         true
% 3.76/0.99  
% 3.76/0.99  ------ Superposition Options
% 3.76/0.99  
% 3.76/0.99  --superposition_flag                    true
% 3.76/0.99  --sup_passive_queue_type                priority_queues
% 3.76/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.76/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.76/0.99  --demod_completeness_check              fast
% 3.76/0.99  --demod_use_ground                      true
% 3.76/0.99  --sup_to_prop_solver                    passive
% 3.76/0.99  --sup_prop_simpl_new                    true
% 3.76/0.99  --sup_prop_simpl_given                  true
% 3.76/0.99  --sup_fun_splitting                     false
% 3.76/0.99  --sup_smt_interval                      50000
% 3.76/0.99  
% 3.76/0.99  ------ Superposition Simplification Setup
% 3.76/0.99  
% 3.76/0.99  --sup_indices_passive                   []
% 3.76/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.76/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.76/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.76/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.76/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.76/0.99  --sup_full_bw                           [BwDemod]
% 3.76/0.99  --sup_immed_triv                        [TrivRules]
% 3.76/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.76/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.76/0.99  --sup_immed_bw_main                     []
% 3.76/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.76/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.76/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.76/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.76/0.99  
% 3.76/0.99  ------ Combination Options
% 3.76/0.99  
% 3.76/0.99  --comb_res_mult                         3
% 3.76/0.99  --comb_sup_mult                         2
% 3.76/0.99  --comb_inst_mult                        10
% 3.76/0.99  
% 3.76/0.99  ------ Debug Options
% 3.76/0.99  
% 3.76/0.99  --dbg_backtrace                         false
% 3.76/0.99  --dbg_dump_prop_clauses                 false
% 3.76/0.99  --dbg_dump_prop_clauses_file            -
% 3.76/0.99  --dbg_out_stat                          false
% 3.76/0.99  
% 3.76/0.99  
% 3.76/0.99  
% 3.76/0.99  
% 3.76/0.99  ------ Proving...
% 3.76/0.99  
% 3.76/0.99  
% 3.76/0.99  % SZS status Theorem for theBenchmark.p
% 3.76/0.99  
% 3.76/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.76/0.99  
% 3.76/0.99  fof(f12,conjecture,(
% 3.76/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 3.76/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.76/0.99  
% 3.76/0.99  fof(f13,negated_conjecture,(
% 3.76/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 3.76/0.99    inference(negated_conjecture,[],[f12])).
% 3.76/0.99  
% 3.76/0.99  fof(f14,plain,(
% 3.76/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 3.76/0.99    inference(pure_predicate_removal,[],[f13])).
% 3.76/0.99  
% 3.76/0.99  fof(f26,plain,(
% 3.76/0.99    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.76/0.99    inference(ennf_transformation,[],[f14])).
% 3.76/0.99  
% 3.76/0.99  fof(f27,plain,(
% 3.76/0.99    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.76/0.99    inference(flattening,[],[f26])).
% 3.76/0.99  
% 3.76/0.99  fof(f44,plain,(
% 3.76/0.99    ( ! [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => (~v2_tex_2(sK5,X0) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(sK5))) )),
% 3.76/0.99    introduced(choice_axiom,[])).
% 3.76/0.99  
% 3.76/0.99  fof(f43,plain,(
% 3.76/0.99    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (~v2_tex_2(X1,sK4) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) & v1_xboole_0(X1)) & l1_pre_topc(sK4) & v2_pre_topc(sK4))),
% 3.76/0.99    introduced(choice_axiom,[])).
% 3.76/0.99  
% 3.76/0.99  fof(f45,plain,(
% 3.76/0.99    (~v2_tex_2(sK5,sK4) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) & v1_xboole_0(sK5)) & l1_pre_topc(sK4) & v2_pre_topc(sK4)),
% 3.76/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f27,f44,f43])).
% 3.76/0.99  
% 3.76/0.99  fof(f70,plain,(
% 3.76/0.99    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))),
% 3.76/0.99    inference(cnf_transformation,[],[f45])).
% 3.76/0.99  
% 3.76/0.99  fof(f11,axiom,(
% 3.76/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0))) & r1_tarski(X2,X1))))))),
% 3.76/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.76/0.99  
% 3.76/0.99  fof(f24,plain,(
% 3.76/0.99    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((? [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.76/0.99    inference(ennf_transformation,[],[f11])).
% 3.76/0.99  
% 3.76/0.99  fof(f25,plain,(
% 3.76/0.99    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.76/0.99    inference(flattening,[],[f24])).
% 3.76/0.99  
% 3.76/0.99  fof(f38,plain,(
% 3.76/0.99    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.76/0.99    inference(nnf_transformation,[],[f25])).
% 3.76/0.99  
% 3.76/0.99  fof(f39,plain,(
% 3.76/0.99    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (? [X5] : (k9_subset_1(u1_struct_0(X0),X1,X5) = X4 & v3_pre_topc(X5,X0) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.76/0.99    inference(rectify,[],[f38])).
% 3.76/0.99  
% 3.76/0.99  fof(f41,plain,(
% 3.76/0.99    ! [X4,X1,X0] : (? [X5] : (k9_subset_1(u1_struct_0(X0),X1,X5) = X4 & v3_pre_topc(X5,X0) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) => (k9_subset_1(u1_struct_0(X0),X1,sK3(X0,X1,X4)) = X4 & v3_pre_topc(sK3(X0,X1,X4),X0) & m1_subset_1(sK3(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.76/0.99    introduced(choice_axiom,[])).
% 3.76/0.99  
% 3.76/0.99  fof(f40,plain,(
% 3.76/0.99    ! [X1,X0] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(sK2(X0,X1),X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.76/0.99    introduced(choice_axiom,[])).
% 3.76/0.99  
% 3.76/0.99  fof(f42,plain,(
% 3.76/0.99    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(sK2(X0,X1),X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : ((k9_subset_1(u1_struct_0(X0),X1,sK3(X0,X1,X4)) = X4 & v3_pre_topc(sK3(X0,X1,X4),X0) & m1_subset_1(sK3(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.76/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f39,f41,f40])).
% 3.76/0.99  
% 3.76/0.99  fof(f65,plain,(
% 3.76/0.99    ( ! [X0,X1] : (v2_tex_2(X1,X0) | r1_tarski(sK2(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.76/0.99    inference(cnf_transformation,[],[f42])).
% 3.76/0.99  
% 3.76/0.99  fof(f68,plain,(
% 3.76/0.99    l1_pre_topc(sK4)),
% 3.76/0.99    inference(cnf_transformation,[],[f45])).
% 3.76/0.99  
% 3.76/0.99  fof(f71,plain,(
% 3.76/0.99    ~v2_tex_2(sK5,sK4)),
% 3.76/0.99    inference(cnf_transformation,[],[f45])).
% 3.76/0.99  
% 3.76/0.99  fof(f69,plain,(
% 3.76/0.99    v1_xboole_0(sK5)),
% 3.76/0.99    inference(cnf_transformation,[],[f45])).
% 3.76/0.99  
% 3.76/0.99  fof(f3,axiom,(
% 3.76/0.99    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 3.76/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.76/0.99  
% 3.76/0.99  fof(f16,plain,(
% 3.76/0.99    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 3.76/0.99    inference(ennf_transformation,[],[f3])).
% 3.76/0.99  
% 3.76/0.99  fof(f51,plain,(
% 3.76/0.99    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 3.76/0.99    inference(cnf_transformation,[],[f16])).
% 3.76/0.99  
% 3.76/0.99  fof(f2,axiom,(
% 3.76/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.76/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.76/0.99  
% 3.76/0.99  fof(f15,plain,(
% 3.76/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.76/0.99    inference(ennf_transformation,[],[f2])).
% 3.76/0.99  
% 3.76/0.99  fof(f32,plain,(
% 3.76/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.76/0.99    inference(nnf_transformation,[],[f15])).
% 3.76/0.99  
% 3.76/0.99  fof(f33,plain,(
% 3.76/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.76/1.00    inference(rectify,[],[f32])).
% 3.76/1.00  
% 3.76/1.00  fof(f34,plain,(
% 3.76/1.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 3.76/1.00    introduced(choice_axiom,[])).
% 3.76/1.00  
% 3.76/1.00  fof(f35,plain,(
% 3.76/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.76/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f33,f34])).
% 3.76/1.00  
% 3.76/1.00  fof(f49,plain,(
% 3.76/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 3.76/1.00    inference(cnf_transformation,[],[f35])).
% 3.76/1.00  
% 3.76/1.00  fof(f7,axiom,(
% 3.76/1.00    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.76/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.76/1.00  
% 3.76/1.00  fof(f57,plain,(
% 3.76/1.00    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.76/1.00    inference(cnf_transformation,[],[f7])).
% 3.76/1.00  
% 3.76/1.00  fof(f9,axiom,(
% 3.76/1.00    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 3.76/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.76/1.00  
% 3.76/1.00  fof(f21,plain,(
% 3.76/1.00    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.76/1.00    inference(ennf_transformation,[],[f9])).
% 3.76/1.00  
% 3.76/1.00  fof(f59,plain,(
% 3.76/1.00    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.76/1.00    inference(cnf_transformation,[],[f21])).
% 3.76/1.00  
% 3.76/1.00  fof(f4,axiom,(
% 3.76/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.76/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.76/1.00  
% 3.76/1.00  fof(f36,plain,(
% 3.76/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.76/1.00    inference(nnf_transformation,[],[f4])).
% 3.76/1.00  
% 3.76/1.00  fof(f37,plain,(
% 3.76/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.76/1.00    inference(flattening,[],[f36])).
% 3.76/1.00  
% 3.76/1.00  fof(f54,plain,(
% 3.76/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.76/1.00    inference(cnf_transformation,[],[f37])).
% 3.76/1.00  
% 3.76/1.00  fof(f1,axiom,(
% 3.76/1.00    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.76/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.76/1.00  
% 3.76/1.00  fof(f28,plain,(
% 3.76/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.76/1.00    inference(nnf_transformation,[],[f1])).
% 3.76/1.00  
% 3.76/1.00  fof(f29,plain,(
% 3.76/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.76/1.00    inference(rectify,[],[f28])).
% 3.76/1.00  
% 3.76/1.00  fof(f30,plain,(
% 3.76/1.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.76/1.00    introduced(choice_axiom,[])).
% 3.76/1.00  
% 3.76/1.00  fof(f31,plain,(
% 3.76/1.00    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.76/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).
% 3.76/1.00  
% 3.76/1.00  fof(f47,plain,(
% 3.76/1.00    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 3.76/1.00    inference(cnf_transformation,[],[f31])).
% 3.76/1.00  
% 3.76/1.00  fof(f6,axiom,(
% 3.76/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 3.76/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.76/1.00  
% 3.76/1.00  fof(f18,plain,(
% 3.76/1.00    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 3.76/1.00    inference(ennf_transformation,[],[f6])).
% 3.76/1.00  
% 3.76/1.00  fof(f56,plain,(
% 3.76/1.00    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.76/1.00    inference(cnf_transformation,[],[f18])).
% 3.76/1.00  
% 3.76/1.00  fof(f5,axiom,(
% 3.76/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 3.76/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.76/1.00  
% 3.76/1.00  fof(f17,plain,(
% 3.76/1.00    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 3.76/1.00    inference(ennf_transformation,[],[f5])).
% 3.76/1.00  
% 3.76/1.00  fof(f55,plain,(
% 3.76/1.00    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.76/1.00    inference(cnf_transformation,[],[f17])).
% 3.76/1.00  
% 3.76/1.00  fof(f66,plain,(
% 3.76/1.00    ( ! [X0,X3,X1] : (v2_tex_2(X1,X0) | k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.76/1.00    inference(cnf_transformation,[],[f42])).
% 3.76/1.00  
% 3.76/1.00  fof(f52,plain,(
% 3.76/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.76/1.00    inference(cnf_transformation,[],[f37])).
% 3.76/1.00  
% 3.76/1.00  fof(f73,plain,(
% 3.76/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.76/1.00    inference(equality_resolution,[],[f52])).
% 3.76/1.00  
% 3.76/1.00  fof(f10,axiom,(
% 3.76/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_xboole_0(X1) => v3_pre_topc(X1,X0))))),
% 3.76/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.76/1.00  
% 3.76/1.00  fof(f22,plain,(
% 3.76/1.00    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) | ~v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.76/1.00    inference(ennf_transformation,[],[f10])).
% 3.76/1.00  
% 3.76/1.00  fof(f23,plain,(
% 3.76/1.00    ! [X0] : (! [X1] : (v3_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.76/1.00    inference(flattening,[],[f22])).
% 3.76/1.00  
% 3.76/1.00  fof(f60,plain,(
% 3.76/1.00    ( ! [X0,X1] : (v3_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.76/1.00    inference(cnf_transformation,[],[f23])).
% 3.76/1.00  
% 3.76/1.00  fof(f67,plain,(
% 3.76/1.00    v2_pre_topc(sK4)),
% 3.76/1.00    inference(cnf_transformation,[],[f45])).
% 3.76/1.00  
% 3.76/1.00  cnf(c_22,negated_conjecture,
% 3.76/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 3.76/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2022,plain,
% 3.76/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_16,plain,
% 3.76/1.00      ( v2_tex_2(X0,X1)
% 3.76/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.76/1.00      | r1_tarski(sK2(X1,X0),X0)
% 3.76/1.00      | ~ l1_pre_topc(X1) ),
% 3.76/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_24,negated_conjecture,
% 3.76/1.00      ( l1_pre_topc(sK4) ),
% 3.76/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_563,plain,
% 3.76/1.00      ( v2_tex_2(X0,X1)
% 3.76/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.76/1.00      | r1_tarski(sK2(X1,X0),X0)
% 3.76/1.00      | sK4 != X1 ),
% 3.76/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_24]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_564,plain,
% 3.76/1.00      ( v2_tex_2(X0,sK4)
% 3.76/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.76/1.00      | r1_tarski(sK2(sK4,X0),X0) ),
% 3.76/1.00      inference(unflattening,[status(thm)],[c_563]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2015,plain,
% 3.76/1.00      ( v2_tex_2(X0,sK4) = iProver_top
% 3.76/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.76/1.00      | r1_tarski(sK2(sK4,X0),X0) = iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_564]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2480,plain,
% 3.76/1.00      ( v2_tex_2(sK5,sK4) = iProver_top
% 3.76/1.00      | r1_tarski(sK2(sK4,sK5),sK5) = iProver_top ),
% 3.76/1.00      inference(superposition,[status(thm)],[c_2022,c_2015]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_29,plain,
% 3.76/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_21,negated_conjecture,
% 3.76/1.00      ( ~ v2_tex_2(sK5,sK4) ),
% 3.76/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_909,plain,
% 3.76/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.76/1.00      | r1_tarski(sK2(sK4,X0),X0)
% 3.76/1.00      | sK4 != sK4
% 3.76/1.00      | sK5 != X0 ),
% 3.76/1.00      inference(resolution_lifted,[status(thm)],[c_21,c_564]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_910,plain,
% 3.76/1.00      ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.76/1.00      | r1_tarski(sK2(sK4,sK5),sK5) ),
% 3.76/1.00      inference(unflattening,[status(thm)],[c_909]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_911,plain,
% 3.76/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.76/1.00      | r1_tarski(sK2(sK4,sK5),sK5) = iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_910]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_3089,plain,
% 3.76/1.00      ( r1_tarski(sK2(sK4,sK5),sK5) = iProver_top ),
% 3.76/1.00      inference(global_propositional_subsumption,
% 3.76/1.00                [status(thm)],
% 3.76/1.00                [c_2480,c_29,c_911]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_23,negated_conjecture,
% 3.76/1.00      ( v1_xboole_0(sK5) ),
% 3.76/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2021,plain,
% 3.76/1.00      ( v1_xboole_0(sK5) = iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_5,plain,
% 3.76/1.00      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 3.76/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2031,plain,
% 3.76/1.00      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2657,plain,
% 3.76/1.00      ( sK5 = k1_xboole_0 ),
% 3.76/1.00      inference(superposition,[status(thm)],[c_2021,c_2031]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_3093,plain,
% 3.76/1.00      ( r1_tarski(sK2(sK4,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 3.76/1.00      inference(light_normalisation,[status(thm)],[c_3089,c_2657]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2800,plain,
% 3.76/1.00      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.76/1.00      inference(demodulation,[status(thm)],[c_2657,c_2021]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_3,plain,
% 3.76/1.00      ( r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 3.76/1.00      inference(cnf_transformation,[],[f49]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2033,plain,
% 3.76/1.00      ( r1_tarski(X0,X1) = iProver_top
% 3.76/1.00      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_11,plain,
% 3.76/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.76/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2026,plain,
% 3.76/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_13,plain,
% 3.76/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.76/1.00      | ~ r2_hidden(X2,X0)
% 3.76/1.00      | ~ v1_xboole_0(X1) ),
% 3.76/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2024,plain,
% 3.76/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.76/1.00      | r2_hidden(X2,X0) != iProver_top
% 3.76/1.00      | v1_xboole_0(X1) != iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_3479,plain,
% 3.76/1.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 3.76/1.00      | v1_xboole_0(X1) != iProver_top ),
% 3.76/1.00      inference(superposition,[status(thm)],[c_2026,c_2024]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_5860,plain,
% 3.76/1.00      ( r1_tarski(k1_xboole_0,X0) = iProver_top
% 3.76/1.00      | v1_xboole_0(X1) != iProver_top ),
% 3.76/1.00      inference(superposition,[status(thm)],[c_2033,c_3479]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_5950,plain,
% 3.76/1.00      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.76/1.00      inference(superposition,[status(thm)],[c_2800,c_5860]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_6,plain,
% 3.76/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.76/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2030,plain,
% 3.76/1.00      ( X0 = X1
% 3.76/1.00      | r1_tarski(X1,X0) != iProver_top
% 3.76/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_5956,plain,
% 3.76/1.00      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.76/1.00      inference(superposition,[status(thm)],[c_5950,c_2030]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_6691,plain,
% 3.76/1.00      ( sK2(sK4,k1_xboole_0) = k1_xboole_0 ),
% 3.76/1.00      inference(superposition,[status(thm)],[c_3093,c_5956]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_0,plain,
% 3.76/1.00      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 3.76/1.00      inference(cnf_transformation,[],[f47]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2036,plain,
% 3.76/1.00      ( r2_hidden(sK0(X0),X0) = iProver_top
% 3.76/1.00      | v1_xboole_0(X0) = iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_10,plain,
% 3.76/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.76/1.00      | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 3.76/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2027,plain,
% 3.76/1.00      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
% 3.76/1.00      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_3609,plain,
% 3.76/1.00      ( k9_subset_1(X0,X1,k1_xboole_0) = k3_xboole_0(X1,k1_xboole_0) ),
% 3.76/1.00      inference(superposition,[status(thm)],[c_2026,c_2027]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_9,plain,
% 3.76/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.76/1.00      | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 3.76/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2028,plain,
% 3.76/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.76/1.00      | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_4605,plain,
% 3.76/1.00      ( m1_subset_1(k3_xboole_0(X0,k1_xboole_0),k1_zfmisc_1(X1)) = iProver_top
% 3.76/1.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) != iProver_top ),
% 3.76/1.00      inference(superposition,[status(thm)],[c_3609,c_2028]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_7108,plain,
% 3.76/1.00      ( m1_subset_1(k3_xboole_0(X0,k1_xboole_0),k1_zfmisc_1(X1)) = iProver_top ),
% 3.76/1.00      inference(forward_subsumption_resolution,
% 3.76/1.00                [status(thm)],
% 3.76/1.00                [c_4605,c_2026]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_7112,plain,
% 3.76/1.00      ( r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) != iProver_top
% 3.76/1.00      | v1_xboole_0(X2) != iProver_top ),
% 3.76/1.00      inference(superposition,[status(thm)],[c_7108,c_2024]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_8699,plain,
% 3.76/1.00      ( v1_xboole_0(X0) != iProver_top
% 3.76/1.00      | v1_xboole_0(k3_xboole_0(X1,k1_xboole_0)) = iProver_top ),
% 3.76/1.00      inference(superposition,[status(thm)],[c_2036,c_7112]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_8718,plain,
% 3.76/1.00      ( v1_xboole_0(k3_xboole_0(X0,k1_xboole_0)) = iProver_top ),
% 3.76/1.00      inference(superposition,[status(thm)],[c_2800,c_8699]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_8831,plain,
% 3.76/1.00      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.76/1.00      inference(superposition,[status(thm)],[c_8718,c_2031]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_15,plain,
% 3.76/1.00      ( v2_tex_2(X0,X1)
% 3.76/1.00      | ~ v3_pre_topc(X2,X1)
% 3.76/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.76/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.76/1.00      | ~ l1_pre_topc(X1)
% 3.76/1.00      | k9_subset_1(u1_struct_0(X1),X0,X2) != sK2(X1,X0) ),
% 3.76/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_578,plain,
% 3.76/1.00      ( v2_tex_2(X0,X1)
% 3.76/1.00      | ~ v3_pre_topc(X2,X1)
% 3.76/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.76/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.76/1.00      | k9_subset_1(u1_struct_0(X1),X0,X2) != sK2(X1,X0)
% 3.76/1.00      | sK4 != X1 ),
% 3.76/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_24]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_579,plain,
% 3.76/1.00      ( v2_tex_2(X0,sK4)
% 3.76/1.00      | ~ v3_pre_topc(X1,sK4)
% 3.76/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.76/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.76/1.00      | k9_subset_1(u1_struct_0(sK4),X0,X1) != sK2(sK4,X0) ),
% 3.76/1.00      inference(unflattening,[status(thm)],[c_578]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2014,plain,
% 3.76/1.00      ( k9_subset_1(u1_struct_0(sK4),X0,X1) != sK2(sK4,X0)
% 3.76/1.00      | v2_tex_2(X0,sK4) = iProver_top
% 3.76/1.00      | v3_pre_topc(X1,sK4) != iProver_top
% 3.76/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.76/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_579]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_4606,plain,
% 3.76/1.00      ( sK2(sK4,X0) != k3_xboole_0(X0,k1_xboole_0)
% 3.76/1.00      | v2_tex_2(X0,sK4) = iProver_top
% 3.76/1.00      | v3_pre_topc(k1_xboole_0,sK4) != iProver_top
% 3.76/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.76/1.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 3.76/1.00      inference(superposition,[status(thm)],[c_3609,c_2014]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_8,plain,
% 3.76/1.00      ( r1_tarski(X0,X0) ),
% 3.76/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_68,plain,
% 3.76/1.00      ( r1_tarski(sK4,sK4) ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_72,plain,
% 3.76/1.00      ( ~ r1_tarski(sK4,sK4) | sK4 = sK4 ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_6]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_14,plain,
% 3.76/1.00      ( v3_pre_topc(X0,X1)
% 3.76/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.76/1.00      | ~ v2_pre_topc(X1)
% 3.76/1.00      | ~ l1_pre_topc(X1)
% 3.76/1.00      | ~ v1_xboole_0(X0) ),
% 3.76/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_25,negated_conjecture,
% 3.76/1.00      ( v2_pre_topc(sK4) ),
% 3.76/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_285,plain,
% 3.76/1.00      ( v3_pre_topc(X0,X1)
% 3.76/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.76/1.00      | ~ l1_pre_topc(X1)
% 3.76/1.00      | ~ v1_xboole_0(X0)
% 3.76/1.00      | sK4 != X1 ),
% 3.76/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_25]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_286,plain,
% 3.76/1.00      ( v3_pre_topc(X0,sK4)
% 3.76/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.76/1.00      | ~ l1_pre_topc(sK4)
% 3.76/1.00      | ~ v1_xboole_0(X0) ),
% 3.76/1.00      inference(unflattening,[status(thm)],[c_285]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_290,plain,
% 3.76/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.76/1.00      | v3_pre_topc(X0,sK4)
% 3.76/1.00      | ~ v1_xboole_0(X0) ),
% 3.76/1.00      inference(global_propositional_subsumption,
% 3.76/1.00                [status(thm)],
% 3.76/1.00                [c_286,c_24]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_291,plain,
% 3.76/1.00      ( v3_pre_topc(X0,sK4)
% 3.76/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.76/1.00      | ~ v1_xboole_0(X0) ),
% 3.76/1.00      inference(renaming,[status(thm)],[c_290]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_362,plain,
% 3.76/1.00      ( v3_pre_topc(X0,sK4)
% 3.76/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.76/1.00      | sK5 != X0 ),
% 3.76/1.00      inference(resolution_lifted,[status(thm)],[c_291,c_23]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_363,plain,
% 3.76/1.00      ( v3_pre_topc(sK5,sK4)
% 3.76/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 3.76/1.00      inference(unflattening,[status(thm)],[c_362]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_364,plain,
% 3.76/1.00      ( v3_pre_topc(sK5,sK4) = iProver_top
% 3.76/1.00      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_363]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_373,plain,
% 3.76/1.00      ( sK5 != X0 | k1_xboole_0 = X0 ),
% 3.76/1.00      inference(resolution_lifted,[status(thm)],[c_5,c_23]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_374,plain,
% 3.76/1.00      ( k1_xboole_0 = sK5 ),
% 3.76/1.00      inference(unflattening,[status(thm)],[c_373]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2222,plain,
% 3.76/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_11]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2226,plain,
% 3.76/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_2222]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1582,plain,
% 3.76/1.00      ( ~ v3_pre_topc(X0,X1) | v3_pre_topc(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.76/1.00      theory(equality) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2284,plain,
% 3.76/1.00      ( v3_pre_topc(X0,X1)
% 3.76/1.00      | ~ v3_pre_topc(sK5,sK4)
% 3.76/1.00      | X1 != sK4
% 3.76/1.00      | X0 != sK5 ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_1582]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2715,plain,
% 3.76/1.00      ( ~ v3_pre_topc(sK5,sK4)
% 3.76/1.00      | v3_pre_topc(k1_xboole_0,X0)
% 3.76/1.00      | X0 != sK4
% 3.76/1.00      | k1_xboole_0 != sK5 ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_2284]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2716,plain,
% 3.76/1.00      ( X0 != sK4
% 3.76/1.00      | k1_xboole_0 != sK5
% 3.76/1.00      | v3_pre_topc(sK5,sK4) != iProver_top
% 3.76/1.00      | v3_pre_topc(k1_xboole_0,X0) = iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_2715]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2718,plain,
% 3.76/1.00      ( sK4 != sK4
% 3.76/1.00      | k1_xboole_0 != sK5
% 3.76/1.00      | v3_pre_topc(sK5,sK4) != iProver_top
% 3.76/1.00      | v3_pre_topc(k1_xboole_0,sK4) = iProver_top ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_2716]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_4962,plain,
% 3.76/1.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.76/1.00      | sK2(sK4,X0) != k3_xboole_0(X0,k1_xboole_0)
% 3.76/1.00      | v2_tex_2(X0,sK4) = iProver_top ),
% 3.76/1.00      inference(global_propositional_subsumption,
% 3.76/1.00                [status(thm)],
% 3.76/1.00                [c_4606,c_29,c_68,c_72,c_364,c_374,c_2226,c_2718]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_4963,plain,
% 3.76/1.00      ( sK2(sK4,X0) != k3_xboole_0(X0,k1_xboole_0)
% 3.76/1.00      | v2_tex_2(X0,sK4) = iProver_top
% 3.76/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 3.76/1.00      inference(renaming,[status(thm)],[c_4962]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_9916,plain,
% 3.76/1.00      ( sK2(sK4,X0) != k1_xboole_0
% 3.76/1.00      | v2_tex_2(X0,sK4) = iProver_top
% 3.76/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 3.76/1.00      inference(demodulation,[status(thm)],[c_8831,c_4963]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_10322,plain,
% 3.76/1.00      ( v2_tex_2(k1_xboole_0,sK4) = iProver_top
% 3.76/1.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 3.76/1.00      inference(superposition,[status(thm)],[c_6691,c_9916]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2023,plain,
% 3.76/1.00      ( v2_tex_2(sK5,sK4) != iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2799,plain,
% 3.76/1.00      ( v2_tex_2(k1_xboole_0,sK4) != iProver_top ),
% 3.76/1.00      inference(demodulation,[status(thm)],[c_2657,c_2023]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(contradiction,plain,
% 3.76/1.00      ( $false ),
% 3.76/1.00      inference(minisat,[status(thm)],[c_10322,c_2799,c_2226]) ).
% 3.76/1.00  
% 3.76/1.00  
% 3.76/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.76/1.00  
% 3.76/1.00  ------                               Statistics
% 3.76/1.00  
% 3.76/1.00  ------ General
% 3.76/1.00  
% 3.76/1.00  abstr_ref_over_cycles:                  0
% 3.76/1.00  abstr_ref_under_cycles:                 0
% 3.76/1.00  gc_basic_clause_elim:                   0
% 3.76/1.00  forced_gc_time:                         0
% 3.76/1.00  parsing_time:                           0.011
% 3.76/1.00  unif_index_cands_time:                  0.
% 3.76/1.00  unif_index_add_time:                    0.
% 3.76/1.00  orderings_time:                         0.
% 3.76/1.00  out_proof_time:                         0.011
% 3.76/1.00  total_time:                             0.39
% 3.76/1.00  num_of_symbols:                         50
% 3.76/1.00  num_of_terms:                           10621
% 3.76/1.00  
% 3.76/1.00  ------ Preprocessing
% 3.76/1.00  
% 3.76/1.00  num_of_splits:                          0
% 3.76/1.00  num_of_split_atoms:                     0
% 3.76/1.00  num_of_reused_defs:                     0
% 3.76/1.00  num_eq_ax_congr_red:                    36
% 3.76/1.00  num_of_sem_filtered_clauses:            1
% 3.76/1.00  num_of_subtypes:                        0
% 3.76/1.00  monotx_restored_types:                  0
% 3.76/1.00  sat_num_of_epr_types:                   0
% 3.76/1.00  sat_num_of_non_cyclic_types:            0
% 3.76/1.00  sat_guarded_non_collapsed_types:        0
% 3.76/1.00  num_pure_diseq_elim:                    0
% 3.76/1.00  simp_replaced_by:                       0
% 3.76/1.00  res_preprocessed:                       121
% 3.76/1.00  prep_upred:                             0
% 3.76/1.00  prep_unflattend:                        33
% 3.76/1.00  smt_new_axioms:                         0
% 3.76/1.00  pred_elim_cands:                        6
% 3.76/1.00  pred_elim:                              2
% 3.76/1.00  pred_elim_cl:                           2
% 3.76/1.00  pred_elim_cycles:                       9
% 3.76/1.00  merged_defs:                            0
% 3.76/1.00  merged_defs_ncl:                        0
% 3.76/1.00  bin_hyper_res:                          0
% 3.76/1.00  prep_cycles:                            4
% 3.76/1.00  pred_elim_time:                         0.033
% 3.76/1.00  splitting_time:                         0.
% 3.76/1.00  sem_filter_time:                        0.
% 3.76/1.00  monotx_time:                            0.001
% 3.76/1.00  subtype_inf_time:                       0.
% 3.76/1.00  
% 3.76/1.00  ------ Problem properties
% 3.76/1.00  
% 3.76/1.00  clauses:                                23
% 3.76/1.00  conjectures:                            3
% 3.76/1.00  epr:                                    7
% 3.76/1.00  horn:                                   19
% 3.76/1.00  ground:                                 3
% 3.76/1.00  unary:                                  5
% 3.76/1.00  binary:                                 7
% 3.76/1.00  lits:                                   60
% 3.76/1.00  lits_eq:                                5
% 3.76/1.00  fd_pure:                                0
% 3.76/1.00  fd_pseudo:                              0
% 3.76/1.00  fd_cond:                                1
% 3.76/1.00  fd_pseudo_cond:                         1
% 3.76/1.00  ac_symbols:                             0
% 3.76/1.00  
% 3.76/1.00  ------ Propositional Solver
% 3.76/1.00  
% 3.76/1.00  prop_solver_calls:                      28
% 3.76/1.00  prop_fast_solver_calls:                 1243
% 3.76/1.00  smt_solver_calls:                       0
% 3.76/1.00  smt_fast_solver_calls:                  0
% 3.76/1.00  prop_num_of_clauses:                    4277
% 3.76/1.00  prop_preprocess_simplified:             9481
% 3.76/1.00  prop_fo_subsumed:                       20
% 3.76/1.00  prop_solver_time:                       0.
% 3.76/1.00  smt_solver_time:                        0.
% 3.76/1.00  smt_fast_solver_time:                   0.
% 3.76/1.00  prop_fast_solver_time:                  0.
% 3.76/1.00  prop_unsat_core_time:                   0.
% 3.76/1.00  
% 3.76/1.00  ------ QBF
% 3.76/1.00  
% 3.76/1.00  qbf_q_res:                              0
% 3.76/1.00  qbf_num_tautologies:                    0
% 3.76/1.00  qbf_prep_cycles:                        0
% 3.76/1.00  
% 3.76/1.00  ------ BMC1
% 3.76/1.00  
% 3.76/1.00  bmc1_current_bound:                     -1
% 3.76/1.00  bmc1_last_solved_bound:                 -1
% 3.76/1.00  bmc1_unsat_core_size:                   -1
% 3.76/1.00  bmc1_unsat_core_parents_size:           -1
% 3.76/1.00  bmc1_merge_next_fun:                    0
% 3.76/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.76/1.00  
% 3.76/1.00  ------ Instantiation
% 3.76/1.00  
% 3.76/1.00  inst_num_of_clauses:                    1035
% 3.76/1.00  inst_num_in_passive:                    271
% 3.76/1.00  inst_num_in_active:                     356
% 3.76/1.00  inst_num_in_unprocessed:                410
% 3.76/1.00  inst_num_of_loops:                      440
% 3.76/1.00  inst_num_of_learning_restarts:          0
% 3.76/1.00  inst_num_moves_active_passive:          82
% 3.76/1.00  inst_lit_activity:                      0
% 3.76/1.00  inst_lit_activity_moves:                0
% 3.76/1.00  inst_num_tautologies:                   0
% 3.76/1.00  inst_num_prop_implied:                  0
% 3.76/1.00  inst_num_existing_simplified:           0
% 3.76/1.00  inst_num_eq_res_simplified:             0
% 3.76/1.00  inst_num_child_elim:                    0
% 3.76/1.00  inst_num_of_dismatching_blockings:      156
% 3.76/1.00  inst_num_of_non_proper_insts:           978
% 3.76/1.00  inst_num_of_duplicates:                 0
% 3.76/1.00  inst_inst_num_from_inst_to_res:         0
% 3.76/1.00  inst_dismatching_checking_time:         0.
% 3.76/1.00  
% 3.76/1.00  ------ Resolution
% 3.76/1.00  
% 3.76/1.00  res_num_of_clauses:                     0
% 3.76/1.00  res_num_in_passive:                     0
% 3.76/1.00  res_num_in_active:                      0
% 3.76/1.00  res_num_of_loops:                       125
% 3.76/1.00  res_forward_subset_subsumed:            49
% 3.76/1.00  res_backward_subset_subsumed:           4
% 3.76/1.00  res_forward_subsumed:                   0
% 3.76/1.00  res_backward_subsumed:                  0
% 3.76/1.00  res_forward_subsumption_resolution:     2
% 3.76/1.00  res_backward_subsumption_resolution:    0
% 3.76/1.00  res_clause_to_clause_subsumption:       1033
% 3.76/1.00  res_orphan_elimination:                 0
% 3.76/1.00  res_tautology_del:                      23
% 3.76/1.00  res_num_eq_res_simplified:              0
% 3.76/1.00  res_num_sel_changes:                    0
% 3.76/1.00  res_moves_from_active_to_pass:          0
% 3.76/1.00  
% 3.76/1.00  ------ Superposition
% 3.76/1.00  
% 3.76/1.00  sup_time_total:                         0.
% 3.76/1.00  sup_time_generating:                    0.
% 3.76/1.00  sup_time_sim_full:                      0.
% 3.76/1.00  sup_time_sim_immed:                     0.
% 3.76/1.00  
% 3.76/1.00  sup_num_of_clauses:                     144
% 3.76/1.00  sup_num_in_active:                      65
% 3.76/1.00  sup_num_in_passive:                     79
% 3.76/1.00  sup_num_of_loops:                       86
% 3.76/1.00  sup_fw_superposition:                   103
% 3.76/1.00  sup_bw_superposition:                   70
% 3.76/1.00  sup_immediate_simplified:               35
% 3.76/1.00  sup_given_eliminated:                   2
% 3.76/1.00  comparisons_done:                       0
% 3.76/1.00  comparisons_avoided:                    0
% 3.76/1.00  
% 3.76/1.00  ------ Simplifications
% 3.76/1.00  
% 3.76/1.00  
% 3.76/1.00  sim_fw_subset_subsumed:                 12
% 3.76/1.00  sim_bw_subset_subsumed:                 4
% 3.76/1.00  sim_fw_subsumed:                        10
% 3.76/1.00  sim_bw_subsumed:                        1
% 3.76/1.00  sim_fw_subsumption_res:                 2
% 3.76/1.00  sim_bw_subsumption_res:                 0
% 3.76/1.00  sim_tautology_del:                      10
% 3.76/1.00  sim_eq_tautology_del:                   2
% 3.76/1.00  sim_eq_res_simp:                        0
% 3.76/1.00  sim_fw_demodulated:                     7
% 3.76/1.00  sim_bw_demodulated:                     20
% 3.76/1.00  sim_light_normalised:                   15
% 3.76/1.00  sim_joinable_taut:                      0
% 3.76/1.00  sim_joinable_simp:                      0
% 3.76/1.00  sim_ac_normalised:                      0
% 3.76/1.00  sim_smt_subsumption:                    0
% 3.76/1.00  
%------------------------------------------------------------------------------
