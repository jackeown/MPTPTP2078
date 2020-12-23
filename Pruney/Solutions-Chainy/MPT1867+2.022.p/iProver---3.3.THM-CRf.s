%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:26:10 EST 2020

% Result     : Theorem 3.44s
% Output     : CNFRefutation 3.44s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 475 expanded)
%              Number of clauses        :   76 ( 143 expanded)
%              Number of leaves         :   17 ( 111 expanded)
%              Depth                    :   19
%              Number of atoms          :  420 (2075 expanded)
%              Number of equality atoms :   90 ( 194 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f49,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
     => ( ~ v2_tex_2(sK5,X0)
        & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
        & v1_xboole_0(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
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

fof(f50,plain,
    ( ~ v2_tex_2(sK5,sK4)
    & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    & v1_xboole_0(sK5)
    & l1_pre_topc(sK4)
    & v2_pre_topc(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f33,f49,f48])).

fof(f78,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f50])).

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
                            & v3_pre_topc(X3,X0) ) )
                    & r1_tarski(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f44,plain,(
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
    inference(rectify,[],[f43])).

fof(f46,plain,(
    ! [X4,X1,X0] :
      ( ? [X5] :
          ( k9_subset_1(u1_struct_0(X0),X1,X5) = X4
          & v3_pre_topc(X5,X0)
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X0),X1,sK3(X0,X1,X4)) = X4
        & v3_pre_topc(sK3(X0,X1,X4),X0)
        & m1_subset_1(sK3(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
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

fof(f47,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f44,f46,f45])).

fof(f73,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | r1_tarski(sK2(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f76,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f50])).

fof(f79,plain,(
    ~ v2_tex_2(sK5,sK4) ),
    inference(cnf_transformation,[],[f50])).

fof(f77,plain,(
    v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f50])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f56,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f34])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f35,f36])).

fof(f52,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f38])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f39,f40])).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f51,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f10,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f74,plain,(
    ! [X0,X3,X1] :
      ( v2_tex_2(X1,X0)
      | k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1)
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v3_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f75,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_3620,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_19,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(sK2(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_27,negated_conjecture,
    ( l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_661,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(sK2(X1,X0),X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_27])).

cnf(c_662,plain,
    ( v2_tex_2(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | r1_tarski(sK2(sK4,X0),X0) ),
    inference(unflattening,[status(thm)],[c_661])).

cnf(c_3609,plain,
    ( v2_tex_2(X0,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r1_tarski(sK2(sK4,X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_662])).

cnf(c_4119,plain,
    ( v2_tex_2(sK5,sK4) = iProver_top
    | r1_tarski(sK2(sK4,sK5),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_3620,c_3609])).

cnf(c_32,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_24,negated_conjecture,
    ( ~ v2_tex_2(sK5,sK4) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1007,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | r1_tarski(sK2(sK4,X0),X0)
    | sK4 != sK4
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_662])).

cnf(c_1008,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | r1_tarski(sK2(sK4,sK5),sK5) ),
    inference(unflattening,[status(thm)],[c_1007])).

cnf(c_1009,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r1_tarski(sK2(sK4,sK5),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1008])).

cnf(c_4552,plain,
    ( r1_tarski(sK2(sK4,sK5),sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4119,c_32,c_1009])).

cnf(c_26,negated_conjecture,
    ( v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_3619,plain,
    ( v1_xboole_0(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_5,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_3628,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4405,plain,
    ( sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3619,c_3628])).

cnf(c_4556,plain,
    ( r1_tarski(sK2(sK4,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4552,c_4405])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_3633,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_13,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_227,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_13])).

cnf(c_228,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_227])).

cnf(c_278,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(bin_hyper_res,[status(thm)],[c_16,c_228])).

cnf(c_3615,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_278])).

cnf(c_4792,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3633,c_3615])).

cnf(c_8455,plain,
    ( v1_xboole_0(sK2(sK4,k1_xboole_0)) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4556,c_4792])).

cnf(c_4410,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4405,c_3619])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_5042,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_hidden(sK0(X0),X1)
    | v1_xboole_0(X0) ),
    inference(resolution,[status(thm)],[c_4,c_0])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_5513,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(resolution,[status(thm)],[c_5042,c_1])).

cnf(c_12,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_4127,plain,
    ( v2_tex_2(k1_xboole_0,sK4)
    | r1_tarski(sK2(sK4,k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12,c_662])).

cnf(c_3875,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_3876,plain,
    ( v2_tex_2(k1_xboole_0,sK4)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4)))
    | r1_tarski(sK2(sK4,k1_xboole_0),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_662])).

cnf(c_3621,plain,
    ( v2_tex_2(sK5,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_4409,plain,
    ( v2_tex_2(k1_xboole_0,sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4405,c_3621])).

cnf(c_4419,plain,
    ( ~ v2_tex_2(k1_xboole_0,sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4409])).

cnf(c_4435,plain,
    ( r1_tarski(sK2(sK4,k1_xboole_0),k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4127,c_3875,c_3876,c_4419])).

cnf(c_5537,plain,
    ( v1_xboole_0(sK2(sK4,k1_xboole_0))
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_5513,c_4435])).

cnf(c_5538,plain,
    ( v1_xboole_0(sK2(sK4,k1_xboole_0)) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5537])).

cnf(c_9485,plain,
    ( v1_xboole_0(sK2(sK4,k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8455,c_4410,c_5538])).

cnf(c_9491,plain,
    ( sK2(sK4,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_9485,c_3628])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X2) = X2 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_274,plain,
    ( ~ r1_tarski(X0,X1)
    | k9_subset_1(X1,X2,X2) = X2 ),
    inference(bin_hyper_res,[status(thm)],[c_10,c_228])).

cnf(c_3617,plain,
    ( k9_subset_1(X0,X1,X1) = X1
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_274])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_8,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_4800,plain,
    ( r1_tarski(k2_subset_1(X0),X0) ),
    inference(resolution,[status(thm)],[c_14,c_8])).

cnf(c_11263,plain,
    ( k9_subset_1(X0,X1,X1) = X1 ),
    inference(resolution,[status(thm)],[c_274,c_4800])).

cnf(c_12046,plain,
    ( k9_subset_1(X0,X1,X1) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3617,c_11263])).

cnf(c_18,plain,
    ( v2_tex_2(X0,X1)
    | ~ v3_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),X0,X2) != sK2(X1,X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_676,plain,
    ( v2_tex_2(X0,X1)
    | ~ v3_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | k9_subset_1(u1_struct_0(X1),X0,X2) != sK2(X1,X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_27])).

cnf(c_677,plain,
    ( v2_tex_2(X0,sK4)
    | ~ v3_pre_topc(X1,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | k9_subset_1(u1_struct_0(sK4),X0,X1) != sK2(sK4,X0) ),
    inference(unflattening,[status(thm)],[c_676])).

cnf(c_3608,plain,
    ( k9_subset_1(u1_struct_0(sK4),X0,X1) != sK2(sK4,X0)
    | v2_tex_2(X0,sK4) = iProver_top
    | v3_pre_topc(X1,sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_677])).

cnf(c_12053,plain,
    ( sK2(sK4,X0) != X0
    | v2_tex_2(X0,sK4) = iProver_top
    | v3_pre_topc(X0,sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_12046,c_3608])).

cnf(c_12709,plain,
    ( v2_tex_2(k1_xboole_0,sK4) = iProver_top
    | v3_pre_topc(k1_xboole_0,sK4) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_9491,c_12053])).

cnf(c_17,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_28,negated_conjecture,
    ( v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_383,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_28])).

cnf(c_384,plain,
    ( v3_pre_topc(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_pre_topc(sK4)
    | ~ v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_383])).

cnf(c_388,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | v3_pre_topc(X0,sK4)
    | ~ v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_384,c_27])).

cnf(c_389,plain,
    ( v3_pre_topc(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_388])).

cnf(c_3614,plain,
    ( v3_pre_topc(X0,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_389])).

cnf(c_3910,plain,
    ( v3_pre_topc(sK5,sK4) = iProver_top
    | v1_xboole_0(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3620,c_3614])).

cnf(c_460,plain,
    ( v3_pre_topc(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_389,c_26])).

cnf(c_461,plain,
    ( v3_pre_topc(sK5,sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(unflattening,[status(thm)],[c_460])).

cnf(c_462,plain,
    ( v3_pre_topc(sK5,sK4) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_461])).

cnf(c_3969,plain,
    ( v3_pre_topc(sK5,sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3910,c_32,c_462])).

cnf(c_4407,plain,
    ( v3_pre_topc(k1_xboole_0,sK4) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4405,c_3969])).

cnf(c_3879,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3875])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12709,c_4409,c_4407,c_3879])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:14:17 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.44/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.44/0.99  
% 3.44/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.44/0.99  
% 3.44/0.99  ------  iProver source info
% 3.44/0.99  
% 3.44/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.44/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.44/0.99  git: non_committed_changes: false
% 3.44/0.99  git: last_make_outside_of_git: false
% 3.44/0.99  
% 3.44/0.99  ------ 
% 3.44/0.99  ------ Parsing...
% 3.44/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.44/0.99  
% 3.44/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.44/0.99  
% 3.44/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.44/0.99  
% 3.44/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.44/0.99  ------ Proving...
% 3.44/0.99  ------ Problem Properties 
% 3.44/0.99  
% 3.44/0.99  
% 3.44/0.99  clauses                                 27
% 3.44/0.99  conjectures                             3
% 3.44/0.99  EPR                                     6
% 3.44/0.99  Horn                                    23
% 3.44/0.99  unary                                   6
% 3.44/0.99  binary                                  11
% 3.44/0.99  lits                                    66
% 3.44/0.99  lits eq                                 7
% 3.44/0.99  fd_pure                                 0
% 3.44/0.99  fd_pseudo                               0
% 3.44/0.99  fd_cond                                 1
% 3.44/0.99  fd_pseudo_cond                          0
% 3.44/0.99  AC symbols                              0
% 3.44/0.99  
% 3.44/0.99  ------ Input Options Time Limit: Unbounded
% 3.44/0.99  
% 3.44/0.99  
% 3.44/0.99  ------ 
% 3.44/0.99  Current options:
% 3.44/0.99  ------ 
% 3.44/0.99  
% 3.44/0.99  
% 3.44/0.99  
% 3.44/0.99  
% 3.44/0.99  ------ Proving...
% 3.44/0.99  
% 3.44/0.99  
% 3.44/0.99  % SZS status Theorem for theBenchmark.p
% 3.44/0.99  
% 3.44/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.44/0.99  
% 3.44/0.99  fof(f16,conjecture,(
% 3.44/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 3.44/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.44/0.99  
% 3.44/0.99  fof(f17,negated_conjecture,(
% 3.44/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 3.44/0.99    inference(negated_conjecture,[],[f16])).
% 3.44/0.99  
% 3.44/0.99  fof(f18,plain,(
% 3.44/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 3.44/0.99    inference(pure_predicate_removal,[],[f17])).
% 3.44/0.99  
% 3.44/0.99  fof(f32,plain,(
% 3.44/0.99    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.44/0.99    inference(ennf_transformation,[],[f18])).
% 3.44/0.99  
% 3.44/0.99  fof(f33,plain,(
% 3.44/0.99    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.44/0.99    inference(flattening,[],[f32])).
% 3.44/0.99  
% 3.44/0.99  fof(f49,plain,(
% 3.44/0.99    ( ! [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => (~v2_tex_2(sK5,X0) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(sK5))) )),
% 3.44/0.99    introduced(choice_axiom,[])).
% 3.44/0.99  
% 3.44/0.99  fof(f48,plain,(
% 3.44/0.99    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (~v2_tex_2(X1,sK4) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) & v1_xboole_0(X1)) & l1_pre_topc(sK4) & v2_pre_topc(sK4))),
% 3.44/0.99    introduced(choice_axiom,[])).
% 3.44/0.99  
% 3.44/0.99  fof(f50,plain,(
% 3.44/0.99    (~v2_tex_2(sK5,sK4) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) & v1_xboole_0(sK5)) & l1_pre_topc(sK4) & v2_pre_topc(sK4)),
% 3.44/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f33,f49,f48])).
% 3.44/0.99  
% 3.44/0.99  fof(f78,plain,(
% 3.44/0.99    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))),
% 3.44/0.99    inference(cnf_transformation,[],[f50])).
% 3.44/0.99  
% 3.44/0.99  fof(f15,axiom,(
% 3.44/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0))) & r1_tarski(X2,X1))))))),
% 3.44/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.44/0.99  
% 3.44/0.99  fof(f30,plain,(
% 3.44/0.99    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((? [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.44/0.99    inference(ennf_transformation,[],[f15])).
% 3.44/0.99  
% 3.44/0.99  fof(f31,plain,(
% 3.44/0.99    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.44/0.99    inference(flattening,[],[f30])).
% 3.44/0.99  
% 3.44/0.99  fof(f43,plain,(
% 3.44/0.99    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.44/0.99    inference(nnf_transformation,[],[f31])).
% 3.44/0.99  
% 3.44/0.99  fof(f44,plain,(
% 3.44/0.99    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (? [X5] : (k9_subset_1(u1_struct_0(X0),X1,X5) = X4 & v3_pre_topc(X5,X0) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.44/0.99    inference(rectify,[],[f43])).
% 3.44/0.99  
% 3.44/0.99  fof(f46,plain,(
% 3.44/0.99    ! [X4,X1,X0] : (? [X5] : (k9_subset_1(u1_struct_0(X0),X1,X5) = X4 & v3_pre_topc(X5,X0) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) => (k9_subset_1(u1_struct_0(X0),X1,sK3(X0,X1,X4)) = X4 & v3_pre_topc(sK3(X0,X1,X4),X0) & m1_subset_1(sK3(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.44/0.99    introduced(choice_axiom,[])).
% 3.44/0.99  
% 3.44/0.99  fof(f45,plain,(
% 3.44/0.99    ! [X1,X0] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(sK2(X0,X1),X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.44/0.99    introduced(choice_axiom,[])).
% 3.44/0.99  
% 3.44/0.99  fof(f47,plain,(
% 3.44/0.99    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(sK2(X0,X1),X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : ((k9_subset_1(u1_struct_0(X0),X1,sK3(X0,X1,X4)) = X4 & v3_pre_topc(sK3(X0,X1,X4),X0) & m1_subset_1(sK3(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.44/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f44,f46,f45])).
% 3.44/0.99  
% 3.44/0.99  fof(f73,plain,(
% 3.44/0.99    ( ! [X0,X1] : (v2_tex_2(X1,X0) | r1_tarski(sK2(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.44/0.99    inference(cnf_transformation,[],[f47])).
% 3.44/0.99  
% 3.44/0.99  fof(f76,plain,(
% 3.44/0.99    l1_pre_topc(sK4)),
% 3.44/0.99    inference(cnf_transformation,[],[f50])).
% 3.44/0.99  
% 3.44/0.99  fof(f79,plain,(
% 3.44/0.99    ~v2_tex_2(sK5,sK4)),
% 3.44/0.99    inference(cnf_transformation,[],[f50])).
% 3.44/0.99  
% 3.44/0.99  fof(f77,plain,(
% 3.44/0.99    v1_xboole_0(sK5)),
% 3.44/0.99    inference(cnf_transformation,[],[f50])).
% 3.44/0.99  
% 3.44/0.99  fof(f3,axiom,(
% 3.44/0.99    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 3.44/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.44/0.99  
% 3.44/0.99  fof(f20,plain,(
% 3.44/0.99    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 3.44/0.99    inference(ennf_transformation,[],[f3])).
% 3.44/0.99  
% 3.44/0.99  fof(f56,plain,(
% 3.44/0.99    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 3.44/0.99    inference(cnf_transformation,[],[f20])).
% 3.44/0.99  
% 3.44/0.99  fof(f1,axiom,(
% 3.44/0.99    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.44/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.44/0.99  
% 3.44/0.99  fof(f34,plain,(
% 3.44/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.44/0.99    inference(nnf_transformation,[],[f1])).
% 3.44/0.99  
% 3.44/0.99  fof(f35,plain,(
% 3.44/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.44/0.99    inference(rectify,[],[f34])).
% 3.44/0.99  
% 3.44/0.99  fof(f36,plain,(
% 3.44/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.44/0.99    introduced(choice_axiom,[])).
% 3.44/0.99  
% 3.44/0.99  fof(f37,plain,(
% 3.44/0.99    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.44/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f35,f36])).
% 3.44/0.99  
% 3.44/0.99  fof(f52,plain,(
% 3.44/0.99    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 3.44/0.99    inference(cnf_transformation,[],[f37])).
% 3.44/0.99  
% 3.44/0.99  fof(f13,axiom,(
% 3.44/0.99    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 3.44/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.44/0.99  
% 3.44/0.99  fof(f27,plain,(
% 3.44/0.99    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.44/0.99    inference(ennf_transformation,[],[f13])).
% 3.44/0.99  
% 3.44/0.99  fof(f67,plain,(
% 3.44/0.99    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.44/0.99    inference(cnf_transformation,[],[f27])).
% 3.44/0.99  
% 3.44/0.99  fof(f11,axiom,(
% 3.44/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.44/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.44/0.99  
% 3.44/0.99  fof(f42,plain,(
% 3.44/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.44/0.99    inference(nnf_transformation,[],[f11])).
% 3.44/0.99  
% 3.44/0.99  fof(f65,plain,(
% 3.44/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.44/0.99    inference(cnf_transformation,[],[f42])).
% 3.44/0.99  
% 3.44/0.99  fof(f2,axiom,(
% 3.44/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.44/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.44/0.99  
% 3.44/0.99  fof(f19,plain,(
% 3.44/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.44/0.99    inference(ennf_transformation,[],[f2])).
% 3.44/0.99  
% 3.44/0.99  fof(f38,plain,(
% 3.44/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.44/0.99    inference(nnf_transformation,[],[f19])).
% 3.44/0.99  
% 3.44/0.99  fof(f39,plain,(
% 3.44/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.44/0.99    inference(rectify,[],[f38])).
% 3.44/0.99  
% 3.44/0.99  fof(f40,plain,(
% 3.44/0.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 3.44/0.99    introduced(choice_axiom,[])).
% 3.44/0.99  
% 3.44/0.99  fof(f41,plain,(
% 3.44/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.44/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f39,f40])).
% 3.44/0.99  
% 3.44/0.99  fof(f53,plain,(
% 3.44/0.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.44/0.99    inference(cnf_transformation,[],[f41])).
% 3.44/0.99  
% 3.44/0.99  fof(f51,plain,(
% 3.44/0.99    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 3.44/0.99    inference(cnf_transformation,[],[f37])).
% 3.44/0.99  
% 3.44/0.99  fof(f10,axiom,(
% 3.44/0.99    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.44/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.44/0.99  
% 3.44/0.99  fof(f63,plain,(
% 3.44/0.99    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.44/0.99    inference(cnf_transformation,[],[f10])).
% 3.44/0.99  
% 3.44/0.99  fof(f8,axiom,(
% 3.44/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X1) = X1)),
% 3.44/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.44/0.99  
% 3.44/0.99  fof(f23,plain,(
% 3.44/0.99    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 3.44/0.99    inference(ennf_transformation,[],[f8])).
% 3.44/0.99  
% 3.44/0.99  fof(f61,plain,(
% 3.44/0.99    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.44/0.99    inference(cnf_transformation,[],[f23])).
% 3.44/0.99  
% 3.44/0.99  fof(f64,plain,(
% 3.44/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.44/0.99    inference(cnf_transformation,[],[f42])).
% 3.44/0.99  
% 3.44/0.99  fof(f6,axiom,(
% 3.44/0.99    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 3.44/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.44/0.99  
% 3.44/0.99  fof(f59,plain,(
% 3.44/0.99    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 3.44/0.99    inference(cnf_transformation,[],[f6])).
% 3.44/0.99  
% 3.44/0.99  fof(f74,plain,(
% 3.44/0.99    ( ! [X0,X3,X1] : (v2_tex_2(X1,X0) | k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.44/0.99    inference(cnf_transformation,[],[f47])).
% 3.44/0.99  
% 3.44/0.99  fof(f14,axiom,(
% 3.44/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_xboole_0(X1) => v3_pre_topc(X1,X0))))),
% 3.44/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.44/0.99  
% 3.44/0.99  fof(f28,plain,(
% 3.44/0.99    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) | ~v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.44/0.99    inference(ennf_transformation,[],[f14])).
% 3.44/0.99  
% 3.44/0.99  fof(f29,plain,(
% 3.44/0.99    ! [X0] : (! [X1] : (v3_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.44/0.99    inference(flattening,[],[f28])).
% 3.44/0.99  
% 3.44/0.99  fof(f68,plain,(
% 3.44/0.99    ( ! [X0,X1] : (v3_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.44/0.99    inference(cnf_transformation,[],[f29])).
% 3.44/0.99  
% 3.44/0.99  fof(f75,plain,(
% 3.44/0.99    v2_pre_topc(sK4)),
% 3.44/0.99    inference(cnf_transformation,[],[f50])).
% 3.44/0.99  
% 3.44/0.99  cnf(c_25,negated_conjecture,
% 3.44/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 3.44/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_3620,plain,
% 3.44/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 3.44/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_19,plain,
% 3.44/0.99      ( v2_tex_2(X0,X1)
% 3.44/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.44/0.99      | r1_tarski(sK2(X1,X0),X0)
% 3.44/0.99      | ~ l1_pre_topc(X1) ),
% 3.44/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_27,negated_conjecture,
% 3.44/0.99      ( l1_pre_topc(sK4) ),
% 3.44/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_661,plain,
% 3.44/0.99      ( v2_tex_2(X0,X1)
% 3.44/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.44/0.99      | r1_tarski(sK2(X1,X0),X0)
% 3.44/0.99      | sK4 != X1 ),
% 3.44/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_27]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_662,plain,
% 3.44/0.99      ( v2_tex_2(X0,sK4)
% 3.44/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.44/0.99      | r1_tarski(sK2(sK4,X0),X0) ),
% 3.44/0.99      inference(unflattening,[status(thm)],[c_661]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_3609,plain,
% 3.44/0.99      ( v2_tex_2(X0,sK4) = iProver_top
% 3.44/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.44/0.99      | r1_tarski(sK2(sK4,X0),X0) = iProver_top ),
% 3.44/0.99      inference(predicate_to_equality,[status(thm)],[c_662]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_4119,plain,
% 3.44/0.99      ( v2_tex_2(sK5,sK4) = iProver_top
% 3.44/0.99      | r1_tarski(sK2(sK4,sK5),sK5) = iProver_top ),
% 3.44/0.99      inference(superposition,[status(thm)],[c_3620,c_3609]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_32,plain,
% 3.44/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 3.44/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_24,negated_conjecture,
% 3.44/0.99      ( ~ v2_tex_2(sK5,sK4) ),
% 3.44/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_1007,plain,
% 3.44/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.44/0.99      | r1_tarski(sK2(sK4,X0),X0)
% 3.44/0.99      | sK4 != sK4
% 3.44/0.99      | sK5 != X0 ),
% 3.44/0.99      inference(resolution_lifted,[status(thm)],[c_24,c_662]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_1008,plain,
% 3.44/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.44/0.99      | r1_tarski(sK2(sK4,sK5),sK5) ),
% 3.44/0.99      inference(unflattening,[status(thm)],[c_1007]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_1009,plain,
% 3.44/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.44/0.99      | r1_tarski(sK2(sK4,sK5),sK5) = iProver_top ),
% 3.44/0.99      inference(predicate_to_equality,[status(thm)],[c_1008]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_4552,plain,
% 3.44/0.99      ( r1_tarski(sK2(sK4,sK5),sK5) = iProver_top ),
% 3.44/0.99      inference(global_propositional_subsumption,
% 3.44/0.99                [status(thm)],
% 3.44/0.99                [c_4119,c_32,c_1009]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_26,negated_conjecture,
% 3.44/0.99      ( v1_xboole_0(sK5) ),
% 3.44/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_3619,plain,
% 3.44/0.99      ( v1_xboole_0(sK5) = iProver_top ),
% 3.44/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_5,plain,
% 3.44/0.99      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 3.44/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_3628,plain,
% 3.44/0.99      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 3.44/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_4405,plain,
% 3.44/0.99      ( sK5 = k1_xboole_0 ),
% 3.44/0.99      inference(superposition,[status(thm)],[c_3619,c_3628]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_4556,plain,
% 3.44/0.99      ( r1_tarski(sK2(sK4,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 3.44/0.99      inference(light_normalisation,[status(thm)],[c_4552,c_4405]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_0,plain,
% 3.44/0.99      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 3.44/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_3633,plain,
% 3.44/0.99      ( r2_hidden(sK0(X0),X0) = iProver_top
% 3.44/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.44/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_16,plain,
% 3.44/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.44/0.99      | ~ r2_hidden(X2,X0)
% 3.44/0.99      | ~ v1_xboole_0(X1) ),
% 3.44/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_13,plain,
% 3.44/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.44/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_227,plain,
% 3.44/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.44/0.99      inference(prop_impl,[status(thm)],[c_13]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_228,plain,
% 3.44/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.44/0.99      inference(renaming,[status(thm)],[c_227]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_278,plain,
% 3.44/0.99      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | ~ v1_xboole_0(X1) ),
% 3.44/0.99      inference(bin_hyper_res,[status(thm)],[c_16,c_228]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_3615,plain,
% 3.44/0.99      ( r1_tarski(X0,X1) != iProver_top
% 3.44/0.99      | r2_hidden(X2,X0) != iProver_top
% 3.44/0.99      | v1_xboole_0(X1) != iProver_top ),
% 3.44/0.99      inference(predicate_to_equality,[status(thm)],[c_278]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_4792,plain,
% 3.44/0.99      ( r1_tarski(X0,X1) != iProver_top
% 3.44/0.99      | v1_xboole_0(X1) != iProver_top
% 3.44/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.44/0.99      inference(superposition,[status(thm)],[c_3633,c_3615]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_8455,plain,
% 3.44/0.99      ( v1_xboole_0(sK2(sK4,k1_xboole_0)) = iProver_top
% 3.44/0.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.44/0.99      inference(superposition,[status(thm)],[c_4556,c_4792]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_4410,plain,
% 3.44/0.99      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.44/0.99      inference(demodulation,[status(thm)],[c_4405,c_3619]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_4,plain,
% 3.44/0.99      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 3.44/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_5042,plain,
% 3.44/0.99      ( ~ r1_tarski(X0,X1) | r2_hidden(sK0(X0),X1) | v1_xboole_0(X0) ),
% 3.44/0.99      inference(resolution,[status(thm)],[c_4,c_0]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_1,plain,
% 3.44/0.99      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.44/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_5513,plain,
% 3.44/0.99      ( ~ r1_tarski(X0,X1) | ~ v1_xboole_0(X1) | v1_xboole_0(X0) ),
% 3.44/0.99      inference(resolution,[status(thm)],[c_5042,c_1]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_12,plain,
% 3.44/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.44/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_4127,plain,
% 3.44/0.99      ( v2_tex_2(k1_xboole_0,sK4)
% 3.44/0.99      | r1_tarski(sK2(sK4,k1_xboole_0),k1_xboole_0) ),
% 3.44/0.99      inference(resolution,[status(thm)],[c_12,c_662]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_3875,plain,
% 3.44/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 3.44/0.99      inference(instantiation,[status(thm)],[c_12]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_3876,plain,
% 3.44/0.99      ( v2_tex_2(k1_xboole_0,sK4)
% 3.44/0.99      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.44/0.99      | r1_tarski(sK2(sK4,k1_xboole_0),k1_xboole_0) ),
% 3.44/0.99      inference(instantiation,[status(thm)],[c_662]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_3621,plain,
% 3.44/0.99      ( v2_tex_2(sK5,sK4) != iProver_top ),
% 3.44/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_4409,plain,
% 3.44/0.99      ( v2_tex_2(k1_xboole_0,sK4) != iProver_top ),
% 3.44/0.99      inference(demodulation,[status(thm)],[c_4405,c_3621]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_4419,plain,
% 3.44/0.99      ( ~ v2_tex_2(k1_xboole_0,sK4) ),
% 3.44/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_4409]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_4435,plain,
% 3.44/0.99      ( r1_tarski(sK2(sK4,k1_xboole_0),k1_xboole_0) ),
% 3.44/0.99      inference(global_propositional_subsumption,
% 3.44/0.99                [status(thm)],
% 3.44/0.99                [c_4127,c_3875,c_3876,c_4419]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_5537,plain,
% 3.44/0.99      ( v1_xboole_0(sK2(sK4,k1_xboole_0)) | ~ v1_xboole_0(k1_xboole_0) ),
% 3.44/0.99      inference(resolution,[status(thm)],[c_5513,c_4435]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_5538,plain,
% 3.44/0.99      ( v1_xboole_0(sK2(sK4,k1_xboole_0)) = iProver_top
% 3.44/0.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.44/0.99      inference(predicate_to_equality,[status(thm)],[c_5537]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_9485,plain,
% 3.44/0.99      ( v1_xboole_0(sK2(sK4,k1_xboole_0)) = iProver_top ),
% 3.44/0.99      inference(global_propositional_subsumption,
% 3.44/0.99                [status(thm)],
% 3.44/0.99                [c_8455,c_4410,c_5538]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_9491,plain,
% 3.44/0.99      ( sK2(sK4,k1_xboole_0) = k1_xboole_0 ),
% 3.44/0.99      inference(superposition,[status(thm)],[c_9485,c_3628]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_10,plain,
% 3.44/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | k9_subset_1(X1,X2,X2) = X2 ),
% 3.44/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_274,plain,
% 3.44/0.99      ( ~ r1_tarski(X0,X1) | k9_subset_1(X1,X2,X2) = X2 ),
% 3.44/0.99      inference(bin_hyper_res,[status(thm)],[c_10,c_228]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_3617,plain,
% 3.44/0.99      ( k9_subset_1(X0,X1,X1) = X1 | r1_tarski(X2,X0) != iProver_top ),
% 3.44/0.99      inference(predicate_to_equality,[status(thm)],[c_274]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_14,plain,
% 3.44/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.44/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_8,plain,
% 3.44/0.99      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 3.44/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_4800,plain,
% 3.44/0.99      ( r1_tarski(k2_subset_1(X0),X0) ),
% 3.44/0.99      inference(resolution,[status(thm)],[c_14,c_8]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_11263,plain,
% 3.44/0.99      ( k9_subset_1(X0,X1,X1) = X1 ),
% 3.44/0.99      inference(resolution,[status(thm)],[c_274,c_4800]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_12046,plain,
% 3.44/0.99      ( k9_subset_1(X0,X1,X1) = X1 ),
% 3.44/0.99      inference(global_propositional_subsumption,
% 3.44/0.99                [status(thm)],
% 3.44/0.99                [c_3617,c_11263]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_18,plain,
% 3.44/0.99      ( v2_tex_2(X0,X1)
% 3.44/0.99      | ~ v3_pre_topc(X2,X1)
% 3.44/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.44/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.44/0.99      | ~ l1_pre_topc(X1)
% 3.44/0.99      | k9_subset_1(u1_struct_0(X1),X0,X2) != sK2(X1,X0) ),
% 3.44/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_676,plain,
% 3.44/0.99      ( v2_tex_2(X0,X1)
% 3.44/0.99      | ~ v3_pre_topc(X2,X1)
% 3.44/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.44/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.44/0.99      | k9_subset_1(u1_struct_0(X1),X0,X2) != sK2(X1,X0)
% 3.44/0.99      | sK4 != X1 ),
% 3.44/0.99      inference(resolution_lifted,[status(thm)],[c_18,c_27]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_677,plain,
% 3.44/0.99      ( v2_tex_2(X0,sK4)
% 3.44/0.99      | ~ v3_pre_topc(X1,sK4)
% 3.44/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.44/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.44/0.99      | k9_subset_1(u1_struct_0(sK4),X0,X1) != sK2(sK4,X0) ),
% 3.44/0.99      inference(unflattening,[status(thm)],[c_676]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_3608,plain,
% 3.44/0.99      ( k9_subset_1(u1_struct_0(sK4),X0,X1) != sK2(sK4,X0)
% 3.44/0.99      | v2_tex_2(X0,sK4) = iProver_top
% 3.44/0.99      | v3_pre_topc(X1,sK4) != iProver_top
% 3.44/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.44/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 3.44/0.99      inference(predicate_to_equality,[status(thm)],[c_677]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_12053,plain,
% 3.44/0.99      ( sK2(sK4,X0) != X0
% 3.44/0.99      | v2_tex_2(X0,sK4) = iProver_top
% 3.44/0.99      | v3_pre_topc(X0,sK4) != iProver_top
% 3.44/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 3.44/0.99      inference(superposition,[status(thm)],[c_12046,c_3608]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_12709,plain,
% 3.44/0.99      ( v2_tex_2(k1_xboole_0,sK4) = iProver_top
% 3.44/0.99      | v3_pre_topc(k1_xboole_0,sK4) != iProver_top
% 3.44/0.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 3.44/0.99      inference(superposition,[status(thm)],[c_9491,c_12053]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_17,plain,
% 3.44/0.99      ( v3_pre_topc(X0,X1)
% 3.44/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.44/0.99      | ~ v2_pre_topc(X1)
% 3.44/0.99      | ~ l1_pre_topc(X1)
% 3.44/0.99      | ~ v1_xboole_0(X0) ),
% 3.44/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_28,negated_conjecture,
% 3.44/0.99      ( v2_pre_topc(sK4) ),
% 3.44/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_383,plain,
% 3.44/0.99      ( v3_pre_topc(X0,X1)
% 3.44/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.44/0.99      | ~ l1_pre_topc(X1)
% 3.44/0.99      | ~ v1_xboole_0(X0)
% 3.44/0.99      | sK4 != X1 ),
% 3.44/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_28]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_384,plain,
% 3.44/0.99      ( v3_pre_topc(X0,sK4)
% 3.44/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.44/0.99      | ~ l1_pre_topc(sK4)
% 3.44/0.99      | ~ v1_xboole_0(X0) ),
% 3.44/0.99      inference(unflattening,[status(thm)],[c_383]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_388,plain,
% 3.44/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.44/0.99      | v3_pre_topc(X0,sK4)
% 3.44/0.99      | ~ v1_xboole_0(X0) ),
% 3.44/0.99      inference(global_propositional_subsumption,
% 3.44/0.99                [status(thm)],
% 3.44/0.99                [c_384,c_27]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_389,plain,
% 3.44/0.99      ( v3_pre_topc(X0,sK4)
% 3.44/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.44/0.99      | ~ v1_xboole_0(X0) ),
% 3.44/0.99      inference(renaming,[status(thm)],[c_388]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_3614,plain,
% 3.44/0.99      ( v3_pre_topc(X0,sK4) = iProver_top
% 3.44/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.44/0.99      | v1_xboole_0(X0) != iProver_top ),
% 3.44/0.99      inference(predicate_to_equality,[status(thm)],[c_389]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_3910,plain,
% 3.44/0.99      ( v3_pre_topc(sK5,sK4) = iProver_top
% 3.44/0.99      | v1_xboole_0(sK5) != iProver_top ),
% 3.44/0.99      inference(superposition,[status(thm)],[c_3620,c_3614]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_460,plain,
% 3.44/0.99      ( v3_pre_topc(X0,sK4)
% 3.44/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.44/0.99      | sK5 != X0 ),
% 3.44/0.99      inference(resolution_lifted,[status(thm)],[c_389,c_26]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_461,plain,
% 3.44/0.99      ( v3_pre_topc(sK5,sK4)
% 3.44/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 3.44/0.99      inference(unflattening,[status(thm)],[c_460]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_462,plain,
% 3.44/0.99      ( v3_pre_topc(sK5,sK4) = iProver_top
% 3.44/0.99      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 3.44/0.99      inference(predicate_to_equality,[status(thm)],[c_461]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_3969,plain,
% 3.44/0.99      ( v3_pre_topc(sK5,sK4) = iProver_top ),
% 3.44/0.99      inference(global_propositional_subsumption,
% 3.44/0.99                [status(thm)],
% 3.44/0.99                [c_3910,c_32,c_462]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_4407,plain,
% 3.44/0.99      ( v3_pre_topc(k1_xboole_0,sK4) = iProver_top ),
% 3.44/0.99      inference(demodulation,[status(thm)],[c_4405,c_3969]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_3879,plain,
% 3.44/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 3.44/0.99      inference(predicate_to_equality,[status(thm)],[c_3875]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(contradiction,plain,
% 3.44/0.99      ( $false ),
% 3.44/0.99      inference(minisat,[status(thm)],[c_12709,c_4409,c_4407,c_3879]) ).
% 3.44/0.99  
% 3.44/0.99  
% 3.44/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.44/0.99  
% 3.44/0.99  ------                               Statistics
% 3.44/0.99  
% 3.44/0.99  ------ Selected
% 3.44/0.99  
% 3.44/0.99  total_time:                             0.312
% 3.44/0.99  
%------------------------------------------------------------------------------
