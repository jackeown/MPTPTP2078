%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:26:14 EST 2020

% Result     : Theorem 1.91s
% Output     : CNFRefutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 448 expanded)
%              Number of clauses        :   80 ( 134 expanded)
%              Number of leaves         :   17 ( 106 expanded)
%              Depth                    :   20
%              Number of atoms          :  446 (2026 expanded)
%              Number of equality atoms :  129 ( 248 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f24])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).

fof(f43,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_xboole_0(X1) )
           => v2_tex_2(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f12,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_xboole_0(X1) )
           => v2_tex_2(X1,X0) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
     => ( ~ v2_tex_2(sK5,X0)
        & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
        & v1_xboole_0(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
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

fof(f41,plain,
    ( ~ v2_tex_2(sK5,sK4)
    & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    & v1_xboole_0(sK5)
    & l1_pre_topc(sK4)
    & v2_pre_topc(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f23,f40,f39])).

fof(f64,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f41])).

fof(f9,axiom,(
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

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

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
    inference(nnf_transformation,[],[f21])).

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f37,plain,(
    ! [X4,X1,X0] :
      ( ? [X5] :
          ( k9_subset_1(u1_struct_0(X0),X1,X5) = X4
          & v4_pre_topc(X5,X0)
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X0),X1,sK3(X0,X1,X4)) = X4
        & v4_pre_topc(sK3(X0,X1,X4),X0)
        & m1_subset_1(sK3(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
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

fof(f38,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f35,f37,f36])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | r1_tarski(sK2(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f62,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f41])).

fof(f65,plain,(
    ~ v2_tex_2(sK5,sK4) ),
    inference(cnf_transformation,[],[f41])).

fof(f63,plain,(
    v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f41])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f47,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f29,f30])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f42,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

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

fof(f50,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f60,plain,(
    ! [X0,X3,X1] :
      ( v2_tex_2(X1,X0)
      | k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1)
      | ~ v4_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f61,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f41])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f67,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f48])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1908,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1896,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_14,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(sK2(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_22,negated_conjecture,
    ( l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_508,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(sK2(X1,X0),X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_22])).

cnf(c_509,plain,
    ( v2_tex_2(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | r1_tarski(sK2(sK4,X0),X0) ),
    inference(unflattening,[status(thm)],[c_508])).

cnf(c_1889,plain,
    ( v2_tex_2(X0,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r1_tarski(sK2(sK4,X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_509])).

cnf(c_2332,plain,
    ( v2_tex_2(sK5,sK4) = iProver_top
    | r1_tarski(sK2(sK4,sK5),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1896,c_1889])).

cnf(c_27,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_19,negated_conjecture,
    ( ~ v2_tex_2(sK5,sK4) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_854,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | r1_tarski(sK2(sK4,X0),X0)
    | sK4 != sK4
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_509])).

cnf(c_855,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | r1_tarski(sK2(sK4,sK5),sK5) ),
    inference(unflattening,[status(thm)],[c_854])).

cnf(c_856,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r1_tarski(sK2(sK4,sK5),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_855])).

cnf(c_2814,plain,
    ( r1_tarski(sK2(sK4,sK5),sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2332,c_27,c_856])).

cnf(c_21,negated_conjecture,
    ( v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1895,plain,
    ( v1_xboole_0(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_5,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1903,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2466,plain,
    ( sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1895,c_1903])).

cnf(c_2818,plain,
    ( r1_tarski(sK2(sK4,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2814,c_2466])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1904,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3929,plain,
    ( r2_hidden(X0,sK2(sK4,k1_xboole_0)) != iProver_top
    | r2_hidden(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2818,c_1904])).

cnf(c_4664,plain,
    ( r2_hidden(sK0(sK2(sK4,k1_xboole_0)),k1_xboole_0) = iProver_top
    | v1_xboole_0(sK2(sK4,k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1908,c_3929])).

cnf(c_26,plain,
    ( v1_xboole_0(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_335,plain,
    ( sK5 != X0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_21])).

cnf(c_336,plain,
    ( k1_xboole_0 = sK5 ),
    inference(unflattening,[status(thm)],[c_335])).

cnf(c_1480,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2235,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1480])).

cnf(c_2587,plain,
    ( ~ v1_xboole_0(sK5)
    | v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 != sK5 ),
    inference(instantiation,[status(thm)],[c_2235])).

cnf(c_2588,plain,
    ( k1_xboole_0 != sK5
    | v1_xboole_0(sK5) != iProver_top
    | v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2587])).

cnf(c_2685,plain,
    ( v1_xboole_0(X0)
    | ~ v1_xboole_0(k1_xboole_0)
    | X0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1480])).

cnf(c_4292,plain,
    ( v1_xboole_0(sK2(sK4,k1_xboole_0))
    | ~ v1_xboole_0(k1_xboole_0)
    | sK2(sK4,k1_xboole_0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2685])).

cnf(c_4293,plain,
    ( sK2(sK4,k1_xboole_0) != k1_xboole_0
    | v1_xboole_0(sK2(sK4,k1_xboole_0)) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4292])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1905,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1907,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3178,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1905,c_1907])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1902,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3761,plain,
    ( sK2(sK4,k1_xboole_0) = k1_xboole_0
    | r1_tarski(k1_xboole_0,sK2(sK4,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2818,c_1902])).

cnf(c_4659,plain,
    ( sK2(sK4,k1_xboole_0) = k1_xboole_0
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3178,c_3761])).

cnf(c_4770,plain,
    ( v1_xboole_0(sK2(sK4,k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4664,c_26,c_336,c_2588,c_4293,c_4659])).

cnf(c_4775,plain,
    ( sK2(sK4,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4770,c_1903])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X2) = X2 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1900,plain,
    ( k9_subset_1(X0,X1,X1) = X1
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_10,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2092,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
    | k9_subset_1(X0,X1,X1) = X1 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_3181,plain,
    ( k9_subset_1(X0,X1,X1) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1900,c_10,c_2092])).

cnf(c_13,plain,
    ( v2_tex_2(X0,X1)
    | ~ v4_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),X0,X2) != sK2(X1,X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_523,plain,
    ( v2_tex_2(X0,X1)
    | ~ v4_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | k9_subset_1(u1_struct_0(X1),X0,X2) != sK2(X1,X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_22])).

cnf(c_524,plain,
    ( v2_tex_2(X0,sK4)
    | ~ v4_pre_topc(X1,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | k9_subset_1(u1_struct_0(sK4),X0,X1) != sK2(sK4,X0) ),
    inference(unflattening,[status(thm)],[c_523])).

cnf(c_1888,plain,
    ( k9_subset_1(u1_struct_0(sK4),X0,X1) != sK2(sK4,X0)
    | v2_tex_2(X0,sK4) = iProver_top
    | v4_pre_topc(X1,sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_524])).

cnf(c_3185,plain,
    ( sK2(sK4,X0) != X0
    | v2_tex_2(X0,sK4) = iProver_top
    | v4_pre_topc(X0,sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3181,c_1888])).

cnf(c_5484,plain,
    ( v2_tex_2(k1_xboole_0,sK4) = iProver_top
    | v4_pre_topc(k1_xboole_0,sK4) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4775,c_3185])).

cnf(c_1897,plain,
    ( v2_tex_2(sK5,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2596,plain,
    ( v2_tex_2(k1_xboole_0,sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2466,c_1897])).

cnf(c_1486,plain,
    ( ~ v4_pre_topc(X0,X1)
    | v4_pre_topc(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2132,plain,
    ( v4_pre_topc(X0,X1)
    | ~ v4_pre_topc(sK5,sK4)
    | X1 != sK4
    | X0 != sK5 ),
    inference(instantiation,[status(thm)],[c_1486])).

cnf(c_2497,plain,
    ( ~ v4_pre_topc(sK5,sK4)
    | v4_pre_topc(k1_xboole_0,X0)
    | X0 != sK4
    | k1_xboole_0 != sK5 ),
    inference(instantiation,[status(thm)],[c_2132])).

cnf(c_2498,plain,
    ( X0 != sK4
    | k1_xboole_0 != sK5
    | v4_pre_topc(sK5,sK4) != iProver_top
    | v4_pre_topc(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2497])).

cnf(c_2500,plain,
    ( sK4 != sK4
    | k1_xboole_0 != sK5
    | v4_pre_topc(sK5,sK4) != iProver_top
    | v4_pre_topc(k1_xboole_0,sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2498])).

cnf(c_2080,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_2084,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2080])).

cnf(c_12,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_23,negated_conjecture,
    ( v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_262,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_23])).

cnf(c_263,plain,
    ( v4_pre_topc(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_pre_topc(sK4)
    | ~ v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_262])).

cnf(c_267,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | v4_pre_topc(X0,sK4)
    | ~ v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_263,c_22])).

cnf(c_268,plain,
    ( v4_pre_topc(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_267])).

cnf(c_324,plain,
    ( v4_pre_topc(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_268,c_21])).

cnf(c_325,plain,
    ( v4_pre_topc(sK5,sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(unflattening,[status(thm)],[c_324])).

cnf(c_326,plain,
    ( v4_pre_topc(sK5,sK4) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_325])).

cnf(c_64,plain,
    ( ~ r1_tarski(sK4,sK4)
    | sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_8,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_60,plain,
    ( r1_tarski(sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5484,c_2596,c_2500,c_2084,c_336,c_326,c_64,c_60,c_27])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:56:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 1.91/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.00  
% 1.91/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.91/1.00  
% 1.91/1.00  ------  iProver source info
% 1.91/1.00  
% 1.91/1.00  git: date: 2020-06-30 10:37:57 +0100
% 1.91/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.91/1.00  git: non_committed_changes: false
% 1.91/1.00  git: last_make_outside_of_git: false
% 1.91/1.00  
% 1.91/1.00  ------ 
% 1.91/1.00  
% 1.91/1.00  ------ Input Options
% 1.91/1.00  
% 1.91/1.00  --out_options                           all
% 1.91/1.00  --tptp_safe_out                         true
% 1.91/1.00  --problem_path                          ""
% 1.91/1.00  --include_path                          ""
% 1.91/1.00  --clausifier                            res/vclausify_rel
% 1.91/1.00  --clausifier_options                    --mode clausify
% 1.91/1.00  --stdin                                 false
% 1.91/1.00  --stats_out                             all
% 1.91/1.00  
% 1.91/1.00  ------ General Options
% 1.91/1.00  
% 1.91/1.00  --fof                                   false
% 1.91/1.00  --time_out_real                         305.
% 1.91/1.00  --time_out_virtual                      -1.
% 1.91/1.00  --symbol_type_check                     false
% 1.91/1.00  --clausify_out                          false
% 1.91/1.00  --sig_cnt_out                           false
% 1.91/1.00  --trig_cnt_out                          false
% 1.91/1.00  --trig_cnt_out_tolerance                1.
% 1.91/1.00  --trig_cnt_out_sk_spl                   false
% 1.91/1.00  --abstr_cl_out                          false
% 1.91/1.00  
% 1.91/1.00  ------ Global Options
% 1.91/1.00  
% 1.91/1.00  --schedule                              default
% 1.91/1.00  --add_important_lit                     false
% 1.91/1.00  --prop_solver_per_cl                    1000
% 1.91/1.00  --min_unsat_core                        false
% 1.91/1.00  --soft_assumptions                      false
% 1.91/1.00  --soft_lemma_size                       3
% 1.91/1.00  --prop_impl_unit_size                   0
% 1.91/1.00  --prop_impl_unit                        []
% 1.91/1.00  --share_sel_clauses                     true
% 1.91/1.00  --reset_solvers                         false
% 1.91/1.00  --bc_imp_inh                            [conj_cone]
% 1.91/1.00  --conj_cone_tolerance                   3.
% 1.91/1.00  --extra_neg_conj                        none
% 1.91/1.00  --large_theory_mode                     true
% 1.91/1.00  --prolific_symb_bound                   200
% 1.91/1.00  --lt_threshold                          2000
% 1.91/1.00  --clause_weak_htbl                      true
% 1.91/1.00  --gc_record_bc_elim                     false
% 1.91/1.00  
% 1.91/1.00  ------ Preprocessing Options
% 1.91/1.00  
% 1.91/1.00  --preprocessing_flag                    true
% 1.91/1.00  --time_out_prep_mult                    0.1
% 1.91/1.00  --splitting_mode                        input
% 1.91/1.00  --splitting_grd                         true
% 1.91/1.00  --splitting_cvd                         false
% 1.91/1.00  --splitting_cvd_svl                     false
% 1.91/1.00  --splitting_nvd                         32
% 1.91/1.00  --sub_typing                            true
% 1.91/1.00  --prep_gs_sim                           true
% 1.91/1.00  --prep_unflatten                        true
% 1.91/1.00  --prep_res_sim                          true
% 1.91/1.00  --prep_upred                            true
% 1.91/1.00  --prep_sem_filter                       exhaustive
% 1.91/1.00  --prep_sem_filter_out                   false
% 1.91/1.00  --pred_elim                             true
% 1.91/1.00  --res_sim_input                         true
% 1.91/1.00  --eq_ax_congr_red                       true
% 1.91/1.00  --pure_diseq_elim                       true
% 1.91/1.00  --brand_transform                       false
% 1.91/1.00  --non_eq_to_eq                          false
% 1.91/1.00  --prep_def_merge                        true
% 1.91/1.00  --prep_def_merge_prop_impl              false
% 1.91/1.00  --prep_def_merge_mbd                    true
% 1.91/1.00  --prep_def_merge_tr_red                 false
% 1.91/1.00  --prep_def_merge_tr_cl                  false
% 1.91/1.00  --smt_preprocessing                     true
% 1.91/1.00  --smt_ac_axioms                         fast
% 1.91/1.00  --preprocessed_out                      false
% 1.91/1.00  --preprocessed_stats                    false
% 1.91/1.00  
% 1.91/1.00  ------ Abstraction refinement Options
% 1.91/1.00  
% 1.91/1.00  --abstr_ref                             []
% 1.91/1.00  --abstr_ref_prep                        false
% 1.91/1.00  --abstr_ref_until_sat                   false
% 1.91/1.00  --abstr_ref_sig_restrict                funpre
% 1.91/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.91/1.00  --abstr_ref_under                       []
% 1.91/1.00  
% 1.91/1.00  ------ SAT Options
% 1.91/1.00  
% 1.91/1.00  --sat_mode                              false
% 1.91/1.00  --sat_fm_restart_options                ""
% 1.91/1.00  --sat_gr_def                            false
% 1.91/1.00  --sat_epr_types                         true
% 1.91/1.00  --sat_non_cyclic_types                  false
% 1.91/1.00  --sat_finite_models                     false
% 1.91/1.00  --sat_fm_lemmas                         false
% 1.91/1.00  --sat_fm_prep                           false
% 1.91/1.00  --sat_fm_uc_incr                        true
% 1.91/1.00  --sat_out_model                         small
% 1.91/1.00  --sat_out_clauses                       false
% 1.91/1.00  
% 1.91/1.00  ------ QBF Options
% 1.91/1.00  
% 1.91/1.00  --qbf_mode                              false
% 1.91/1.00  --qbf_elim_univ                         false
% 1.91/1.00  --qbf_dom_inst                          none
% 1.91/1.00  --qbf_dom_pre_inst                      false
% 1.91/1.00  --qbf_sk_in                             false
% 1.91/1.00  --qbf_pred_elim                         true
% 1.91/1.00  --qbf_split                             512
% 1.91/1.00  
% 1.91/1.00  ------ BMC1 Options
% 1.91/1.00  
% 1.91/1.00  --bmc1_incremental                      false
% 1.91/1.00  --bmc1_axioms                           reachable_all
% 1.91/1.00  --bmc1_min_bound                        0
% 1.91/1.00  --bmc1_max_bound                        -1
% 1.91/1.00  --bmc1_max_bound_default                -1
% 1.91/1.00  --bmc1_symbol_reachability              true
% 1.91/1.00  --bmc1_property_lemmas                  false
% 1.91/1.00  --bmc1_k_induction                      false
% 1.91/1.00  --bmc1_non_equiv_states                 false
% 1.91/1.00  --bmc1_deadlock                         false
% 1.91/1.00  --bmc1_ucm                              false
% 1.91/1.00  --bmc1_add_unsat_core                   none
% 1.91/1.00  --bmc1_unsat_core_children              false
% 1.91/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.91/1.00  --bmc1_out_stat                         full
% 1.91/1.00  --bmc1_ground_init                      false
% 1.91/1.00  --bmc1_pre_inst_next_state              false
% 1.91/1.00  --bmc1_pre_inst_state                   false
% 1.91/1.00  --bmc1_pre_inst_reach_state             false
% 1.91/1.00  --bmc1_out_unsat_core                   false
% 1.91/1.00  --bmc1_aig_witness_out                  false
% 1.91/1.00  --bmc1_verbose                          false
% 1.91/1.00  --bmc1_dump_clauses_tptp                false
% 1.91/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.91/1.00  --bmc1_dump_file                        -
% 1.91/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.91/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.91/1.00  --bmc1_ucm_extend_mode                  1
% 1.91/1.00  --bmc1_ucm_init_mode                    2
% 1.91/1.00  --bmc1_ucm_cone_mode                    none
% 1.91/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.91/1.00  --bmc1_ucm_relax_model                  4
% 1.91/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.91/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.91/1.00  --bmc1_ucm_layered_model                none
% 1.91/1.00  --bmc1_ucm_max_lemma_size               10
% 1.91/1.00  
% 1.91/1.00  ------ AIG Options
% 1.91/1.00  
% 1.91/1.00  --aig_mode                              false
% 1.91/1.00  
% 1.91/1.00  ------ Instantiation Options
% 1.91/1.00  
% 1.91/1.00  --instantiation_flag                    true
% 1.91/1.00  --inst_sos_flag                         false
% 1.91/1.00  --inst_sos_phase                        true
% 1.91/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.91/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.91/1.00  --inst_lit_sel_side                     num_symb
% 1.91/1.00  --inst_solver_per_active                1400
% 1.91/1.00  --inst_solver_calls_frac                1.
% 1.91/1.00  --inst_passive_queue_type               priority_queues
% 1.91/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.91/1.00  --inst_passive_queues_freq              [25;2]
% 1.91/1.00  --inst_dismatching                      true
% 1.91/1.00  --inst_eager_unprocessed_to_passive     true
% 1.91/1.00  --inst_prop_sim_given                   true
% 1.91/1.00  --inst_prop_sim_new                     false
% 1.91/1.00  --inst_subs_new                         false
% 1.91/1.00  --inst_eq_res_simp                      false
% 1.91/1.00  --inst_subs_given                       false
% 1.91/1.00  --inst_orphan_elimination               true
% 1.91/1.00  --inst_learning_loop_flag               true
% 1.91/1.00  --inst_learning_start                   3000
% 1.91/1.00  --inst_learning_factor                  2
% 1.91/1.00  --inst_start_prop_sim_after_learn       3
% 1.91/1.00  --inst_sel_renew                        solver
% 1.91/1.00  --inst_lit_activity_flag                true
% 1.91/1.00  --inst_restr_to_given                   false
% 1.91/1.00  --inst_activity_threshold               500
% 1.91/1.00  --inst_out_proof                        true
% 1.91/1.00  
% 1.91/1.00  ------ Resolution Options
% 1.91/1.00  
% 1.91/1.00  --resolution_flag                       true
% 1.91/1.00  --res_lit_sel                           adaptive
% 1.91/1.00  --res_lit_sel_side                      none
% 1.91/1.00  --res_ordering                          kbo
% 1.91/1.00  --res_to_prop_solver                    active
% 1.91/1.00  --res_prop_simpl_new                    false
% 1.91/1.00  --res_prop_simpl_given                  true
% 1.91/1.00  --res_passive_queue_type                priority_queues
% 1.91/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.91/1.00  --res_passive_queues_freq               [15;5]
% 1.91/1.00  --res_forward_subs                      full
% 1.91/1.00  --res_backward_subs                     full
% 1.91/1.00  --res_forward_subs_resolution           true
% 1.91/1.00  --res_backward_subs_resolution          true
% 1.91/1.00  --res_orphan_elimination                true
% 1.91/1.00  --res_time_limit                        2.
% 1.91/1.00  --res_out_proof                         true
% 1.91/1.00  
% 1.91/1.00  ------ Superposition Options
% 1.91/1.00  
% 1.91/1.00  --superposition_flag                    true
% 1.91/1.00  --sup_passive_queue_type                priority_queues
% 1.91/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.91/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.91/1.00  --demod_completeness_check              fast
% 1.91/1.00  --demod_use_ground                      true
% 1.91/1.00  --sup_to_prop_solver                    passive
% 1.91/1.00  --sup_prop_simpl_new                    true
% 1.91/1.00  --sup_prop_simpl_given                  true
% 1.91/1.00  --sup_fun_splitting                     false
% 1.91/1.00  --sup_smt_interval                      50000
% 1.91/1.00  
% 1.91/1.00  ------ Superposition Simplification Setup
% 1.91/1.00  
% 1.91/1.00  --sup_indices_passive                   []
% 1.91/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.91/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.91/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.91/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.91/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.91/1.00  --sup_full_bw                           [BwDemod]
% 1.91/1.00  --sup_immed_triv                        [TrivRules]
% 1.91/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.91/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.91/1.00  --sup_immed_bw_main                     []
% 1.91/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.91/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.91/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.91/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.91/1.00  
% 1.91/1.00  ------ Combination Options
% 1.91/1.00  
% 1.91/1.00  --comb_res_mult                         3
% 1.91/1.00  --comb_sup_mult                         2
% 1.91/1.00  --comb_inst_mult                        10
% 1.91/1.00  
% 1.91/1.00  ------ Debug Options
% 1.91/1.00  
% 1.91/1.00  --dbg_backtrace                         false
% 1.91/1.00  --dbg_dump_prop_clauses                 false
% 1.91/1.00  --dbg_dump_prop_clauses_file            -
% 1.91/1.00  --dbg_out_stat                          false
% 1.91/1.00  ------ Parsing...
% 1.91/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.91/1.00  
% 1.91/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 1.91/1.00  
% 1.91/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.91/1.00  
% 1.91/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.91/1.00  ------ Proving...
% 1.91/1.00  ------ Problem Properties 
% 1.91/1.00  
% 1.91/1.00  
% 1.91/1.00  clauses                                 21
% 1.91/1.00  conjectures                             3
% 1.91/1.00  EPR                                     7
% 1.91/1.00  Horn                                    17
% 1.91/1.00  unary                                   5
% 1.91/1.00  binary                                  6
% 1.91/1.00  lits                                    55
% 1.91/1.00  lits eq                                 5
% 1.91/1.00  fd_pure                                 0
% 1.91/1.00  fd_pseudo                               0
% 1.91/1.00  fd_cond                                 1
% 1.91/1.00  fd_pseudo_cond                          1
% 1.91/1.00  AC symbols                              0
% 1.91/1.00  
% 1.91/1.00  ------ Schedule dynamic 5 is on 
% 1.91/1.00  
% 1.91/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.91/1.00  
% 1.91/1.00  
% 1.91/1.00  ------ 
% 1.91/1.00  Current options:
% 1.91/1.00  ------ 
% 1.91/1.00  
% 1.91/1.00  ------ Input Options
% 1.91/1.00  
% 1.91/1.00  --out_options                           all
% 1.91/1.00  --tptp_safe_out                         true
% 1.91/1.00  --problem_path                          ""
% 1.91/1.00  --include_path                          ""
% 1.91/1.00  --clausifier                            res/vclausify_rel
% 1.91/1.00  --clausifier_options                    --mode clausify
% 1.91/1.00  --stdin                                 false
% 1.91/1.00  --stats_out                             all
% 1.91/1.00  
% 1.91/1.00  ------ General Options
% 1.91/1.00  
% 1.91/1.00  --fof                                   false
% 1.91/1.00  --time_out_real                         305.
% 1.91/1.00  --time_out_virtual                      -1.
% 1.91/1.00  --symbol_type_check                     false
% 1.91/1.00  --clausify_out                          false
% 1.91/1.00  --sig_cnt_out                           false
% 1.91/1.00  --trig_cnt_out                          false
% 1.91/1.00  --trig_cnt_out_tolerance                1.
% 1.91/1.00  --trig_cnt_out_sk_spl                   false
% 1.91/1.00  --abstr_cl_out                          false
% 1.91/1.00  
% 1.91/1.00  ------ Global Options
% 1.91/1.00  
% 1.91/1.00  --schedule                              default
% 1.91/1.00  --add_important_lit                     false
% 1.91/1.00  --prop_solver_per_cl                    1000
% 1.91/1.00  --min_unsat_core                        false
% 1.91/1.00  --soft_assumptions                      false
% 1.91/1.00  --soft_lemma_size                       3
% 1.91/1.00  --prop_impl_unit_size                   0
% 1.91/1.00  --prop_impl_unit                        []
% 1.91/1.00  --share_sel_clauses                     true
% 1.91/1.00  --reset_solvers                         false
% 1.91/1.00  --bc_imp_inh                            [conj_cone]
% 1.91/1.00  --conj_cone_tolerance                   3.
% 1.91/1.00  --extra_neg_conj                        none
% 1.91/1.00  --large_theory_mode                     true
% 1.91/1.00  --prolific_symb_bound                   200
% 1.91/1.00  --lt_threshold                          2000
% 1.91/1.00  --clause_weak_htbl                      true
% 1.91/1.00  --gc_record_bc_elim                     false
% 1.91/1.00  
% 1.91/1.00  ------ Preprocessing Options
% 1.91/1.00  
% 1.91/1.00  --preprocessing_flag                    true
% 1.91/1.00  --time_out_prep_mult                    0.1
% 1.91/1.00  --splitting_mode                        input
% 1.91/1.00  --splitting_grd                         true
% 1.91/1.00  --splitting_cvd                         false
% 1.91/1.00  --splitting_cvd_svl                     false
% 1.91/1.00  --splitting_nvd                         32
% 1.91/1.00  --sub_typing                            true
% 1.91/1.00  --prep_gs_sim                           true
% 1.91/1.00  --prep_unflatten                        true
% 1.91/1.00  --prep_res_sim                          true
% 1.91/1.00  --prep_upred                            true
% 1.91/1.00  --prep_sem_filter                       exhaustive
% 1.91/1.00  --prep_sem_filter_out                   false
% 1.91/1.00  --pred_elim                             true
% 1.91/1.00  --res_sim_input                         true
% 1.91/1.00  --eq_ax_congr_red                       true
% 1.91/1.00  --pure_diseq_elim                       true
% 1.91/1.00  --brand_transform                       false
% 1.91/1.00  --non_eq_to_eq                          false
% 1.91/1.00  --prep_def_merge                        true
% 1.91/1.00  --prep_def_merge_prop_impl              false
% 1.91/1.00  --prep_def_merge_mbd                    true
% 1.91/1.00  --prep_def_merge_tr_red                 false
% 1.91/1.00  --prep_def_merge_tr_cl                  false
% 1.91/1.00  --smt_preprocessing                     true
% 1.91/1.00  --smt_ac_axioms                         fast
% 1.91/1.00  --preprocessed_out                      false
% 1.91/1.00  --preprocessed_stats                    false
% 1.91/1.00  
% 1.91/1.00  ------ Abstraction refinement Options
% 1.91/1.00  
% 1.91/1.00  --abstr_ref                             []
% 1.91/1.00  --abstr_ref_prep                        false
% 1.91/1.00  --abstr_ref_until_sat                   false
% 1.91/1.00  --abstr_ref_sig_restrict                funpre
% 1.91/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.91/1.00  --abstr_ref_under                       []
% 1.91/1.00  
% 1.91/1.00  ------ SAT Options
% 1.91/1.00  
% 1.91/1.00  --sat_mode                              false
% 1.91/1.00  --sat_fm_restart_options                ""
% 1.91/1.00  --sat_gr_def                            false
% 1.91/1.00  --sat_epr_types                         true
% 1.91/1.00  --sat_non_cyclic_types                  false
% 1.91/1.00  --sat_finite_models                     false
% 1.91/1.00  --sat_fm_lemmas                         false
% 1.91/1.00  --sat_fm_prep                           false
% 1.91/1.00  --sat_fm_uc_incr                        true
% 1.91/1.00  --sat_out_model                         small
% 1.91/1.00  --sat_out_clauses                       false
% 1.91/1.00  
% 1.91/1.00  ------ QBF Options
% 1.91/1.00  
% 1.91/1.00  --qbf_mode                              false
% 1.91/1.00  --qbf_elim_univ                         false
% 1.91/1.00  --qbf_dom_inst                          none
% 1.91/1.00  --qbf_dom_pre_inst                      false
% 1.91/1.00  --qbf_sk_in                             false
% 1.91/1.00  --qbf_pred_elim                         true
% 1.91/1.00  --qbf_split                             512
% 1.91/1.00  
% 1.91/1.00  ------ BMC1 Options
% 1.91/1.00  
% 1.91/1.00  --bmc1_incremental                      false
% 1.91/1.00  --bmc1_axioms                           reachable_all
% 1.91/1.00  --bmc1_min_bound                        0
% 1.91/1.00  --bmc1_max_bound                        -1
% 1.91/1.00  --bmc1_max_bound_default                -1
% 1.91/1.01  --bmc1_symbol_reachability              true
% 1.91/1.01  --bmc1_property_lemmas                  false
% 1.91/1.01  --bmc1_k_induction                      false
% 1.91/1.01  --bmc1_non_equiv_states                 false
% 1.91/1.01  --bmc1_deadlock                         false
% 1.91/1.01  --bmc1_ucm                              false
% 1.91/1.01  --bmc1_add_unsat_core                   none
% 1.91/1.01  --bmc1_unsat_core_children              false
% 1.91/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 1.91/1.01  --bmc1_out_stat                         full
% 1.91/1.01  --bmc1_ground_init                      false
% 1.91/1.01  --bmc1_pre_inst_next_state              false
% 1.91/1.01  --bmc1_pre_inst_state                   false
% 1.91/1.01  --bmc1_pre_inst_reach_state             false
% 1.91/1.01  --bmc1_out_unsat_core                   false
% 1.91/1.01  --bmc1_aig_witness_out                  false
% 1.91/1.01  --bmc1_verbose                          false
% 1.91/1.01  --bmc1_dump_clauses_tptp                false
% 1.91/1.01  --bmc1_dump_unsat_core_tptp             false
% 1.91/1.01  --bmc1_dump_file                        -
% 1.91/1.01  --bmc1_ucm_expand_uc_limit              128
% 1.91/1.01  --bmc1_ucm_n_expand_iterations          6
% 1.91/1.01  --bmc1_ucm_extend_mode                  1
% 1.91/1.01  --bmc1_ucm_init_mode                    2
% 1.91/1.01  --bmc1_ucm_cone_mode                    none
% 1.91/1.01  --bmc1_ucm_reduced_relation_type        0
% 1.91/1.01  --bmc1_ucm_relax_model                  4
% 1.91/1.01  --bmc1_ucm_full_tr_after_sat            true
% 1.91/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 1.91/1.01  --bmc1_ucm_layered_model                none
% 1.91/1.01  --bmc1_ucm_max_lemma_size               10
% 1.91/1.01  
% 1.91/1.01  ------ AIG Options
% 1.91/1.01  
% 1.91/1.01  --aig_mode                              false
% 1.91/1.01  
% 1.91/1.01  ------ Instantiation Options
% 1.91/1.01  
% 1.91/1.01  --instantiation_flag                    true
% 1.91/1.01  --inst_sos_flag                         false
% 1.91/1.01  --inst_sos_phase                        true
% 1.91/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.91/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.91/1.01  --inst_lit_sel_side                     none
% 1.91/1.01  --inst_solver_per_active                1400
% 1.91/1.01  --inst_solver_calls_frac                1.
% 1.91/1.01  --inst_passive_queue_type               priority_queues
% 1.91/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.91/1.01  --inst_passive_queues_freq              [25;2]
% 1.91/1.01  --inst_dismatching                      true
% 1.91/1.01  --inst_eager_unprocessed_to_passive     true
% 1.91/1.01  --inst_prop_sim_given                   true
% 1.91/1.01  --inst_prop_sim_new                     false
% 1.91/1.01  --inst_subs_new                         false
% 1.91/1.01  --inst_eq_res_simp                      false
% 1.91/1.01  --inst_subs_given                       false
% 1.91/1.01  --inst_orphan_elimination               true
% 1.91/1.01  --inst_learning_loop_flag               true
% 1.91/1.01  --inst_learning_start                   3000
% 1.91/1.01  --inst_learning_factor                  2
% 1.91/1.01  --inst_start_prop_sim_after_learn       3
% 1.91/1.01  --inst_sel_renew                        solver
% 1.91/1.01  --inst_lit_activity_flag                true
% 1.91/1.01  --inst_restr_to_given                   false
% 1.91/1.01  --inst_activity_threshold               500
% 1.91/1.01  --inst_out_proof                        true
% 1.91/1.01  
% 1.91/1.01  ------ Resolution Options
% 1.91/1.01  
% 1.91/1.01  --resolution_flag                       false
% 1.91/1.01  --res_lit_sel                           adaptive
% 1.91/1.01  --res_lit_sel_side                      none
% 1.91/1.01  --res_ordering                          kbo
% 1.91/1.01  --res_to_prop_solver                    active
% 1.91/1.01  --res_prop_simpl_new                    false
% 1.91/1.01  --res_prop_simpl_given                  true
% 1.91/1.01  --res_passive_queue_type                priority_queues
% 1.91/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.91/1.01  --res_passive_queues_freq               [15;5]
% 1.91/1.01  --res_forward_subs                      full
% 1.91/1.01  --res_backward_subs                     full
% 1.91/1.01  --res_forward_subs_resolution           true
% 1.91/1.01  --res_backward_subs_resolution          true
% 1.91/1.01  --res_orphan_elimination                true
% 1.91/1.01  --res_time_limit                        2.
% 1.91/1.01  --res_out_proof                         true
% 1.91/1.01  
% 1.91/1.01  ------ Superposition Options
% 1.91/1.01  
% 1.91/1.01  --superposition_flag                    true
% 1.91/1.01  --sup_passive_queue_type                priority_queues
% 1.91/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.91/1.01  --sup_passive_queues_freq               [8;1;4]
% 1.91/1.01  --demod_completeness_check              fast
% 1.91/1.01  --demod_use_ground                      true
% 1.91/1.01  --sup_to_prop_solver                    passive
% 1.91/1.01  --sup_prop_simpl_new                    true
% 1.91/1.01  --sup_prop_simpl_given                  true
% 1.91/1.01  --sup_fun_splitting                     false
% 1.91/1.01  --sup_smt_interval                      50000
% 1.91/1.01  
% 1.91/1.01  ------ Superposition Simplification Setup
% 1.91/1.01  
% 1.91/1.01  --sup_indices_passive                   []
% 1.91/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.91/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.91/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.91/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 1.91/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.91/1.01  --sup_full_bw                           [BwDemod]
% 1.91/1.01  --sup_immed_triv                        [TrivRules]
% 1.91/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.91/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.91/1.01  --sup_immed_bw_main                     []
% 1.91/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.91/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 1.91/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.91/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.91/1.01  
% 1.91/1.01  ------ Combination Options
% 1.91/1.01  
% 1.91/1.01  --comb_res_mult                         3
% 1.91/1.01  --comb_sup_mult                         2
% 1.91/1.01  --comb_inst_mult                        10
% 1.91/1.01  
% 1.91/1.01  ------ Debug Options
% 1.91/1.01  
% 1.91/1.01  --dbg_backtrace                         false
% 1.91/1.01  --dbg_dump_prop_clauses                 false
% 1.91/1.01  --dbg_dump_prop_clauses_file            -
% 1.91/1.01  --dbg_out_stat                          false
% 1.91/1.01  
% 1.91/1.01  
% 1.91/1.01  
% 1.91/1.01  
% 1.91/1.01  ------ Proving...
% 1.91/1.01  
% 1.91/1.01  
% 1.91/1.01  % SZS status Theorem for theBenchmark.p
% 1.91/1.01  
% 1.91/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 1.91/1.01  
% 1.91/1.01  fof(f1,axiom,(
% 1.91/1.01    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.91/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.91/1.01  
% 1.91/1.01  fof(f24,plain,(
% 1.91/1.01    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.91/1.01    inference(nnf_transformation,[],[f1])).
% 1.91/1.01  
% 1.91/1.01  fof(f25,plain,(
% 1.91/1.01    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.91/1.01    inference(rectify,[],[f24])).
% 1.91/1.01  
% 1.91/1.01  fof(f26,plain,(
% 1.91/1.01    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 1.91/1.01    introduced(choice_axiom,[])).
% 1.91/1.01  
% 1.91/1.01  fof(f27,plain,(
% 1.91/1.01    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.91/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).
% 1.91/1.01  
% 1.91/1.01  fof(f43,plain,(
% 1.91/1.01    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 1.91/1.01    inference(cnf_transformation,[],[f27])).
% 1.91/1.01  
% 1.91/1.01  fof(f10,conjecture,(
% 1.91/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 1.91/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.91/1.01  
% 1.91/1.01  fof(f11,negated_conjecture,(
% 1.91/1.01    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 1.91/1.01    inference(negated_conjecture,[],[f10])).
% 1.91/1.01  
% 1.91/1.01  fof(f12,plain,(
% 1.91/1.01    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 1.91/1.01    inference(pure_predicate_removal,[],[f11])).
% 1.91/1.01  
% 1.91/1.01  fof(f22,plain,(
% 1.91/1.01    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.91/1.01    inference(ennf_transformation,[],[f12])).
% 1.91/1.01  
% 1.91/1.01  fof(f23,plain,(
% 1.91/1.01    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.91/1.01    inference(flattening,[],[f22])).
% 1.91/1.01  
% 1.91/1.01  fof(f40,plain,(
% 1.91/1.01    ( ! [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => (~v2_tex_2(sK5,X0) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(sK5))) )),
% 1.91/1.01    introduced(choice_axiom,[])).
% 1.91/1.01  
% 1.91/1.01  fof(f39,plain,(
% 1.91/1.01    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (~v2_tex_2(X1,sK4) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) & v1_xboole_0(X1)) & l1_pre_topc(sK4) & v2_pre_topc(sK4))),
% 1.91/1.01    introduced(choice_axiom,[])).
% 1.91/1.01  
% 1.91/1.01  fof(f41,plain,(
% 1.91/1.01    (~v2_tex_2(sK5,sK4) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) & v1_xboole_0(sK5)) & l1_pre_topc(sK4) & v2_pre_topc(sK4)),
% 1.91/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f23,f40,f39])).
% 1.91/1.01  
% 1.91/1.01  fof(f64,plain,(
% 1.91/1.01    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))),
% 1.91/1.01    inference(cnf_transformation,[],[f41])).
% 1.91/1.01  
% 1.91/1.01  fof(f9,axiom,(
% 1.91/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0))) & r1_tarski(X2,X1))))))),
% 1.91/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.91/1.01  
% 1.91/1.01  fof(f20,plain,(
% 1.91/1.01    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((? [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.91/1.01    inference(ennf_transformation,[],[f9])).
% 1.91/1.01  
% 1.91/1.01  fof(f21,plain,(
% 1.91/1.01    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.91/1.01    inference(flattening,[],[f20])).
% 1.91/1.01  
% 1.91/1.01  fof(f34,plain,(
% 1.91/1.01    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.91/1.01    inference(nnf_transformation,[],[f21])).
% 1.91/1.01  
% 1.91/1.01  fof(f35,plain,(
% 1.91/1.01    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (? [X5] : (k9_subset_1(u1_struct_0(X0),X1,X5) = X4 & v4_pre_topc(X5,X0) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.91/1.01    inference(rectify,[],[f34])).
% 1.91/1.01  
% 1.91/1.01  fof(f37,plain,(
% 1.91/1.01    ! [X4,X1,X0] : (? [X5] : (k9_subset_1(u1_struct_0(X0),X1,X5) = X4 & v4_pre_topc(X5,X0) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) => (k9_subset_1(u1_struct_0(X0),X1,sK3(X0,X1,X4)) = X4 & v4_pre_topc(sK3(X0,X1,X4),X0) & m1_subset_1(sK3(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.91/1.01    introduced(choice_axiom,[])).
% 1.91/1.01  
% 1.91/1.01  fof(f36,plain,(
% 1.91/1.01    ! [X1,X0] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(sK2(X0,X1),X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.91/1.01    introduced(choice_axiom,[])).
% 1.91/1.01  
% 1.91/1.01  fof(f38,plain,(
% 1.91/1.01    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(sK2(X0,X1),X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : ((k9_subset_1(u1_struct_0(X0),X1,sK3(X0,X1,X4)) = X4 & v4_pre_topc(sK3(X0,X1,X4),X0) & m1_subset_1(sK3(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.91/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f35,f37,f36])).
% 1.91/1.01  
% 1.91/1.01  fof(f59,plain,(
% 1.91/1.01    ( ! [X0,X1] : (v2_tex_2(X1,X0) | r1_tarski(sK2(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.91/1.01    inference(cnf_transformation,[],[f38])).
% 1.91/1.01  
% 1.91/1.01  fof(f62,plain,(
% 1.91/1.01    l1_pre_topc(sK4)),
% 1.91/1.01    inference(cnf_transformation,[],[f41])).
% 1.91/1.01  
% 1.91/1.01  fof(f65,plain,(
% 1.91/1.01    ~v2_tex_2(sK5,sK4)),
% 1.91/1.01    inference(cnf_transformation,[],[f41])).
% 1.91/1.01  
% 1.91/1.01  fof(f63,plain,(
% 1.91/1.01    v1_xboole_0(sK5)),
% 1.91/1.01    inference(cnf_transformation,[],[f41])).
% 1.91/1.01  
% 1.91/1.01  fof(f3,axiom,(
% 1.91/1.01    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.91/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.91/1.01  
% 1.91/1.01  fof(f14,plain,(
% 1.91/1.01    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.91/1.01    inference(ennf_transformation,[],[f3])).
% 1.91/1.01  
% 1.91/1.01  fof(f47,plain,(
% 1.91/1.01    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 1.91/1.01    inference(cnf_transformation,[],[f14])).
% 1.91/1.01  
% 1.91/1.01  fof(f2,axiom,(
% 1.91/1.01    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.91/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.91/1.01  
% 1.91/1.01  fof(f13,plain,(
% 1.91/1.01    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.91/1.01    inference(ennf_transformation,[],[f2])).
% 1.91/1.01  
% 1.91/1.01  fof(f28,plain,(
% 1.91/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.91/1.01    inference(nnf_transformation,[],[f13])).
% 1.91/1.01  
% 1.91/1.01  fof(f29,plain,(
% 1.91/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.91/1.01    inference(rectify,[],[f28])).
% 1.91/1.01  
% 1.91/1.01  fof(f30,plain,(
% 1.91/1.01    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 1.91/1.01    introduced(choice_axiom,[])).
% 1.91/1.01  
% 1.91/1.01  fof(f31,plain,(
% 1.91/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.91/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f29,f30])).
% 1.91/1.01  
% 1.91/1.01  fof(f44,plain,(
% 1.91/1.01    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 1.91/1.01    inference(cnf_transformation,[],[f31])).
% 1.91/1.01  
% 1.91/1.01  fof(f45,plain,(
% 1.91/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 1.91/1.01    inference(cnf_transformation,[],[f31])).
% 1.91/1.01  
% 1.91/1.01  fof(f42,plain,(
% 1.91/1.01    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 1.91/1.01    inference(cnf_transformation,[],[f27])).
% 1.91/1.01  
% 1.91/1.01  fof(f4,axiom,(
% 1.91/1.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.91/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.91/1.01  
% 1.91/1.01  fof(f32,plain,(
% 1.91/1.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.91/1.01    inference(nnf_transformation,[],[f4])).
% 1.91/1.01  
% 1.91/1.01  fof(f33,plain,(
% 1.91/1.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.91/1.01    inference(flattening,[],[f32])).
% 1.91/1.01  
% 1.91/1.01  fof(f50,plain,(
% 1.91/1.01    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 1.91/1.01    inference(cnf_transformation,[],[f33])).
% 1.91/1.01  
% 1.91/1.01  fof(f5,axiom,(
% 1.91/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X1) = X1)),
% 1.91/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.91/1.01  
% 1.91/1.01  fof(f15,plain,(
% 1.91/1.01    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.91/1.01    inference(ennf_transformation,[],[f5])).
% 1.91/1.01  
% 1.91/1.01  fof(f51,plain,(
% 1.91/1.01    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 1.91/1.01    inference(cnf_transformation,[],[f15])).
% 1.91/1.01  
% 1.91/1.01  fof(f6,axiom,(
% 1.91/1.01    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.91/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.91/1.01  
% 1.91/1.01  fof(f52,plain,(
% 1.91/1.01    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.91/1.01    inference(cnf_transformation,[],[f6])).
% 1.91/1.01  
% 1.91/1.01  fof(f60,plain,(
% 1.91/1.01    ( ! [X0,X3,X1] : (v2_tex_2(X1,X0) | k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.91/1.01    inference(cnf_transformation,[],[f38])).
% 1.91/1.01  
% 1.91/1.01  fof(f8,axiom,(
% 1.91/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_xboole_0(X1) => v4_pre_topc(X1,X0))))),
% 1.91/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.91/1.01  
% 1.91/1.01  fof(f18,plain,(
% 1.91/1.01    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) | ~v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.91/1.01    inference(ennf_transformation,[],[f8])).
% 1.91/1.01  
% 1.91/1.01  fof(f19,plain,(
% 1.91/1.01    ! [X0] : (! [X1] : (v4_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.91/1.01    inference(flattening,[],[f18])).
% 1.91/1.01  
% 1.91/1.01  fof(f54,plain,(
% 1.91/1.01    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.91/1.01    inference(cnf_transformation,[],[f19])).
% 1.91/1.01  
% 1.91/1.01  fof(f61,plain,(
% 1.91/1.01    v2_pre_topc(sK4)),
% 1.91/1.01    inference(cnf_transformation,[],[f41])).
% 1.91/1.01  
% 1.91/1.01  fof(f48,plain,(
% 1.91/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.91/1.01    inference(cnf_transformation,[],[f33])).
% 1.91/1.01  
% 1.91/1.01  fof(f67,plain,(
% 1.91/1.01    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.91/1.01    inference(equality_resolution,[],[f48])).
% 1.91/1.01  
% 1.91/1.01  cnf(c_0,plain,
% 1.91/1.01      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 1.91/1.01      inference(cnf_transformation,[],[f43]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_1908,plain,
% 1.91/1.01      ( r2_hidden(sK0(X0),X0) = iProver_top
% 1.91/1.01      | v1_xboole_0(X0) = iProver_top ),
% 1.91/1.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_20,negated_conjecture,
% 1.91/1.01      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 1.91/1.01      inference(cnf_transformation,[],[f64]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_1896,plain,
% 1.91/1.01      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 1.91/1.01      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_14,plain,
% 1.91/1.01      ( v2_tex_2(X0,X1)
% 1.91/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.91/1.01      | r1_tarski(sK2(X1,X0),X0)
% 1.91/1.01      | ~ l1_pre_topc(X1) ),
% 1.91/1.01      inference(cnf_transformation,[],[f59]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_22,negated_conjecture,
% 1.91/1.01      ( l1_pre_topc(sK4) ),
% 1.91/1.01      inference(cnf_transformation,[],[f62]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_508,plain,
% 1.91/1.01      ( v2_tex_2(X0,X1)
% 1.91/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.91/1.01      | r1_tarski(sK2(X1,X0),X0)
% 1.91/1.01      | sK4 != X1 ),
% 1.91/1.01      inference(resolution_lifted,[status(thm)],[c_14,c_22]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_509,plain,
% 1.91/1.01      ( v2_tex_2(X0,sK4)
% 1.91/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 1.91/1.01      | r1_tarski(sK2(sK4,X0),X0) ),
% 1.91/1.01      inference(unflattening,[status(thm)],[c_508]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_1889,plain,
% 1.91/1.01      ( v2_tex_2(X0,sK4) = iProver_top
% 1.91/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 1.91/1.01      | r1_tarski(sK2(sK4,X0),X0) = iProver_top ),
% 1.91/1.01      inference(predicate_to_equality,[status(thm)],[c_509]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_2332,plain,
% 1.91/1.01      ( v2_tex_2(sK5,sK4) = iProver_top
% 1.91/1.01      | r1_tarski(sK2(sK4,sK5),sK5) = iProver_top ),
% 1.91/1.01      inference(superposition,[status(thm)],[c_1896,c_1889]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_27,plain,
% 1.91/1.01      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 1.91/1.01      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_19,negated_conjecture,
% 1.91/1.01      ( ~ v2_tex_2(sK5,sK4) ),
% 1.91/1.01      inference(cnf_transformation,[],[f65]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_854,plain,
% 1.91/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 1.91/1.01      | r1_tarski(sK2(sK4,X0),X0)
% 1.91/1.01      | sK4 != sK4
% 1.91/1.01      | sK5 != X0 ),
% 1.91/1.01      inference(resolution_lifted,[status(thm)],[c_19,c_509]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_855,plain,
% 1.91/1.01      ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
% 1.91/1.01      | r1_tarski(sK2(sK4,sK5),sK5) ),
% 1.91/1.01      inference(unflattening,[status(thm)],[c_854]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_856,plain,
% 1.91/1.01      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 1.91/1.01      | r1_tarski(sK2(sK4,sK5),sK5) = iProver_top ),
% 1.91/1.01      inference(predicate_to_equality,[status(thm)],[c_855]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_2814,plain,
% 1.91/1.01      ( r1_tarski(sK2(sK4,sK5),sK5) = iProver_top ),
% 1.91/1.01      inference(global_propositional_subsumption,
% 1.91/1.01                [status(thm)],
% 1.91/1.01                [c_2332,c_27,c_856]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_21,negated_conjecture,
% 1.91/1.01      ( v1_xboole_0(sK5) ),
% 1.91/1.01      inference(cnf_transformation,[],[f63]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_1895,plain,
% 1.91/1.01      ( v1_xboole_0(sK5) = iProver_top ),
% 1.91/1.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_5,plain,
% 1.91/1.01      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 1.91/1.01      inference(cnf_transformation,[],[f47]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_1903,plain,
% 1.91/1.01      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 1.91/1.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_2466,plain,
% 1.91/1.01      ( sK5 = k1_xboole_0 ),
% 1.91/1.01      inference(superposition,[status(thm)],[c_1895,c_1903]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_2818,plain,
% 1.91/1.01      ( r1_tarski(sK2(sK4,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 1.91/1.01      inference(light_normalisation,[status(thm)],[c_2814,c_2466]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_4,plain,
% 1.91/1.01      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 1.91/1.01      inference(cnf_transformation,[],[f44]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_1904,plain,
% 1.91/1.01      ( r1_tarski(X0,X1) != iProver_top
% 1.91/1.01      | r2_hidden(X2,X0) != iProver_top
% 1.91/1.01      | r2_hidden(X2,X1) = iProver_top ),
% 1.91/1.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_3929,plain,
% 1.91/1.01      ( r2_hidden(X0,sK2(sK4,k1_xboole_0)) != iProver_top
% 1.91/1.01      | r2_hidden(X0,k1_xboole_0) = iProver_top ),
% 1.91/1.01      inference(superposition,[status(thm)],[c_2818,c_1904]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_4664,plain,
% 1.91/1.01      ( r2_hidden(sK0(sK2(sK4,k1_xboole_0)),k1_xboole_0) = iProver_top
% 1.91/1.01      | v1_xboole_0(sK2(sK4,k1_xboole_0)) = iProver_top ),
% 1.91/1.01      inference(superposition,[status(thm)],[c_1908,c_3929]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_26,plain,
% 1.91/1.01      ( v1_xboole_0(sK5) = iProver_top ),
% 1.91/1.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_335,plain,
% 1.91/1.01      ( sK5 != X0 | k1_xboole_0 = X0 ),
% 1.91/1.01      inference(resolution_lifted,[status(thm)],[c_5,c_21]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_336,plain,
% 1.91/1.01      ( k1_xboole_0 = sK5 ),
% 1.91/1.01      inference(unflattening,[status(thm)],[c_335]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_1480,plain,
% 1.91/1.01      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 1.91/1.01      theory(equality) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_2235,plain,
% 1.91/1.01      ( ~ v1_xboole_0(X0)
% 1.91/1.01      | v1_xboole_0(k1_xboole_0)
% 1.91/1.01      | k1_xboole_0 != X0 ),
% 1.91/1.01      inference(instantiation,[status(thm)],[c_1480]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_2587,plain,
% 1.91/1.01      ( ~ v1_xboole_0(sK5)
% 1.91/1.01      | v1_xboole_0(k1_xboole_0)
% 1.91/1.01      | k1_xboole_0 != sK5 ),
% 1.91/1.01      inference(instantiation,[status(thm)],[c_2235]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_2588,plain,
% 1.91/1.01      ( k1_xboole_0 != sK5
% 1.91/1.01      | v1_xboole_0(sK5) != iProver_top
% 1.91/1.01      | v1_xboole_0(k1_xboole_0) = iProver_top ),
% 1.91/1.01      inference(predicate_to_equality,[status(thm)],[c_2587]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_2685,plain,
% 1.91/1.01      ( v1_xboole_0(X0)
% 1.91/1.01      | ~ v1_xboole_0(k1_xboole_0)
% 1.91/1.01      | X0 != k1_xboole_0 ),
% 1.91/1.01      inference(instantiation,[status(thm)],[c_1480]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_4292,plain,
% 1.91/1.01      ( v1_xboole_0(sK2(sK4,k1_xboole_0))
% 1.91/1.01      | ~ v1_xboole_0(k1_xboole_0)
% 1.91/1.01      | sK2(sK4,k1_xboole_0) != k1_xboole_0 ),
% 1.91/1.01      inference(instantiation,[status(thm)],[c_2685]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_4293,plain,
% 1.91/1.01      ( sK2(sK4,k1_xboole_0) != k1_xboole_0
% 1.91/1.01      | v1_xboole_0(sK2(sK4,k1_xboole_0)) = iProver_top
% 1.91/1.01      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 1.91/1.01      inference(predicate_to_equality,[status(thm)],[c_4292]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_3,plain,
% 1.91/1.01      ( r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 1.91/1.01      inference(cnf_transformation,[],[f45]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_1905,plain,
% 1.91/1.01      ( r1_tarski(X0,X1) = iProver_top
% 1.91/1.01      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 1.91/1.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_1,plain,
% 1.91/1.01      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 1.91/1.01      inference(cnf_transformation,[],[f42]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_1907,plain,
% 1.91/1.01      ( r2_hidden(X0,X1) != iProver_top
% 1.91/1.01      | v1_xboole_0(X1) != iProver_top ),
% 1.91/1.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_3178,plain,
% 1.91/1.01      ( r1_tarski(X0,X1) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 1.91/1.01      inference(superposition,[status(thm)],[c_1905,c_1907]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_6,plain,
% 1.91/1.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 1.91/1.01      inference(cnf_transformation,[],[f50]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_1902,plain,
% 1.91/1.01      ( X0 = X1
% 1.91/1.01      | r1_tarski(X1,X0) != iProver_top
% 1.91/1.01      | r1_tarski(X0,X1) != iProver_top ),
% 1.91/1.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_3761,plain,
% 1.91/1.01      ( sK2(sK4,k1_xboole_0) = k1_xboole_0
% 1.91/1.01      | r1_tarski(k1_xboole_0,sK2(sK4,k1_xboole_0)) != iProver_top ),
% 1.91/1.01      inference(superposition,[status(thm)],[c_2818,c_1902]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_4659,plain,
% 1.91/1.01      ( sK2(sK4,k1_xboole_0) = k1_xboole_0
% 1.91/1.01      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 1.91/1.01      inference(superposition,[status(thm)],[c_3178,c_3761]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_4770,plain,
% 1.91/1.01      ( v1_xboole_0(sK2(sK4,k1_xboole_0)) = iProver_top ),
% 1.91/1.01      inference(global_propositional_subsumption,
% 1.91/1.01                [status(thm)],
% 1.91/1.01                [c_4664,c_26,c_336,c_2588,c_4293,c_4659]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_4775,plain,
% 1.91/1.01      ( sK2(sK4,k1_xboole_0) = k1_xboole_0 ),
% 1.91/1.01      inference(superposition,[status(thm)],[c_4770,c_1903]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_9,plain,
% 1.91/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | k9_subset_1(X1,X2,X2) = X2 ),
% 1.91/1.01      inference(cnf_transformation,[],[f51]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_1900,plain,
% 1.91/1.01      ( k9_subset_1(X0,X1,X1) = X1
% 1.91/1.01      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 1.91/1.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_10,plain,
% 1.91/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 1.91/1.01      inference(cnf_transformation,[],[f52]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_2092,plain,
% 1.91/1.01      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
% 1.91/1.01      | k9_subset_1(X0,X1,X1) = X1 ),
% 1.91/1.01      inference(instantiation,[status(thm)],[c_9]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_3181,plain,
% 1.91/1.01      ( k9_subset_1(X0,X1,X1) = X1 ),
% 1.91/1.01      inference(global_propositional_subsumption,
% 1.91/1.01                [status(thm)],
% 1.91/1.01                [c_1900,c_10,c_2092]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_13,plain,
% 1.91/1.01      ( v2_tex_2(X0,X1)
% 1.91/1.01      | ~ v4_pre_topc(X2,X1)
% 1.91/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.91/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.91/1.01      | ~ l1_pre_topc(X1)
% 1.91/1.01      | k9_subset_1(u1_struct_0(X1),X0,X2) != sK2(X1,X0) ),
% 1.91/1.01      inference(cnf_transformation,[],[f60]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_523,plain,
% 1.91/1.01      ( v2_tex_2(X0,X1)
% 1.91/1.01      | ~ v4_pre_topc(X2,X1)
% 1.91/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.91/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.91/1.01      | k9_subset_1(u1_struct_0(X1),X0,X2) != sK2(X1,X0)
% 1.91/1.01      | sK4 != X1 ),
% 1.91/1.01      inference(resolution_lifted,[status(thm)],[c_13,c_22]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_524,plain,
% 1.91/1.01      ( v2_tex_2(X0,sK4)
% 1.91/1.01      | ~ v4_pre_topc(X1,sK4)
% 1.91/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 1.91/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 1.91/1.01      | k9_subset_1(u1_struct_0(sK4),X0,X1) != sK2(sK4,X0) ),
% 1.91/1.01      inference(unflattening,[status(thm)],[c_523]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_1888,plain,
% 1.91/1.01      ( k9_subset_1(u1_struct_0(sK4),X0,X1) != sK2(sK4,X0)
% 1.91/1.01      | v2_tex_2(X0,sK4) = iProver_top
% 1.91/1.01      | v4_pre_topc(X1,sK4) != iProver_top
% 1.91/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 1.91/1.01      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 1.91/1.01      inference(predicate_to_equality,[status(thm)],[c_524]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_3185,plain,
% 1.91/1.01      ( sK2(sK4,X0) != X0
% 1.91/1.01      | v2_tex_2(X0,sK4) = iProver_top
% 1.91/1.01      | v4_pre_topc(X0,sK4) != iProver_top
% 1.91/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 1.91/1.01      inference(superposition,[status(thm)],[c_3181,c_1888]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_5484,plain,
% 1.91/1.01      ( v2_tex_2(k1_xboole_0,sK4) = iProver_top
% 1.91/1.01      | v4_pre_topc(k1_xboole_0,sK4) != iProver_top
% 1.91/1.01      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 1.91/1.01      inference(superposition,[status(thm)],[c_4775,c_3185]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_1897,plain,
% 1.91/1.01      ( v2_tex_2(sK5,sK4) != iProver_top ),
% 1.91/1.01      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_2596,plain,
% 1.91/1.01      ( v2_tex_2(k1_xboole_0,sK4) != iProver_top ),
% 1.91/1.01      inference(demodulation,[status(thm)],[c_2466,c_1897]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_1486,plain,
% 1.91/1.01      ( ~ v4_pre_topc(X0,X1) | v4_pre_topc(X2,X3) | X2 != X0 | X3 != X1 ),
% 1.91/1.01      theory(equality) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_2132,plain,
% 1.91/1.01      ( v4_pre_topc(X0,X1)
% 1.91/1.01      | ~ v4_pre_topc(sK5,sK4)
% 1.91/1.01      | X1 != sK4
% 1.91/1.01      | X0 != sK5 ),
% 1.91/1.01      inference(instantiation,[status(thm)],[c_1486]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_2497,plain,
% 1.91/1.01      ( ~ v4_pre_topc(sK5,sK4)
% 1.91/1.01      | v4_pre_topc(k1_xboole_0,X0)
% 1.91/1.01      | X0 != sK4
% 1.91/1.01      | k1_xboole_0 != sK5 ),
% 1.91/1.01      inference(instantiation,[status(thm)],[c_2132]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_2498,plain,
% 1.91/1.01      ( X0 != sK4
% 1.91/1.01      | k1_xboole_0 != sK5
% 1.91/1.01      | v4_pre_topc(sK5,sK4) != iProver_top
% 1.91/1.01      | v4_pre_topc(k1_xboole_0,X0) = iProver_top ),
% 1.91/1.01      inference(predicate_to_equality,[status(thm)],[c_2497]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_2500,plain,
% 1.91/1.01      ( sK4 != sK4
% 1.91/1.01      | k1_xboole_0 != sK5
% 1.91/1.01      | v4_pre_topc(sK5,sK4) != iProver_top
% 1.91/1.01      | v4_pre_topc(k1_xboole_0,sK4) = iProver_top ),
% 1.91/1.01      inference(instantiation,[status(thm)],[c_2498]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_2080,plain,
% 1.91/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 1.91/1.01      inference(instantiation,[status(thm)],[c_10]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_2084,plain,
% 1.91/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 1.91/1.01      inference(predicate_to_equality,[status(thm)],[c_2080]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_12,plain,
% 1.91/1.01      ( v4_pre_topc(X0,X1)
% 1.91/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.91/1.01      | ~ v2_pre_topc(X1)
% 1.91/1.01      | ~ l1_pre_topc(X1)
% 1.91/1.01      | ~ v1_xboole_0(X0) ),
% 1.91/1.01      inference(cnf_transformation,[],[f54]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_23,negated_conjecture,
% 1.91/1.01      ( v2_pre_topc(sK4) ),
% 1.91/1.01      inference(cnf_transformation,[],[f61]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_262,plain,
% 1.91/1.01      ( v4_pre_topc(X0,X1)
% 1.91/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.91/1.01      | ~ l1_pre_topc(X1)
% 1.91/1.01      | ~ v1_xboole_0(X0)
% 1.91/1.01      | sK4 != X1 ),
% 1.91/1.01      inference(resolution_lifted,[status(thm)],[c_12,c_23]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_263,plain,
% 1.91/1.01      ( v4_pre_topc(X0,sK4)
% 1.91/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 1.91/1.01      | ~ l1_pre_topc(sK4)
% 1.91/1.01      | ~ v1_xboole_0(X0) ),
% 1.91/1.01      inference(unflattening,[status(thm)],[c_262]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_267,plain,
% 1.91/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 1.91/1.01      | v4_pre_topc(X0,sK4)
% 1.91/1.01      | ~ v1_xboole_0(X0) ),
% 1.91/1.01      inference(global_propositional_subsumption,
% 1.91/1.01                [status(thm)],
% 1.91/1.01                [c_263,c_22]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_268,plain,
% 1.91/1.01      ( v4_pre_topc(X0,sK4)
% 1.91/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 1.91/1.01      | ~ v1_xboole_0(X0) ),
% 1.91/1.01      inference(renaming,[status(thm)],[c_267]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_324,plain,
% 1.91/1.01      ( v4_pre_topc(X0,sK4)
% 1.91/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 1.91/1.01      | sK5 != X0 ),
% 1.91/1.01      inference(resolution_lifted,[status(thm)],[c_268,c_21]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_325,plain,
% 1.91/1.01      ( v4_pre_topc(sK5,sK4)
% 1.91/1.01      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 1.91/1.01      inference(unflattening,[status(thm)],[c_324]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_326,plain,
% 1.91/1.01      ( v4_pre_topc(sK5,sK4) = iProver_top
% 1.91/1.01      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 1.91/1.01      inference(predicate_to_equality,[status(thm)],[c_325]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_64,plain,
% 1.91/1.01      ( ~ r1_tarski(sK4,sK4) | sK4 = sK4 ),
% 1.91/1.01      inference(instantiation,[status(thm)],[c_6]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_8,plain,
% 1.91/1.01      ( r1_tarski(X0,X0) ),
% 1.91/1.01      inference(cnf_transformation,[],[f67]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_60,plain,
% 1.91/1.01      ( r1_tarski(sK4,sK4) ),
% 1.91/1.01      inference(instantiation,[status(thm)],[c_8]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(contradiction,plain,
% 1.91/1.01      ( $false ),
% 1.91/1.01      inference(minisat,
% 1.91/1.01                [status(thm)],
% 1.91/1.01                [c_5484,c_2596,c_2500,c_2084,c_336,c_326,c_64,c_60,c_27]) ).
% 1.91/1.01  
% 1.91/1.01  
% 1.91/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 1.91/1.01  
% 1.91/1.01  ------                               Statistics
% 1.91/1.01  
% 1.91/1.01  ------ General
% 1.91/1.01  
% 1.91/1.01  abstr_ref_over_cycles:                  0
% 1.91/1.01  abstr_ref_under_cycles:                 0
% 1.91/1.01  gc_basic_clause_elim:                   0
% 1.91/1.01  forced_gc_time:                         0
% 1.91/1.01  parsing_time:                           0.011
% 1.91/1.01  unif_index_cands_time:                  0.
% 1.91/1.01  unif_index_add_time:                    0.
% 1.91/1.01  orderings_time:                         0.
% 1.91/1.01  out_proof_time:                         0.006
% 1.91/1.01  total_time:                             0.18
% 1.91/1.01  num_of_symbols:                         49
% 1.91/1.01  num_of_terms:                           3992
% 1.91/1.01  
% 1.91/1.01  ------ Preprocessing
% 1.91/1.01  
% 1.91/1.01  num_of_splits:                          0
% 1.91/1.01  num_of_split_atoms:                     0
% 1.91/1.01  num_of_reused_defs:                     0
% 1.91/1.01  num_eq_ax_congr_red:                    30
% 1.91/1.01  num_of_sem_filtered_clauses:            1
% 1.91/1.01  num_of_subtypes:                        0
% 1.91/1.01  monotx_restored_types:                  0
% 1.91/1.01  sat_num_of_epr_types:                   0
% 1.91/1.01  sat_num_of_non_cyclic_types:            0
% 1.91/1.01  sat_guarded_non_collapsed_types:        0
% 1.91/1.01  num_pure_diseq_elim:                    0
% 1.91/1.01  simp_replaced_by:                       0
% 1.91/1.01  res_preprocessed:                       113
% 1.91/1.01  prep_upred:                             0
% 1.91/1.01  prep_unflattend:                        29
% 1.91/1.01  smt_new_axioms:                         0
% 1.91/1.01  pred_elim_cands:                        6
% 1.91/1.01  pred_elim:                              2
% 1.91/1.01  pred_elim_cl:                           2
% 1.91/1.01  pred_elim_cycles:                       9
% 1.91/1.01  merged_defs:                            0
% 1.91/1.01  merged_defs_ncl:                        0
% 1.91/1.01  bin_hyper_res:                          0
% 1.91/1.01  prep_cycles:                            4
% 1.91/1.01  pred_elim_time:                         0.021
% 1.91/1.01  splitting_time:                         0.
% 1.91/1.01  sem_filter_time:                        0.
% 1.91/1.01  monotx_time:                            0.001
% 1.91/1.01  subtype_inf_time:                       0.
% 1.91/1.01  
% 1.91/1.01  ------ Problem properties
% 1.91/1.01  
% 1.91/1.01  clauses:                                21
% 1.91/1.01  conjectures:                            3
% 1.91/1.01  epr:                                    7
% 1.91/1.01  horn:                                   17
% 1.91/1.01  ground:                                 3
% 1.91/1.01  unary:                                  5
% 1.91/1.01  binary:                                 6
% 1.91/1.01  lits:                                   55
% 1.91/1.01  lits_eq:                                5
% 1.91/1.01  fd_pure:                                0
% 1.91/1.01  fd_pseudo:                              0
% 1.91/1.01  fd_cond:                                1
% 1.91/1.01  fd_pseudo_cond:                         1
% 1.91/1.01  ac_symbols:                             0
% 1.91/1.01  
% 1.91/1.01  ------ Propositional Solver
% 1.91/1.01  
% 1.91/1.01  prop_solver_calls:                      27
% 1.91/1.01  prop_fast_solver_calls:                 1060
% 1.91/1.01  smt_solver_calls:                       0
% 1.91/1.01  smt_fast_solver_calls:                  0
% 1.91/1.01  prop_num_of_clauses:                    1767
% 1.91/1.01  prop_preprocess_simplified:             5241
% 1.91/1.01  prop_fo_subsumed:                       22
% 1.91/1.01  prop_solver_time:                       0.
% 1.91/1.01  smt_solver_time:                        0.
% 1.91/1.01  smt_fast_solver_time:                   0.
% 1.91/1.01  prop_fast_solver_time:                  0.
% 1.91/1.01  prop_unsat_core_time:                   0.
% 1.91/1.01  
% 1.91/1.01  ------ QBF
% 1.91/1.01  
% 1.91/1.01  qbf_q_res:                              0
% 1.91/1.01  qbf_num_tautologies:                    0
% 1.91/1.01  qbf_prep_cycles:                        0
% 1.91/1.01  
% 1.91/1.01  ------ BMC1
% 1.91/1.01  
% 1.91/1.01  bmc1_current_bound:                     -1
% 1.91/1.01  bmc1_last_solved_bound:                 -1
% 1.91/1.01  bmc1_unsat_core_size:                   -1
% 1.91/1.01  bmc1_unsat_core_parents_size:           -1
% 1.91/1.01  bmc1_merge_next_fun:                    0
% 1.91/1.01  bmc1_unsat_core_clauses_time:           0.
% 1.91/1.01  
% 1.91/1.01  ------ Instantiation
% 1.91/1.01  
% 1.91/1.01  inst_num_of_clauses:                    486
% 1.91/1.01  inst_num_in_passive:                    62
% 1.91/1.01  inst_num_in_active:                     243
% 1.91/1.01  inst_num_in_unprocessed:                183
% 1.91/1.01  inst_num_of_loops:                      290
% 1.91/1.01  inst_num_of_learning_restarts:          0
% 1.91/1.01  inst_num_moves_active_passive:          44
% 1.91/1.01  inst_lit_activity:                      0
% 1.91/1.01  inst_lit_activity_moves:                0
% 1.91/1.01  inst_num_tautologies:                   0
% 1.91/1.01  inst_num_prop_implied:                  0
% 1.91/1.01  inst_num_existing_simplified:           0
% 1.91/1.01  inst_num_eq_res_simplified:             0
% 1.91/1.01  inst_num_child_elim:                    0
% 1.91/1.01  inst_num_of_dismatching_blockings:      73
% 1.91/1.01  inst_num_of_non_proper_insts:           400
% 1.91/1.01  inst_num_of_duplicates:                 0
% 1.91/1.01  inst_inst_num_from_inst_to_res:         0
% 1.91/1.01  inst_dismatching_checking_time:         0.
% 1.91/1.01  
% 1.91/1.01  ------ Resolution
% 1.91/1.01  
% 1.91/1.01  res_num_of_clauses:                     0
% 1.91/1.01  res_num_in_passive:                     0
% 1.91/1.01  res_num_in_active:                      0
% 1.91/1.01  res_num_of_loops:                       117
% 1.91/1.01  res_forward_subset_subsumed:            49
% 1.91/1.01  res_backward_subset_subsumed:           4
% 1.91/1.01  res_forward_subsumed:                   0
% 1.91/1.01  res_backward_subsumed:                  0
% 1.91/1.01  res_forward_subsumption_resolution:     2
% 1.91/1.01  res_backward_subsumption_resolution:    0
% 1.91/1.01  res_clause_to_clause_subsumption:       684
% 1.91/1.01  res_orphan_elimination:                 0
% 1.91/1.01  res_tautology_del:                      30
% 1.91/1.01  res_num_eq_res_simplified:              0
% 1.91/1.01  res_num_sel_changes:                    0
% 1.91/1.01  res_moves_from_active_to_pass:          0
% 1.91/1.01  
% 1.91/1.01  ------ Superposition
% 1.91/1.01  
% 1.91/1.01  sup_time_total:                         0.
% 1.91/1.01  sup_time_generating:                    0.
% 1.91/1.01  sup_time_sim_full:                      0.
% 1.91/1.01  sup_time_sim_immed:                     0.
% 1.91/1.01  
% 1.91/1.01  sup_num_of_clauses:                     77
% 1.91/1.01  sup_num_in_active:                      47
% 1.91/1.01  sup_num_in_passive:                     30
% 1.91/1.01  sup_num_of_loops:                       56
% 1.91/1.01  sup_fw_superposition:                   50
% 1.91/1.01  sup_bw_superposition:                   36
% 1.91/1.01  sup_immediate_simplified:               13
% 1.91/1.01  sup_given_eliminated:                   0
% 1.91/1.01  comparisons_done:                       0
% 1.91/1.01  comparisons_avoided:                    0
% 1.91/1.01  
% 1.91/1.01  ------ Simplifications
% 1.91/1.01  
% 1.91/1.01  
% 1.91/1.01  sim_fw_subset_subsumed:                 4
% 1.91/1.01  sim_bw_subset_subsumed:                 3
% 1.91/1.01  sim_fw_subsumed:                        9
% 1.91/1.01  sim_bw_subsumed:                        0
% 1.91/1.01  sim_fw_subsumption_res:                 0
% 1.91/1.01  sim_bw_subsumption_res:                 0
% 1.91/1.01  sim_tautology_del:                      8
% 1.91/1.01  sim_eq_tautology_del:                   2
% 1.91/1.01  sim_eq_res_simp:                        0
% 1.91/1.01  sim_fw_demodulated:                     0
% 1.91/1.01  sim_bw_demodulated:                     9
% 1.91/1.01  sim_light_normalised:                   8
% 1.91/1.01  sim_joinable_taut:                      0
% 1.91/1.01  sim_joinable_simp:                      0
% 1.91/1.01  sim_ac_normalised:                      0
% 1.91/1.01  sim_smt_subsumption:                    0
% 1.91/1.01  
%------------------------------------------------------------------------------
