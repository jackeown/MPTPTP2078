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
% DateTime   : Thu Dec  3 12:25:54 EST 2020

% Result     : Theorem 2.40s
% Output     : CNFRefutation 2.40s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 998 expanded)
%              Number of clauses        :   96 ( 287 expanded)
%              Number of leaves         :   18 ( 288 expanded)
%              Depth                    :   27
%              Number of atoms          :  535 (6400 expanded)
%              Number of equality atoms :  197 (1250 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f18])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f58,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f32])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
     => ( k1_xboole_0 != X0
       => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f12,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f11])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tarski(X1,X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(definition_unfolding,[],[f38,f35])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f9,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( k1_tarski(X2) = k9_subset_1(u1_struct_0(X0),X1,X3)
                            & v3_pre_topc(X3,X0) ) )
                    & r2_hidden(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tex_2(X1,X0)
             => ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ~ ( ! [X3] :
                          ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                         => ~ ( k1_tarski(X2) = k9_subset_1(u1_struct_0(X0),X1,X3)
                              & v3_pre_topc(X3,X0) ) )
                      & r2_hidden(X2,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),X1,X3)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),X1,X3)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),X1,X3)
              | ~ v3_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ! [X3] :
            ( k1_tarski(sK4) != k9_subset_1(u1_struct_0(X0),X1,X3)
            | ~ v3_pre_topc(X3,X0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & r2_hidden(sK4,X1)
        & m1_subset_1(sK4,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),X1,X3)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ! [X3] :
                ( k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),sK3,X3)
                | ~ v3_pre_topc(X3,X0)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            & r2_hidden(X2,sK3)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & v2_tex_2(sK3,X0)
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ! [X3] :
                    ( k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),X1,X3)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & r2_hidden(X2,X1)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & v2_tex_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( k1_tarski(X2) != k9_subset_1(u1_struct_0(sK2),X1,X3)
                  | ~ v3_pre_topc(X3,sK2)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(sK2)) )
          & v2_tex_2(X1,sK2)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
      & l1_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ! [X3] :
        ( k1_tarski(sK4) != k9_subset_1(u1_struct_0(sK2),sK3,X3)
        | ~ v3_pre_topc(X3,sK2)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
    & r2_hidden(sK4,sK3)
    & m1_subset_1(sK4,u1_struct_0(sK2))
    & v2_tex_2(sK3,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & l1_pre_topc(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f17,f29,f28,f27])).

fof(f49,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f30])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
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

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f22,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f23,plain,(
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
    inference(rectify,[],[f22])).

fof(f25,plain,(
    ! [X4,X1,X0] :
      ( ? [X5] :
          ( k9_subset_1(u1_struct_0(X0),X1,X5) = X4
          & v3_pre_topc(X5,X0)
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X0),X1,sK1(X0,X1,X4)) = X4
        & v3_pre_topc(sK1(X0,X1,X4),X0)
        & m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
              | ~ v3_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ! [X3] :
            ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK0(X0,X1)
            | ~ v3_pre_topc(X3,X0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & r1_tarski(sK0(X0,X1),X1)
        & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ( ! [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK0(X0,X1)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & r1_tarski(sK0(X0,X1),X1)
                & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X4] :
                  ( ( k9_subset_1(u1_struct_0(X0),X1,sK1(X0,X1,X4)) = X4
                    & v3_pre_topc(sK1(X0,X1,X4),X0)
                    & m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r1_tarski(X4,X1)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f25,f24])).

fof(f44,plain,(
    ! [X4,X0,X1] :
      ( k9_subset_1(u1_struct_0(X0),X1,sK1(X0,X1,X4)) = X4
      | ~ r1_tarski(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f48,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f51,plain,(
    m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f30])).

fof(f42,plain,(
    ! [X4,X0,X1] :
      ( m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tarski(X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f37,f35])).

fof(f52,plain,(
    r2_hidden(sK4,sK3) ),
    inference(cnf_transformation,[],[f30])).

fof(f50,plain,(
    v2_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f53,plain,(
    ! [X3] :
      ( k1_tarski(sK4) != k9_subset_1(u1_struct_0(sK2),sK3,X3)
      | ~ v3_pre_topc(X3,sK2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f57,plain,(
    ! [X3] :
      ( k2_tarski(sK4,sK4) != k9_subset_1(u1_struct_0(sK2),sK3,X3)
      | ~ v3_pre_topc(X3,sK2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(definition_unfolding,[],[f53,f35])).

fof(f43,plain,(
    ! [X4,X0,X1] :
      ( v3_pre_topc(sK1(X0,X1,X4),X0)
      | ~ r1_tarski(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f33,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1944,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1))
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1942,plain,
    ( k1_xboole_0 = X0
    | m1_subset_1(X1,X0) != iProver_top
    | m1_subset_1(k2_tarski(X1,X1),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1940,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3153,plain,
    ( k1_xboole_0 = X0
    | m1_subset_1(X1,X0) != iProver_top
    | r1_tarski(k2_tarski(X1,X1),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1942,c_1940])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1936,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_7,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1941,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_13,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | ~ l1_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),X0,sK1(X1,X0,X2)) = X2 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_21,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_448,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | k9_subset_1(u1_struct_0(X1),X0,sK1(X1,X0,X2)) = X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_21])).

cnf(c_449,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X1,X0)
    | k9_subset_1(u1_struct_0(sK2),X0,sK1(sK2,X0,X1)) = X1 ),
    inference(unflattening,[status(thm)],[c_448])).

cnf(c_1930,plain,
    ( k9_subset_1(u1_struct_0(sK2),X0,sK1(sK2,X0,X1)) = X1
    | v2_tex_2(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_449])).

cnf(c_2581,plain,
    ( k9_subset_1(u1_struct_0(sK2),X0,sK1(sK2,X0,X1)) = X1
    | v2_tex_2(X0,sK2) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1941,c_1930])).

cnf(c_3490,plain,
    ( k9_subset_1(u1_struct_0(sK2),X0,sK1(sK2,X0,sK3)) = sK3
    | v2_tex_2(X0,sK2) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK2)) != iProver_top
    | r1_tarski(sK3,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1936,c_2581])).

cnf(c_4215,plain,
    ( k9_subset_1(u1_struct_0(sK2),k2_tarski(X0,X0),sK1(sK2,k2_tarski(X0,X0),sK3)) = sK3
    | u1_struct_0(sK2) = k1_xboole_0
    | v2_tex_2(k2_tarski(X0,X0),sK2) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | r1_tarski(sK3,k2_tarski(X0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3153,c_3490])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_25,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_15,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK1(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_427,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK1(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_21])).

cnf(c_428,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(sK1(sK2,X0,X1),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X1,X0) ),
    inference(unflattening,[status(thm)],[c_427])).

cnf(c_1931,plain,
    ( v2_tex_2(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK1(sK2,X0,X1),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_428])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k2_tarski(X0,X0),X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_170,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k2_tarski(X0,X0),X1) ),
    inference(prop_impl,[status(thm)],[c_4])).

cnf(c_17,negated_conjecture,
    ( r2_hidden(sK4,sK3) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_317,plain,
    ( r1_tarski(k2_tarski(X0,X0),X1)
    | sK3 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_170,c_17])).

cnf(c_318,plain,
    ( r1_tarski(k2_tarski(sK4,sK4),sK3) ),
    inference(unflattening,[status(thm)],[c_317])).

cnf(c_1933,plain,
    ( r1_tarski(k2_tarski(sK4,sK4),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_318])).

cnf(c_2582,plain,
    ( k9_subset_1(u1_struct_0(sK2),sK3,sK1(sK2,sK3,X0)) = X0
    | v2_tex_2(sK3,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1936,c_1930])).

cnf(c_23,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_19,negated_conjecture,
    ( v2_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_737,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X1,X0)
    | k9_subset_1(u1_struct_0(sK2),X0,sK1(sK2,X0,X1)) = X1
    | sK3 != X0
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_449])).

cnf(c_738,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X0,sK3)
    | k9_subset_1(u1_struct_0(sK2),sK3,sK1(sK2,sK3,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_737])).

cnf(c_739,plain,
    ( k9_subset_1(u1_struct_0(sK2),sK3,sK1(sK2,sK3,X0)) = X0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(X0,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_738])).

cnf(c_2604,plain,
    ( k9_subset_1(u1_struct_0(sK2),sK3,sK1(sK2,sK3,X0)) = X0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(X0,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2582,c_23,c_739])).

cnf(c_3154,plain,
    ( k9_subset_1(u1_struct_0(sK2),sK3,sK1(sK2,sK3,k2_tarski(X0,X0))) = k2_tarski(X0,X0)
    | u1_struct_0(sK2) = k1_xboole_0
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | r1_tarski(k2_tarski(X0,X0),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1942,c_2604])).

cnf(c_4574,plain,
    ( k9_subset_1(u1_struct_0(sK2),sK3,sK1(sK2,sK3,k2_tarski(sK4,sK4))) = k2_tarski(sK4,sK4)
    | u1_struct_0(sK2) = k1_xboole_0
    | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1933,c_3154])).

cnf(c_4594,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | k9_subset_1(u1_struct_0(sK2),sK3,sK1(sK2,sK3,k2_tarski(sK4,sK4))) = k2_tarski(sK4,sK4)
    | u1_struct_0(sK2) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4574])).

cnf(c_4596,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | k9_subset_1(u1_struct_0(sK2),sK3,sK1(sK2,sK3,k2_tarski(sK4,sK4))) = k2_tarski(sK4,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4574,c_18,c_4594])).

cnf(c_4597,plain,
    ( k9_subset_1(u1_struct_0(sK2),sK3,sK1(sK2,sK3,k2_tarski(sK4,sK4))) = k2_tarski(sK4,sK4)
    | u1_struct_0(sK2) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_4596])).

cnf(c_16,negated_conjecture,
    ( ~ v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k2_tarski(sK4,sK4) != k9_subset_1(u1_struct_0(sK2),sK3,X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1939,plain,
    ( k2_tarski(sK4,sK4) != k9_subset_1(u1_struct_0(sK2),sK3,X0)
    | v3_pre_topc(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4600,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | v3_pre_topc(sK1(sK2,sK3,k2_tarski(sK4,sK4)),sK2) != iProver_top
    | m1_subset_1(sK1(sK2,sK3,k2_tarski(sK4,sK4)),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4597,c_1939])).

cnf(c_4695,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | v3_pre_topc(sK1(sK2,sK3,k2_tarski(sK4,sK4)),sK2) != iProver_top
    | v2_tex_2(sK3,sK2) != iProver_top
    | m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(k2_tarski(sK4,sK4),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1931,c_4600])).

cnf(c_24,plain,
    ( v2_tex_2(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_319,plain,
    ( r1_tarski(k2_tarski(sK4,sK4),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_318])).

cnf(c_14,plain,
    ( v3_pre_topc(sK1(X0,X1,X2),X0)
    | ~ v2_tex_2(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r1_tarski(X2,X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_406,plain,
    ( v3_pre_topc(sK1(X0,X1,X2),X0)
    | ~ v2_tex_2(X1,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r1_tarski(X2,X1)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_21])).

cnf(c_407,plain,
    ( v3_pre_topc(sK1(sK2,X0,X1),sK2)
    | ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X1,X0) ),
    inference(unflattening,[status(thm)],[c_406])).

cnf(c_2086,plain,
    ( v3_pre_topc(sK1(sK2,sK3,X0),sK2)
    | ~ v2_tex_2(sK3,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X0,sK3) ),
    inference(instantiation,[status(thm)],[c_407])).

cnf(c_2185,plain,
    ( v3_pre_topc(sK1(sK2,sK3,k2_tarski(sK4,sK4)),sK2)
    | ~ v2_tex_2(sK3,sK2)
    | ~ m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(k2_tarski(sK4,sK4),sK3) ),
    inference(instantiation,[status(thm)],[c_2086])).

cnf(c_2186,plain,
    ( v3_pre_topc(sK1(sK2,sK3,k2_tarski(sK4,sK4)),sK2) = iProver_top
    | v2_tex_2(sK3,sK2) != iProver_top
    | m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(k2_tarski(sK4,sK4),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2185])).

cnf(c_5021,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4695,c_23,c_24,c_319,c_2186])).

cnf(c_5027,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1942,c_5021])).

cnf(c_5180,plain,
    ( u1_struct_0(sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4215,c_25,c_5027])).

cnf(c_5199,plain,
    ( k9_subset_1(k1_xboole_0,X0,sK1(sK2,X0,sK3)) = sK3
    | v2_tex_2(X0,sK2) != iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top
    | r1_tarski(sK3,X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5180,c_3490])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_66,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_310,plain,
    ( ~ r1_tarski(X0,X1)
    | sK3 != X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_17])).

cnf(c_311,plain,
    ( ~ r1_tarski(sK3,sK4) ),
    inference(unflattening,[status(thm)],[c_310])).

cnf(c_2104,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK4))
    | r1_tarski(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2180,plain,
    ( r1_tarski(k1_xboole_0,sK3) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2183,plain,
    ( r1_tarski(k1_xboole_0,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2180])).

cnf(c_1466,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2217,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_1466])).

cnf(c_2230,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1466])).

cnf(c_2372,plain,
    ( r1_tarski(k1_xboole_0,sK4) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_2414,plain,
    ( ~ r1_tarski(X0,sK3)
    | ~ r1_tarski(sK3,X0)
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2415,plain,
    ( sK3 = X0
    | r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(sK3,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2414])).

cnf(c_3089,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK4))
    | ~ r1_tarski(X0,sK4) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1468,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2188,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,sK3)
    | X2 != X0
    | sK3 != X1 ),
    inference(instantiation,[status(thm)],[c_1468])).

cnf(c_2443,plain,
    ( ~ r1_tarski(X0,sK3)
    | r1_tarski(X1,sK3)
    | X1 != X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2188])).

cnf(c_3305,plain,
    ( r1_tarski(X0,sK3)
    | ~ r1_tarski(k1_xboole_0,sK3)
    | X0 != k1_xboole_0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2443])).

cnf(c_3306,plain,
    ( X0 != k1_xboole_0
    | sK3 != sK3
    | r1_tarski(X0,sK3) = iProver_top
    | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3305])).

cnf(c_1471,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2127,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | X0 != X2
    | X1 != k1_zfmisc_1(X3) ),
    inference(instantiation,[status(thm)],[c_1471])).

cnf(c_2387,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(X2,k1_zfmisc_1(X1))
    | X2 != X0
    | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_2127])).

cnf(c_3399,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK4))
    | m1_subset_1(sK3,k1_zfmisc_1(sK4))
    | k1_zfmisc_1(sK4) != k1_zfmisc_1(sK4)
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_2387])).

cnf(c_4411,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,X0)
    | X0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_4412,plain,
    ( X0 = k1_xboole_0
    | r1_tarski(X0,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4411])).

cnf(c_1470,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_4426,plain,
    ( k1_zfmisc_1(sK4) = k1_zfmisc_1(sK4)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1470])).

cnf(c_2377,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,sK4)
    | X2 != X0
    | sK4 != X1 ),
    inference(instantiation,[status(thm)],[c_1468])).

cnf(c_3355,plain,
    ( ~ r1_tarski(X0,sK4)
    | r1_tarski(X1,sK4)
    | X1 != X0
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_2377])).

cnf(c_4540,plain,
    ( r1_tarski(X0,sK4)
    | ~ r1_tarski(k1_xboole_0,sK4)
    | X0 != k1_xboole_0
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_3355])).

cnf(c_6235,plain,
    ( r1_tarski(X0,k1_xboole_0) != iProver_top
    | r1_tarski(sK3,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5199,c_66,c_311,c_2104,c_2183,c_2217,c_2230,c_2372,c_2415,c_3089,c_3306,c_3399,c_4412,c_4426,c_4540])).

cnf(c_6243,plain,
    ( r1_tarski(sK3,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1944,c_6235])).

cnf(c_2451,plain,
    ( r1_tarski(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1936,c_1940])).

cnf(c_5209,plain,
    ( r1_tarski(sK3,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5180,c_2451])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6243,c_5209])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:45:29 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 2.40/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.40/0.98  
% 2.40/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.40/0.98  
% 2.40/0.98  ------  iProver source info
% 2.40/0.98  
% 2.40/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.40/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.40/0.98  git: non_committed_changes: false
% 2.40/0.98  git: last_make_outside_of_git: false
% 2.40/0.98  
% 2.40/0.98  ------ 
% 2.40/0.98  
% 2.40/0.98  ------ Input Options
% 2.40/0.98  
% 2.40/0.98  --out_options                           all
% 2.40/0.98  --tptp_safe_out                         true
% 2.40/0.98  --problem_path                          ""
% 2.40/0.98  --include_path                          ""
% 2.40/0.98  --clausifier                            res/vclausify_rel
% 2.40/0.98  --clausifier_options                    --mode clausify
% 2.40/0.98  --stdin                                 false
% 2.40/0.98  --stats_out                             all
% 2.40/0.98  
% 2.40/0.98  ------ General Options
% 2.40/0.98  
% 2.40/0.98  --fof                                   false
% 2.40/0.98  --time_out_real                         305.
% 2.40/0.98  --time_out_virtual                      -1.
% 2.40/0.98  --symbol_type_check                     false
% 2.40/0.98  --clausify_out                          false
% 2.40/0.98  --sig_cnt_out                           false
% 2.40/0.98  --trig_cnt_out                          false
% 2.40/0.98  --trig_cnt_out_tolerance                1.
% 2.40/0.98  --trig_cnt_out_sk_spl                   false
% 2.40/0.98  --abstr_cl_out                          false
% 2.40/0.98  
% 2.40/0.98  ------ Global Options
% 2.40/0.98  
% 2.40/0.98  --schedule                              default
% 2.40/0.98  --add_important_lit                     false
% 2.40/0.98  --prop_solver_per_cl                    1000
% 2.40/0.98  --min_unsat_core                        false
% 2.40/0.98  --soft_assumptions                      false
% 2.40/0.98  --soft_lemma_size                       3
% 2.40/0.98  --prop_impl_unit_size                   0
% 2.40/0.98  --prop_impl_unit                        []
% 2.40/0.98  --share_sel_clauses                     true
% 2.40/0.98  --reset_solvers                         false
% 2.40/0.98  --bc_imp_inh                            [conj_cone]
% 2.40/0.98  --conj_cone_tolerance                   3.
% 2.40/0.98  --extra_neg_conj                        none
% 2.40/0.98  --large_theory_mode                     true
% 2.40/0.98  --prolific_symb_bound                   200
% 2.40/0.98  --lt_threshold                          2000
% 2.40/0.98  --clause_weak_htbl                      true
% 2.40/0.98  --gc_record_bc_elim                     false
% 2.40/0.98  
% 2.40/0.98  ------ Preprocessing Options
% 2.40/0.98  
% 2.40/0.98  --preprocessing_flag                    true
% 2.40/0.98  --time_out_prep_mult                    0.1
% 2.40/0.98  --splitting_mode                        input
% 2.40/0.98  --splitting_grd                         true
% 2.40/0.98  --splitting_cvd                         false
% 2.40/0.98  --splitting_cvd_svl                     false
% 2.40/0.98  --splitting_nvd                         32
% 2.40/0.98  --sub_typing                            true
% 2.40/0.98  --prep_gs_sim                           true
% 2.40/0.98  --prep_unflatten                        true
% 2.40/0.98  --prep_res_sim                          true
% 2.40/0.98  --prep_upred                            true
% 2.40/0.98  --prep_sem_filter                       exhaustive
% 2.40/0.98  --prep_sem_filter_out                   false
% 2.40/0.98  --pred_elim                             true
% 2.40/0.98  --res_sim_input                         true
% 2.40/0.98  --eq_ax_congr_red                       true
% 2.40/0.98  --pure_diseq_elim                       true
% 2.40/0.98  --brand_transform                       false
% 2.40/0.98  --non_eq_to_eq                          false
% 2.40/0.98  --prep_def_merge                        true
% 2.40/0.98  --prep_def_merge_prop_impl              false
% 2.40/0.98  --prep_def_merge_mbd                    true
% 2.40/0.98  --prep_def_merge_tr_red                 false
% 2.40/0.98  --prep_def_merge_tr_cl                  false
% 2.40/0.98  --smt_preprocessing                     true
% 2.40/0.98  --smt_ac_axioms                         fast
% 2.40/0.98  --preprocessed_out                      false
% 2.40/0.98  --preprocessed_stats                    false
% 2.40/0.98  
% 2.40/0.98  ------ Abstraction refinement Options
% 2.40/0.98  
% 2.40/0.98  --abstr_ref                             []
% 2.40/0.98  --abstr_ref_prep                        false
% 2.40/0.98  --abstr_ref_until_sat                   false
% 2.40/0.98  --abstr_ref_sig_restrict                funpre
% 2.40/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.40/0.98  --abstr_ref_under                       []
% 2.40/0.98  
% 2.40/0.98  ------ SAT Options
% 2.40/0.98  
% 2.40/0.98  --sat_mode                              false
% 2.40/0.98  --sat_fm_restart_options                ""
% 2.40/0.98  --sat_gr_def                            false
% 2.40/0.98  --sat_epr_types                         true
% 2.40/0.98  --sat_non_cyclic_types                  false
% 2.40/0.98  --sat_finite_models                     false
% 2.40/0.98  --sat_fm_lemmas                         false
% 2.40/0.98  --sat_fm_prep                           false
% 2.40/0.98  --sat_fm_uc_incr                        true
% 2.40/0.98  --sat_out_model                         small
% 2.40/0.98  --sat_out_clauses                       false
% 2.40/0.98  
% 2.40/0.98  ------ QBF Options
% 2.40/0.98  
% 2.40/0.98  --qbf_mode                              false
% 2.40/0.98  --qbf_elim_univ                         false
% 2.40/0.98  --qbf_dom_inst                          none
% 2.40/0.98  --qbf_dom_pre_inst                      false
% 2.40/0.98  --qbf_sk_in                             false
% 2.40/0.98  --qbf_pred_elim                         true
% 2.40/0.98  --qbf_split                             512
% 2.40/0.98  
% 2.40/0.98  ------ BMC1 Options
% 2.40/0.98  
% 2.40/0.98  --bmc1_incremental                      false
% 2.40/0.98  --bmc1_axioms                           reachable_all
% 2.40/0.98  --bmc1_min_bound                        0
% 2.40/0.98  --bmc1_max_bound                        -1
% 2.40/0.98  --bmc1_max_bound_default                -1
% 2.40/0.98  --bmc1_symbol_reachability              true
% 2.40/0.98  --bmc1_property_lemmas                  false
% 2.40/0.98  --bmc1_k_induction                      false
% 2.40/0.98  --bmc1_non_equiv_states                 false
% 2.40/0.98  --bmc1_deadlock                         false
% 2.40/0.98  --bmc1_ucm                              false
% 2.40/0.98  --bmc1_add_unsat_core                   none
% 2.40/0.98  --bmc1_unsat_core_children              false
% 2.40/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.40/0.98  --bmc1_out_stat                         full
% 2.40/0.98  --bmc1_ground_init                      false
% 2.40/0.98  --bmc1_pre_inst_next_state              false
% 2.40/0.98  --bmc1_pre_inst_state                   false
% 2.40/0.98  --bmc1_pre_inst_reach_state             false
% 2.40/0.98  --bmc1_out_unsat_core                   false
% 2.40/0.98  --bmc1_aig_witness_out                  false
% 2.40/0.98  --bmc1_verbose                          false
% 2.40/0.98  --bmc1_dump_clauses_tptp                false
% 2.40/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.40/0.98  --bmc1_dump_file                        -
% 2.40/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.40/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.40/0.98  --bmc1_ucm_extend_mode                  1
% 2.40/0.98  --bmc1_ucm_init_mode                    2
% 2.40/0.98  --bmc1_ucm_cone_mode                    none
% 2.40/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.40/0.98  --bmc1_ucm_relax_model                  4
% 2.40/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.40/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.40/0.98  --bmc1_ucm_layered_model                none
% 2.40/0.98  --bmc1_ucm_max_lemma_size               10
% 2.40/0.98  
% 2.40/0.98  ------ AIG Options
% 2.40/0.98  
% 2.40/0.98  --aig_mode                              false
% 2.40/0.98  
% 2.40/0.98  ------ Instantiation Options
% 2.40/0.98  
% 2.40/0.98  --instantiation_flag                    true
% 2.40/0.98  --inst_sos_flag                         false
% 2.40/0.98  --inst_sos_phase                        true
% 2.40/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.40/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.40/0.98  --inst_lit_sel_side                     num_symb
% 2.40/0.98  --inst_solver_per_active                1400
% 2.40/0.98  --inst_solver_calls_frac                1.
% 2.40/0.98  --inst_passive_queue_type               priority_queues
% 2.40/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.40/0.98  --inst_passive_queues_freq              [25;2]
% 2.40/0.98  --inst_dismatching                      true
% 2.40/0.98  --inst_eager_unprocessed_to_passive     true
% 2.40/0.98  --inst_prop_sim_given                   true
% 2.40/0.98  --inst_prop_sim_new                     false
% 2.40/0.98  --inst_subs_new                         false
% 2.40/0.98  --inst_eq_res_simp                      false
% 2.40/0.98  --inst_subs_given                       false
% 2.40/0.98  --inst_orphan_elimination               true
% 2.40/0.98  --inst_learning_loop_flag               true
% 2.40/0.98  --inst_learning_start                   3000
% 2.40/0.98  --inst_learning_factor                  2
% 2.40/0.98  --inst_start_prop_sim_after_learn       3
% 2.40/0.98  --inst_sel_renew                        solver
% 2.40/0.98  --inst_lit_activity_flag                true
% 2.40/0.98  --inst_restr_to_given                   false
% 2.40/0.98  --inst_activity_threshold               500
% 2.40/0.98  --inst_out_proof                        true
% 2.40/0.98  
% 2.40/0.98  ------ Resolution Options
% 2.40/0.98  
% 2.40/0.98  --resolution_flag                       true
% 2.40/0.98  --res_lit_sel                           adaptive
% 2.40/0.98  --res_lit_sel_side                      none
% 2.40/0.98  --res_ordering                          kbo
% 2.40/0.98  --res_to_prop_solver                    active
% 2.40/0.98  --res_prop_simpl_new                    false
% 2.40/0.98  --res_prop_simpl_given                  true
% 2.40/0.98  --res_passive_queue_type                priority_queues
% 2.40/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.40/0.98  --res_passive_queues_freq               [15;5]
% 2.40/0.98  --res_forward_subs                      full
% 2.40/0.98  --res_backward_subs                     full
% 2.40/0.98  --res_forward_subs_resolution           true
% 2.40/0.98  --res_backward_subs_resolution          true
% 2.40/0.98  --res_orphan_elimination                true
% 2.40/0.98  --res_time_limit                        2.
% 2.40/0.98  --res_out_proof                         true
% 2.40/0.98  
% 2.40/0.98  ------ Superposition Options
% 2.40/0.98  
% 2.40/0.98  --superposition_flag                    true
% 2.40/0.98  --sup_passive_queue_type                priority_queues
% 2.40/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.40/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.40/0.98  --demod_completeness_check              fast
% 2.40/0.98  --demod_use_ground                      true
% 2.40/0.98  --sup_to_prop_solver                    passive
% 2.40/0.98  --sup_prop_simpl_new                    true
% 2.40/0.98  --sup_prop_simpl_given                  true
% 2.40/0.98  --sup_fun_splitting                     false
% 2.40/0.98  --sup_smt_interval                      50000
% 2.40/0.98  
% 2.40/0.98  ------ Superposition Simplification Setup
% 2.40/0.98  
% 2.40/0.98  --sup_indices_passive                   []
% 2.40/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.40/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.40/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.40/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.40/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.40/0.98  --sup_full_bw                           [BwDemod]
% 2.40/0.98  --sup_immed_triv                        [TrivRules]
% 2.40/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.40/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.40/0.98  --sup_immed_bw_main                     []
% 2.40/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.40/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.40/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.40/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.40/0.98  
% 2.40/0.98  ------ Combination Options
% 2.40/0.98  
% 2.40/0.98  --comb_res_mult                         3
% 2.40/0.98  --comb_sup_mult                         2
% 2.40/0.98  --comb_inst_mult                        10
% 2.40/0.98  
% 2.40/0.98  ------ Debug Options
% 2.40/0.98  
% 2.40/0.98  --dbg_backtrace                         false
% 2.40/0.98  --dbg_dump_prop_clauses                 false
% 2.40/0.98  --dbg_dump_prop_clauses_file            -
% 2.40/0.98  --dbg_out_stat                          false
% 2.40/0.98  ------ Parsing...
% 2.40/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.40/0.98  
% 2.40/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.40/0.98  
% 2.40/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.40/0.98  
% 2.40/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.40/0.98  ------ Proving...
% 2.40/0.98  ------ Problem Properties 
% 2.40/0.98  
% 2.40/0.98  
% 2.40/0.98  clauses                                 19
% 2.40/0.98  conjectures                             4
% 2.40/0.98  EPR                                     5
% 2.40/0.98  Horn                                    16
% 2.40/0.98  unary                                   7
% 2.40/0.98  binary                                  3
% 2.40/0.98  lits                                    48
% 2.40/0.98  lits eq                                 5
% 2.40/0.98  fd_pure                                 0
% 2.40/0.98  fd_pseudo                               0
% 2.40/0.98  fd_cond                                 1
% 2.40/0.98  fd_pseudo_cond                          1
% 2.40/0.98  AC symbols                              0
% 2.40/0.98  
% 2.40/0.98  ------ Schedule dynamic 5 is on 
% 2.40/0.98  
% 2.40/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.40/0.98  
% 2.40/0.98  
% 2.40/0.98  ------ 
% 2.40/0.98  Current options:
% 2.40/0.98  ------ 
% 2.40/0.98  
% 2.40/0.98  ------ Input Options
% 2.40/0.98  
% 2.40/0.98  --out_options                           all
% 2.40/0.98  --tptp_safe_out                         true
% 2.40/0.98  --problem_path                          ""
% 2.40/0.98  --include_path                          ""
% 2.40/0.98  --clausifier                            res/vclausify_rel
% 2.40/0.98  --clausifier_options                    --mode clausify
% 2.40/0.98  --stdin                                 false
% 2.40/0.98  --stats_out                             all
% 2.40/0.98  
% 2.40/0.98  ------ General Options
% 2.40/0.98  
% 2.40/0.98  --fof                                   false
% 2.40/0.98  --time_out_real                         305.
% 2.40/0.98  --time_out_virtual                      -1.
% 2.40/0.98  --symbol_type_check                     false
% 2.40/0.98  --clausify_out                          false
% 2.40/0.98  --sig_cnt_out                           false
% 2.40/0.98  --trig_cnt_out                          false
% 2.40/0.98  --trig_cnt_out_tolerance                1.
% 2.40/0.98  --trig_cnt_out_sk_spl                   false
% 2.40/0.98  --abstr_cl_out                          false
% 2.40/0.98  
% 2.40/0.98  ------ Global Options
% 2.40/0.98  
% 2.40/0.98  --schedule                              default
% 2.40/0.98  --add_important_lit                     false
% 2.40/0.98  --prop_solver_per_cl                    1000
% 2.40/0.98  --min_unsat_core                        false
% 2.40/0.98  --soft_assumptions                      false
% 2.40/0.98  --soft_lemma_size                       3
% 2.40/0.98  --prop_impl_unit_size                   0
% 2.40/0.98  --prop_impl_unit                        []
% 2.40/0.98  --share_sel_clauses                     true
% 2.40/0.98  --reset_solvers                         false
% 2.40/0.98  --bc_imp_inh                            [conj_cone]
% 2.40/0.98  --conj_cone_tolerance                   3.
% 2.40/0.98  --extra_neg_conj                        none
% 2.40/0.98  --large_theory_mode                     true
% 2.40/0.98  --prolific_symb_bound                   200
% 2.40/0.98  --lt_threshold                          2000
% 2.40/0.98  --clause_weak_htbl                      true
% 2.40/0.98  --gc_record_bc_elim                     false
% 2.40/0.98  
% 2.40/0.98  ------ Preprocessing Options
% 2.40/0.98  
% 2.40/0.98  --preprocessing_flag                    true
% 2.40/0.98  --time_out_prep_mult                    0.1
% 2.40/0.98  --splitting_mode                        input
% 2.40/0.98  --splitting_grd                         true
% 2.40/0.98  --splitting_cvd                         false
% 2.40/0.98  --splitting_cvd_svl                     false
% 2.40/0.98  --splitting_nvd                         32
% 2.40/0.98  --sub_typing                            true
% 2.40/0.98  --prep_gs_sim                           true
% 2.40/0.98  --prep_unflatten                        true
% 2.40/0.98  --prep_res_sim                          true
% 2.40/0.98  --prep_upred                            true
% 2.40/0.98  --prep_sem_filter                       exhaustive
% 2.40/0.98  --prep_sem_filter_out                   false
% 2.40/0.98  --pred_elim                             true
% 2.40/0.98  --res_sim_input                         true
% 2.40/0.98  --eq_ax_congr_red                       true
% 2.40/0.98  --pure_diseq_elim                       true
% 2.40/0.98  --brand_transform                       false
% 2.40/0.98  --non_eq_to_eq                          false
% 2.40/0.98  --prep_def_merge                        true
% 2.40/0.98  --prep_def_merge_prop_impl              false
% 2.40/0.98  --prep_def_merge_mbd                    true
% 2.40/0.98  --prep_def_merge_tr_red                 false
% 2.40/0.98  --prep_def_merge_tr_cl                  false
% 2.40/0.98  --smt_preprocessing                     true
% 2.40/0.98  --smt_ac_axioms                         fast
% 2.40/0.98  --preprocessed_out                      false
% 2.40/0.98  --preprocessed_stats                    false
% 2.40/0.98  
% 2.40/0.98  ------ Abstraction refinement Options
% 2.40/0.98  
% 2.40/0.98  --abstr_ref                             []
% 2.40/0.98  --abstr_ref_prep                        false
% 2.40/0.98  --abstr_ref_until_sat                   false
% 2.40/0.98  --abstr_ref_sig_restrict                funpre
% 2.40/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.40/0.98  --abstr_ref_under                       []
% 2.40/0.98  
% 2.40/0.98  ------ SAT Options
% 2.40/0.98  
% 2.40/0.98  --sat_mode                              false
% 2.40/0.98  --sat_fm_restart_options                ""
% 2.40/0.98  --sat_gr_def                            false
% 2.40/0.98  --sat_epr_types                         true
% 2.40/0.98  --sat_non_cyclic_types                  false
% 2.40/0.98  --sat_finite_models                     false
% 2.40/0.98  --sat_fm_lemmas                         false
% 2.40/0.98  --sat_fm_prep                           false
% 2.40/0.98  --sat_fm_uc_incr                        true
% 2.40/0.98  --sat_out_model                         small
% 2.40/0.98  --sat_out_clauses                       false
% 2.40/0.98  
% 2.40/0.98  ------ QBF Options
% 2.40/0.98  
% 2.40/0.98  --qbf_mode                              false
% 2.40/0.98  --qbf_elim_univ                         false
% 2.40/0.98  --qbf_dom_inst                          none
% 2.40/0.98  --qbf_dom_pre_inst                      false
% 2.40/0.98  --qbf_sk_in                             false
% 2.40/0.98  --qbf_pred_elim                         true
% 2.40/0.98  --qbf_split                             512
% 2.40/0.98  
% 2.40/0.98  ------ BMC1 Options
% 2.40/0.98  
% 2.40/0.98  --bmc1_incremental                      false
% 2.40/0.98  --bmc1_axioms                           reachable_all
% 2.40/0.98  --bmc1_min_bound                        0
% 2.40/0.98  --bmc1_max_bound                        -1
% 2.40/0.98  --bmc1_max_bound_default                -1
% 2.40/0.98  --bmc1_symbol_reachability              true
% 2.40/0.98  --bmc1_property_lemmas                  false
% 2.40/0.98  --bmc1_k_induction                      false
% 2.40/0.98  --bmc1_non_equiv_states                 false
% 2.40/0.98  --bmc1_deadlock                         false
% 2.40/0.98  --bmc1_ucm                              false
% 2.40/0.98  --bmc1_add_unsat_core                   none
% 2.40/0.98  --bmc1_unsat_core_children              false
% 2.40/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.40/0.98  --bmc1_out_stat                         full
% 2.40/0.98  --bmc1_ground_init                      false
% 2.40/0.98  --bmc1_pre_inst_next_state              false
% 2.40/0.98  --bmc1_pre_inst_state                   false
% 2.40/0.98  --bmc1_pre_inst_reach_state             false
% 2.40/0.98  --bmc1_out_unsat_core                   false
% 2.40/0.98  --bmc1_aig_witness_out                  false
% 2.40/0.98  --bmc1_verbose                          false
% 2.40/0.98  --bmc1_dump_clauses_tptp                false
% 2.40/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.40/0.98  --bmc1_dump_file                        -
% 2.40/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.40/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.40/0.98  --bmc1_ucm_extend_mode                  1
% 2.40/0.98  --bmc1_ucm_init_mode                    2
% 2.40/0.98  --bmc1_ucm_cone_mode                    none
% 2.40/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.40/0.98  --bmc1_ucm_relax_model                  4
% 2.40/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.40/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.40/0.98  --bmc1_ucm_layered_model                none
% 2.40/0.98  --bmc1_ucm_max_lemma_size               10
% 2.40/0.98  
% 2.40/0.98  ------ AIG Options
% 2.40/0.98  
% 2.40/0.98  --aig_mode                              false
% 2.40/0.98  
% 2.40/0.98  ------ Instantiation Options
% 2.40/0.98  
% 2.40/0.98  --instantiation_flag                    true
% 2.40/0.98  --inst_sos_flag                         false
% 2.40/0.98  --inst_sos_phase                        true
% 2.40/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.40/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.40/0.98  --inst_lit_sel_side                     none
% 2.40/0.98  --inst_solver_per_active                1400
% 2.40/0.98  --inst_solver_calls_frac                1.
% 2.40/0.98  --inst_passive_queue_type               priority_queues
% 2.40/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.40/0.98  --inst_passive_queues_freq              [25;2]
% 2.40/0.98  --inst_dismatching                      true
% 2.40/0.98  --inst_eager_unprocessed_to_passive     true
% 2.40/0.98  --inst_prop_sim_given                   true
% 2.40/0.98  --inst_prop_sim_new                     false
% 2.40/0.98  --inst_subs_new                         false
% 2.40/0.98  --inst_eq_res_simp                      false
% 2.40/0.98  --inst_subs_given                       false
% 2.40/0.98  --inst_orphan_elimination               true
% 2.40/0.98  --inst_learning_loop_flag               true
% 2.40/0.98  --inst_learning_start                   3000
% 2.40/0.98  --inst_learning_factor                  2
% 2.40/0.98  --inst_start_prop_sim_after_learn       3
% 2.40/0.98  --inst_sel_renew                        solver
% 2.40/0.98  --inst_lit_activity_flag                true
% 2.40/0.98  --inst_restr_to_given                   false
% 2.40/0.98  --inst_activity_threshold               500
% 2.40/0.98  --inst_out_proof                        true
% 2.40/0.98  
% 2.40/0.98  ------ Resolution Options
% 2.40/0.98  
% 2.40/0.98  --resolution_flag                       false
% 2.40/0.98  --res_lit_sel                           adaptive
% 2.40/0.98  --res_lit_sel_side                      none
% 2.40/0.98  --res_ordering                          kbo
% 2.40/0.98  --res_to_prop_solver                    active
% 2.40/0.98  --res_prop_simpl_new                    false
% 2.40/0.98  --res_prop_simpl_given                  true
% 2.40/0.98  --res_passive_queue_type                priority_queues
% 2.40/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.40/0.98  --res_passive_queues_freq               [15;5]
% 2.40/0.98  --res_forward_subs                      full
% 2.40/0.98  --res_backward_subs                     full
% 2.40/0.98  --res_forward_subs_resolution           true
% 2.40/0.98  --res_backward_subs_resolution          true
% 2.40/0.98  --res_orphan_elimination                true
% 2.40/0.98  --res_time_limit                        2.
% 2.40/0.98  --res_out_proof                         true
% 2.40/0.98  
% 2.40/0.98  ------ Superposition Options
% 2.40/0.98  
% 2.40/0.98  --superposition_flag                    true
% 2.40/0.98  --sup_passive_queue_type                priority_queues
% 2.40/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.40/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.40/0.98  --demod_completeness_check              fast
% 2.40/0.98  --demod_use_ground                      true
% 2.40/0.98  --sup_to_prop_solver                    passive
% 2.40/0.98  --sup_prop_simpl_new                    true
% 2.40/0.98  --sup_prop_simpl_given                  true
% 2.40/0.98  --sup_fun_splitting                     false
% 2.40/0.98  --sup_smt_interval                      50000
% 2.40/0.98  
% 2.40/0.98  ------ Superposition Simplification Setup
% 2.40/0.98  
% 2.40/0.98  --sup_indices_passive                   []
% 2.40/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.40/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.40/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.40/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.40/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.40/0.98  --sup_full_bw                           [BwDemod]
% 2.40/0.98  --sup_immed_triv                        [TrivRules]
% 2.40/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.40/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.40/0.98  --sup_immed_bw_main                     []
% 2.40/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.40/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.40/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.40/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.40/0.98  
% 2.40/0.98  ------ Combination Options
% 2.40/0.98  
% 2.40/0.98  --comb_res_mult                         3
% 2.40/0.98  --comb_sup_mult                         2
% 2.40/0.98  --comb_inst_mult                        10
% 2.40/0.98  
% 2.40/0.98  ------ Debug Options
% 2.40/0.98  
% 2.40/0.98  --dbg_backtrace                         false
% 2.40/0.98  --dbg_dump_prop_clauses                 false
% 2.40/0.98  --dbg_dump_prop_clauses_file            -
% 2.40/0.98  --dbg_out_stat                          false
% 2.40/0.98  
% 2.40/0.98  
% 2.40/0.98  
% 2.40/0.98  
% 2.40/0.98  ------ Proving...
% 2.40/0.98  
% 2.40/0.98  
% 2.40/0.98  % SZS status Theorem for theBenchmark.p
% 2.40/0.98  
% 2.40/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.40/0.98  
% 2.40/0.98  fof(f1,axiom,(
% 2.40/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.40/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/0.98  
% 2.40/0.98  fof(f18,plain,(
% 2.40/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.40/0.98    inference(nnf_transformation,[],[f1])).
% 2.40/0.98  
% 2.40/0.98  fof(f19,plain,(
% 2.40/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.40/0.98    inference(flattening,[],[f18])).
% 2.40/0.98  
% 2.40/0.98  fof(f32,plain,(
% 2.40/0.98    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.40/0.98    inference(cnf_transformation,[],[f19])).
% 2.40/0.98  
% 2.40/0.98  fof(f58,plain,(
% 2.40/0.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.40/0.98    inference(equality_resolution,[],[f32])).
% 2.40/0.98  
% 2.40/0.98  fof(f5,axiom,(
% 2.40/0.98    ! [X0,X1] : (m1_subset_1(X1,X0) => (k1_xboole_0 != X0 => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))))),
% 2.40/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/0.98  
% 2.40/0.98  fof(f11,plain,(
% 2.40/0.98    ! [X0,X1] : ((m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0) | ~m1_subset_1(X1,X0))),
% 2.40/0.98    inference(ennf_transformation,[],[f5])).
% 2.40/0.98  
% 2.40/0.98  fof(f12,plain,(
% 2.40/0.98    ! [X0,X1] : (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X1,X0))),
% 2.40/0.98    inference(flattening,[],[f11])).
% 2.40/0.98  
% 2.40/0.98  fof(f38,plain,(
% 2.40/0.98    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X1,X0)) )),
% 2.40/0.98    inference(cnf_transformation,[],[f12])).
% 2.40/0.98  
% 2.40/0.98  fof(f3,axiom,(
% 2.40/0.98    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.40/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/0.98  
% 2.40/0.98  fof(f35,plain,(
% 2.40/0.98    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.40/0.98    inference(cnf_transformation,[],[f3])).
% 2.40/0.98  
% 2.40/0.98  fof(f56,plain,(
% 2.40/0.98    ( ! [X0,X1] : (m1_subset_1(k2_tarski(X1,X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X1,X0)) )),
% 2.40/0.98    inference(definition_unfolding,[],[f38,f35])).
% 2.40/0.98  
% 2.40/0.98  fof(f6,axiom,(
% 2.40/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.40/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/0.98  
% 2.40/0.98  fof(f21,plain,(
% 2.40/0.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.40/0.98    inference(nnf_transformation,[],[f6])).
% 2.40/0.98  
% 2.40/0.98  fof(f39,plain,(
% 2.40/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.40/0.98    inference(cnf_transformation,[],[f21])).
% 2.40/0.98  
% 2.40/0.98  fof(f9,conjecture,(
% 2.40/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k1_tarski(X2) = k9_subset_1(u1_struct_0(X0),X1,X3) & v3_pre_topc(X3,X0))) & r2_hidden(X2,X1))))))),
% 2.40/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/0.98  
% 2.40/0.98  fof(f10,negated_conjecture,(
% 2.40/0.98    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k1_tarski(X2) = k9_subset_1(u1_struct_0(X0),X1,X3) & v3_pre_topc(X3,X0))) & r2_hidden(X2,X1))))))),
% 2.40/0.98    inference(negated_conjecture,[],[f9])).
% 2.40/0.98  
% 2.40/0.98  fof(f16,plain,(
% 2.40/0.98    ? [X0] : (? [X1] : ((? [X2] : ((! [X3] : ((k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),X1,X3) | ~v3_pre_topc(X3,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1)) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 2.40/0.98    inference(ennf_transformation,[],[f10])).
% 2.40/0.98  
% 2.40/0.98  fof(f17,plain,(
% 2.40/0.98    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),X1,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 2.40/0.98    inference(flattening,[],[f16])).
% 2.40/0.98  
% 2.40/0.98  fof(f29,plain,(
% 2.40/0.98    ( ! [X0,X1] : (? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),X1,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) => (! [X3] : (k1_tarski(sK4) != k9_subset_1(u1_struct_0(X0),X1,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(sK4,X1) & m1_subset_1(sK4,u1_struct_0(X0)))) )),
% 2.40/0.98    introduced(choice_axiom,[])).
% 2.40/0.98  
% 2.40/0.98  fof(f28,plain,(
% 2.40/0.98    ( ! [X0] : (? [X1] : (? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),X1,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),sK3,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,sK3) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(sK3,X0) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.40/0.98    introduced(choice_axiom,[])).
% 2.40/0.98  
% 2.40/0.98  fof(f27,plain,(
% 2.40/0.98    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),X1,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(sK2),X1,X3) | ~v3_pre_topc(X3,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(sK2))) & v2_tex_2(X1,sK2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2))),
% 2.40/0.98    introduced(choice_axiom,[])).
% 2.40/0.98  
% 2.40/0.98  fof(f30,plain,(
% 2.40/0.98    ((! [X3] : (k1_tarski(sK4) != k9_subset_1(u1_struct_0(sK2),sK3,X3) | ~v3_pre_topc(X3,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & r2_hidden(sK4,sK3) & m1_subset_1(sK4,u1_struct_0(sK2))) & v2_tex_2(sK3,sK2) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2)),
% 2.40/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f17,f29,f28,f27])).
% 2.40/0.98  
% 2.40/0.98  fof(f49,plain,(
% 2.40/0.98    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 2.40/0.98    inference(cnf_transformation,[],[f30])).
% 2.40/0.98  
% 2.40/0.98  fof(f40,plain,(
% 2.40/0.98    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.40/0.98    inference(cnf_transformation,[],[f21])).
% 2.40/0.98  
% 2.40/0.98  fof(f8,axiom,(
% 2.40/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0))) & r1_tarski(X2,X1))))))),
% 2.40/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/0.98  
% 2.40/0.98  fof(f14,plain,(
% 2.40/0.98    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((? [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.40/0.98    inference(ennf_transformation,[],[f8])).
% 2.40/0.98  
% 2.40/0.98  fof(f15,plain,(
% 2.40/0.98    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.40/0.98    inference(flattening,[],[f14])).
% 2.40/0.98  
% 2.40/0.98  fof(f22,plain,(
% 2.40/0.98    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.40/0.98    inference(nnf_transformation,[],[f15])).
% 2.40/0.98  
% 2.40/0.98  fof(f23,plain,(
% 2.40/0.98    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (? [X5] : (k9_subset_1(u1_struct_0(X0),X1,X5) = X4 & v3_pre_topc(X5,X0) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.40/0.98    inference(rectify,[],[f22])).
% 2.40/0.98  
% 2.40/0.98  fof(f25,plain,(
% 2.40/0.98    ! [X4,X1,X0] : (? [X5] : (k9_subset_1(u1_struct_0(X0),X1,X5) = X4 & v3_pre_topc(X5,X0) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) => (k9_subset_1(u1_struct_0(X0),X1,sK1(X0,X1,X4)) = X4 & v3_pre_topc(sK1(X0,X1,X4),X0) & m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.40/0.98    introduced(choice_axiom,[])).
% 2.40/0.98  
% 2.40/0.98  fof(f24,plain,(
% 2.40/0.98    ! [X1,X0] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK0(X0,X1) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(sK0(X0,X1),X1) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.40/0.98    introduced(choice_axiom,[])).
% 2.40/0.98  
% 2.40/0.98  fof(f26,plain,(
% 2.40/0.98    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK0(X0,X1) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(sK0(X0,X1),X1) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : ((k9_subset_1(u1_struct_0(X0),X1,sK1(X0,X1,X4)) = X4 & v3_pre_topc(sK1(X0,X1,X4),X0) & m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.40/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f25,f24])).
% 2.40/0.98  
% 2.40/0.98  fof(f44,plain,(
% 2.40/0.98    ( ! [X4,X0,X1] : (k9_subset_1(u1_struct_0(X0),X1,sK1(X0,X1,X4)) = X4 | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.40/0.98    inference(cnf_transformation,[],[f26])).
% 2.40/0.98  
% 2.40/0.98  fof(f48,plain,(
% 2.40/0.98    l1_pre_topc(sK2)),
% 2.40/0.98    inference(cnf_transformation,[],[f30])).
% 2.40/0.98  
% 2.40/0.98  fof(f51,plain,(
% 2.40/0.98    m1_subset_1(sK4,u1_struct_0(sK2))),
% 2.40/0.98    inference(cnf_transformation,[],[f30])).
% 2.40/0.98  
% 2.40/0.98  fof(f42,plain,(
% 2.40/0.98    ( ! [X4,X0,X1] : (m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.40/0.98    inference(cnf_transformation,[],[f26])).
% 2.40/0.98  
% 2.40/0.98  fof(f4,axiom,(
% 2.40/0.98    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 2.40/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/0.98  
% 2.40/0.98  fof(f20,plain,(
% 2.40/0.98    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 2.40/0.98    inference(nnf_transformation,[],[f4])).
% 2.40/0.98  
% 2.40/0.98  fof(f37,plain,(
% 2.40/0.98    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 2.40/0.98    inference(cnf_transformation,[],[f20])).
% 2.40/0.98  
% 2.40/0.98  fof(f54,plain,(
% 2.40/0.98    ( ! [X0,X1] : (r1_tarski(k2_tarski(X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 2.40/0.98    inference(definition_unfolding,[],[f37,f35])).
% 2.40/0.98  
% 2.40/0.98  fof(f52,plain,(
% 2.40/0.98    r2_hidden(sK4,sK3)),
% 2.40/0.98    inference(cnf_transformation,[],[f30])).
% 2.40/0.98  
% 2.40/0.98  fof(f50,plain,(
% 2.40/0.98    v2_tex_2(sK3,sK2)),
% 2.40/0.98    inference(cnf_transformation,[],[f30])).
% 2.40/0.98  
% 2.40/0.98  fof(f53,plain,(
% 2.40/0.98    ( ! [X3] : (k1_tarski(sK4) != k9_subset_1(u1_struct_0(sK2),sK3,X3) | ~v3_pre_topc(X3,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) )),
% 2.40/0.98    inference(cnf_transformation,[],[f30])).
% 2.40/0.98  
% 2.40/0.98  fof(f57,plain,(
% 2.40/0.98    ( ! [X3] : (k2_tarski(sK4,sK4) != k9_subset_1(u1_struct_0(sK2),sK3,X3) | ~v3_pre_topc(X3,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) )),
% 2.40/0.98    inference(definition_unfolding,[],[f53,f35])).
% 2.40/0.98  
% 2.40/0.98  fof(f43,plain,(
% 2.40/0.98    ( ! [X4,X0,X1] : (v3_pre_topc(sK1(X0,X1,X4),X0) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.40/0.98    inference(cnf_transformation,[],[f26])).
% 2.40/0.98  
% 2.40/0.98  fof(f2,axiom,(
% 2.40/0.98    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.40/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/0.98  
% 2.40/0.98  fof(f34,plain,(
% 2.40/0.98    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.40/0.98    inference(cnf_transformation,[],[f2])).
% 2.40/0.98  
% 2.40/0.98  fof(f7,axiom,(
% 2.40/0.98    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 2.40/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/0.98  
% 2.40/0.98  fof(f13,plain,(
% 2.40/0.98    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 2.40/0.98    inference(ennf_transformation,[],[f7])).
% 2.40/0.98  
% 2.40/0.98  fof(f41,plain,(
% 2.40/0.98    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 2.40/0.98    inference(cnf_transformation,[],[f13])).
% 2.40/0.98  
% 2.40/0.98  fof(f33,plain,(
% 2.40/0.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.40/0.98    inference(cnf_transformation,[],[f19])).
% 2.40/0.98  
% 2.40/0.98  cnf(c_1,plain,
% 2.40/0.98      ( r1_tarski(X0,X0) ),
% 2.40/0.98      inference(cnf_transformation,[],[f58]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_1944,plain,
% 2.40/0.98      ( r1_tarski(X0,X0) = iProver_top ),
% 2.40/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_6,plain,
% 2.40/0.98      ( ~ m1_subset_1(X0,X1)
% 2.40/0.98      | m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1))
% 2.40/0.98      | k1_xboole_0 = X1 ),
% 2.40/0.98      inference(cnf_transformation,[],[f56]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_1942,plain,
% 2.40/0.98      ( k1_xboole_0 = X0
% 2.40/0.98      | m1_subset_1(X1,X0) != iProver_top
% 2.40/0.98      | m1_subset_1(k2_tarski(X1,X1),k1_zfmisc_1(X0)) = iProver_top ),
% 2.40/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_8,plain,
% 2.40/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.40/0.98      inference(cnf_transformation,[],[f39]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_1940,plain,
% 2.40/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.40/0.98      | r1_tarski(X0,X1) = iProver_top ),
% 2.40/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_3153,plain,
% 2.40/0.98      ( k1_xboole_0 = X0
% 2.40/0.98      | m1_subset_1(X1,X0) != iProver_top
% 2.40/0.98      | r1_tarski(k2_tarski(X1,X1),X0) = iProver_top ),
% 2.40/0.98      inference(superposition,[status(thm)],[c_1942,c_1940]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_20,negated_conjecture,
% 2.40/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.40/0.98      inference(cnf_transformation,[],[f49]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_1936,plain,
% 2.40/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 2.40/0.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_7,plain,
% 2.40/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.40/0.98      inference(cnf_transformation,[],[f40]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_1941,plain,
% 2.40/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 2.40/0.98      | r1_tarski(X0,X1) != iProver_top ),
% 2.40/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_13,plain,
% 2.40/0.98      ( ~ v2_tex_2(X0,X1)
% 2.40/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.40/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.40/0.98      | ~ r1_tarski(X2,X0)
% 2.40/0.98      | ~ l1_pre_topc(X1)
% 2.40/0.98      | k9_subset_1(u1_struct_0(X1),X0,sK1(X1,X0,X2)) = X2 ),
% 2.40/0.98      inference(cnf_transformation,[],[f44]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_21,negated_conjecture,
% 2.40/0.98      ( l1_pre_topc(sK2) ),
% 2.40/0.98      inference(cnf_transformation,[],[f48]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_448,plain,
% 2.40/0.98      ( ~ v2_tex_2(X0,X1)
% 2.40/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.40/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.40/0.98      | ~ r1_tarski(X2,X0)
% 2.40/0.98      | k9_subset_1(u1_struct_0(X1),X0,sK1(X1,X0,X2)) = X2
% 2.40/0.98      | sK2 != X1 ),
% 2.40/0.98      inference(resolution_lifted,[status(thm)],[c_13,c_21]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_449,plain,
% 2.40/0.98      ( ~ v2_tex_2(X0,sK2)
% 2.40/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.40/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.40/0.98      | ~ r1_tarski(X1,X0)
% 2.40/0.98      | k9_subset_1(u1_struct_0(sK2),X0,sK1(sK2,X0,X1)) = X1 ),
% 2.40/0.98      inference(unflattening,[status(thm)],[c_448]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_1930,plain,
% 2.40/0.98      ( k9_subset_1(u1_struct_0(sK2),X0,sK1(sK2,X0,X1)) = X1
% 2.40/0.98      | v2_tex_2(X0,sK2) != iProver_top
% 2.40/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.40/0.98      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.40/0.98      | r1_tarski(X1,X0) != iProver_top ),
% 2.40/0.98      inference(predicate_to_equality,[status(thm)],[c_449]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_2581,plain,
% 2.40/0.98      ( k9_subset_1(u1_struct_0(sK2),X0,sK1(sK2,X0,X1)) = X1
% 2.40/0.98      | v2_tex_2(X0,sK2) != iProver_top
% 2.40/0.98      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.40/0.98      | r1_tarski(X1,X0) != iProver_top
% 2.40/0.98      | r1_tarski(X0,u1_struct_0(sK2)) != iProver_top ),
% 2.40/0.98      inference(superposition,[status(thm)],[c_1941,c_1930]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_3490,plain,
% 2.40/0.98      ( k9_subset_1(u1_struct_0(sK2),X0,sK1(sK2,X0,sK3)) = sK3
% 2.40/0.98      | v2_tex_2(X0,sK2) != iProver_top
% 2.40/0.99      | r1_tarski(X0,u1_struct_0(sK2)) != iProver_top
% 2.40/0.99      | r1_tarski(sK3,X0) != iProver_top ),
% 2.40/0.99      inference(superposition,[status(thm)],[c_1936,c_2581]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_4215,plain,
% 2.40/0.99      ( k9_subset_1(u1_struct_0(sK2),k2_tarski(X0,X0),sK1(sK2,k2_tarski(X0,X0),sK3)) = sK3
% 2.40/0.99      | u1_struct_0(sK2) = k1_xboole_0
% 2.40/0.99      | v2_tex_2(k2_tarski(X0,X0),sK2) != iProver_top
% 2.40/0.99      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 2.40/0.99      | r1_tarski(sK3,k2_tarski(X0,X0)) != iProver_top ),
% 2.40/0.99      inference(superposition,[status(thm)],[c_3153,c_3490]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_18,negated_conjecture,
% 2.40/0.99      ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
% 2.40/0.99      inference(cnf_transformation,[],[f51]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_25,plain,
% 2.40/0.99      ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
% 2.40/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_15,plain,
% 2.40/0.99      ( ~ v2_tex_2(X0,X1)
% 2.40/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.40/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.40/0.99      | m1_subset_1(sK1(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
% 2.40/0.99      | ~ r1_tarski(X2,X0)
% 2.40/0.99      | ~ l1_pre_topc(X1) ),
% 2.40/0.99      inference(cnf_transformation,[],[f42]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_427,plain,
% 2.40/0.99      ( ~ v2_tex_2(X0,X1)
% 2.40/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.40/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.40/0.99      | m1_subset_1(sK1(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
% 2.40/0.99      | ~ r1_tarski(X2,X0)
% 2.40/0.99      | sK2 != X1 ),
% 2.40/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_21]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_428,plain,
% 2.40/0.99      ( ~ v2_tex_2(X0,sK2)
% 2.40/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.40/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.40/0.99      | m1_subset_1(sK1(sK2,X0,X1),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.40/0.99      | ~ r1_tarski(X1,X0) ),
% 2.40/0.99      inference(unflattening,[status(thm)],[c_427]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_1931,plain,
% 2.40/0.99      ( v2_tex_2(X0,sK2) != iProver_top
% 2.40/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.40/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.40/0.99      | m1_subset_1(sK1(sK2,X0,X1),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 2.40/0.99      | r1_tarski(X1,X0) != iProver_top ),
% 2.40/0.99      inference(predicate_to_equality,[status(thm)],[c_428]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_4,plain,
% 2.40/0.99      ( ~ r2_hidden(X0,X1) | r1_tarski(k2_tarski(X0,X0),X1) ),
% 2.40/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_170,plain,
% 2.40/0.99      ( ~ r2_hidden(X0,X1) | r1_tarski(k2_tarski(X0,X0),X1) ),
% 2.40/0.99      inference(prop_impl,[status(thm)],[c_4]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_17,negated_conjecture,
% 2.40/0.99      ( r2_hidden(sK4,sK3) ),
% 2.40/0.99      inference(cnf_transformation,[],[f52]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_317,plain,
% 2.40/0.99      ( r1_tarski(k2_tarski(X0,X0),X1) | sK3 != X1 | sK4 != X0 ),
% 2.40/0.99      inference(resolution_lifted,[status(thm)],[c_170,c_17]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_318,plain,
% 2.40/0.99      ( r1_tarski(k2_tarski(sK4,sK4),sK3) ),
% 2.40/0.99      inference(unflattening,[status(thm)],[c_317]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_1933,plain,
% 2.40/0.99      ( r1_tarski(k2_tarski(sK4,sK4),sK3) = iProver_top ),
% 2.40/0.99      inference(predicate_to_equality,[status(thm)],[c_318]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_2582,plain,
% 2.40/0.99      ( k9_subset_1(u1_struct_0(sK2),sK3,sK1(sK2,sK3,X0)) = X0
% 2.40/0.99      | v2_tex_2(sK3,sK2) != iProver_top
% 2.40/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.40/0.99      | r1_tarski(X0,sK3) != iProver_top ),
% 2.40/0.99      inference(superposition,[status(thm)],[c_1936,c_1930]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_23,plain,
% 2.40/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 2.40/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_19,negated_conjecture,
% 2.40/0.99      ( v2_tex_2(sK3,sK2) ),
% 2.40/0.99      inference(cnf_transformation,[],[f50]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_737,plain,
% 2.40/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.40/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.40/0.99      | ~ r1_tarski(X1,X0)
% 2.40/0.99      | k9_subset_1(u1_struct_0(sK2),X0,sK1(sK2,X0,X1)) = X1
% 2.40/0.99      | sK3 != X0
% 2.40/0.99      | sK2 != sK2 ),
% 2.40/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_449]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_738,plain,
% 2.40/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.40/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.40/0.99      | ~ r1_tarski(X0,sK3)
% 2.40/0.99      | k9_subset_1(u1_struct_0(sK2),sK3,sK1(sK2,sK3,X0)) = X0 ),
% 2.40/0.99      inference(unflattening,[status(thm)],[c_737]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_739,plain,
% 2.40/0.99      ( k9_subset_1(u1_struct_0(sK2),sK3,sK1(sK2,sK3,X0)) = X0
% 2.40/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.40/0.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.40/0.99      | r1_tarski(X0,sK3) != iProver_top ),
% 2.40/0.99      inference(predicate_to_equality,[status(thm)],[c_738]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_2604,plain,
% 2.40/0.99      ( k9_subset_1(u1_struct_0(sK2),sK3,sK1(sK2,sK3,X0)) = X0
% 2.40/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.40/0.99      | r1_tarski(X0,sK3) != iProver_top ),
% 2.40/0.99      inference(global_propositional_subsumption,
% 2.40/0.99                [status(thm)],
% 2.40/0.99                [c_2582,c_23,c_739]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_3154,plain,
% 2.40/0.99      ( k9_subset_1(u1_struct_0(sK2),sK3,sK1(sK2,sK3,k2_tarski(X0,X0))) = k2_tarski(X0,X0)
% 2.40/0.99      | u1_struct_0(sK2) = k1_xboole_0
% 2.40/0.99      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 2.40/0.99      | r1_tarski(k2_tarski(X0,X0),sK3) != iProver_top ),
% 2.40/0.99      inference(superposition,[status(thm)],[c_1942,c_2604]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_4574,plain,
% 2.40/0.99      ( k9_subset_1(u1_struct_0(sK2),sK3,sK1(sK2,sK3,k2_tarski(sK4,sK4))) = k2_tarski(sK4,sK4)
% 2.40/0.99      | u1_struct_0(sK2) = k1_xboole_0
% 2.40/0.99      | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top ),
% 2.40/0.99      inference(superposition,[status(thm)],[c_1933,c_3154]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_4594,plain,
% 2.40/0.99      ( ~ m1_subset_1(sK4,u1_struct_0(sK2))
% 2.40/0.99      | k9_subset_1(u1_struct_0(sK2),sK3,sK1(sK2,sK3,k2_tarski(sK4,sK4))) = k2_tarski(sK4,sK4)
% 2.40/0.99      | u1_struct_0(sK2) = k1_xboole_0 ),
% 2.40/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_4574]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_4596,plain,
% 2.40/0.99      ( u1_struct_0(sK2) = k1_xboole_0
% 2.40/0.99      | k9_subset_1(u1_struct_0(sK2),sK3,sK1(sK2,sK3,k2_tarski(sK4,sK4))) = k2_tarski(sK4,sK4) ),
% 2.40/0.99      inference(global_propositional_subsumption,
% 2.40/0.99                [status(thm)],
% 2.40/0.99                [c_4574,c_18,c_4594]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_4597,plain,
% 2.40/0.99      ( k9_subset_1(u1_struct_0(sK2),sK3,sK1(sK2,sK3,k2_tarski(sK4,sK4))) = k2_tarski(sK4,sK4)
% 2.40/0.99      | u1_struct_0(sK2) = k1_xboole_0 ),
% 2.40/0.99      inference(renaming,[status(thm)],[c_4596]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_16,negated_conjecture,
% 2.40/0.99      ( ~ v3_pre_topc(X0,sK2)
% 2.40/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.40/0.99      | k2_tarski(sK4,sK4) != k9_subset_1(u1_struct_0(sK2),sK3,X0) ),
% 2.40/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_1939,plain,
% 2.40/0.99      ( k2_tarski(sK4,sK4) != k9_subset_1(u1_struct_0(sK2),sK3,X0)
% 2.40/0.99      | v3_pre_topc(X0,sK2) != iProver_top
% 2.40/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 2.40/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_4600,plain,
% 2.40/0.99      ( u1_struct_0(sK2) = k1_xboole_0
% 2.40/0.99      | v3_pre_topc(sK1(sK2,sK3,k2_tarski(sK4,sK4)),sK2) != iProver_top
% 2.40/0.99      | m1_subset_1(sK1(sK2,sK3,k2_tarski(sK4,sK4)),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 2.40/0.99      inference(superposition,[status(thm)],[c_4597,c_1939]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_4695,plain,
% 2.40/0.99      ( u1_struct_0(sK2) = k1_xboole_0
% 2.40/0.99      | v3_pre_topc(sK1(sK2,sK3,k2_tarski(sK4,sK4)),sK2) != iProver_top
% 2.40/0.99      | v2_tex_2(sK3,sK2) != iProver_top
% 2.40/0.99      | m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.40/0.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.40/0.99      | r1_tarski(k2_tarski(sK4,sK4),sK3) != iProver_top ),
% 2.40/0.99      inference(superposition,[status(thm)],[c_1931,c_4600]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_24,plain,
% 2.40/0.99      ( v2_tex_2(sK3,sK2) = iProver_top ),
% 2.40/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_319,plain,
% 2.40/0.99      ( r1_tarski(k2_tarski(sK4,sK4),sK3) = iProver_top ),
% 2.40/0.99      inference(predicate_to_equality,[status(thm)],[c_318]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_14,plain,
% 2.40/0.99      ( v3_pre_topc(sK1(X0,X1,X2),X0)
% 2.40/0.99      | ~ v2_tex_2(X1,X0)
% 2.40/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.40/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 2.40/0.99      | ~ r1_tarski(X2,X1)
% 2.40/0.99      | ~ l1_pre_topc(X0) ),
% 2.40/0.99      inference(cnf_transformation,[],[f43]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_406,plain,
% 2.40/0.99      ( v3_pre_topc(sK1(X0,X1,X2),X0)
% 2.40/0.99      | ~ v2_tex_2(X1,X0)
% 2.40/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 2.40/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.40/0.99      | ~ r1_tarski(X2,X1)
% 2.40/0.99      | sK2 != X0 ),
% 2.40/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_21]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_407,plain,
% 2.40/0.99      ( v3_pre_topc(sK1(sK2,X0,X1),sK2)
% 2.40/0.99      | ~ v2_tex_2(X0,sK2)
% 2.40/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.40/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.40/0.99      | ~ r1_tarski(X1,X0) ),
% 2.40/0.99      inference(unflattening,[status(thm)],[c_406]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_2086,plain,
% 2.40/0.99      ( v3_pre_topc(sK1(sK2,sK3,X0),sK2)
% 2.40/0.99      | ~ v2_tex_2(sK3,sK2)
% 2.40/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.40/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.40/0.99      | ~ r1_tarski(X0,sK3) ),
% 2.40/0.99      inference(instantiation,[status(thm)],[c_407]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_2185,plain,
% 2.40/0.99      ( v3_pre_topc(sK1(sK2,sK3,k2_tarski(sK4,sK4)),sK2)
% 2.40/0.99      | ~ v2_tex_2(sK3,sK2)
% 2.40/0.99      | ~ m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.40/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.40/0.99      | ~ r1_tarski(k2_tarski(sK4,sK4),sK3) ),
% 2.40/0.99      inference(instantiation,[status(thm)],[c_2086]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_2186,plain,
% 2.40/0.99      ( v3_pre_topc(sK1(sK2,sK3,k2_tarski(sK4,sK4)),sK2) = iProver_top
% 2.40/0.99      | v2_tex_2(sK3,sK2) != iProver_top
% 2.40/0.99      | m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.40/0.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.40/0.99      | r1_tarski(k2_tarski(sK4,sK4),sK3) != iProver_top ),
% 2.40/0.99      inference(predicate_to_equality,[status(thm)],[c_2185]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_5021,plain,
% 2.40/0.99      ( u1_struct_0(sK2) = k1_xboole_0
% 2.40/0.99      | m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 2.40/0.99      inference(global_propositional_subsumption,
% 2.40/0.99                [status(thm)],
% 2.40/0.99                [c_4695,c_23,c_24,c_319,c_2186]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_5027,plain,
% 2.40/0.99      ( u1_struct_0(sK2) = k1_xboole_0
% 2.40/0.99      | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top ),
% 2.40/0.99      inference(superposition,[status(thm)],[c_1942,c_5021]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_5180,plain,
% 2.40/0.99      ( u1_struct_0(sK2) = k1_xboole_0 ),
% 2.40/0.99      inference(global_propositional_subsumption,
% 2.40/0.99                [status(thm)],
% 2.40/0.99                [c_4215,c_25,c_5027]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_5199,plain,
% 2.40/0.99      ( k9_subset_1(k1_xboole_0,X0,sK1(sK2,X0,sK3)) = sK3
% 2.40/0.99      | v2_tex_2(X0,sK2) != iProver_top
% 2.40/0.99      | r1_tarski(X0,k1_xboole_0) != iProver_top
% 2.40/0.99      | r1_tarski(sK3,X0) != iProver_top ),
% 2.40/0.99      inference(demodulation,[status(thm)],[c_5180,c_3490]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_3,plain,
% 2.40/0.99      ( r1_tarski(k1_xboole_0,X0) ),
% 2.40/0.99      inference(cnf_transformation,[],[f34]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_66,plain,
% 2.40/0.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.40/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_9,plain,
% 2.40/0.99      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 2.40/0.99      inference(cnf_transformation,[],[f41]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_310,plain,
% 2.40/0.99      ( ~ r1_tarski(X0,X1) | sK3 != X0 | sK4 != X1 ),
% 2.40/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_17]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_311,plain,
% 2.40/0.99      ( ~ r1_tarski(sK3,sK4) ),
% 2.40/0.99      inference(unflattening,[status(thm)],[c_310]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_2104,plain,
% 2.40/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK4)) | r1_tarski(sK3,sK4) ),
% 2.40/0.99      inference(instantiation,[status(thm)],[c_8]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_2180,plain,
% 2.40/0.99      ( r1_tarski(k1_xboole_0,sK3) ),
% 2.40/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_2183,plain,
% 2.40/0.99      ( r1_tarski(k1_xboole_0,sK3) = iProver_top ),
% 2.40/0.99      inference(predicate_to_equality,[status(thm)],[c_2180]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_1466,plain,( X0 = X0 ),theory(equality) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_2217,plain,
% 2.40/0.99      ( sK4 = sK4 ),
% 2.40/0.99      inference(instantiation,[status(thm)],[c_1466]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_2230,plain,
% 2.40/0.99      ( sK3 = sK3 ),
% 2.40/0.99      inference(instantiation,[status(thm)],[c_1466]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_2372,plain,
% 2.40/0.99      ( r1_tarski(k1_xboole_0,sK4) ),
% 2.40/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_0,plain,
% 2.40/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 2.40/0.99      inference(cnf_transformation,[],[f33]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_2414,plain,
% 2.40/0.99      ( ~ r1_tarski(X0,sK3) | ~ r1_tarski(sK3,X0) | sK3 = X0 ),
% 2.40/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_2415,plain,
% 2.40/0.99      ( sK3 = X0
% 2.40/0.99      | r1_tarski(X0,sK3) != iProver_top
% 2.40/0.99      | r1_tarski(sK3,X0) != iProver_top ),
% 2.40/0.99      inference(predicate_to_equality,[status(thm)],[c_2414]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_3089,plain,
% 2.40/0.99      ( m1_subset_1(X0,k1_zfmisc_1(sK4)) | ~ r1_tarski(X0,sK4) ),
% 2.40/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_1468,plain,
% 2.40/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.40/0.99      theory(equality) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_2188,plain,
% 2.40/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,sK3) | X2 != X0 | sK3 != X1 ),
% 2.40/0.99      inference(instantiation,[status(thm)],[c_1468]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_2443,plain,
% 2.40/0.99      ( ~ r1_tarski(X0,sK3) | r1_tarski(X1,sK3) | X1 != X0 | sK3 != sK3 ),
% 2.40/0.99      inference(instantiation,[status(thm)],[c_2188]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_3305,plain,
% 2.40/0.99      ( r1_tarski(X0,sK3)
% 2.40/0.99      | ~ r1_tarski(k1_xboole_0,sK3)
% 2.40/0.99      | X0 != k1_xboole_0
% 2.40/0.99      | sK3 != sK3 ),
% 2.40/0.99      inference(instantiation,[status(thm)],[c_2443]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_3306,plain,
% 2.40/0.99      ( X0 != k1_xboole_0
% 2.40/0.99      | sK3 != sK3
% 2.40/0.99      | r1_tarski(X0,sK3) = iProver_top
% 2.40/0.99      | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
% 2.40/0.99      inference(predicate_to_equality,[status(thm)],[c_3305]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_1471,plain,
% 2.40/0.99      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.40/0.99      theory(equality) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_2127,plain,
% 2.40/0.99      ( m1_subset_1(X0,X1)
% 2.40/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
% 2.40/0.99      | X0 != X2
% 2.40/0.99      | X1 != k1_zfmisc_1(X3) ),
% 2.40/0.99      inference(instantiation,[status(thm)],[c_1471]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_2387,plain,
% 2.40/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.40/0.99      | m1_subset_1(X2,k1_zfmisc_1(X1))
% 2.40/0.99      | X2 != X0
% 2.40/0.99      | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
% 2.40/0.99      inference(instantiation,[status(thm)],[c_2127]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_3399,plain,
% 2.40/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK4))
% 2.40/0.99      | m1_subset_1(sK3,k1_zfmisc_1(sK4))
% 2.40/0.99      | k1_zfmisc_1(sK4) != k1_zfmisc_1(sK4)
% 2.40/0.99      | sK3 != X0 ),
% 2.40/0.99      inference(instantiation,[status(thm)],[c_2387]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_4411,plain,
% 2.40/0.99      ( ~ r1_tarski(X0,k1_xboole_0)
% 2.40/0.99      | ~ r1_tarski(k1_xboole_0,X0)
% 2.40/0.99      | X0 = k1_xboole_0 ),
% 2.40/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_4412,plain,
% 2.40/0.99      ( X0 = k1_xboole_0
% 2.40/0.99      | r1_tarski(X0,k1_xboole_0) != iProver_top
% 2.40/0.99      | r1_tarski(k1_xboole_0,X0) != iProver_top ),
% 2.40/0.99      inference(predicate_to_equality,[status(thm)],[c_4411]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_1470,plain,
% 2.40/0.99      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 2.40/0.99      theory(equality) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_4426,plain,
% 2.40/0.99      ( k1_zfmisc_1(sK4) = k1_zfmisc_1(sK4) | sK4 != sK4 ),
% 2.40/0.99      inference(instantiation,[status(thm)],[c_1470]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_2377,plain,
% 2.40/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,sK4) | X2 != X0 | sK4 != X1 ),
% 2.40/0.99      inference(instantiation,[status(thm)],[c_1468]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_3355,plain,
% 2.40/0.99      ( ~ r1_tarski(X0,sK4) | r1_tarski(X1,sK4) | X1 != X0 | sK4 != sK4 ),
% 2.40/0.99      inference(instantiation,[status(thm)],[c_2377]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_4540,plain,
% 2.40/0.99      ( r1_tarski(X0,sK4)
% 2.40/0.99      | ~ r1_tarski(k1_xboole_0,sK4)
% 2.40/0.99      | X0 != k1_xboole_0
% 2.40/0.99      | sK4 != sK4 ),
% 2.40/0.99      inference(instantiation,[status(thm)],[c_3355]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_6235,plain,
% 2.40/0.99      ( r1_tarski(X0,k1_xboole_0) != iProver_top
% 2.40/0.99      | r1_tarski(sK3,X0) != iProver_top ),
% 2.40/0.99      inference(global_propositional_subsumption,
% 2.40/0.99                [status(thm)],
% 2.40/0.99                [c_5199,c_66,c_311,c_2104,c_2183,c_2217,c_2230,c_2372,
% 2.40/0.99                 c_2415,c_3089,c_3306,c_3399,c_4412,c_4426,c_4540]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_6243,plain,
% 2.40/0.99      ( r1_tarski(sK3,k1_xboole_0) != iProver_top ),
% 2.40/0.99      inference(superposition,[status(thm)],[c_1944,c_6235]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_2451,plain,
% 2.40/0.99      ( r1_tarski(sK3,u1_struct_0(sK2)) = iProver_top ),
% 2.40/0.99      inference(superposition,[status(thm)],[c_1936,c_1940]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_5209,plain,
% 2.40/0.99      ( r1_tarski(sK3,k1_xboole_0) = iProver_top ),
% 2.40/0.99      inference(demodulation,[status(thm)],[c_5180,c_2451]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(contradiction,plain,
% 2.40/0.99      ( $false ),
% 2.40/0.99      inference(minisat,[status(thm)],[c_6243,c_5209]) ).
% 2.40/0.99  
% 2.40/0.99  
% 2.40/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.40/0.99  
% 2.40/0.99  ------                               Statistics
% 2.40/0.99  
% 2.40/0.99  ------ General
% 2.40/0.99  
% 2.40/0.99  abstr_ref_over_cycles:                  0
% 2.40/0.99  abstr_ref_under_cycles:                 0
% 2.40/0.99  gc_basic_clause_elim:                   0
% 2.40/0.99  forced_gc_time:                         0
% 2.40/0.99  parsing_time:                           0.008
% 2.40/0.99  unif_index_cands_time:                  0.
% 2.40/0.99  unif_index_add_time:                    0.
% 2.40/0.99  orderings_time:                         0.
% 2.40/0.99  out_proof_time:                         0.01
% 2.40/0.99  total_time:                             0.198
% 2.40/0.99  num_of_symbols:                         47
% 2.40/0.99  num_of_terms:                           4284
% 2.40/0.99  
% 2.40/0.99  ------ Preprocessing
% 2.40/0.99  
% 2.40/0.99  num_of_splits:                          0
% 2.40/0.99  num_of_split_atoms:                     0
% 2.40/0.99  num_of_reused_defs:                     0
% 2.40/0.99  num_eq_ax_congr_red:                    12
% 2.40/0.99  num_of_sem_filtered_clauses:            1
% 2.40/0.99  num_of_subtypes:                        0
% 2.40/0.99  monotx_restored_types:                  0
% 2.40/0.99  sat_num_of_epr_types:                   0
% 2.40/0.99  sat_num_of_non_cyclic_types:            0
% 2.40/0.99  sat_guarded_non_collapsed_types:        0
% 2.40/0.99  num_pure_diseq_elim:                    0
% 2.40/0.99  simp_replaced_by:                       0
% 2.40/0.99  res_preprocessed:                       103
% 2.40/0.99  prep_upred:                             0
% 2.40/0.99  prep_unflattend:                        30
% 2.40/0.99  smt_new_axioms:                         0
% 2.40/0.99  pred_elim_cands:                        4
% 2.40/0.99  pred_elim:                              2
% 2.40/0.99  pred_elim_cl:                           2
% 2.40/0.99  pred_elim_cycles:                       7
% 2.40/0.99  merged_defs:                            10
% 2.40/0.99  merged_defs_ncl:                        0
% 2.40/0.99  bin_hyper_res:                          10
% 2.40/0.99  prep_cycles:                            4
% 2.40/0.99  pred_elim_time:                         0.022
% 2.40/0.99  splitting_time:                         0.
% 2.40/0.99  sem_filter_time:                        0.
% 2.40/0.99  monotx_time:                            0.
% 2.40/0.99  subtype_inf_time:                       0.
% 2.40/0.99  
% 2.40/0.99  ------ Problem properties
% 2.40/0.99  
% 2.40/0.99  clauses:                                19
% 2.40/0.99  conjectures:                            4
% 2.40/0.99  epr:                                    5
% 2.40/0.99  horn:                                   16
% 2.40/0.99  ground:                                 5
% 2.40/0.99  unary:                                  7
% 2.40/0.99  binary:                                 3
% 2.40/0.99  lits:                                   48
% 2.40/0.99  lits_eq:                                5
% 2.40/0.99  fd_pure:                                0
% 2.40/0.99  fd_pseudo:                              0
% 2.40/0.99  fd_cond:                                1
% 2.40/0.99  fd_pseudo_cond:                         1
% 2.40/0.99  ac_symbols:                             0
% 2.40/0.99  
% 2.40/0.99  ------ Propositional Solver
% 2.40/0.99  
% 2.40/0.99  prop_solver_calls:                      30
% 2.40/0.99  prop_fast_solver_calls:                 1026
% 2.40/0.99  smt_solver_calls:                       0
% 2.40/0.99  smt_fast_solver_calls:                  0
% 2.40/0.99  prop_num_of_clauses:                    1954
% 2.40/0.99  prop_preprocess_simplified:             5265
% 2.40/0.99  prop_fo_subsumed:                       31
% 2.40/0.99  prop_solver_time:                       0.
% 2.40/0.99  smt_solver_time:                        0.
% 2.40/0.99  smt_fast_solver_time:                   0.
% 2.40/0.99  prop_fast_solver_time:                  0.
% 2.40/0.99  prop_unsat_core_time:                   0.
% 2.40/0.99  
% 2.40/0.99  ------ QBF
% 2.40/0.99  
% 2.40/0.99  qbf_q_res:                              0
% 2.40/0.99  qbf_num_tautologies:                    0
% 2.40/0.99  qbf_prep_cycles:                        0
% 2.40/0.99  
% 2.40/0.99  ------ BMC1
% 2.40/0.99  
% 2.40/0.99  bmc1_current_bound:                     -1
% 2.40/0.99  bmc1_last_solved_bound:                 -1
% 2.40/0.99  bmc1_unsat_core_size:                   -1
% 2.40/0.99  bmc1_unsat_core_parents_size:           -1
% 2.40/0.99  bmc1_merge_next_fun:                    0
% 2.40/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.40/0.99  
% 2.40/0.99  ------ Instantiation
% 2.40/0.99  
% 2.40/0.99  inst_num_of_clauses:                    590
% 2.40/0.99  inst_num_in_passive:                    279
% 2.40/0.99  inst_num_in_active:                     297
% 2.40/0.99  inst_num_in_unprocessed:                16
% 2.40/0.99  inst_num_of_loops:                      330
% 2.40/0.99  inst_num_of_learning_restarts:          0
% 2.40/0.99  inst_num_moves_active_passive:          29
% 2.40/0.99  inst_lit_activity:                      0
% 2.40/0.99  inst_lit_activity_moves:                0
% 2.40/0.99  inst_num_tautologies:                   0
% 2.40/0.99  inst_num_prop_implied:                  0
% 2.40/0.99  inst_num_existing_simplified:           0
% 2.40/0.99  inst_num_eq_res_simplified:             0
% 2.40/0.99  inst_num_child_elim:                    0
% 2.40/0.99  inst_num_of_dismatching_blockings:      148
% 2.40/0.99  inst_num_of_non_proper_insts:           729
% 2.40/0.99  inst_num_of_duplicates:                 0
% 2.40/0.99  inst_inst_num_from_inst_to_res:         0
% 2.40/0.99  inst_dismatching_checking_time:         0.
% 2.40/0.99  
% 2.40/0.99  ------ Resolution
% 2.40/0.99  
% 2.40/0.99  res_num_of_clauses:                     0
% 2.40/0.99  res_num_in_passive:                     0
% 2.40/0.99  res_num_in_active:                      0
% 2.40/0.99  res_num_of_loops:                       107
% 2.40/0.99  res_forward_subset_subsumed:            92
% 2.40/0.99  res_backward_subset_subsumed:           4
% 2.40/0.99  res_forward_subsumed:                   0
% 2.40/0.99  res_backward_subsumed:                  0
% 2.40/0.99  res_forward_subsumption_resolution:     2
% 2.40/0.99  res_backward_subsumption_resolution:    0
% 2.40/0.99  res_clause_to_clause_subsumption:       901
% 2.40/0.99  res_orphan_elimination:                 0
% 2.40/0.99  res_tautology_del:                      62
% 2.40/0.99  res_num_eq_res_simplified:              0
% 2.40/0.99  res_num_sel_changes:                    0
% 2.40/0.99  res_moves_from_active_to_pass:          0
% 2.40/0.99  
% 2.40/0.99  ------ Superposition
% 2.40/0.99  
% 2.40/0.99  sup_time_total:                         0.
% 2.40/0.99  sup_time_generating:                    0.
% 2.40/0.99  sup_time_sim_full:                      0.
% 2.40/0.99  sup_time_sim_immed:                     0.
% 2.40/0.99  
% 2.40/0.99  sup_num_of_clauses:                     75
% 2.40/0.99  sup_num_in_active:                      27
% 2.40/0.99  sup_num_in_passive:                     48
% 2.40/0.99  sup_num_of_loops:                       64
% 2.40/0.99  sup_fw_superposition:                   59
% 2.40/0.99  sup_bw_superposition:                   40
% 2.40/0.99  sup_immediate_simplified:               11
% 2.40/0.99  sup_given_eliminated:                   1
% 2.40/0.99  comparisons_done:                       0
% 2.40/0.99  comparisons_avoided:                    6
% 2.40/0.99  
% 2.40/0.99  ------ Simplifications
% 2.40/0.99  
% 2.40/0.99  
% 2.40/0.99  sim_fw_subset_subsumed:                 9
% 2.40/0.99  sim_bw_subset_subsumed:                 8
% 2.40/0.99  sim_fw_subsumed:                        1
% 2.40/0.99  sim_bw_subsumed:                        0
% 2.40/0.99  sim_fw_subsumption_res:                 2
% 2.40/0.99  sim_bw_subsumption_res:                 0
% 2.40/0.99  sim_tautology_del:                      1
% 2.40/0.99  sim_eq_tautology_del:                   10
% 2.40/0.99  sim_eq_res_simp:                        0
% 2.40/0.99  sim_fw_demodulated:                     0
% 2.40/0.99  sim_bw_demodulated:                     34
% 2.40/0.99  sim_light_normalised:                   2
% 2.40/0.99  sim_joinable_taut:                      0
% 2.40/0.99  sim_joinable_simp:                      0
% 2.40/0.99  sim_ac_normalised:                      0
% 2.40/0.99  sim_smt_subsumption:                    0
% 2.40/0.99  
%------------------------------------------------------------------------------
