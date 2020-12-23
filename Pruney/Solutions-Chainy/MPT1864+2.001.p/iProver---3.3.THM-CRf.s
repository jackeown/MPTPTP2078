%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:25:54 EST 2020

% Result     : Theorem 2.99s
% Output     : CNFRefutation 2.99s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 562 expanded)
%              Number of clauses        :   68 ( 153 expanded)
%              Number of leaves         :   16 ( 163 expanded)
%              Depth                    :   27
%              Number of atoms          :  446 (3237 expanded)
%              Number of equality atoms :  149 ( 624 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f61,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f42,f43])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_enumset1(X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f45,f61])).

fof(f9,axiom,(
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
    inference(nnf_transformation,[],[f9])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f10,axiom,(
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
    inference(ennf_transformation,[],[f10])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

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
    inference(nnf_transformation,[],[f18])).

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
     => ( k9_subset_1(u1_struct_0(X0),X1,sK2(X0,X1,X4)) = X4
        & v3_pre_topc(sK2(X0,X1,X4),X0)
        & m1_subset_1(sK2(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
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
            ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK1(X0,X1)
            | ~ v3_pre_topc(X3,X0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & r1_tarski(sK1(X0,X1),X1)
        & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f28,f30,f29])).

fof(f50,plain,(
    ! [X4,X0,X1] :
      ( v3_pre_topc(sK2(X0,X1,X4),X0)
      | ~ r1_tarski(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f11,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
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
    inference(negated_conjecture,[],[f11])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),X1,X3)
              | ~ v3_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ! [X3] :
            ( k1_tarski(sK5) != k9_subset_1(u1_struct_0(X0),X1,X3)
            | ~ v3_pre_topc(X3,X0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & r2_hidden(sK5,X1)
        & m1_subset_1(sK5,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
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
                ( k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),sK4,X3)
                | ~ v3_pre_topc(X3,X0)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            & r2_hidden(X2,sK4)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & v2_tex_2(sK4,X0)
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
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
                  ( k1_tarski(X2) != k9_subset_1(u1_struct_0(sK3),X1,X3)
                  | ~ v3_pre_topc(X3,sK3)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(sK3)) )
          & v2_tex_2(X1,sK3)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) )
      & l1_pre_topc(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ! [X3] :
        ( k1_tarski(sK5) != k9_subset_1(u1_struct_0(sK3),sK4,X3)
        | ~ v3_pre_topc(X3,sK3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3))) )
    & r2_hidden(sK5,sK4)
    & m1_subset_1(sK5,u1_struct_0(sK3))
    & v2_tex_2(sK4,sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    & l1_pre_topc(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f20,f34,f33,f32])).

fof(f55,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f49,plain,(
    ! [X4,X0,X1] :
      ( m1_subset_1(sK2(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f59,plain,(
    r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f35])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f56,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f35])).

fof(f51,plain,(
    ! [X4,X0,X1] :
      ( k9_subset_1(u1_struct_0(X0),X1,sK2(X0,X1,X4)) = X4
      | ~ r1_tarski(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f57,plain,(
    v2_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f60,plain,(
    ! [X3] :
      ( k1_tarski(sK5) != k9_subset_1(u1_struct_0(sK3),sK4,X3)
      | ~ v3_pre_topc(X3,sK3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f64,plain,(
    ! [X3] :
      ( k1_enumset1(sK5,sK5,sK5) != k9_subset_1(u1_struct_0(sK3),sK4,X3)
      | ~ v3_pre_topc(X3,sK3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3))) ) ),
    inference(definition_unfolding,[],[f60,f61])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f21,plain,(
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

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f21])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).

fof(f37,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k1_enumset1(X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1983,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(k1_enumset1(X0,X0,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_9,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1981,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_15,plain,
    ( v3_pre_topc(sK2(X0,X1,X2),X0)
    | ~ v2_tex_2(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r1_tarski(X2,X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_22,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_380,plain,
    ( v3_pre_topc(sK2(X0,X1,X2),X0)
    | ~ v2_tex_2(X1,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r1_tarski(X2,X1)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_22])).

cnf(c_381,plain,
    ( v3_pre_topc(sK2(sK3,X0,X1),sK3)
    | ~ v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_tarski(X1,X0) ),
    inference(unflattening,[status(thm)],[c_380])).

cnf(c_1974,plain,
    ( v3_pre_topc(sK2(sK3,X0,X1),sK3) = iProver_top
    | v2_tex_2(X0,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_381])).

cnf(c_16,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK2(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_401,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK2(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_22])).

cnf(c_402,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(sK2(sK3,X0,X1),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_tarski(X1,X0) ),
    inference(unflattening,[status(thm)],[c_401])).

cnf(c_1973,plain,
    ( v2_tex_2(X0,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK2(sK3,X0,X1),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_402])).

cnf(c_18,negated_conjecture,
    ( r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1978,plain,
    ( r2_hidden(sK5,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1984,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3370,plain,
    ( k3_xboole_0(k1_enumset1(X0,X0,X0),X1) = k1_enumset1(X0,X0,X0)
    | r2_hidden(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1983,c_1984])).

cnf(c_5163,plain,
    ( k3_xboole_0(k1_enumset1(sK5,sK5,sK5),sK4) = k1_enumset1(sK5,sK5,sK5) ),
    inference(superposition,[status(thm)],[c_1978,c_3370])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k3_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1985,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k3_xboole_0(X0,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2675,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k3_xboole_0(X2,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_1985])).

cnf(c_5178,plain,
    ( r1_tarski(k1_enumset1(sK5,sK5,sK5),X0) = iProver_top
    | r1_tarski(sK4,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5163,c_2675])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1975,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_14,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | ~ l1_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),X0,sK2(X1,X0,X2)) = X2 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_422,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | k9_subset_1(u1_struct_0(X1),X0,sK2(X1,X0,X2)) = X2
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_22])).

cnf(c_423,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_tarski(X1,X0)
    | k9_subset_1(u1_struct_0(sK3),X0,sK2(sK3,X0,X1)) = X1 ),
    inference(unflattening,[status(thm)],[c_422])).

cnf(c_1972,plain,
    ( k9_subset_1(u1_struct_0(sK3),X0,sK2(sK3,X0,X1)) = X1
    | v2_tex_2(X0,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_423])).

cnf(c_2273,plain,
    ( k9_subset_1(u1_struct_0(sK3),sK4,sK2(sK3,sK4,X0)) = X0
    | v2_tex_2(sK4,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r1_tarski(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1975,c_1972])).

cnf(c_24,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_20,negated_conjecture,
    ( v2_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_711,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_tarski(X1,X0)
    | k9_subset_1(u1_struct_0(sK3),X0,sK2(sK3,X0,X1)) = X1
    | sK4 != X0
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_423])).

cnf(c_712,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_tarski(X0,sK4)
    | k9_subset_1(u1_struct_0(sK3),sK4,sK2(sK3,sK4,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_711])).

cnf(c_713,plain,
    ( k9_subset_1(u1_struct_0(sK3),sK4,sK2(sK3,sK4,X0)) = X0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r1_tarski(X0,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_712])).

cnf(c_2433,plain,
    ( k9_subset_1(u1_struct_0(sK3),sK4,sK2(sK3,sK4,X0)) = X0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r1_tarski(X0,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2273,c_24,c_713])).

cnf(c_2437,plain,
    ( k9_subset_1(u1_struct_0(sK3),sK4,sK2(sK3,sK4,X0)) = X0
    | r1_tarski(X0,u1_struct_0(sK3)) != iProver_top
    | r1_tarski(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1981,c_2433])).

cnf(c_3373,plain,
    ( k9_subset_1(u1_struct_0(sK3),sK4,sK2(sK3,sK4,k1_enumset1(X0,X0,X0))) = k1_enumset1(X0,X0,X0)
    | r2_hidden(X0,u1_struct_0(sK3)) != iProver_top
    | r1_tarski(k1_enumset1(X0,X0,X0),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1983,c_2437])).

cnf(c_7612,plain,
    ( k9_subset_1(u1_struct_0(sK3),sK4,sK2(sK3,sK4,k1_enumset1(sK5,sK5,sK5))) = k1_enumset1(sK5,sK5,sK5)
    | r2_hidden(sK5,u1_struct_0(sK3)) != iProver_top
    | r1_tarski(sK4,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5178,c_3373])).

cnf(c_27,plain,
    ( r2_hidden(sK5,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1980,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2366,plain,
    ( r1_tarski(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1975,c_1980])).

cnf(c_2203,plain,
    ( ~ r2_hidden(X0,sK4)
    | r1_tarski(k1_enumset1(X0,X0,X0),sK4) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_3938,plain,
    ( ~ r2_hidden(sK5,sK4)
    | r1_tarski(k1_enumset1(sK5,sK5,sK5),sK4) ),
    inference(instantiation,[status(thm)],[c_2203])).

cnf(c_3939,plain,
    ( r2_hidden(sK5,sK4) != iProver_top
    | r1_tarski(k1_enumset1(sK5,sK5,sK5),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3938])).

cnf(c_2679,plain,
    ( k9_subset_1(u1_struct_0(sK3),sK4,sK2(sK3,sK4,k3_xboole_0(X0,X1))) = k3_xboole_0(X0,X1)
    | r1_tarski(X0,u1_struct_0(sK3)) != iProver_top
    | r1_tarski(k3_xboole_0(X0,X1),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1985,c_2437])).

cnf(c_4936,plain,
    ( k9_subset_1(u1_struct_0(sK3),sK4,sK2(sK3,sK4,k3_xboole_0(X0,X1))) = k3_xboole_0(X0,X1)
    | r1_tarski(X0,u1_struct_0(sK3)) != iProver_top
    | r1_tarski(k3_xboole_0(X1,X0),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_2679])).

cnf(c_5173,plain,
    ( k9_subset_1(u1_struct_0(sK3),sK4,sK2(sK3,sK4,k3_xboole_0(sK4,k1_enumset1(sK5,sK5,sK5)))) = k3_xboole_0(sK4,k1_enumset1(sK5,sK5,sK5))
    | r1_tarski(k1_enumset1(sK5,sK5,sK5),sK4) != iProver_top
    | r1_tarski(sK4,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5163,c_4936])).

cnf(c_5176,plain,
    ( k3_xboole_0(sK4,k1_enumset1(sK5,sK5,sK5)) = k1_enumset1(sK5,sK5,sK5) ),
    inference(superposition,[status(thm)],[c_5163,c_0])).

cnf(c_5181,plain,
    ( k9_subset_1(u1_struct_0(sK3),sK4,sK2(sK3,sK4,k1_enumset1(sK5,sK5,sK5))) = k1_enumset1(sK5,sK5,sK5)
    | r1_tarski(k1_enumset1(sK5,sK5,sK5),sK4) != iProver_top
    | r1_tarski(sK4,u1_struct_0(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5173,c_5176])).

cnf(c_7618,plain,
    ( k9_subset_1(u1_struct_0(sK3),sK4,sK2(sK3,sK4,k1_enumset1(sK5,sK5,sK5))) = k1_enumset1(sK5,sK5,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7612,c_27,c_2366,c_3939,c_5181])).

cnf(c_17,negated_conjecture,
    ( ~ v3_pre_topc(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | k1_enumset1(sK5,sK5,sK5) != k9_subset_1(u1_struct_0(sK3),sK4,X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1979,plain,
    ( k1_enumset1(sK5,sK5,sK5) != k9_subset_1(u1_struct_0(sK3),sK4,X0)
    | v3_pre_topc(X0,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_7620,plain,
    ( v3_pre_topc(sK2(sK3,sK4,k1_enumset1(sK5,sK5,sK5)),sK3) != iProver_top
    | m1_subset_1(sK2(sK3,sK4,k1_enumset1(sK5,sK5,sK5)),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7618,c_1979])).

cnf(c_8145,plain,
    ( v3_pre_topc(sK2(sK3,sK4,k1_enumset1(sK5,sK5,sK5)),sK3) != iProver_top
    | v2_tex_2(sK4,sK3) != iProver_top
    | m1_subset_1(k1_enumset1(sK5,sK5,sK5),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r1_tarski(k1_enumset1(sK5,sK5,sK5),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1973,c_7620])).

cnf(c_25,plain,
    ( v2_tex_2(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_9398,plain,
    ( v3_pre_topc(sK2(sK3,sK4,k1_enumset1(sK5,sK5,sK5)),sK3) != iProver_top
    | m1_subset_1(k1_enumset1(sK5,sK5,sK5),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8145,c_24,c_25,c_27,c_3939])).

cnf(c_9402,plain,
    ( v2_tex_2(sK4,sK3) != iProver_top
    | m1_subset_1(k1_enumset1(sK5,sK5,sK5),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r1_tarski(k1_enumset1(sK5,sK5,sK5),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1974,c_9398])).

cnf(c_10066,plain,
    ( m1_subset_1(k1_enumset1(sK5,sK5,sK5),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9402,c_24,c_25,c_27,c_3939])).

cnf(c_10070,plain,
    ( r1_tarski(k1_enumset1(sK5,sK5,sK5),u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1981,c_10066])).

cnf(c_10519,plain,
    ( r2_hidden(sK5,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1983,c_10070])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1986,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3385,plain,
    ( r2_hidden(sK5,X0) = iProver_top
    | r1_tarski(sK4,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1978,c_1986])).

cnf(c_3597,plain,
    ( r2_hidden(sK5,u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2366,c_3385])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10519,c_3597])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:49:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.99/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.99/1.01  
% 2.99/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.99/1.01  
% 2.99/1.01  ------  iProver source info
% 2.99/1.01  
% 2.99/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.99/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.99/1.01  git: non_committed_changes: false
% 2.99/1.01  git: last_make_outside_of_git: false
% 2.99/1.01  
% 2.99/1.01  ------ 
% 2.99/1.01  
% 2.99/1.01  ------ Input Options
% 2.99/1.01  
% 2.99/1.01  --out_options                           all
% 2.99/1.01  --tptp_safe_out                         true
% 2.99/1.01  --problem_path                          ""
% 2.99/1.01  --include_path                          ""
% 2.99/1.01  --clausifier                            res/vclausify_rel
% 2.99/1.01  --clausifier_options                    ""
% 2.99/1.01  --stdin                                 false
% 2.99/1.01  --stats_out                             all
% 2.99/1.01  
% 2.99/1.01  ------ General Options
% 2.99/1.01  
% 2.99/1.01  --fof                                   false
% 2.99/1.01  --time_out_real                         305.
% 2.99/1.01  --time_out_virtual                      -1.
% 2.99/1.01  --symbol_type_check                     false
% 2.99/1.01  --clausify_out                          false
% 2.99/1.01  --sig_cnt_out                           false
% 2.99/1.01  --trig_cnt_out                          false
% 2.99/1.01  --trig_cnt_out_tolerance                1.
% 2.99/1.01  --trig_cnt_out_sk_spl                   false
% 2.99/1.01  --abstr_cl_out                          false
% 2.99/1.01  
% 2.99/1.01  ------ Global Options
% 2.99/1.01  
% 2.99/1.01  --schedule                              default
% 2.99/1.01  --add_important_lit                     false
% 2.99/1.01  --prop_solver_per_cl                    1000
% 2.99/1.01  --min_unsat_core                        false
% 2.99/1.01  --soft_assumptions                      false
% 2.99/1.01  --soft_lemma_size                       3
% 2.99/1.01  --prop_impl_unit_size                   0
% 2.99/1.01  --prop_impl_unit                        []
% 2.99/1.01  --share_sel_clauses                     true
% 2.99/1.01  --reset_solvers                         false
% 2.99/1.01  --bc_imp_inh                            [conj_cone]
% 2.99/1.01  --conj_cone_tolerance                   3.
% 2.99/1.01  --extra_neg_conj                        none
% 2.99/1.01  --large_theory_mode                     true
% 2.99/1.01  --prolific_symb_bound                   200
% 2.99/1.01  --lt_threshold                          2000
% 2.99/1.01  --clause_weak_htbl                      true
% 2.99/1.01  --gc_record_bc_elim                     false
% 2.99/1.01  
% 2.99/1.01  ------ Preprocessing Options
% 2.99/1.01  
% 2.99/1.01  --preprocessing_flag                    true
% 2.99/1.01  --time_out_prep_mult                    0.1
% 2.99/1.01  --splitting_mode                        input
% 2.99/1.01  --splitting_grd                         true
% 2.99/1.01  --splitting_cvd                         false
% 2.99/1.01  --splitting_cvd_svl                     false
% 2.99/1.01  --splitting_nvd                         32
% 2.99/1.01  --sub_typing                            true
% 2.99/1.01  --prep_gs_sim                           true
% 2.99/1.01  --prep_unflatten                        true
% 2.99/1.01  --prep_res_sim                          true
% 2.99/1.01  --prep_upred                            true
% 2.99/1.01  --prep_sem_filter                       exhaustive
% 2.99/1.01  --prep_sem_filter_out                   false
% 2.99/1.01  --pred_elim                             true
% 2.99/1.01  --res_sim_input                         true
% 2.99/1.01  --eq_ax_congr_red                       true
% 2.99/1.01  --pure_diseq_elim                       true
% 2.99/1.01  --brand_transform                       false
% 2.99/1.01  --non_eq_to_eq                          false
% 2.99/1.01  --prep_def_merge                        true
% 2.99/1.01  --prep_def_merge_prop_impl              false
% 2.99/1.01  --prep_def_merge_mbd                    true
% 2.99/1.01  --prep_def_merge_tr_red                 false
% 2.99/1.01  --prep_def_merge_tr_cl                  false
% 2.99/1.01  --smt_preprocessing                     true
% 2.99/1.01  --smt_ac_axioms                         fast
% 2.99/1.01  --preprocessed_out                      false
% 2.99/1.01  --preprocessed_stats                    false
% 2.99/1.01  
% 2.99/1.01  ------ Abstraction refinement Options
% 2.99/1.01  
% 2.99/1.01  --abstr_ref                             []
% 2.99/1.01  --abstr_ref_prep                        false
% 2.99/1.01  --abstr_ref_until_sat                   false
% 2.99/1.01  --abstr_ref_sig_restrict                funpre
% 2.99/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.99/1.01  --abstr_ref_under                       []
% 2.99/1.01  
% 2.99/1.01  ------ SAT Options
% 2.99/1.01  
% 2.99/1.01  --sat_mode                              false
% 2.99/1.01  --sat_fm_restart_options                ""
% 2.99/1.01  --sat_gr_def                            false
% 2.99/1.01  --sat_epr_types                         true
% 2.99/1.01  --sat_non_cyclic_types                  false
% 2.99/1.01  --sat_finite_models                     false
% 2.99/1.01  --sat_fm_lemmas                         false
% 2.99/1.01  --sat_fm_prep                           false
% 2.99/1.01  --sat_fm_uc_incr                        true
% 2.99/1.01  --sat_out_model                         small
% 2.99/1.01  --sat_out_clauses                       false
% 2.99/1.01  
% 2.99/1.01  ------ QBF Options
% 2.99/1.01  
% 2.99/1.01  --qbf_mode                              false
% 2.99/1.01  --qbf_elim_univ                         false
% 2.99/1.01  --qbf_dom_inst                          none
% 2.99/1.01  --qbf_dom_pre_inst                      false
% 2.99/1.01  --qbf_sk_in                             false
% 2.99/1.01  --qbf_pred_elim                         true
% 2.99/1.01  --qbf_split                             512
% 2.99/1.01  
% 2.99/1.01  ------ BMC1 Options
% 2.99/1.01  
% 2.99/1.01  --bmc1_incremental                      false
% 2.99/1.01  --bmc1_axioms                           reachable_all
% 2.99/1.01  --bmc1_min_bound                        0
% 2.99/1.01  --bmc1_max_bound                        -1
% 2.99/1.01  --bmc1_max_bound_default                -1
% 2.99/1.01  --bmc1_symbol_reachability              true
% 2.99/1.01  --bmc1_property_lemmas                  false
% 2.99/1.01  --bmc1_k_induction                      false
% 2.99/1.01  --bmc1_non_equiv_states                 false
% 2.99/1.01  --bmc1_deadlock                         false
% 2.99/1.01  --bmc1_ucm                              false
% 2.99/1.01  --bmc1_add_unsat_core                   none
% 2.99/1.01  --bmc1_unsat_core_children              false
% 2.99/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.99/1.01  --bmc1_out_stat                         full
% 2.99/1.01  --bmc1_ground_init                      false
% 2.99/1.01  --bmc1_pre_inst_next_state              false
% 2.99/1.01  --bmc1_pre_inst_state                   false
% 2.99/1.01  --bmc1_pre_inst_reach_state             false
% 2.99/1.01  --bmc1_out_unsat_core                   false
% 2.99/1.01  --bmc1_aig_witness_out                  false
% 2.99/1.01  --bmc1_verbose                          false
% 2.99/1.01  --bmc1_dump_clauses_tptp                false
% 2.99/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.99/1.01  --bmc1_dump_file                        -
% 2.99/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.99/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.99/1.01  --bmc1_ucm_extend_mode                  1
% 2.99/1.01  --bmc1_ucm_init_mode                    2
% 2.99/1.01  --bmc1_ucm_cone_mode                    none
% 2.99/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.99/1.01  --bmc1_ucm_relax_model                  4
% 2.99/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.99/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.99/1.01  --bmc1_ucm_layered_model                none
% 2.99/1.01  --bmc1_ucm_max_lemma_size               10
% 2.99/1.01  
% 2.99/1.01  ------ AIG Options
% 2.99/1.01  
% 2.99/1.01  --aig_mode                              false
% 2.99/1.01  
% 2.99/1.01  ------ Instantiation Options
% 2.99/1.01  
% 2.99/1.01  --instantiation_flag                    true
% 2.99/1.01  --inst_sos_flag                         true
% 2.99/1.01  --inst_sos_phase                        true
% 2.99/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.99/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.99/1.01  --inst_lit_sel_side                     num_symb
% 2.99/1.01  --inst_solver_per_active                1400
% 2.99/1.01  --inst_solver_calls_frac                1.
% 2.99/1.01  --inst_passive_queue_type               priority_queues
% 2.99/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.99/1.01  --inst_passive_queues_freq              [25;2]
% 2.99/1.01  --inst_dismatching                      true
% 2.99/1.01  --inst_eager_unprocessed_to_passive     true
% 2.99/1.01  --inst_prop_sim_given                   true
% 2.99/1.01  --inst_prop_sim_new                     false
% 2.99/1.01  --inst_subs_new                         false
% 2.99/1.01  --inst_eq_res_simp                      false
% 2.99/1.01  --inst_subs_given                       false
% 2.99/1.01  --inst_orphan_elimination               true
% 2.99/1.01  --inst_learning_loop_flag               true
% 2.99/1.01  --inst_learning_start                   3000
% 2.99/1.01  --inst_learning_factor                  2
% 2.99/1.01  --inst_start_prop_sim_after_learn       3
% 2.99/1.01  --inst_sel_renew                        solver
% 2.99/1.01  --inst_lit_activity_flag                true
% 2.99/1.01  --inst_restr_to_given                   false
% 2.99/1.01  --inst_activity_threshold               500
% 2.99/1.01  --inst_out_proof                        true
% 2.99/1.01  
% 2.99/1.01  ------ Resolution Options
% 2.99/1.01  
% 2.99/1.01  --resolution_flag                       true
% 2.99/1.01  --res_lit_sel                           adaptive
% 2.99/1.01  --res_lit_sel_side                      none
% 2.99/1.01  --res_ordering                          kbo
% 2.99/1.01  --res_to_prop_solver                    active
% 2.99/1.01  --res_prop_simpl_new                    false
% 2.99/1.01  --res_prop_simpl_given                  true
% 2.99/1.01  --res_passive_queue_type                priority_queues
% 2.99/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.99/1.01  --res_passive_queues_freq               [15;5]
% 2.99/1.01  --res_forward_subs                      full
% 2.99/1.01  --res_backward_subs                     full
% 2.99/1.01  --res_forward_subs_resolution           true
% 2.99/1.01  --res_backward_subs_resolution          true
% 2.99/1.01  --res_orphan_elimination                true
% 2.99/1.01  --res_time_limit                        2.
% 2.99/1.01  --res_out_proof                         true
% 2.99/1.01  
% 2.99/1.01  ------ Superposition Options
% 2.99/1.01  
% 2.99/1.01  --superposition_flag                    true
% 2.99/1.01  --sup_passive_queue_type                priority_queues
% 2.99/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.99/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.99/1.01  --demod_completeness_check              fast
% 2.99/1.01  --demod_use_ground                      true
% 2.99/1.01  --sup_to_prop_solver                    passive
% 2.99/1.01  --sup_prop_simpl_new                    true
% 2.99/1.01  --sup_prop_simpl_given                  true
% 2.99/1.01  --sup_fun_splitting                     true
% 2.99/1.01  --sup_smt_interval                      50000
% 2.99/1.01  
% 2.99/1.01  ------ Superposition Simplification Setup
% 2.99/1.01  
% 2.99/1.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 2.99/1.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 2.99/1.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 2.99/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 2.99/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.99/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 2.99/1.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 2.99/1.01  --sup_immed_triv                        [TrivRules]
% 2.99/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.99/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 2.99/1.01  --sup_immed_bw_main                     []
% 2.99/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 2.99/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.99/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 2.99/1.01  --sup_input_bw                          []
% 2.99/1.01  
% 2.99/1.01  ------ Combination Options
% 2.99/1.01  
% 2.99/1.01  --comb_res_mult                         3
% 2.99/1.01  --comb_sup_mult                         2
% 2.99/1.01  --comb_inst_mult                        10
% 2.99/1.01  
% 2.99/1.01  ------ Debug Options
% 2.99/1.01  
% 2.99/1.01  --dbg_backtrace                         false
% 2.99/1.01  --dbg_dump_prop_clauses                 false
% 2.99/1.01  --dbg_dump_prop_clauses_file            -
% 2.99/1.01  --dbg_out_stat                          false
% 2.99/1.01  ------ Parsing...
% 2.99/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.99/1.01  
% 2.99/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.99/1.01  
% 2.99/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.99/1.01  
% 2.99/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.99/1.01  ------ Proving...
% 2.99/1.01  ------ Problem Properties 
% 2.99/1.01  
% 2.99/1.01  
% 2.99/1.01  clauses                                 21
% 2.99/1.01  conjectures                             5
% 2.99/1.01  EPR                                     3
% 2.99/1.01  Horn                                    18
% 2.99/1.01  unary                                   5
% 2.99/1.01  binary                                  8
% 2.99/1.01  lits                                    53
% 2.99/1.01  lits eq                                 5
% 2.99/1.01  fd_pure                                 0
% 2.99/1.01  fd_pseudo                               0
% 2.99/1.01  fd_cond                                 0
% 2.99/1.01  fd_pseudo_cond                          0
% 2.99/1.01  AC symbols                              0
% 2.99/1.01  
% 2.99/1.01  ------ Schedule dynamic 5 is on 
% 2.99/1.01  
% 2.99/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.99/1.01  
% 2.99/1.01  
% 2.99/1.01  ------ 
% 2.99/1.01  Current options:
% 2.99/1.01  ------ 
% 2.99/1.01  
% 2.99/1.01  ------ Input Options
% 2.99/1.01  
% 2.99/1.01  --out_options                           all
% 2.99/1.01  --tptp_safe_out                         true
% 2.99/1.01  --problem_path                          ""
% 2.99/1.01  --include_path                          ""
% 2.99/1.01  --clausifier                            res/vclausify_rel
% 2.99/1.01  --clausifier_options                    ""
% 2.99/1.01  --stdin                                 false
% 2.99/1.01  --stats_out                             all
% 2.99/1.01  
% 2.99/1.01  ------ General Options
% 2.99/1.01  
% 2.99/1.01  --fof                                   false
% 2.99/1.01  --time_out_real                         305.
% 2.99/1.01  --time_out_virtual                      -1.
% 2.99/1.01  --symbol_type_check                     false
% 2.99/1.01  --clausify_out                          false
% 2.99/1.01  --sig_cnt_out                           false
% 2.99/1.01  --trig_cnt_out                          false
% 2.99/1.01  --trig_cnt_out_tolerance                1.
% 2.99/1.01  --trig_cnt_out_sk_spl                   false
% 2.99/1.01  --abstr_cl_out                          false
% 2.99/1.01  
% 2.99/1.01  ------ Global Options
% 2.99/1.01  
% 2.99/1.01  --schedule                              default
% 2.99/1.01  --add_important_lit                     false
% 2.99/1.01  --prop_solver_per_cl                    1000
% 2.99/1.01  --min_unsat_core                        false
% 2.99/1.01  --soft_assumptions                      false
% 2.99/1.01  --soft_lemma_size                       3
% 2.99/1.01  --prop_impl_unit_size                   0
% 2.99/1.01  --prop_impl_unit                        []
% 2.99/1.01  --share_sel_clauses                     true
% 2.99/1.01  --reset_solvers                         false
% 2.99/1.01  --bc_imp_inh                            [conj_cone]
% 2.99/1.01  --conj_cone_tolerance                   3.
% 2.99/1.01  --extra_neg_conj                        none
% 2.99/1.01  --large_theory_mode                     true
% 2.99/1.01  --prolific_symb_bound                   200
% 2.99/1.01  --lt_threshold                          2000
% 2.99/1.01  --clause_weak_htbl                      true
% 2.99/1.01  --gc_record_bc_elim                     false
% 2.99/1.01  
% 2.99/1.01  ------ Preprocessing Options
% 2.99/1.01  
% 2.99/1.01  --preprocessing_flag                    true
% 2.99/1.01  --time_out_prep_mult                    0.1
% 2.99/1.01  --splitting_mode                        input
% 2.99/1.01  --splitting_grd                         true
% 2.99/1.01  --splitting_cvd                         false
% 2.99/1.01  --splitting_cvd_svl                     false
% 2.99/1.01  --splitting_nvd                         32
% 2.99/1.01  --sub_typing                            true
% 2.99/1.01  --prep_gs_sim                           true
% 2.99/1.01  --prep_unflatten                        true
% 2.99/1.01  --prep_res_sim                          true
% 2.99/1.01  --prep_upred                            true
% 2.99/1.01  --prep_sem_filter                       exhaustive
% 2.99/1.01  --prep_sem_filter_out                   false
% 2.99/1.01  --pred_elim                             true
% 2.99/1.01  --res_sim_input                         true
% 2.99/1.01  --eq_ax_congr_red                       true
% 2.99/1.01  --pure_diseq_elim                       true
% 2.99/1.01  --brand_transform                       false
% 2.99/1.01  --non_eq_to_eq                          false
% 2.99/1.01  --prep_def_merge                        true
% 2.99/1.01  --prep_def_merge_prop_impl              false
% 2.99/1.01  --prep_def_merge_mbd                    true
% 2.99/1.01  --prep_def_merge_tr_red                 false
% 2.99/1.01  --prep_def_merge_tr_cl                  false
% 2.99/1.01  --smt_preprocessing                     true
% 2.99/1.01  --smt_ac_axioms                         fast
% 2.99/1.01  --preprocessed_out                      false
% 2.99/1.01  --preprocessed_stats                    false
% 2.99/1.01  
% 2.99/1.01  ------ Abstraction refinement Options
% 2.99/1.01  
% 2.99/1.01  --abstr_ref                             []
% 2.99/1.01  --abstr_ref_prep                        false
% 2.99/1.01  --abstr_ref_until_sat                   false
% 2.99/1.01  --abstr_ref_sig_restrict                funpre
% 2.99/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.99/1.01  --abstr_ref_under                       []
% 2.99/1.01  
% 2.99/1.01  ------ SAT Options
% 2.99/1.01  
% 2.99/1.01  --sat_mode                              false
% 2.99/1.01  --sat_fm_restart_options                ""
% 2.99/1.01  --sat_gr_def                            false
% 2.99/1.01  --sat_epr_types                         true
% 2.99/1.01  --sat_non_cyclic_types                  false
% 2.99/1.01  --sat_finite_models                     false
% 2.99/1.01  --sat_fm_lemmas                         false
% 2.99/1.01  --sat_fm_prep                           false
% 2.99/1.01  --sat_fm_uc_incr                        true
% 2.99/1.01  --sat_out_model                         small
% 2.99/1.01  --sat_out_clauses                       false
% 2.99/1.01  
% 2.99/1.01  ------ QBF Options
% 2.99/1.01  
% 2.99/1.01  --qbf_mode                              false
% 2.99/1.01  --qbf_elim_univ                         false
% 2.99/1.01  --qbf_dom_inst                          none
% 2.99/1.01  --qbf_dom_pre_inst                      false
% 2.99/1.01  --qbf_sk_in                             false
% 2.99/1.01  --qbf_pred_elim                         true
% 2.99/1.01  --qbf_split                             512
% 2.99/1.01  
% 2.99/1.01  ------ BMC1 Options
% 2.99/1.01  
% 2.99/1.01  --bmc1_incremental                      false
% 2.99/1.01  --bmc1_axioms                           reachable_all
% 2.99/1.01  --bmc1_min_bound                        0
% 2.99/1.01  --bmc1_max_bound                        -1
% 2.99/1.01  --bmc1_max_bound_default                -1
% 2.99/1.01  --bmc1_symbol_reachability              true
% 2.99/1.01  --bmc1_property_lemmas                  false
% 2.99/1.01  --bmc1_k_induction                      false
% 2.99/1.01  --bmc1_non_equiv_states                 false
% 2.99/1.01  --bmc1_deadlock                         false
% 2.99/1.01  --bmc1_ucm                              false
% 2.99/1.01  --bmc1_add_unsat_core                   none
% 2.99/1.01  --bmc1_unsat_core_children              false
% 2.99/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.99/1.01  --bmc1_out_stat                         full
% 2.99/1.01  --bmc1_ground_init                      false
% 2.99/1.01  --bmc1_pre_inst_next_state              false
% 2.99/1.01  --bmc1_pre_inst_state                   false
% 2.99/1.01  --bmc1_pre_inst_reach_state             false
% 2.99/1.01  --bmc1_out_unsat_core                   false
% 2.99/1.01  --bmc1_aig_witness_out                  false
% 2.99/1.01  --bmc1_verbose                          false
% 2.99/1.01  --bmc1_dump_clauses_tptp                false
% 2.99/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.99/1.01  --bmc1_dump_file                        -
% 2.99/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.99/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.99/1.01  --bmc1_ucm_extend_mode                  1
% 2.99/1.01  --bmc1_ucm_init_mode                    2
% 2.99/1.01  --bmc1_ucm_cone_mode                    none
% 2.99/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.99/1.01  --bmc1_ucm_relax_model                  4
% 2.99/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.99/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.99/1.01  --bmc1_ucm_layered_model                none
% 2.99/1.01  --bmc1_ucm_max_lemma_size               10
% 2.99/1.01  
% 2.99/1.01  ------ AIG Options
% 2.99/1.01  
% 2.99/1.01  --aig_mode                              false
% 2.99/1.01  
% 2.99/1.01  ------ Instantiation Options
% 2.99/1.01  
% 2.99/1.01  --instantiation_flag                    true
% 2.99/1.01  --inst_sos_flag                         true
% 2.99/1.01  --inst_sos_phase                        true
% 2.99/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.99/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.99/1.01  --inst_lit_sel_side                     none
% 2.99/1.01  --inst_solver_per_active                1400
% 2.99/1.01  --inst_solver_calls_frac                1.
% 2.99/1.01  --inst_passive_queue_type               priority_queues
% 2.99/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.99/1.01  --inst_passive_queues_freq              [25;2]
% 2.99/1.01  --inst_dismatching                      true
% 2.99/1.01  --inst_eager_unprocessed_to_passive     true
% 2.99/1.01  --inst_prop_sim_given                   true
% 2.99/1.01  --inst_prop_sim_new                     false
% 2.99/1.01  --inst_subs_new                         false
% 2.99/1.01  --inst_eq_res_simp                      false
% 2.99/1.01  --inst_subs_given                       false
% 2.99/1.01  --inst_orphan_elimination               true
% 2.99/1.01  --inst_learning_loop_flag               true
% 2.99/1.01  --inst_learning_start                   3000
% 2.99/1.01  --inst_learning_factor                  2
% 2.99/1.01  --inst_start_prop_sim_after_learn       3
% 2.99/1.01  --inst_sel_renew                        solver
% 2.99/1.01  --inst_lit_activity_flag                true
% 2.99/1.01  --inst_restr_to_given                   false
% 2.99/1.01  --inst_activity_threshold               500
% 2.99/1.01  --inst_out_proof                        true
% 2.99/1.01  
% 2.99/1.01  ------ Resolution Options
% 2.99/1.01  
% 2.99/1.01  --resolution_flag                       false
% 2.99/1.01  --res_lit_sel                           adaptive
% 2.99/1.01  --res_lit_sel_side                      none
% 2.99/1.01  --res_ordering                          kbo
% 2.99/1.01  --res_to_prop_solver                    active
% 2.99/1.01  --res_prop_simpl_new                    false
% 2.99/1.01  --res_prop_simpl_given                  true
% 2.99/1.01  --res_passive_queue_type                priority_queues
% 2.99/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.99/1.01  --res_passive_queues_freq               [15;5]
% 2.99/1.01  --res_forward_subs                      full
% 2.99/1.01  --res_backward_subs                     full
% 2.99/1.01  --res_forward_subs_resolution           true
% 2.99/1.01  --res_backward_subs_resolution          true
% 2.99/1.01  --res_orphan_elimination                true
% 2.99/1.01  --res_time_limit                        2.
% 2.99/1.01  --res_out_proof                         true
% 2.99/1.01  
% 2.99/1.01  ------ Superposition Options
% 2.99/1.01  
% 2.99/1.01  --superposition_flag                    true
% 2.99/1.01  --sup_passive_queue_type                priority_queues
% 2.99/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.99/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.99/1.01  --demod_completeness_check              fast
% 2.99/1.01  --demod_use_ground                      true
% 2.99/1.01  --sup_to_prop_solver                    passive
% 2.99/1.01  --sup_prop_simpl_new                    true
% 2.99/1.01  --sup_prop_simpl_given                  true
% 2.99/1.01  --sup_fun_splitting                     true
% 2.99/1.01  --sup_smt_interval                      50000
% 2.99/1.01  
% 2.99/1.01  ------ Superposition Simplification Setup
% 2.99/1.01  
% 2.99/1.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 2.99/1.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 2.99/1.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 2.99/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 2.99/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.99/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 2.99/1.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 2.99/1.01  --sup_immed_triv                        [TrivRules]
% 2.99/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.99/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 2.99/1.01  --sup_immed_bw_main                     []
% 2.99/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 2.99/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.99/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 2.99/1.01  --sup_input_bw                          []
% 2.99/1.01  
% 2.99/1.01  ------ Combination Options
% 2.99/1.01  
% 2.99/1.01  --comb_res_mult                         3
% 2.99/1.01  --comb_sup_mult                         2
% 2.99/1.01  --comb_inst_mult                        10
% 2.99/1.01  
% 2.99/1.01  ------ Debug Options
% 2.99/1.01  
% 2.99/1.01  --dbg_backtrace                         false
% 2.99/1.01  --dbg_dump_prop_clauses                 false
% 2.99/1.01  --dbg_dump_prop_clauses_file            -
% 2.99/1.01  --dbg_out_stat                          false
% 2.99/1.01  
% 2.99/1.01  
% 2.99/1.01  
% 2.99/1.01  
% 2.99/1.01  ------ Proving...
% 2.99/1.01  
% 2.99/1.01  
% 2.99/1.01  % SZS status Theorem for theBenchmark.p
% 2.99/1.01  
% 2.99/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.99/1.01  
% 2.99/1.01  fof(f7,axiom,(
% 2.99/1.01    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 2.99/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.99/1.01  
% 2.99/1.01  fof(f25,plain,(
% 2.99/1.01    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 2.99/1.01    inference(nnf_transformation,[],[f7])).
% 2.99/1.01  
% 2.99/1.01  fof(f45,plain,(
% 2.99/1.01    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 2.99/1.01    inference(cnf_transformation,[],[f25])).
% 2.99/1.01  
% 2.99/1.01  fof(f5,axiom,(
% 2.99/1.01    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.99/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.99/1.01  
% 2.99/1.01  fof(f42,plain,(
% 2.99/1.01    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.99/1.01    inference(cnf_transformation,[],[f5])).
% 2.99/1.01  
% 2.99/1.01  fof(f6,axiom,(
% 2.99/1.01    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.99/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.99/1.01  
% 2.99/1.01  fof(f43,plain,(
% 2.99/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.99/1.01    inference(cnf_transformation,[],[f6])).
% 2.99/1.01  
% 2.99/1.01  fof(f61,plain,(
% 2.99/1.01    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 2.99/1.01    inference(definition_unfolding,[],[f42,f43])).
% 2.99/1.01  
% 2.99/1.01  fof(f62,plain,(
% 2.99/1.01    ( ! [X0,X1] : (r1_tarski(k1_enumset1(X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 2.99/1.01    inference(definition_unfolding,[],[f45,f61])).
% 2.99/1.01  
% 2.99/1.01  fof(f9,axiom,(
% 2.99/1.01    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.99/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.99/1.01  
% 2.99/1.01  fof(f26,plain,(
% 2.99/1.01    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.99/1.01    inference(nnf_transformation,[],[f9])).
% 2.99/1.01  
% 2.99/1.01  fof(f48,plain,(
% 2.99/1.01    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.99/1.01    inference(cnf_transformation,[],[f26])).
% 2.99/1.01  
% 2.99/1.01  fof(f10,axiom,(
% 2.99/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0))) & r1_tarski(X2,X1))))))),
% 2.99/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.99/1.01  
% 2.99/1.01  fof(f17,plain,(
% 2.99/1.01    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((? [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.99/1.01    inference(ennf_transformation,[],[f10])).
% 2.99/1.01  
% 2.99/1.01  fof(f18,plain,(
% 2.99/1.01    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.99/1.01    inference(flattening,[],[f17])).
% 2.99/1.01  
% 2.99/1.01  fof(f27,plain,(
% 2.99/1.01    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.99/1.01    inference(nnf_transformation,[],[f18])).
% 2.99/1.01  
% 2.99/1.01  fof(f28,plain,(
% 2.99/1.01    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (? [X5] : (k9_subset_1(u1_struct_0(X0),X1,X5) = X4 & v3_pre_topc(X5,X0) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.99/1.01    inference(rectify,[],[f27])).
% 2.99/1.01  
% 2.99/1.01  fof(f30,plain,(
% 2.99/1.01    ! [X4,X1,X0] : (? [X5] : (k9_subset_1(u1_struct_0(X0),X1,X5) = X4 & v3_pre_topc(X5,X0) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) => (k9_subset_1(u1_struct_0(X0),X1,sK2(X0,X1,X4)) = X4 & v3_pre_topc(sK2(X0,X1,X4),X0) & m1_subset_1(sK2(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.99/1.01    introduced(choice_axiom,[])).
% 2.99/1.01  
% 2.99/1.01  fof(f29,plain,(
% 2.99/1.01    ! [X1,X0] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK1(X0,X1) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(sK1(X0,X1),X1) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.99/1.01    introduced(choice_axiom,[])).
% 2.99/1.01  
% 2.99/1.01  fof(f31,plain,(
% 2.99/1.01    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK1(X0,X1) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(sK1(X0,X1),X1) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : ((k9_subset_1(u1_struct_0(X0),X1,sK2(X0,X1,X4)) = X4 & v3_pre_topc(sK2(X0,X1,X4),X0) & m1_subset_1(sK2(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.99/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f28,f30,f29])).
% 2.99/1.01  
% 2.99/1.01  fof(f50,plain,(
% 2.99/1.01    ( ! [X4,X0,X1] : (v3_pre_topc(sK2(X0,X1,X4),X0) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.99/1.01    inference(cnf_transformation,[],[f31])).
% 2.99/1.01  
% 2.99/1.01  fof(f11,conjecture,(
% 2.99/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k1_tarski(X2) = k9_subset_1(u1_struct_0(X0),X1,X3) & v3_pre_topc(X3,X0))) & r2_hidden(X2,X1))))))),
% 2.99/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.99/1.01  
% 2.99/1.01  fof(f12,negated_conjecture,(
% 2.99/1.01    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k1_tarski(X2) = k9_subset_1(u1_struct_0(X0),X1,X3) & v3_pre_topc(X3,X0))) & r2_hidden(X2,X1))))))),
% 2.99/1.01    inference(negated_conjecture,[],[f11])).
% 2.99/1.01  
% 2.99/1.01  fof(f19,plain,(
% 2.99/1.01    ? [X0] : (? [X1] : ((? [X2] : ((! [X3] : ((k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),X1,X3) | ~v3_pre_topc(X3,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1)) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 2.99/1.01    inference(ennf_transformation,[],[f12])).
% 2.99/1.01  
% 2.99/1.01  fof(f20,plain,(
% 2.99/1.01    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),X1,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 2.99/1.01    inference(flattening,[],[f19])).
% 2.99/1.01  
% 2.99/1.01  fof(f34,plain,(
% 2.99/1.01    ( ! [X0,X1] : (? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),X1,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) => (! [X3] : (k1_tarski(sK5) != k9_subset_1(u1_struct_0(X0),X1,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(sK5,X1) & m1_subset_1(sK5,u1_struct_0(X0)))) )),
% 2.99/1.01    introduced(choice_axiom,[])).
% 2.99/1.01  
% 2.99/1.01  fof(f33,plain,(
% 2.99/1.01    ( ! [X0] : (? [X1] : (? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),X1,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),sK4,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,sK4) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(sK4,X0) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.99/1.01    introduced(choice_axiom,[])).
% 2.99/1.01  
% 2.99/1.01  fof(f32,plain,(
% 2.99/1.01    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),X1,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(sK3),X1,X3) | ~v3_pre_topc(X3,sK3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(sK3))) & v2_tex_2(X1,sK3) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))) & l1_pre_topc(sK3))),
% 2.99/1.01    introduced(choice_axiom,[])).
% 2.99/1.01  
% 2.99/1.01  fof(f35,plain,(
% 2.99/1.01    ((! [X3] : (k1_tarski(sK5) != k9_subset_1(u1_struct_0(sK3),sK4,X3) | ~v3_pre_topc(X3,sK3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3)))) & r2_hidden(sK5,sK4) & m1_subset_1(sK5,u1_struct_0(sK3))) & v2_tex_2(sK4,sK3) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))) & l1_pre_topc(sK3)),
% 2.99/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f20,f34,f33,f32])).
% 2.99/1.01  
% 2.99/1.01  fof(f55,plain,(
% 2.99/1.01    l1_pre_topc(sK3)),
% 2.99/1.01    inference(cnf_transformation,[],[f35])).
% 2.99/1.01  
% 2.99/1.01  fof(f49,plain,(
% 2.99/1.01    ( ! [X4,X0,X1] : (m1_subset_1(sK2(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.99/1.01    inference(cnf_transformation,[],[f31])).
% 2.99/1.01  
% 2.99/1.01  fof(f59,plain,(
% 2.99/1.01    r2_hidden(sK5,sK4)),
% 2.99/1.01    inference(cnf_transformation,[],[f35])).
% 2.99/1.01  
% 2.99/1.01  fof(f4,axiom,(
% 2.99/1.01    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.99/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.99/1.01  
% 2.99/1.01  fof(f15,plain,(
% 2.99/1.01    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.99/1.01    inference(ennf_transformation,[],[f4])).
% 2.99/1.01  
% 2.99/1.01  fof(f41,plain,(
% 2.99/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 2.99/1.01    inference(cnf_transformation,[],[f15])).
% 2.99/1.01  
% 2.99/1.01  fof(f1,axiom,(
% 2.99/1.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.99/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.99/1.01  
% 2.99/1.01  fof(f36,plain,(
% 2.99/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.99/1.01    inference(cnf_transformation,[],[f1])).
% 2.99/1.01  
% 2.99/1.01  fof(f3,axiom,(
% 2.99/1.01    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k3_xboole_0(X0,X2),X1))),
% 2.99/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.99/1.01  
% 2.99/1.01  fof(f14,plain,(
% 2.99/1.01    ! [X0,X1,X2] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 2.99/1.01    inference(ennf_transformation,[],[f3])).
% 2.99/1.01  
% 2.99/1.01  fof(f40,plain,(
% 2.99/1.01    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 2.99/1.01    inference(cnf_transformation,[],[f14])).
% 2.99/1.01  
% 2.99/1.01  fof(f56,plain,(
% 2.99/1.01    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))),
% 2.99/1.01    inference(cnf_transformation,[],[f35])).
% 2.99/1.01  
% 2.99/1.01  fof(f51,plain,(
% 2.99/1.01    ( ! [X4,X0,X1] : (k9_subset_1(u1_struct_0(X0),X1,sK2(X0,X1,X4)) = X4 | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.99/1.01    inference(cnf_transformation,[],[f31])).
% 2.99/1.01  
% 2.99/1.01  fof(f57,plain,(
% 2.99/1.01    v2_tex_2(sK4,sK3)),
% 2.99/1.01    inference(cnf_transformation,[],[f35])).
% 2.99/1.01  
% 2.99/1.01  fof(f47,plain,(
% 2.99/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.99/1.01    inference(cnf_transformation,[],[f26])).
% 2.99/1.01  
% 2.99/1.01  fof(f60,plain,(
% 2.99/1.01    ( ! [X3] : (k1_tarski(sK5) != k9_subset_1(u1_struct_0(sK3),sK4,X3) | ~v3_pre_topc(X3,sK3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3)))) )),
% 2.99/1.01    inference(cnf_transformation,[],[f35])).
% 2.99/1.01  
% 2.99/1.01  fof(f64,plain,(
% 2.99/1.01    ( ! [X3] : (k1_enumset1(sK5,sK5,sK5) != k9_subset_1(u1_struct_0(sK3),sK4,X3) | ~v3_pre_topc(X3,sK3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3)))) )),
% 2.99/1.01    inference(definition_unfolding,[],[f60,f61])).
% 2.99/1.01  
% 2.99/1.01  fof(f2,axiom,(
% 2.99/1.01    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.99/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.99/1.01  
% 2.99/1.01  fof(f13,plain,(
% 2.99/1.01    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.99/1.01    inference(ennf_transformation,[],[f2])).
% 2.99/1.01  
% 2.99/1.01  fof(f21,plain,(
% 2.99/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.99/1.01    inference(nnf_transformation,[],[f13])).
% 2.99/1.01  
% 2.99/1.01  fof(f22,plain,(
% 2.99/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.99/1.01    inference(rectify,[],[f21])).
% 2.99/1.01  
% 2.99/1.01  fof(f23,plain,(
% 2.99/1.01    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.99/1.01    introduced(choice_axiom,[])).
% 2.99/1.01  
% 2.99/1.01  fof(f24,plain,(
% 2.99/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.99/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).
% 2.99/1.01  
% 2.99/1.01  fof(f37,plain,(
% 2.99/1.01    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 2.99/1.01    inference(cnf_transformation,[],[f24])).
% 2.99/1.01  
% 2.99/1.01  cnf(c_6,plain,
% 2.99/1.01      ( ~ r2_hidden(X0,X1) | r1_tarski(k1_enumset1(X0,X0,X0),X1) ),
% 2.99/1.01      inference(cnf_transformation,[],[f62]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_1983,plain,
% 2.99/1.01      ( r2_hidden(X0,X1) != iProver_top
% 2.99/1.01      | r1_tarski(k1_enumset1(X0,X0,X0),X1) = iProver_top ),
% 2.99/1.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_9,plain,
% 2.99/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.99/1.01      inference(cnf_transformation,[],[f48]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_1981,plain,
% 2.99/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 2.99/1.01      | r1_tarski(X0,X1) != iProver_top ),
% 2.99/1.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_15,plain,
% 2.99/1.01      ( v3_pre_topc(sK2(X0,X1,X2),X0)
% 2.99/1.01      | ~ v2_tex_2(X1,X0)
% 2.99/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.99/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 2.99/1.01      | ~ r1_tarski(X2,X1)
% 2.99/1.01      | ~ l1_pre_topc(X0) ),
% 2.99/1.01      inference(cnf_transformation,[],[f50]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_22,negated_conjecture,
% 2.99/1.01      ( l1_pre_topc(sK3) ),
% 2.99/1.01      inference(cnf_transformation,[],[f55]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_380,plain,
% 2.99/1.01      ( v3_pre_topc(sK2(X0,X1,X2),X0)
% 2.99/1.01      | ~ v2_tex_2(X1,X0)
% 2.99/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 2.99/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.99/1.01      | ~ r1_tarski(X2,X1)
% 2.99/1.01      | sK3 != X0 ),
% 2.99/1.01      inference(resolution_lifted,[status(thm)],[c_15,c_22]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_381,plain,
% 2.99/1.01      ( v3_pre_topc(sK2(sK3,X0,X1),sK3)
% 2.99/1.01      | ~ v2_tex_2(X0,sK3)
% 2.99/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.99/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.99/1.01      | ~ r1_tarski(X1,X0) ),
% 2.99/1.01      inference(unflattening,[status(thm)],[c_380]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_1974,plain,
% 2.99/1.01      ( v3_pre_topc(sK2(sK3,X0,X1),sK3) = iProver_top
% 2.99/1.01      | v2_tex_2(X0,sK3) != iProver_top
% 2.99/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.99/1.01      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.99/1.01      | r1_tarski(X1,X0) != iProver_top ),
% 2.99/1.01      inference(predicate_to_equality,[status(thm)],[c_381]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_16,plain,
% 2.99/1.01      ( ~ v2_tex_2(X0,X1)
% 2.99/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.99/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.99/1.01      | m1_subset_1(sK2(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
% 2.99/1.01      | ~ r1_tarski(X2,X0)
% 2.99/1.01      | ~ l1_pre_topc(X1) ),
% 2.99/1.01      inference(cnf_transformation,[],[f49]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_401,plain,
% 2.99/1.01      ( ~ v2_tex_2(X0,X1)
% 2.99/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.99/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.99/1.01      | m1_subset_1(sK2(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
% 2.99/1.01      | ~ r1_tarski(X2,X0)
% 2.99/1.01      | sK3 != X1 ),
% 2.99/1.01      inference(resolution_lifted,[status(thm)],[c_16,c_22]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_402,plain,
% 2.99/1.01      ( ~ v2_tex_2(X0,sK3)
% 2.99/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.99/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.99/1.01      | m1_subset_1(sK2(sK3,X0,X1),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.99/1.01      | ~ r1_tarski(X1,X0) ),
% 2.99/1.01      inference(unflattening,[status(thm)],[c_401]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_1973,plain,
% 2.99/1.01      ( v2_tex_2(X0,sK3) != iProver_top
% 2.99/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.99/1.01      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.99/1.01      | m1_subset_1(sK2(sK3,X0,X1),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 2.99/1.01      | r1_tarski(X1,X0) != iProver_top ),
% 2.99/1.01      inference(predicate_to_equality,[status(thm)],[c_402]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_18,negated_conjecture,
% 2.99/1.01      ( r2_hidden(sK5,sK4) ),
% 2.99/1.01      inference(cnf_transformation,[],[f59]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_1978,plain,
% 2.99/1.01      ( r2_hidden(sK5,sK4) = iProver_top ),
% 2.99/1.01      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_5,plain,
% 2.99/1.01      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 2.99/1.01      inference(cnf_transformation,[],[f41]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_1984,plain,
% 2.99/1.01      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 2.99/1.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_3370,plain,
% 2.99/1.01      ( k3_xboole_0(k1_enumset1(X0,X0,X0),X1) = k1_enumset1(X0,X0,X0)
% 2.99/1.01      | r2_hidden(X0,X1) != iProver_top ),
% 2.99/1.01      inference(superposition,[status(thm)],[c_1983,c_1984]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_5163,plain,
% 2.99/1.01      ( k3_xboole_0(k1_enumset1(sK5,sK5,sK5),sK4) = k1_enumset1(sK5,sK5,sK5) ),
% 2.99/1.01      inference(superposition,[status(thm)],[c_1978,c_3370]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_0,plain,
% 2.99/1.01      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 2.99/1.01      inference(cnf_transformation,[],[f36]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_4,plain,
% 2.99/1.01      ( ~ r1_tarski(X0,X1) | r1_tarski(k3_xboole_0(X0,X2),X1) ),
% 2.99/1.01      inference(cnf_transformation,[],[f40]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_1985,plain,
% 2.99/1.01      ( r1_tarski(X0,X1) != iProver_top
% 2.99/1.01      | r1_tarski(k3_xboole_0(X0,X2),X1) = iProver_top ),
% 2.99/1.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_2675,plain,
% 2.99/1.01      ( r1_tarski(X0,X1) != iProver_top
% 2.99/1.01      | r1_tarski(k3_xboole_0(X2,X0),X1) = iProver_top ),
% 2.99/1.01      inference(superposition,[status(thm)],[c_0,c_1985]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_5178,plain,
% 2.99/1.01      ( r1_tarski(k1_enumset1(sK5,sK5,sK5),X0) = iProver_top
% 2.99/1.01      | r1_tarski(sK4,X0) != iProver_top ),
% 2.99/1.01      inference(superposition,[status(thm)],[c_5163,c_2675]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_21,negated_conjecture,
% 2.99/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.99/1.01      inference(cnf_transformation,[],[f56]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_1975,plain,
% 2.99/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 2.99/1.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_14,plain,
% 2.99/1.01      ( ~ v2_tex_2(X0,X1)
% 2.99/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.99/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.99/1.01      | ~ r1_tarski(X2,X0)
% 2.99/1.01      | ~ l1_pre_topc(X1)
% 2.99/1.01      | k9_subset_1(u1_struct_0(X1),X0,sK2(X1,X0,X2)) = X2 ),
% 2.99/1.01      inference(cnf_transformation,[],[f51]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_422,plain,
% 2.99/1.01      ( ~ v2_tex_2(X0,X1)
% 2.99/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.99/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.99/1.01      | ~ r1_tarski(X2,X0)
% 2.99/1.01      | k9_subset_1(u1_struct_0(X1),X0,sK2(X1,X0,X2)) = X2
% 2.99/1.01      | sK3 != X1 ),
% 2.99/1.01      inference(resolution_lifted,[status(thm)],[c_14,c_22]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_423,plain,
% 2.99/1.01      ( ~ v2_tex_2(X0,sK3)
% 2.99/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.99/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.99/1.01      | ~ r1_tarski(X1,X0)
% 2.99/1.01      | k9_subset_1(u1_struct_0(sK3),X0,sK2(sK3,X0,X1)) = X1 ),
% 2.99/1.01      inference(unflattening,[status(thm)],[c_422]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_1972,plain,
% 2.99/1.01      ( k9_subset_1(u1_struct_0(sK3),X0,sK2(sK3,X0,X1)) = X1
% 2.99/1.01      | v2_tex_2(X0,sK3) != iProver_top
% 2.99/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.99/1.01      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.99/1.01      | r1_tarski(X1,X0) != iProver_top ),
% 2.99/1.01      inference(predicate_to_equality,[status(thm)],[c_423]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_2273,plain,
% 2.99/1.01      ( k9_subset_1(u1_struct_0(sK3),sK4,sK2(sK3,sK4,X0)) = X0
% 2.99/1.01      | v2_tex_2(sK4,sK3) != iProver_top
% 2.99/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.99/1.01      | r1_tarski(X0,sK4) != iProver_top ),
% 2.99/1.01      inference(superposition,[status(thm)],[c_1975,c_1972]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_24,plain,
% 2.99/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 2.99/1.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_20,negated_conjecture,
% 2.99/1.01      ( v2_tex_2(sK4,sK3) ),
% 2.99/1.01      inference(cnf_transformation,[],[f57]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_711,plain,
% 2.99/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.99/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.99/1.01      | ~ r1_tarski(X1,X0)
% 2.99/1.01      | k9_subset_1(u1_struct_0(sK3),X0,sK2(sK3,X0,X1)) = X1
% 2.99/1.01      | sK4 != X0
% 2.99/1.01      | sK3 != sK3 ),
% 2.99/1.01      inference(resolution_lifted,[status(thm)],[c_20,c_423]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_712,plain,
% 2.99/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.99/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.99/1.01      | ~ r1_tarski(X0,sK4)
% 2.99/1.01      | k9_subset_1(u1_struct_0(sK3),sK4,sK2(sK3,sK4,X0)) = X0 ),
% 2.99/1.01      inference(unflattening,[status(thm)],[c_711]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_713,plain,
% 2.99/1.01      ( k9_subset_1(u1_struct_0(sK3),sK4,sK2(sK3,sK4,X0)) = X0
% 2.99/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.99/1.01      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.99/1.01      | r1_tarski(X0,sK4) != iProver_top ),
% 2.99/1.01      inference(predicate_to_equality,[status(thm)],[c_712]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_2433,plain,
% 2.99/1.01      ( k9_subset_1(u1_struct_0(sK3),sK4,sK2(sK3,sK4,X0)) = X0
% 2.99/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.99/1.01      | r1_tarski(X0,sK4) != iProver_top ),
% 2.99/1.01      inference(global_propositional_subsumption,
% 2.99/1.01                [status(thm)],
% 2.99/1.01                [c_2273,c_24,c_713]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_2437,plain,
% 2.99/1.01      ( k9_subset_1(u1_struct_0(sK3),sK4,sK2(sK3,sK4,X0)) = X0
% 2.99/1.01      | r1_tarski(X0,u1_struct_0(sK3)) != iProver_top
% 2.99/1.01      | r1_tarski(X0,sK4) != iProver_top ),
% 2.99/1.01      inference(superposition,[status(thm)],[c_1981,c_2433]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_3373,plain,
% 2.99/1.01      ( k9_subset_1(u1_struct_0(sK3),sK4,sK2(sK3,sK4,k1_enumset1(X0,X0,X0))) = k1_enumset1(X0,X0,X0)
% 2.99/1.01      | r2_hidden(X0,u1_struct_0(sK3)) != iProver_top
% 2.99/1.01      | r1_tarski(k1_enumset1(X0,X0,X0),sK4) != iProver_top ),
% 2.99/1.01      inference(superposition,[status(thm)],[c_1983,c_2437]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_7612,plain,
% 2.99/1.01      ( k9_subset_1(u1_struct_0(sK3),sK4,sK2(sK3,sK4,k1_enumset1(sK5,sK5,sK5))) = k1_enumset1(sK5,sK5,sK5)
% 2.99/1.01      | r2_hidden(sK5,u1_struct_0(sK3)) != iProver_top
% 2.99/1.01      | r1_tarski(sK4,sK4) != iProver_top ),
% 2.99/1.01      inference(superposition,[status(thm)],[c_5178,c_3373]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_27,plain,
% 2.99/1.01      ( r2_hidden(sK5,sK4) = iProver_top ),
% 2.99/1.01      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_10,plain,
% 2.99/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.99/1.01      inference(cnf_transformation,[],[f47]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_1980,plain,
% 2.99/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.99/1.01      | r1_tarski(X0,X1) = iProver_top ),
% 2.99/1.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_2366,plain,
% 2.99/1.01      ( r1_tarski(sK4,u1_struct_0(sK3)) = iProver_top ),
% 2.99/1.01      inference(superposition,[status(thm)],[c_1975,c_1980]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_2203,plain,
% 2.99/1.01      ( ~ r2_hidden(X0,sK4) | r1_tarski(k1_enumset1(X0,X0,X0),sK4) ),
% 2.99/1.01      inference(instantiation,[status(thm)],[c_6]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_3938,plain,
% 2.99/1.01      ( ~ r2_hidden(sK5,sK4) | r1_tarski(k1_enumset1(sK5,sK5,sK5),sK4) ),
% 2.99/1.01      inference(instantiation,[status(thm)],[c_2203]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_3939,plain,
% 2.99/1.01      ( r2_hidden(sK5,sK4) != iProver_top
% 2.99/1.01      | r1_tarski(k1_enumset1(sK5,sK5,sK5),sK4) = iProver_top ),
% 2.99/1.01      inference(predicate_to_equality,[status(thm)],[c_3938]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_2679,plain,
% 2.99/1.01      ( k9_subset_1(u1_struct_0(sK3),sK4,sK2(sK3,sK4,k3_xboole_0(X0,X1))) = k3_xboole_0(X0,X1)
% 2.99/1.01      | r1_tarski(X0,u1_struct_0(sK3)) != iProver_top
% 2.99/1.01      | r1_tarski(k3_xboole_0(X0,X1),sK4) != iProver_top ),
% 2.99/1.01      inference(superposition,[status(thm)],[c_1985,c_2437]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_4936,plain,
% 2.99/1.01      ( k9_subset_1(u1_struct_0(sK3),sK4,sK2(sK3,sK4,k3_xboole_0(X0,X1))) = k3_xboole_0(X0,X1)
% 2.99/1.01      | r1_tarski(X0,u1_struct_0(sK3)) != iProver_top
% 2.99/1.01      | r1_tarski(k3_xboole_0(X1,X0),sK4) != iProver_top ),
% 2.99/1.01      inference(superposition,[status(thm)],[c_0,c_2679]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_5173,plain,
% 2.99/1.01      ( k9_subset_1(u1_struct_0(sK3),sK4,sK2(sK3,sK4,k3_xboole_0(sK4,k1_enumset1(sK5,sK5,sK5)))) = k3_xboole_0(sK4,k1_enumset1(sK5,sK5,sK5))
% 2.99/1.01      | r1_tarski(k1_enumset1(sK5,sK5,sK5),sK4) != iProver_top
% 2.99/1.01      | r1_tarski(sK4,u1_struct_0(sK3)) != iProver_top ),
% 2.99/1.01      inference(superposition,[status(thm)],[c_5163,c_4936]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_5176,plain,
% 2.99/1.01      ( k3_xboole_0(sK4,k1_enumset1(sK5,sK5,sK5)) = k1_enumset1(sK5,sK5,sK5) ),
% 2.99/1.01      inference(superposition,[status(thm)],[c_5163,c_0]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_5181,plain,
% 2.99/1.01      ( k9_subset_1(u1_struct_0(sK3),sK4,sK2(sK3,sK4,k1_enumset1(sK5,sK5,sK5))) = k1_enumset1(sK5,sK5,sK5)
% 2.99/1.01      | r1_tarski(k1_enumset1(sK5,sK5,sK5),sK4) != iProver_top
% 2.99/1.01      | r1_tarski(sK4,u1_struct_0(sK3)) != iProver_top ),
% 2.99/1.01      inference(demodulation,[status(thm)],[c_5173,c_5176]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_7618,plain,
% 2.99/1.01      ( k9_subset_1(u1_struct_0(sK3),sK4,sK2(sK3,sK4,k1_enumset1(sK5,sK5,sK5))) = k1_enumset1(sK5,sK5,sK5) ),
% 2.99/1.01      inference(global_propositional_subsumption,
% 2.99/1.01                [status(thm)],
% 2.99/1.01                [c_7612,c_27,c_2366,c_3939,c_5181]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_17,negated_conjecture,
% 2.99/1.01      ( ~ v3_pre_topc(X0,sK3)
% 2.99/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.99/1.01      | k1_enumset1(sK5,sK5,sK5) != k9_subset_1(u1_struct_0(sK3),sK4,X0) ),
% 2.99/1.01      inference(cnf_transformation,[],[f64]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_1979,plain,
% 2.99/1.01      ( k1_enumset1(sK5,sK5,sK5) != k9_subset_1(u1_struct_0(sK3),sK4,X0)
% 2.99/1.01      | v3_pre_topc(X0,sK3) != iProver_top
% 2.99/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.99/1.01      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_7620,plain,
% 2.99/1.01      ( v3_pre_topc(sK2(sK3,sK4,k1_enumset1(sK5,sK5,sK5)),sK3) != iProver_top
% 2.99/1.01      | m1_subset_1(sK2(sK3,sK4,k1_enumset1(sK5,sK5,sK5)),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.99/1.01      inference(superposition,[status(thm)],[c_7618,c_1979]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_8145,plain,
% 2.99/1.01      ( v3_pre_topc(sK2(sK3,sK4,k1_enumset1(sK5,sK5,sK5)),sK3) != iProver_top
% 2.99/1.01      | v2_tex_2(sK4,sK3) != iProver_top
% 2.99/1.01      | m1_subset_1(k1_enumset1(sK5,sK5,sK5),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.99/1.01      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.99/1.01      | r1_tarski(k1_enumset1(sK5,sK5,sK5),sK4) != iProver_top ),
% 2.99/1.01      inference(superposition,[status(thm)],[c_1973,c_7620]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_25,plain,
% 2.99/1.01      ( v2_tex_2(sK4,sK3) = iProver_top ),
% 2.99/1.01      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_9398,plain,
% 2.99/1.01      ( v3_pre_topc(sK2(sK3,sK4,k1_enumset1(sK5,sK5,sK5)),sK3) != iProver_top
% 2.99/1.01      | m1_subset_1(k1_enumset1(sK5,sK5,sK5),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.99/1.01      inference(global_propositional_subsumption,
% 2.99/1.01                [status(thm)],
% 2.99/1.01                [c_8145,c_24,c_25,c_27,c_3939]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_9402,plain,
% 2.99/1.01      ( v2_tex_2(sK4,sK3) != iProver_top
% 2.99/1.01      | m1_subset_1(k1_enumset1(sK5,sK5,sK5),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.99/1.01      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.99/1.01      | r1_tarski(k1_enumset1(sK5,sK5,sK5),sK4) != iProver_top ),
% 2.99/1.01      inference(superposition,[status(thm)],[c_1974,c_9398]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_10066,plain,
% 2.99/1.01      ( m1_subset_1(k1_enumset1(sK5,sK5,sK5),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.99/1.01      inference(global_propositional_subsumption,
% 2.99/1.01                [status(thm)],
% 2.99/1.01                [c_9402,c_24,c_25,c_27,c_3939]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_10070,plain,
% 2.99/1.01      ( r1_tarski(k1_enumset1(sK5,sK5,sK5),u1_struct_0(sK3)) != iProver_top ),
% 2.99/1.01      inference(superposition,[status(thm)],[c_1981,c_10066]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_10519,plain,
% 2.99/1.01      ( r2_hidden(sK5,u1_struct_0(sK3)) != iProver_top ),
% 2.99/1.01      inference(superposition,[status(thm)],[c_1983,c_10070]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_3,plain,
% 2.99/1.01      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 2.99/1.01      inference(cnf_transformation,[],[f37]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_1986,plain,
% 2.99/1.01      ( r2_hidden(X0,X1) != iProver_top
% 2.99/1.01      | r2_hidden(X0,X2) = iProver_top
% 2.99/1.01      | r1_tarski(X1,X2) != iProver_top ),
% 2.99/1.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_3385,plain,
% 2.99/1.01      ( r2_hidden(sK5,X0) = iProver_top
% 2.99/1.01      | r1_tarski(sK4,X0) != iProver_top ),
% 2.99/1.01      inference(superposition,[status(thm)],[c_1978,c_1986]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_3597,plain,
% 2.99/1.01      ( r2_hidden(sK5,u1_struct_0(sK3)) = iProver_top ),
% 2.99/1.01      inference(superposition,[status(thm)],[c_2366,c_3385]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(contradiction,plain,
% 2.99/1.01      ( $false ),
% 2.99/1.01      inference(minisat,[status(thm)],[c_10519,c_3597]) ).
% 2.99/1.01  
% 2.99/1.01  
% 2.99/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.99/1.01  
% 2.99/1.01  ------                               Statistics
% 2.99/1.01  
% 2.99/1.01  ------ General
% 2.99/1.01  
% 2.99/1.01  abstr_ref_over_cycles:                  0
% 2.99/1.01  abstr_ref_under_cycles:                 0
% 2.99/1.01  gc_basic_clause_elim:                   0
% 2.99/1.01  forced_gc_time:                         0
% 2.99/1.01  parsing_time:                           0.01
% 2.99/1.01  unif_index_cands_time:                  0.
% 2.99/1.01  unif_index_add_time:                    0.
% 2.99/1.01  orderings_time:                         0.
% 2.99/1.01  out_proof_time:                         0.013
% 2.99/1.01  total_time:                             0.469
% 2.99/1.01  num_of_symbols:                         48
% 2.99/1.01  num_of_terms:                           11646
% 2.99/1.01  
% 2.99/1.01  ------ Preprocessing
% 2.99/1.01  
% 2.99/1.01  num_of_splits:                          0
% 2.99/1.01  num_of_split_atoms:                     0
% 2.99/1.01  num_of_reused_defs:                     0
% 2.99/1.01  num_eq_ax_congr_red:                    26
% 2.99/1.01  num_of_sem_filtered_clauses:            1
% 2.99/1.01  num_of_subtypes:                        0
% 2.99/1.01  monotx_restored_types:                  0
% 2.99/1.01  sat_num_of_epr_types:                   0
% 2.99/1.01  sat_num_of_non_cyclic_types:            0
% 2.99/1.01  sat_guarded_non_collapsed_types:        0
% 2.99/1.01  num_pure_diseq_elim:                    0
% 2.99/1.01  simp_replaced_by:                       0
% 2.99/1.01  res_preprocessed:                       112
% 2.99/1.01  prep_upred:                             0
% 2.99/1.01  prep_unflattend:                        26
% 2.99/1.01  smt_new_axioms:                         0
% 2.99/1.01  pred_elim_cands:                        5
% 2.99/1.01  pred_elim:                              1
% 2.99/1.01  pred_elim_cl:                           1
% 2.99/1.01  pred_elim_cycles:                       6
% 2.99/1.01  merged_defs:                            16
% 2.99/1.01  merged_defs_ncl:                        0
% 2.99/1.01  bin_hyper_res:                          17
% 2.99/1.01  prep_cycles:                            4
% 2.99/1.01  pred_elim_time:                         0.022
% 2.99/1.01  splitting_time:                         0.
% 2.99/1.01  sem_filter_time:                        0.
% 2.99/1.01  monotx_time:                            0.
% 2.99/1.01  subtype_inf_time:                       0.
% 2.99/1.01  
% 2.99/1.01  ------ Problem properties
% 2.99/1.01  
% 2.99/1.01  clauses:                                21
% 2.99/1.01  conjectures:                            5
% 2.99/1.01  epr:                                    3
% 2.99/1.01  horn:                                   18
% 2.99/1.01  ground:                                 4
% 2.99/1.01  unary:                                  5
% 2.99/1.01  binary:                                 8
% 2.99/1.01  lits:                                   53
% 2.99/1.01  lits_eq:                                5
% 2.99/1.01  fd_pure:                                0
% 2.99/1.01  fd_pseudo:                              0
% 2.99/1.01  fd_cond:                                0
% 2.99/1.01  fd_pseudo_cond:                         0
% 2.99/1.01  ac_symbols:                             0
% 2.99/1.01  
% 2.99/1.01  ------ Propositional Solver
% 2.99/1.01  
% 2.99/1.01  prop_solver_calls:                      31
% 2.99/1.01  prop_fast_solver_calls:                 1264
% 2.99/1.01  smt_solver_calls:                       0
% 2.99/1.01  smt_fast_solver_calls:                  0
% 2.99/1.01  prop_num_of_clauses:                    4454
% 2.99/1.01  prop_preprocess_simplified:             9786
% 2.99/1.01  prop_fo_subsumed:                       31
% 2.99/1.01  prop_solver_time:                       0.
% 2.99/1.01  smt_solver_time:                        0.
% 2.99/1.01  smt_fast_solver_time:                   0.
% 2.99/1.01  prop_fast_solver_time:                  0.
% 2.99/1.01  prop_unsat_core_time:                   0.
% 2.99/1.01  
% 2.99/1.01  ------ QBF
% 2.99/1.01  
% 2.99/1.01  qbf_q_res:                              0
% 2.99/1.01  qbf_num_tautologies:                    0
% 2.99/1.01  qbf_prep_cycles:                        0
% 2.99/1.01  
% 2.99/1.01  ------ BMC1
% 2.99/1.01  
% 2.99/1.01  bmc1_current_bound:                     -1
% 2.99/1.01  bmc1_last_solved_bound:                 -1
% 2.99/1.01  bmc1_unsat_core_size:                   -1
% 2.99/1.01  bmc1_unsat_core_parents_size:           -1
% 2.99/1.01  bmc1_merge_next_fun:                    0
% 2.99/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.99/1.01  
% 2.99/1.01  ------ Instantiation
% 2.99/1.01  
% 2.99/1.01  inst_num_of_clauses:                    1166
% 2.99/1.01  inst_num_in_passive:                    363
% 2.99/1.01  inst_num_in_active:                     488
% 2.99/1.01  inst_num_in_unprocessed:                318
% 2.99/1.01  inst_num_of_loops:                      630
% 2.99/1.01  inst_num_of_learning_restarts:          0
% 2.99/1.01  inst_num_moves_active_passive:          135
% 2.99/1.01  inst_lit_activity:                      0
% 2.99/1.01  inst_lit_activity_moves:                0
% 2.99/1.01  inst_num_tautologies:                   0
% 2.99/1.01  inst_num_prop_implied:                  0
% 2.99/1.01  inst_num_existing_simplified:           0
% 2.99/1.01  inst_num_eq_res_simplified:             0
% 2.99/1.01  inst_num_child_elim:                    0
% 2.99/1.01  inst_num_of_dismatching_blockings:      656
% 2.99/1.01  inst_num_of_non_proper_insts:           1502
% 2.99/1.01  inst_num_of_duplicates:                 0
% 2.99/1.01  inst_inst_num_from_inst_to_res:         0
% 2.99/1.01  inst_dismatching_checking_time:         0.
% 2.99/1.01  
% 2.99/1.01  ------ Resolution
% 2.99/1.01  
% 2.99/1.01  res_num_of_clauses:                     0
% 2.99/1.01  res_num_in_passive:                     0
% 2.99/1.01  res_num_in_active:                      0
% 2.99/1.01  res_num_of_loops:                       116
% 2.99/1.01  res_forward_subset_subsumed:            56
% 2.99/1.01  res_backward_subset_subsumed:           10
% 2.99/1.01  res_forward_subsumed:                   0
% 2.99/1.01  res_backward_subsumed:                  0
% 2.99/1.01  res_forward_subsumption_resolution:     2
% 2.99/1.01  res_backward_subsumption_resolution:    0
% 2.99/1.01  res_clause_to_clause_subsumption:       1867
% 2.99/1.01  res_orphan_elimination:                 0
% 2.99/1.01  res_tautology_del:                      124
% 2.99/1.01  res_num_eq_res_simplified:              0
% 2.99/1.01  res_num_sel_changes:                    0
% 2.99/1.01  res_moves_from_active_to_pass:          0
% 2.99/1.01  
% 2.99/1.01  ------ Superposition
% 2.99/1.01  
% 2.99/1.01  sup_time_total:                         0.
% 2.99/1.01  sup_time_generating:                    0.
% 2.99/1.01  sup_time_sim_full:                      0.
% 2.99/1.01  sup_time_sim_immed:                     0.
% 2.99/1.01  
% 2.99/1.01  sup_num_of_clauses:                     267
% 2.99/1.01  sup_num_in_active:                      125
% 2.99/1.01  sup_num_in_passive:                     142
% 2.99/1.01  sup_num_of_loops:                       125
% 2.99/1.01  sup_fw_superposition:                   360
% 2.99/1.01  sup_bw_superposition:                   344
% 2.99/1.01  sup_immediate_simplified:               147
% 2.99/1.01  sup_given_eliminated:                   0
% 2.99/1.01  comparisons_done:                       0
% 2.99/1.01  comparisons_avoided:                    0
% 2.99/1.01  
% 2.99/1.01  ------ Simplifications
% 2.99/1.01  
% 2.99/1.01  
% 2.99/1.01  sim_fw_subset_subsumed:                 7
% 2.99/1.01  sim_bw_subset_subsumed:                 2
% 2.99/1.01  sim_fw_subsumed:                        30
% 2.99/1.01  sim_bw_subsumed:                        1
% 2.99/1.01  sim_fw_subsumption_res:                 0
% 2.99/1.01  sim_bw_subsumption_res:                 0
% 2.99/1.01  sim_tautology_del:                      32
% 2.99/1.01  sim_eq_tautology_del:                   10
% 2.99/1.01  sim_eq_res_simp:                        0
% 2.99/1.01  sim_fw_demodulated:                     85
% 2.99/1.01  sim_bw_demodulated:                     0
% 2.99/1.01  sim_light_normalised:                   29
% 2.99/1.01  sim_joinable_taut:                      0
% 2.99/1.01  sim_joinable_simp:                      0
% 2.99/1.01  sim_ac_normalised:                      0
% 2.99/1.01  sim_smt_subsumption:                    0
% 2.99/1.01  
%------------------------------------------------------------------------------
