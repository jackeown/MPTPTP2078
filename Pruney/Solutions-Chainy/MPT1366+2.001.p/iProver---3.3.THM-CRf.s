%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:18:04 EST 2020

% Result     : Theorem 1.17s
% Output     : CNFRefutation 1.17s
% Verified   : 
% Statistics : Number of formulae       :  146 (1157 expanded)
%              Number of clauses        :   95 ( 296 expanded)
%              Number of leaves         :   15 ( 302 expanded)
%              Depth                    :   29
%              Number of atoms          :  961 (8261 expanded)
%              Number of equality atoms :  130 ( 375 expanded)
%              Maximal formula depth    :   21 (   7 average)
%              Maximal clause size      :   26 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v8_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_compts_1(X1,X0)
             => ( ! [X2] :
                    ( m1_subset_1(X2,u1_struct_0(X0))
                   => ~ ( ! [X3] :
                            ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                           => ! [X4] :
                                ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                               => ~ ( r1_xboole_0(X3,X4)
                                    & r1_tarski(X1,X4)
                                    & r2_hidden(X2,X3)
                                    & v3_pre_topc(X4,X0)
                                    & v3_pre_topc(X3,X0) ) ) )
                        & r2_hidden(X2,k3_subset_1(u1_struct_0(X0),X1)) ) )
                | k1_xboole_0 = X1 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( r1_xboole_0(X3,X4)
                      & r1_tarski(X1,X4)
                      & r2_hidden(X2,X3)
                      & v3_pre_topc(X4,X0)
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X2,k3_subset_1(u1_struct_0(X0),X1))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | k1_xboole_0 = X1
          | ~ v2_compts_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ v8_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( r1_xboole_0(X3,X4)
                      & r1_tarski(X1,X4)
                      & r2_hidden(X2,X3)
                      & v3_pre_topc(X4,X0)
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X2,k3_subset_1(u1_struct_0(X0),X1))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | k1_xboole_0 = X1
          | ~ v2_compts_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ v8_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f8])).

fof(f26,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( r1_xboole_0(X3,X4)
          & r1_tarski(X1,X4)
          & r2_hidden(X2,X3)
          & v3_pre_topc(X4,X0)
          & v3_pre_topc(X3,X0)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r1_xboole_0(X3,sK7(X0,X1,X2))
        & r1_tarski(X1,sK7(X0,X1,X2))
        & r2_hidden(X2,X3)
        & v3_pre_topc(sK7(X0,X1,X2),X0)
        & v3_pre_topc(X3,X0)
        & m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ? [X4] :
              ( r1_xboole_0(X3,X4)
              & r1_tarski(X1,X4)
              & r2_hidden(X2,X3)
              & v3_pre_topc(X4,X0)
              & v3_pre_topc(X3,X0)
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X4] :
            ( r1_xboole_0(sK6(X0,X1,X2),X4)
            & r1_tarski(X1,X4)
            & r2_hidden(X2,sK6(X0,X1,X2))
            & v3_pre_topc(X4,X0)
            & v3_pre_topc(sK6(X0,X1,X2),X0)
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_xboole_0(sK6(X0,X1,X2),sK7(X0,X1,X2))
                & r1_tarski(X1,sK7(X0,X1,X2))
                & r2_hidden(X2,sK6(X0,X1,X2))
                & v3_pre_topc(sK7(X0,X1,X2),X0)
                & v3_pre_topc(sK6(X0,X1,X2),X0)
                & m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
                & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X2,k3_subset_1(u1_struct_0(X0),X1))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | k1_xboole_0 = X1
          | ~ v2_compts_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ v8_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f9,f26,f25])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,sK7(X0,X1,X2))
      | ~ r2_hidden(X2,k3_subset_1(u1_struct_0(X0),X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k1_xboole_0 = X1
      | ~ v2_compts_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v8_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f4,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( ( v1_compts_1(X0)
          & v8_pre_topc(X0) )
       => v9_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ( ( v1_compts_1(X0)
            & v8_pre_topc(X0) )
         => v9_pre_topc(X0) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f12,plain,(
    ? [X0] :
      ( ~ v9_pre_topc(X0)
      & v1_compts_1(X0)
      & v8_pre_topc(X0)
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f13,plain,(
    ? [X0] :
      ( ~ v9_pre_topc(X0)
      & v1_compts_1(X0)
      & v8_pre_topc(X0)
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f28,plain,
    ( ? [X0] :
        ( ~ v9_pre_topc(X0)
        & v1_compts_1(X0)
        & v8_pre_topc(X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ~ v9_pre_topc(sK8)
      & v1_compts_1(sK8)
      & v8_pre_topc(sK8)
      & l1_pre_topc(sK8)
      & v2_pre_topc(sK8)
      & ~ v2_struct_0(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ~ v9_pre_topc(sK8)
    & v1_compts_1(sK8)
    & v8_pre_topc(sK8)
    & l1_pre_topc(sK8)
    & v2_pre_topc(sK8)
    & ~ v2_struct_0(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f13,f28])).

fof(f56,plain,(
    l1_pre_topc(sK8) ),
    inference(cnf_transformation,[],[f29])).

fof(f55,plain,(
    v2_pre_topc(sK8) ),
    inference(cnf_transformation,[],[f29])).

fof(f57,plain,(
    v8_pre_topc(sK8) ),
    inference(cnf_transformation,[],[f29])).

fof(f14,plain,(
    ! [X0] :
      ( sP0(X0)
    <=> ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( r1_xboole_0(X3,X4)
                      & r1_tarski(X2,X4)
                      & r2_hidden(X1,X3)
                      & v3_pre_topc(X4,X0)
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X1,k3_subset_1(u1_struct_0(X0),X2))
              | ~ v4_pre_topc(X2,X0)
              | k1_xboole_0 = X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f18,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1] :
            ( ? [X2] :
                ( ! [X3] :
                    ( ! [X4] :
                        ( ~ r1_xboole_0(X3,X4)
                        | ~ r1_tarski(X2,X4)
                        | ~ r2_hidden(X1,X3)
                        | ~ v3_pre_topc(X4,X0)
                        | ~ v3_pre_topc(X3,X0)
                        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & r2_hidden(X1,k3_subset_1(u1_struct_0(X0),X2))
                & v4_pre_topc(X2,X0)
                & k1_xboole_0 != X2
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,u1_struct_0(X0)) ) )
      & ( ! [X1] :
            ( ! [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( r1_xboole_0(X3,X4)
                        & r1_tarski(X2,X4)
                        & r2_hidden(X1,X3)
                        & v3_pre_topc(X4,X0)
                        & v3_pre_topc(X3,X0)
                        & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X1,k3_subset_1(u1_struct_0(X0),X2))
                | ~ v4_pre_topc(X2,X0)
                | k1_xboole_0 = X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) )
        | ~ sP0(X0) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f19,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1] :
            ( ? [X2] :
                ( ! [X3] :
                    ( ! [X4] :
                        ( ~ r1_xboole_0(X3,X4)
                        | ~ r1_tarski(X2,X4)
                        | ~ r2_hidden(X1,X3)
                        | ~ v3_pre_topc(X4,X0)
                        | ~ v3_pre_topc(X3,X0)
                        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & r2_hidden(X1,k3_subset_1(u1_struct_0(X0),X2))
                & v4_pre_topc(X2,X0)
                & k1_xboole_0 != X2
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,u1_struct_0(X0)) ) )
      & ( ! [X5] :
            ( ! [X6] :
                ( ? [X7] :
                    ( ? [X8] :
                        ( r1_xboole_0(X7,X8)
                        & r1_tarski(X6,X8)
                        & r2_hidden(X5,X7)
                        & v3_pre_topc(X8,X0)
                        & v3_pre_topc(X7,X0)
                        & m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X0))) )
                    & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X5,k3_subset_1(u1_struct_0(X0),X6))
                | ~ v4_pre_topc(X6,X0)
                | k1_xboole_0 = X6
                | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
        | ~ sP0(X0) ) ) ),
    inference(rectify,[],[f18])).

fof(f23,plain,(
    ! [X7,X6,X5,X0] :
      ( ? [X8] :
          ( r1_xboole_0(X7,X8)
          & r1_tarski(X6,X8)
          & r2_hidden(X5,X7)
          & v3_pre_topc(X8,X0)
          & v3_pre_topc(X7,X0)
          & m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r1_xboole_0(X7,sK5(X0,X5,X6))
        & r1_tarski(X6,sK5(X0,X5,X6))
        & r2_hidden(X5,X7)
        & v3_pre_topc(sK5(X0,X5,X6),X0)
        & v3_pre_topc(X7,X0)
        & m1_subset_1(sK5(X0,X5,X6),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X6,X5,X0] :
      ( ? [X7] :
          ( ? [X8] :
              ( r1_xboole_0(X7,X8)
              & r1_tarski(X6,X8)
              & r2_hidden(X5,X7)
              & v3_pre_topc(X8,X0)
              & v3_pre_topc(X7,X0)
              & m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X8] :
            ( r1_xboole_0(sK4(X0,X5,X6),X8)
            & r1_tarski(X6,X8)
            & r2_hidden(X5,sK4(X0,X5,X6))
            & v3_pre_topc(X8,X0)
            & v3_pre_topc(sK4(X0,X5,X6),X0)
            & m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK4(X0,X5,X6),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( ! [X4] :
                  ( ~ r1_xboole_0(X3,X4)
                  | ~ r1_tarski(X2,X4)
                  | ~ r2_hidden(X1,X3)
                  | ~ v3_pre_topc(X4,X0)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & r2_hidden(X1,k3_subset_1(u1_struct_0(X0),X2))
          & v4_pre_topc(X2,X0)
          & k1_xboole_0 != X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ! [X3] :
            ( ! [X4] :
                ( ~ r1_xboole_0(X3,X4)
                | ~ r1_tarski(sK3(X0),X4)
                | ~ r2_hidden(X1,X3)
                | ~ v3_pre_topc(X4,X0)
                | ~ v3_pre_topc(X3,X0)
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & r2_hidden(X1,k3_subset_1(u1_struct_0(X0),sK3(X0)))
        & v4_pre_topc(sK3(X0),X0)
        & k1_xboole_0 != sK3(X0)
        & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ~ r1_xboole_0(X3,X4)
                      | ~ r1_tarski(X2,X4)
                      | ~ r2_hidden(X1,X3)
                      | ~ v3_pre_topc(X4,X0)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & r2_hidden(X1,k3_subset_1(u1_struct_0(X0),X2))
              & v4_pre_topc(X2,X0)
              & k1_xboole_0 != X2
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ! [X3] :
                ( ! [X4] :
                    ( ~ r1_xboole_0(X3,X4)
                    | ~ r1_tarski(X2,X4)
                    | ~ r2_hidden(sK2(X0),X3)
                    | ~ v3_pre_topc(X4,X0)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            & r2_hidden(sK2(X0),k3_subset_1(u1_struct_0(X0),X2))
            & v4_pre_topc(X2,X0)
            & k1_xboole_0 != X2
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK2(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ( ! [X3] :
              ( ! [X4] :
                  ( ~ r1_xboole_0(X3,X4)
                  | ~ r1_tarski(sK3(X0),X4)
                  | ~ r2_hidden(sK2(X0),X3)
                  | ~ v3_pre_topc(X4,X0)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & r2_hidden(sK2(X0),k3_subset_1(u1_struct_0(X0),sK3(X0)))
          & v4_pre_topc(sK3(X0),X0)
          & k1_xboole_0 != sK3(X0)
          & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))
          & m1_subset_1(sK2(X0),u1_struct_0(X0)) ) )
      & ( ! [X5] :
            ( ! [X6] :
                ( ( r1_xboole_0(sK4(X0,X5,X6),sK5(X0,X5,X6))
                  & r1_tarski(X6,sK5(X0,X5,X6))
                  & r2_hidden(X5,sK4(X0,X5,X6))
                  & v3_pre_topc(sK5(X0,X5,X6),X0)
                  & v3_pre_topc(sK4(X0,X5,X6),X0)
                  & m1_subset_1(sK5(X0,X5,X6),k1_zfmisc_1(u1_struct_0(X0)))
                  & m1_subset_1(sK4(X0,X5,X6),k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X5,k3_subset_1(u1_struct_0(X0),X6))
                | ~ v4_pre_topc(X6,X0)
                | k1_xboole_0 = X6
                | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
        | ~ sP0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f19,f23,f22,f21,f20])).

fof(f44,plain,(
    ! [X4,X0,X3] :
      ( sP0(X0)
      | ~ r1_xboole_0(X3,X4)
      | ~ r1_tarski(sK3(X0),X4)
      | ~ r2_hidden(sK2(X0),X3)
      | ~ v3_pre_topc(X4,X0)
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f15,plain,(
    ! [X0] :
      ( ( v9_pre_topc(X0)
      <=> sP0(X0) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f17,plain,(
    ! [X0] :
      ( ( ( v9_pre_topc(X0)
          | ~ sP0(X0) )
        & ( sP0(X0)
          | ~ v9_pre_topc(X0) ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f31,plain,(
    ! [X0] :
      ( v9_pre_topc(X0)
      | ~ sP0(X0)
      | ~ sP1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v9_pre_topc(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ! [X4] :
                            ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                           => ~ ( r1_xboole_0(X3,X4)
                                & r1_tarski(X2,X4)
                                & r2_hidden(X1,X3)
                                & v3_pre_topc(X4,X0)
                                & v3_pre_topc(X3,X0) ) ) )
                    & r2_hidden(X1,k3_subset_1(u1_struct_0(X0),X2))
                    & v4_pre_topc(X2,X0)
                    & k1_xboole_0 != X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0] :
      ( ( v9_pre_topc(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( r1_xboole_0(X3,X4)
                        & r1_tarski(X2,X4)
                        & r2_hidden(X1,X3)
                        & v3_pre_topc(X4,X0)
                        & v3_pre_topc(X3,X0)
                        & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X1,k3_subset_1(u1_struct_0(X0),X2))
                | ~ v4_pre_topc(X2,X0)
                | k1_xboole_0 = X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f7,plain,(
    ! [X0] :
      ( ( v9_pre_topc(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( r1_xboole_0(X3,X4)
                        & r1_tarski(X2,X4)
                        & r2_hidden(X1,X3)
                        & v3_pre_topc(X4,X0)
                        & v3_pre_topc(X3,X0)
                        & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X1,k3_subset_1(u1_struct_0(X0),X2))
                | ~ v4_pre_topc(X2,X0)
                | k1_xboole_0 = X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f6])).

fof(f16,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f7,f15,f14])).

fof(f45,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f54,plain,(
    ~ v2_struct_0(sK8) ),
    inference(cnf_transformation,[],[f29])).

fof(f59,plain,(
    ~ v9_pre_topc(sK8) ),
    inference(cnf_transformation,[],[f29])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(sK6(X0,X1,X2),sK7(X0,X1,X2))
      | ~ r2_hidden(X2,k3_subset_1(u1_struct_0(X0),X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k1_xboole_0 = X1
      | ~ v2_compts_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v8_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X2,k3_subset_1(u1_struct_0(X0),X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k1_xboole_0 = X1
      | ~ v2_compts_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v8_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X2,k3_subset_1(u1_struct_0(X0),X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k1_xboole_0 = X1
      | ~ v2_compts_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v8_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(sK6(X0,X1,X2),X0)
      | ~ r2_hidden(X2,k3_subset_1(u1_struct_0(X0),X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k1_xboole_0 = X1
      | ~ v2_compts_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v8_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(sK7(X0,X1,X2),X0)
      | ~ r2_hidden(X2,k3_subset_1(u1_struct_0(X0),X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k1_xboole_0 = X1
      | ~ v2_compts_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v8_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f42,plain,(
    ! [X0] :
      ( sP0(X0)
      | v4_pre_topc(sK3(X0),X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v4_pre_topc(X1,X0)
              & v1_compts_1(X0) )
           => v2_compts_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_compts_1(X1,X0)
          | ~ v4_pre_topc(X1,X0)
          | ~ v1_compts_1(X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_compts_1(X1,X0)
          | ~ v4_pre_topc(X1,X0)
          | ~ v1_compts_1(X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v2_compts_1(X1,X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ v1_compts_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f58,plain,(
    v1_compts_1(sK8) ),
    inference(cnf_transformation,[],[f29])).

fof(f40,plain,(
    ! [X0] :
      ( sP0(X0)
      | m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f41,plain,(
    ! [X0] :
      ( sP0(X0)
      | k1_xboole_0 != sK3(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,sK6(X0,X1,X2))
      | ~ r2_hidden(X2,k3_subset_1(u1_struct_0(X0),X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k1_xboole_0 = X1
      | ~ v2_compts_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v8_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f43,plain,(
    ! [X0] :
      ( sP0(X0)
      | r2_hidden(sK2(X0),k3_subset_1(u1_struct_0(X0),sK3(X0))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f39,plain,(
    ! [X0] :
      ( sP0(X0)
      | m1_subset_1(sK2(X0),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_1322,plain,
    ( X0_54 = X0_54 ),
    theory(equality)).

cnf(c_1626,plain,
    ( sK7(sK8,sK3(sK8),sK2(sK8)) = sK7(sK8,sK3(sK8),sK2(sK8)) ),
    inference(instantiation,[status(thm)],[c_1322])).

cnf(c_17,plain,
    ( ~ v2_compts_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,k3_subset_1(u1_struct_0(X1),X0))
    | r1_tarski(X0,sK7(X1,X0,X2))
    | ~ v8_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_27,negated_conjecture,
    ( l1_pre_topc(sK8) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_928,plain,
    ( ~ v2_compts_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,k3_subset_1(u1_struct_0(X1),X0))
    | r1_tarski(X0,sK7(X1,X0,X2))
    | ~ v8_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | sK8 != X1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_27])).

cnf(c_929,plain,
    ( ~ v2_compts_1(X0,sK8)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ r2_hidden(X1,k3_subset_1(u1_struct_0(sK8),X0))
    | r1_tarski(X0,sK7(sK8,X0,X1))
    | ~ v8_pre_topc(sK8)
    | ~ v2_pre_topc(sK8)
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_928])).

cnf(c_28,negated_conjecture,
    ( v2_pre_topc(sK8) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_26,negated_conjecture,
    ( v8_pre_topc(sK8) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_933,plain,
    ( ~ v2_compts_1(X0,sK8)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ r2_hidden(X1,k3_subset_1(u1_struct_0(sK8),X0))
    | r1_tarski(X0,sK7(sK8,X0,X1))
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_929,c_28,c_26])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X0,X1)
    | ~ v3_pre_topc(X2,X1)
    | ~ r2_hidden(sK2(X1),X2)
    | ~ r1_tarski(sK3(X1),X0)
    | ~ r1_xboole_0(X2,X0)
    | sP0(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_0,plain,
    ( ~ sP1(X0)
    | ~ sP0(X0)
    | v9_pre_topc(X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_15,plain,
    ( v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | sP1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK8) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_340,plain,
    ( ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | sP1(X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_29])).

cnf(c_341,plain,
    ( ~ v2_pre_topc(sK8)
    | ~ l1_pre_topc(sK8)
    | sP1(sK8) ),
    inference(unflattening,[status(thm)],[c_340])).

cnf(c_343,plain,
    ( sP1(sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_341,c_28,c_27])).

cnf(c_355,plain,
    ( ~ sP0(X0)
    | v9_pre_topc(X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_343])).

cnf(c_356,plain,
    ( ~ sP0(sK8)
    | v9_pre_topc(sK8) ),
    inference(unflattening,[status(thm)],[c_355])).

cnf(c_24,negated_conjecture,
    ( ~ v9_pre_topc(sK8) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_358,plain,
    ( ~ sP0(sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_356,c_24])).

cnf(c_638,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X0,X1)
    | ~ v3_pre_topc(X2,X1)
    | ~ r2_hidden(sK2(X1),X2)
    | ~ r1_tarski(sK3(X1),X0)
    | ~ r1_xboole_0(X2,X0)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_358])).

cnf(c_639,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ v3_pre_topc(X1,sK8)
    | ~ v3_pre_topc(X0,sK8)
    | ~ r2_hidden(sK2(sK8),X1)
    | ~ r1_tarski(sK3(sK8),X0)
    | ~ r1_xboole_0(X1,X0) ),
    inference(unflattening,[status(thm)],[c_638])).

cnf(c_16,plain,
    ( ~ v2_compts_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,k3_subset_1(u1_struct_0(X1),X0))
    | r1_xboole_0(sK6(X1,X0,X2),sK7(X1,X0,X2))
    | ~ v8_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_958,plain,
    ( ~ v2_compts_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,k3_subset_1(u1_struct_0(X1),X0))
    | r1_xboole_0(sK6(X1,X0,X2),sK7(X1,X0,X2))
    | ~ v8_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | sK8 != X1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_27])).

cnf(c_959,plain,
    ( ~ v2_compts_1(X0,sK8)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ r2_hidden(X1,k3_subset_1(u1_struct_0(sK8),X0))
    | r1_xboole_0(sK6(sK8,X0,X1),sK7(sK8,X0,X1))
    | ~ v8_pre_topc(sK8)
    | ~ v2_pre_topc(sK8)
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_958])).

cnf(c_963,plain,
    ( ~ v2_compts_1(X0,sK8)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ r2_hidden(X1,k3_subset_1(u1_struct_0(sK8),X0))
    | r1_xboole_0(sK6(sK8,X0,X1),sK7(sK8,X0,X1))
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_959,c_28,c_26])).

cnf(c_1037,plain,
    ( ~ v2_compts_1(X0,sK8)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ m1_subset_1(X3,u1_struct_0(sK8))
    | ~ v3_pre_topc(X1,sK8)
    | ~ v3_pre_topc(X2,sK8)
    | ~ r2_hidden(X3,k3_subset_1(u1_struct_0(sK8),X0))
    | ~ r2_hidden(sK2(sK8),X2)
    | ~ r1_tarski(sK3(sK8),X1)
    | sK7(sK8,X0,X3) != X1
    | sK6(sK8,X0,X3) != X2
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_639,c_963])).

cnf(c_1038,plain,
    ( ~ v2_compts_1(X0,sK8)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(sK7(sK8,X0,X1),k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ m1_subset_1(sK6(sK8,X0,X1),k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ v3_pre_topc(sK7(sK8,X0,X1),sK8)
    | ~ v3_pre_topc(sK6(sK8,X0,X1),sK8)
    | ~ r2_hidden(X1,k3_subset_1(u1_struct_0(sK8),X0))
    | ~ r2_hidden(sK2(sK8),sK6(sK8,X0,X1))
    | ~ r1_tarski(sK3(sK8),sK7(sK8,X0,X1))
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_1037])).

cnf(c_22,plain,
    ( ~ v2_compts_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(sK6(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,k3_subset_1(u1_struct_0(X1),X0))
    | ~ v8_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_778,plain,
    ( ~ v2_compts_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(sK6(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,k3_subset_1(u1_struct_0(X1),X0))
    | ~ v8_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | sK8 != X1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_27])).

cnf(c_779,plain,
    ( ~ v2_compts_1(X0,sK8)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | m1_subset_1(sK6(sK8,X0,X1),k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ r2_hidden(X1,k3_subset_1(u1_struct_0(sK8),X0))
    | ~ v8_pre_topc(sK8)
    | ~ v2_pre_topc(sK8)
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_778])).

cnf(c_783,plain,
    ( ~ v2_compts_1(X0,sK8)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | m1_subset_1(sK6(sK8,X0,X1),k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ r2_hidden(X1,k3_subset_1(u1_struct_0(sK8),X0))
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_779,c_28,c_26])).

cnf(c_21,plain,
    ( ~ v2_compts_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(sK7(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,k3_subset_1(u1_struct_0(X1),X0))
    | ~ v8_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_808,plain,
    ( ~ v2_compts_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(sK7(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,k3_subset_1(u1_struct_0(X1),X0))
    | ~ v8_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | sK8 != X1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_27])).

cnf(c_809,plain,
    ( ~ v2_compts_1(X0,sK8)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | m1_subset_1(sK7(sK8,X0,X1),k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ r2_hidden(X1,k3_subset_1(u1_struct_0(sK8),X0))
    | ~ v8_pre_topc(sK8)
    | ~ v2_pre_topc(sK8)
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_808])).

cnf(c_813,plain,
    ( ~ v2_compts_1(X0,sK8)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | m1_subset_1(sK7(sK8,X0,X1),k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ r2_hidden(X1,k3_subset_1(u1_struct_0(sK8),X0))
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_809,c_28,c_26])).

cnf(c_20,plain,
    ( ~ v2_compts_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v3_pre_topc(sK6(X1,X0,X2),X1)
    | ~ r2_hidden(X2,k3_subset_1(u1_struct_0(X1),X0))
    | ~ v8_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_838,plain,
    ( ~ v2_compts_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v3_pre_topc(sK6(X1,X0,X2),X1)
    | ~ r2_hidden(X2,k3_subset_1(u1_struct_0(X1),X0))
    | ~ v8_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | sK8 != X1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_27])).

cnf(c_839,plain,
    ( ~ v2_compts_1(X0,sK8)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | v3_pre_topc(sK6(sK8,X0,X1),sK8)
    | ~ r2_hidden(X1,k3_subset_1(u1_struct_0(sK8),X0))
    | ~ v8_pre_topc(sK8)
    | ~ v2_pre_topc(sK8)
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_838])).

cnf(c_843,plain,
    ( ~ v2_compts_1(X0,sK8)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | v3_pre_topc(sK6(sK8,X0,X1),sK8)
    | ~ r2_hidden(X1,k3_subset_1(u1_struct_0(sK8),X0))
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_839,c_28,c_26])).

cnf(c_19,plain,
    ( ~ v2_compts_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v3_pre_topc(sK7(X1,X0,X2),X1)
    | ~ r2_hidden(X2,k3_subset_1(u1_struct_0(X1),X0))
    | ~ v8_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_868,plain,
    ( ~ v2_compts_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v3_pre_topc(sK7(X1,X0,X2),X1)
    | ~ r2_hidden(X2,k3_subset_1(u1_struct_0(X1),X0))
    | ~ v8_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | sK8 != X1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_27])).

cnf(c_869,plain,
    ( ~ v2_compts_1(X0,sK8)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | v3_pre_topc(sK7(sK8,X0,X1),sK8)
    | ~ r2_hidden(X1,k3_subset_1(u1_struct_0(sK8),X0))
    | ~ v8_pre_topc(sK8)
    | ~ v2_pre_topc(sK8)
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_868])).

cnf(c_873,plain,
    ( ~ v2_compts_1(X0,sK8)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | v3_pre_topc(sK7(sK8,X0,X1),sK8)
    | ~ r2_hidden(X1,k3_subset_1(u1_struct_0(sK8),X0))
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_869,c_28,c_26])).

cnf(c_1042,plain,
    ( ~ v2_compts_1(X0,sK8)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ r2_hidden(X1,k3_subset_1(u1_struct_0(sK8),X0))
    | ~ r2_hidden(sK2(sK8),sK6(sK8,X0,X1))
    | ~ r1_tarski(sK3(sK8),sK7(sK8,X0,X1))
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1038,c_783,c_813,c_843,c_873])).

cnf(c_1078,plain,
    ( ~ v2_compts_1(X0,sK8)
    | ~ v2_compts_1(X1,sK8)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X3,u1_struct_0(sK8))
    | ~ r2_hidden(X2,k3_subset_1(u1_struct_0(sK8),X0))
    | ~ r2_hidden(X3,k3_subset_1(u1_struct_0(sK8),X1))
    | ~ r2_hidden(sK2(sK8),sK6(sK8,X1,X3))
    | sK7(sK8,X1,X3) != sK7(sK8,X0,X2)
    | sK3(sK8) != X0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_933,c_1042])).

cnf(c_1079,plain,
    ( ~ v2_compts_1(X0,sK8)
    | ~ v2_compts_1(sK3(sK8),sK8)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(sK3(sK8),k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ r2_hidden(X2,k3_subset_1(u1_struct_0(sK8),X0))
    | ~ r2_hidden(X1,k3_subset_1(u1_struct_0(sK8),sK3(sK8)))
    | ~ r2_hidden(sK2(sK8),sK6(sK8,X0,X2))
    | sK7(sK8,X0,X2) != sK7(sK8,sK3(sK8),X1)
    | k1_xboole_0 = X0
    | k1_xboole_0 = sK3(sK8) ),
    inference(unflattening,[status(thm)],[c_1078])).

cnf(c_4,plain,
    ( v4_pre_topc(sK3(X0),X0)
    | sP0(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_23,plain,
    ( v2_compts_1(X0,X1)
    | ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_compts_1(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_25,negated_conjecture,
    ( v1_compts_1(sK8) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_368,plain,
    ( v2_compts_1(X0,X1)
    | ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_25])).

cnf(c_369,plain,
    ( v2_compts_1(X0,sK8)
    | ~ v4_pre_topc(X0,sK8)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ l1_pre_topc(sK8) ),
    inference(unflattening,[status(thm)],[c_368])).

cnf(c_373,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ v4_pre_topc(X0,sK8)
    | v2_compts_1(X0,sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_369,c_27])).

cnf(c_374,plain,
    ( v2_compts_1(X0,sK8)
    | ~ v4_pre_topc(X0,sK8)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(renaming,[status(thm)],[c_373])).

cnf(c_595,plain,
    ( v2_compts_1(X0,sK8)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | sP0(X1)
    | sK3(X1) != X0
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_374])).

cnf(c_596,plain,
    ( v2_compts_1(sK3(sK8),sK8)
    | ~ m1_subset_1(sK3(sK8),k1_zfmisc_1(u1_struct_0(sK8)))
    | sP0(sK8) ),
    inference(unflattening,[status(thm)],[c_595])).

cnf(c_598,plain,
    ( ~ m1_subset_1(sK3(sK8),k1_zfmisc_1(u1_struct_0(sK8)))
    | v2_compts_1(sK3(sK8),sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_596,c_24,c_356])).

cnf(c_599,plain,
    ( v2_compts_1(sK3(sK8),sK8)
    | ~ m1_subset_1(sK3(sK8),k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(renaming,[status(thm)],[c_598])).

cnf(c_6,plain,
    ( m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | sP0(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_619,plain,
    ( m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_358])).

cnf(c_620,plain,
    ( m1_subset_1(sK3(sK8),k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(unflattening,[status(thm)],[c_619])).

cnf(c_1083,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ v2_compts_1(X0,sK8)
    | ~ r2_hidden(X2,k3_subset_1(u1_struct_0(sK8),X0))
    | ~ r2_hidden(X1,k3_subset_1(u1_struct_0(sK8),sK3(sK8)))
    | ~ r2_hidden(sK2(sK8),sK6(sK8,X0,X2))
    | sK7(sK8,X0,X2) != sK7(sK8,sK3(sK8),X1)
    | k1_xboole_0 = X0
    | k1_xboole_0 = sK3(sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1079,c_24,c_356,c_596,c_620])).

cnf(c_1084,plain,
    ( ~ v2_compts_1(X0,sK8)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ r2_hidden(X1,k3_subset_1(u1_struct_0(sK8),X0))
    | ~ r2_hidden(X2,k3_subset_1(u1_struct_0(sK8),sK3(sK8)))
    | ~ r2_hidden(sK2(sK8),sK6(sK8,X0,X1))
    | sK7(sK8,X0,X1) != sK7(sK8,sK3(sK8),X2)
    | k1_xboole_0 = X0
    | k1_xboole_0 = sK3(sK8) ),
    inference(renaming,[status(thm)],[c_1083])).

cnf(c_668,plain,
    ( v2_compts_1(sK3(sK8),sK8) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_620,c_599])).

cnf(c_1131,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ r2_hidden(X2,k3_subset_1(u1_struct_0(sK8),X0))
    | ~ r2_hidden(X1,k3_subset_1(u1_struct_0(sK8),sK3(sK8)))
    | ~ r2_hidden(sK2(sK8),sK6(sK8,X0,X2))
    | sK7(sK8,sK3(sK8),X1) != sK7(sK8,X0,X2)
    | sK3(sK8) != X0
    | sK3(sK8) = k1_xboole_0
    | sK8 != sK8
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_1084,c_668])).

cnf(c_1132,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(sK3(sK8),k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ r2_hidden(X0,k3_subset_1(u1_struct_0(sK8),sK3(sK8)))
    | ~ r2_hidden(X1,k3_subset_1(u1_struct_0(sK8),sK3(sK8)))
    | ~ r2_hidden(sK2(sK8),sK6(sK8,sK3(sK8),X0))
    | sK7(sK8,sK3(sK8),X1) != sK7(sK8,sK3(sK8),X0)
    | sK3(sK8) = k1_xboole_0
    | k1_xboole_0 = sK3(sK8) ),
    inference(unflattening,[status(thm)],[c_1131])).

cnf(c_5,plain,
    ( sP0(X0)
    | sK3(X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_626,plain,
    ( sK3(X0) != k1_xboole_0
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_358])).

cnf(c_627,plain,
    ( sK3(sK8) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_626])).

cnf(c_1136,plain,
    ( sK7(sK8,sK3(sK8),X1) != sK7(sK8,sK3(sK8),X0)
    | ~ r2_hidden(sK2(sK8),sK6(sK8,sK3(sK8),X0))
    | ~ r2_hidden(X1,k3_subset_1(u1_struct_0(sK8),sK3(sK8)))
    | ~ r2_hidden(X0,k3_subset_1(u1_struct_0(sK8),sK3(sK8)))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | k1_xboole_0 = sK3(sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1132,c_620,c_627])).

cnf(c_1137,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ r2_hidden(X0,k3_subset_1(u1_struct_0(sK8),sK3(sK8)))
    | ~ r2_hidden(X1,k3_subset_1(u1_struct_0(sK8),sK3(sK8)))
    | ~ r2_hidden(sK2(sK8),sK6(sK8,sK3(sK8),X1))
    | sK7(sK8,sK3(sK8),X0) != sK7(sK8,sK3(sK8),X1)
    | k1_xboole_0 = sK3(sK8) ),
    inference(renaming,[status(thm)],[c_1136])).

cnf(c_1316,plain,
    ( ~ m1_subset_1(X0_54,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_54,u1_struct_0(sK8))
    | ~ r2_hidden(X0_54,k3_subset_1(u1_struct_0(sK8),sK3(sK8)))
    | ~ r2_hidden(X1_54,k3_subset_1(u1_struct_0(sK8),sK3(sK8)))
    | ~ r2_hidden(sK2(sK8),sK6(sK8,sK3(sK8),X1_54))
    | sK7(sK8,sK3(sK8),X0_54) != sK7(sK8,sK3(sK8),X1_54)
    | k1_xboole_0 = sK3(sK8) ),
    inference(subtyping,[status(esa)],[c_1137])).

cnf(c_1563,plain,
    ( ~ m1_subset_1(X0_54,u1_struct_0(sK8))
    | ~ m1_subset_1(sK2(sK8),u1_struct_0(sK8))
    | ~ r2_hidden(X0_54,k3_subset_1(u1_struct_0(sK8),sK3(sK8)))
    | ~ r2_hidden(sK2(sK8),sK6(sK8,sK3(sK8),X0_54))
    | ~ r2_hidden(sK2(sK8),k3_subset_1(u1_struct_0(sK8),sK3(sK8)))
    | sK7(sK8,sK3(sK8),sK2(sK8)) != sK7(sK8,sK3(sK8),X0_54)
    | k1_xboole_0 = sK3(sK8) ),
    inference(instantiation,[status(thm)],[c_1316])).

cnf(c_1616,plain,
    ( ~ m1_subset_1(sK2(sK8),u1_struct_0(sK8))
    | ~ r2_hidden(sK2(sK8),sK6(sK8,sK3(sK8),sK2(sK8)))
    | ~ r2_hidden(sK2(sK8),k3_subset_1(u1_struct_0(sK8),sK3(sK8)))
    | sK7(sK8,sK3(sK8),sK2(sK8)) != sK7(sK8,sK3(sK8),sK2(sK8))
    | k1_xboole_0 = sK3(sK8) ),
    inference(instantiation,[status(thm)],[c_1563])).

cnf(c_1589,plain,
    ( sK3(sK8) = sK3(sK8) ),
    inference(instantiation,[status(thm)],[c_1322])).

cnf(c_1323,plain,
    ( X0_54 != X1_54
    | X2_54 != X1_54
    | X2_54 = X0_54 ),
    theory(equality)).

cnf(c_1546,plain,
    ( sK3(sK8) != X0_54
    | sK3(sK8) = k1_xboole_0
    | k1_xboole_0 != X0_54 ),
    inference(instantiation,[status(thm)],[c_1323])).

cnf(c_1588,plain,
    ( sK3(sK8) != sK3(sK8)
    | sK3(sK8) = k1_xboole_0
    | k1_xboole_0 != sK3(sK8) ),
    inference(instantiation,[status(thm)],[c_1546])).

cnf(c_18,plain,
    ( ~ v2_compts_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,sK6(X1,X0,X2))
    | ~ r2_hidden(X2,k3_subset_1(u1_struct_0(X1),X0))
    | ~ v8_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_898,plain,
    ( ~ v2_compts_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,sK6(X1,X0,X2))
    | ~ r2_hidden(X2,k3_subset_1(u1_struct_0(X1),X0))
    | ~ v8_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | sK8 != X1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_27])).

cnf(c_899,plain,
    ( ~ v2_compts_1(X0,sK8)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | r2_hidden(X1,sK6(sK8,X0,X1))
    | ~ r2_hidden(X1,k3_subset_1(u1_struct_0(sK8),X0))
    | ~ v8_pre_topc(sK8)
    | ~ v2_pre_topc(sK8)
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_898])).

cnf(c_903,plain,
    ( ~ v2_compts_1(X0,sK8)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | r2_hidden(X1,sK6(sK8,X0,X1))
    | ~ r2_hidden(X1,k3_subset_1(u1_struct_0(sK8),X0))
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_899,c_28,c_26])).

cnf(c_1164,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | r2_hidden(X1,sK6(sK8,X0,X1))
    | ~ r2_hidden(X1,k3_subset_1(u1_struct_0(sK8),X0))
    | sK3(sK8) != X0
    | sK8 != sK8
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_903,c_668])).

cnf(c_1165,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(sK3(sK8),k1_zfmisc_1(u1_struct_0(sK8)))
    | r2_hidden(X0,sK6(sK8,sK3(sK8),X0))
    | ~ r2_hidden(X0,k3_subset_1(u1_struct_0(sK8),sK3(sK8)))
    | k1_xboole_0 = sK3(sK8) ),
    inference(unflattening,[status(thm)],[c_1164])).

cnf(c_1169,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | r2_hidden(X0,sK6(sK8,sK3(sK8),X0))
    | ~ r2_hidden(X0,k3_subset_1(u1_struct_0(sK8),sK3(sK8)))
    | k1_xboole_0 = sK3(sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1165,c_620])).

cnf(c_1315,plain,
    ( ~ m1_subset_1(X0_54,u1_struct_0(sK8))
    | r2_hidden(X0_54,sK6(sK8,sK3(sK8),X0_54))
    | ~ r2_hidden(X0_54,k3_subset_1(u1_struct_0(sK8),sK3(sK8)))
    | k1_xboole_0 = sK3(sK8) ),
    inference(subtyping,[status(esa)],[c_1169])).

cnf(c_1543,plain,
    ( ~ m1_subset_1(sK2(sK8),u1_struct_0(sK8))
    | r2_hidden(sK2(sK8),sK6(sK8,sK3(sK8),sK2(sK8)))
    | ~ r2_hidden(sK2(sK8),k3_subset_1(u1_struct_0(sK8),sK3(sK8)))
    | k1_xboole_0 = sK3(sK8) ),
    inference(instantiation,[status(thm)],[c_1315])).

cnf(c_1318,plain,
    ( sK3(sK8) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_627])).

cnf(c_3,plain,
    ( r2_hidden(sK2(X0),k3_subset_1(u1_struct_0(X0),sK3(X0)))
    | sP0(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_631,plain,
    ( r2_hidden(sK2(X0),k3_subset_1(u1_struct_0(X0),sK3(X0)))
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_358])).

cnf(c_632,plain,
    ( r2_hidden(sK2(sK8),k3_subset_1(u1_struct_0(sK8),sK3(sK8))) ),
    inference(unflattening,[status(thm)],[c_631])).

cnf(c_7,plain,
    ( m1_subset_1(sK2(X0),u1_struct_0(X0))
    | sP0(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_612,plain,
    ( m1_subset_1(sK2(X0),u1_struct_0(X0))
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_358])).

cnf(c_613,plain,
    ( m1_subset_1(sK2(sK8),u1_struct_0(sK8)) ),
    inference(unflattening,[status(thm)],[c_612])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1626,c_1616,c_1589,c_1588,c_1543,c_1318,c_632,c_613])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:23:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  % Running in FOF mode
% 1.17/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.17/0.98  
% 1.17/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.17/0.98  
% 1.17/0.98  ------  iProver source info
% 1.17/0.98  
% 1.17/0.98  git: date: 2020-06-30 10:37:57 +0100
% 1.17/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.17/0.98  git: non_committed_changes: false
% 1.17/0.98  git: last_make_outside_of_git: false
% 1.17/0.98  
% 1.17/0.98  ------ 
% 1.17/0.98  
% 1.17/0.98  ------ Input Options
% 1.17/0.98  
% 1.17/0.98  --out_options                           all
% 1.17/0.98  --tptp_safe_out                         true
% 1.17/0.98  --problem_path                          ""
% 1.17/0.98  --include_path                          ""
% 1.17/0.98  --clausifier                            res/vclausify_rel
% 1.17/0.98  --clausifier_options                    --mode clausify
% 1.17/0.98  --stdin                                 false
% 1.17/0.98  --stats_out                             all
% 1.17/0.98  
% 1.17/0.98  ------ General Options
% 1.17/0.98  
% 1.17/0.98  --fof                                   false
% 1.17/0.98  --time_out_real                         305.
% 1.17/0.98  --time_out_virtual                      -1.
% 1.17/0.98  --symbol_type_check                     false
% 1.17/0.98  --clausify_out                          false
% 1.17/0.98  --sig_cnt_out                           false
% 1.17/0.98  --trig_cnt_out                          false
% 1.17/0.98  --trig_cnt_out_tolerance                1.
% 1.17/0.98  --trig_cnt_out_sk_spl                   false
% 1.17/0.98  --abstr_cl_out                          false
% 1.17/0.98  
% 1.17/0.98  ------ Global Options
% 1.17/0.98  
% 1.17/0.98  --schedule                              default
% 1.17/0.98  --add_important_lit                     false
% 1.17/0.98  --prop_solver_per_cl                    1000
% 1.17/0.98  --min_unsat_core                        false
% 1.17/0.98  --soft_assumptions                      false
% 1.17/0.98  --soft_lemma_size                       3
% 1.17/0.98  --prop_impl_unit_size                   0
% 1.17/0.98  --prop_impl_unit                        []
% 1.17/0.98  --share_sel_clauses                     true
% 1.17/0.98  --reset_solvers                         false
% 1.17/0.98  --bc_imp_inh                            [conj_cone]
% 1.17/0.98  --conj_cone_tolerance                   3.
% 1.17/0.98  --extra_neg_conj                        none
% 1.17/0.98  --large_theory_mode                     true
% 1.17/0.98  --prolific_symb_bound                   200
% 1.17/0.98  --lt_threshold                          2000
% 1.17/0.98  --clause_weak_htbl                      true
% 1.17/0.98  --gc_record_bc_elim                     false
% 1.17/0.98  
% 1.17/0.98  ------ Preprocessing Options
% 1.17/0.98  
% 1.17/0.98  --preprocessing_flag                    true
% 1.17/0.98  --time_out_prep_mult                    0.1
% 1.17/0.98  --splitting_mode                        input
% 1.17/0.98  --splitting_grd                         true
% 1.17/0.98  --splitting_cvd                         false
% 1.17/0.98  --splitting_cvd_svl                     false
% 1.17/0.98  --splitting_nvd                         32
% 1.17/0.98  --sub_typing                            true
% 1.17/0.98  --prep_gs_sim                           true
% 1.17/0.98  --prep_unflatten                        true
% 1.17/0.98  --prep_res_sim                          true
% 1.17/0.98  --prep_upred                            true
% 1.17/0.98  --prep_sem_filter                       exhaustive
% 1.17/0.98  --prep_sem_filter_out                   false
% 1.17/0.98  --pred_elim                             true
% 1.17/0.98  --res_sim_input                         true
% 1.17/0.98  --eq_ax_congr_red                       true
% 1.17/0.98  --pure_diseq_elim                       true
% 1.17/0.98  --brand_transform                       false
% 1.17/0.98  --non_eq_to_eq                          false
% 1.17/0.98  --prep_def_merge                        true
% 1.17/0.98  --prep_def_merge_prop_impl              false
% 1.17/0.98  --prep_def_merge_mbd                    true
% 1.17/0.98  --prep_def_merge_tr_red                 false
% 1.17/0.98  --prep_def_merge_tr_cl                  false
% 1.17/0.98  --smt_preprocessing                     true
% 1.17/0.98  --smt_ac_axioms                         fast
% 1.17/0.98  --preprocessed_out                      false
% 1.17/0.98  --preprocessed_stats                    false
% 1.17/0.98  
% 1.17/0.98  ------ Abstraction refinement Options
% 1.17/0.98  
% 1.17/0.98  --abstr_ref                             []
% 1.17/0.98  --abstr_ref_prep                        false
% 1.17/0.98  --abstr_ref_until_sat                   false
% 1.17/0.98  --abstr_ref_sig_restrict                funpre
% 1.17/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.17/0.98  --abstr_ref_under                       []
% 1.17/0.98  
% 1.17/0.98  ------ SAT Options
% 1.17/0.98  
% 1.17/0.98  --sat_mode                              false
% 1.17/0.98  --sat_fm_restart_options                ""
% 1.17/0.98  --sat_gr_def                            false
% 1.17/0.98  --sat_epr_types                         true
% 1.17/0.98  --sat_non_cyclic_types                  false
% 1.17/0.98  --sat_finite_models                     false
% 1.17/0.98  --sat_fm_lemmas                         false
% 1.17/0.98  --sat_fm_prep                           false
% 1.17/0.98  --sat_fm_uc_incr                        true
% 1.17/0.98  --sat_out_model                         small
% 1.17/0.98  --sat_out_clauses                       false
% 1.17/0.98  
% 1.17/0.98  ------ QBF Options
% 1.17/0.98  
% 1.17/0.98  --qbf_mode                              false
% 1.17/0.98  --qbf_elim_univ                         false
% 1.17/0.98  --qbf_dom_inst                          none
% 1.17/0.98  --qbf_dom_pre_inst                      false
% 1.17/0.98  --qbf_sk_in                             false
% 1.17/0.98  --qbf_pred_elim                         true
% 1.17/0.98  --qbf_split                             512
% 1.17/0.98  
% 1.17/0.98  ------ BMC1 Options
% 1.17/0.98  
% 1.17/0.98  --bmc1_incremental                      false
% 1.17/0.98  --bmc1_axioms                           reachable_all
% 1.17/0.98  --bmc1_min_bound                        0
% 1.17/0.98  --bmc1_max_bound                        -1
% 1.17/0.98  --bmc1_max_bound_default                -1
% 1.17/0.98  --bmc1_symbol_reachability              true
% 1.17/0.98  --bmc1_property_lemmas                  false
% 1.17/0.98  --bmc1_k_induction                      false
% 1.17/0.98  --bmc1_non_equiv_states                 false
% 1.17/0.98  --bmc1_deadlock                         false
% 1.17/0.98  --bmc1_ucm                              false
% 1.17/0.98  --bmc1_add_unsat_core                   none
% 1.17/0.98  --bmc1_unsat_core_children              false
% 1.17/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.17/0.98  --bmc1_out_stat                         full
% 1.17/0.98  --bmc1_ground_init                      false
% 1.17/0.98  --bmc1_pre_inst_next_state              false
% 1.17/0.98  --bmc1_pre_inst_state                   false
% 1.17/0.98  --bmc1_pre_inst_reach_state             false
% 1.17/0.98  --bmc1_out_unsat_core                   false
% 1.17/0.98  --bmc1_aig_witness_out                  false
% 1.17/0.98  --bmc1_verbose                          false
% 1.17/0.98  --bmc1_dump_clauses_tptp                false
% 1.17/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.17/0.98  --bmc1_dump_file                        -
% 1.17/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.17/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.17/0.98  --bmc1_ucm_extend_mode                  1
% 1.17/0.98  --bmc1_ucm_init_mode                    2
% 1.17/0.98  --bmc1_ucm_cone_mode                    none
% 1.17/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.17/0.98  --bmc1_ucm_relax_model                  4
% 1.17/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.17/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.17/0.98  --bmc1_ucm_layered_model                none
% 1.17/0.98  --bmc1_ucm_max_lemma_size               10
% 1.17/0.98  
% 1.17/0.98  ------ AIG Options
% 1.17/0.98  
% 1.17/0.98  --aig_mode                              false
% 1.17/0.98  
% 1.17/0.98  ------ Instantiation Options
% 1.17/0.98  
% 1.17/0.98  --instantiation_flag                    true
% 1.17/0.98  --inst_sos_flag                         false
% 1.17/0.98  --inst_sos_phase                        true
% 1.17/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.17/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.17/0.98  --inst_lit_sel_side                     num_symb
% 1.17/0.98  --inst_solver_per_active                1400
% 1.17/0.98  --inst_solver_calls_frac                1.
% 1.17/0.98  --inst_passive_queue_type               priority_queues
% 1.17/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.17/0.98  --inst_passive_queues_freq              [25;2]
% 1.17/0.98  --inst_dismatching                      true
% 1.17/0.98  --inst_eager_unprocessed_to_passive     true
% 1.17/0.98  --inst_prop_sim_given                   true
% 1.17/0.98  --inst_prop_sim_new                     false
% 1.17/0.98  --inst_subs_new                         false
% 1.17/0.98  --inst_eq_res_simp                      false
% 1.17/0.98  --inst_subs_given                       false
% 1.17/0.98  --inst_orphan_elimination               true
% 1.17/0.98  --inst_learning_loop_flag               true
% 1.17/0.98  --inst_learning_start                   3000
% 1.17/0.98  --inst_learning_factor                  2
% 1.17/0.98  --inst_start_prop_sim_after_learn       3
% 1.17/0.98  --inst_sel_renew                        solver
% 1.17/0.98  --inst_lit_activity_flag                true
% 1.17/0.98  --inst_restr_to_given                   false
% 1.17/0.98  --inst_activity_threshold               500
% 1.17/0.98  --inst_out_proof                        true
% 1.17/0.98  
% 1.17/0.98  ------ Resolution Options
% 1.17/0.98  
% 1.17/0.98  --resolution_flag                       true
% 1.17/0.98  --res_lit_sel                           adaptive
% 1.17/0.98  --res_lit_sel_side                      none
% 1.17/0.98  --res_ordering                          kbo
% 1.17/0.98  --res_to_prop_solver                    active
% 1.17/0.98  --res_prop_simpl_new                    false
% 1.17/0.98  --res_prop_simpl_given                  true
% 1.17/0.98  --res_passive_queue_type                priority_queues
% 1.17/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.17/0.98  --res_passive_queues_freq               [15;5]
% 1.17/0.98  --res_forward_subs                      full
% 1.17/0.98  --res_backward_subs                     full
% 1.17/0.98  --res_forward_subs_resolution           true
% 1.17/0.98  --res_backward_subs_resolution          true
% 1.17/0.98  --res_orphan_elimination                true
% 1.17/0.98  --res_time_limit                        2.
% 1.17/0.98  --res_out_proof                         true
% 1.17/0.98  
% 1.17/0.98  ------ Superposition Options
% 1.17/0.98  
% 1.17/0.98  --superposition_flag                    true
% 1.17/0.98  --sup_passive_queue_type                priority_queues
% 1.17/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.17/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.17/0.98  --demod_completeness_check              fast
% 1.17/0.98  --demod_use_ground                      true
% 1.17/0.98  --sup_to_prop_solver                    passive
% 1.17/0.98  --sup_prop_simpl_new                    true
% 1.17/0.98  --sup_prop_simpl_given                  true
% 1.17/0.98  --sup_fun_splitting                     false
% 1.17/0.98  --sup_smt_interval                      50000
% 1.17/0.98  
% 1.17/0.98  ------ Superposition Simplification Setup
% 1.17/0.98  
% 1.17/0.98  --sup_indices_passive                   []
% 1.17/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.17/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.17/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.17/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.17/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.17/0.98  --sup_full_bw                           [BwDemod]
% 1.17/0.98  --sup_immed_triv                        [TrivRules]
% 1.17/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.17/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.17/0.98  --sup_immed_bw_main                     []
% 1.17/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.17/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.17/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.17/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.17/0.98  
% 1.17/0.98  ------ Combination Options
% 1.17/0.98  
% 1.17/0.98  --comb_res_mult                         3
% 1.17/0.98  --comb_sup_mult                         2
% 1.17/0.98  --comb_inst_mult                        10
% 1.17/0.98  
% 1.17/0.98  ------ Debug Options
% 1.17/0.98  
% 1.17/0.98  --dbg_backtrace                         false
% 1.17/0.98  --dbg_dump_prop_clauses                 false
% 1.17/0.98  --dbg_dump_prop_clauses_file            -
% 1.17/0.98  --dbg_out_stat                          false
% 1.17/0.98  ------ Parsing...
% 1.17/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.17/0.98  
% 1.17/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 11 0s  sf_e  pe_s  pe_e 
% 1.17/0.98  
% 1.17/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.17/0.98  
% 1.17/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.17/0.98  ------ Proving...
% 1.17/0.98  ------ Problem Properties 
% 1.17/0.98  
% 1.17/0.98  
% 1.17/0.98  clauses                                 8
% 1.17/0.98  conjectures                             0
% 1.17/0.98  EPR                                     0
% 1.17/0.98  Horn                                    5
% 1.17/0.98  unary                                   4
% 1.17/0.98  binary                                  0
% 1.17/0.98  lits                                    23
% 1.17/0.98  lits eq                                 6
% 1.17/0.98  fd_pure                                 0
% 1.17/0.98  fd_pseudo                               0
% 1.17/0.98  fd_cond                                 0
% 1.17/0.98  fd_pseudo_cond                          0
% 1.17/0.98  AC symbols                              0
% 1.17/0.98  
% 1.17/0.98  ------ Schedule dynamic 5 is on 
% 1.17/0.98  
% 1.17/0.98  ------ no conjectures: strip conj schedule 
% 1.17/0.98  
% 1.17/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" stripped conjectures Time Limit: 10.
% 1.17/0.98  
% 1.17/0.98  
% 1.17/0.98  ------ 
% 1.17/0.98  Current options:
% 1.17/0.98  ------ 
% 1.17/0.98  
% 1.17/0.98  ------ Input Options
% 1.17/0.98  
% 1.17/0.98  --out_options                           all
% 1.17/0.98  --tptp_safe_out                         true
% 1.17/0.98  --problem_path                          ""
% 1.17/0.98  --include_path                          ""
% 1.17/0.98  --clausifier                            res/vclausify_rel
% 1.17/0.98  --clausifier_options                    --mode clausify
% 1.17/0.98  --stdin                                 false
% 1.17/0.98  --stats_out                             all
% 1.17/0.98  
% 1.17/0.98  ------ General Options
% 1.17/0.98  
% 1.17/0.98  --fof                                   false
% 1.17/0.98  --time_out_real                         305.
% 1.17/0.98  --time_out_virtual                      -1.
% 1.17/0.98  --symbol_type_check                     false
% 1.17/0.98  --clausify_out                          false
% 1.17/0.98  --sig_cnt_out                           false
% 1.17/0.98  --trig_cnt_out                          false
% 1.17/0.98  --trig_cnt_out_tolerance                1.
% 1.17/0.98  --trig_cnt_out_sk_spl                   false
% 1.17/0.98  --abstr_cl_out                          false
% 1.17/0.98  
% 1.17/0.98  ------ Global Options
% 1.17/0.98  
% 1.17/0.98  --schedule                              default
% 1.17/0.98  --add_important_lit                     false
% 1.17/0.98  --prop_solver_per_cl                    1000
% 1.17/0.98  --min_unsat_core                        false
% 1.17/0.98  --soft_assumptions                      false
% 1.17/0.98  --soft_lemma_size                       3
% 1.17/0.98  --prop_impl_unit_size                   0
% 1.17/0.98  --prop_impl_unit                        []
% 1.17/0.98  --share_sel_clauses                     true
% 1.17/0.98  --reset_solvers                         false
% 1.17/0.98  --bc_imp_inh                            [conj_cone]
% 1.17/0.98  --conj_cone_tolerance                   3.
% 1.17/0.98  --extra_neg_conj                        none
% 1.17/0.98  --large_theory_mode                     true
% 1.17/0.98  --prolific_symb_bound                   200
% 1.17/0.98  --lt_threshold                          2000
% 1.17/0.98  --clause_weak_htbl                      true
% 1.17/0.98  --gc_record_bc_elim                     false
% 1.17/0.98  
% 1.17/0.98  ------ Preprocessing Options
% 1.17/0.98  
% 1.17/0.98  --preprocessing_flag                    true
% 1.17/0.98  --time_out_prep_mult                    0.1
% 1.17/0.98  --splitting_mode                        input
% 1.17/0.98  --splitting_grd                         true
% 1.17/0.98  --splitting_cvd                         false
% 1.17/0.98  --splitting_cvd_svl                     false
% 1.17/0.98  --splitting_nvd                         32
% 1.17/0.98  --sub_typing                            true
% 1.17/0.98  --prep_gs_sim                           true
% 1.17/0.98  --prep_unflatten                        true
% 1.17/0.98  --prep_res_sim                          true
% 1.17/0.98  --prep_upred                            true
% 1.17/0.98  --prep_sem_filter                       exhaustive
% 1.17/0.98  --prep_sem_filter_out                   false
% 1.17/0.98  --pred_elim                             true
% 1.17/0.98  --res_sim_input                         true
% 1.17/0.98  --eq_ax_congr_red                       true
% 1.17/0.98  --pure_diseq_elim                       true
% 1.17/0.98  --brand_transform                       false
% 1.17/0.98  --non_eq_to_eq                          false
% 1.17/0.98  --prep_def_merge                        true
% 1.17/0.98  --prep_def_merge_prop_impl              false
% 1.17/0.98  --prep_def_merge_mbd                    true
% 1.17/0.98  --prep_def_merge_tr_red                 false
% 1.17/0.98  --prep_def_merge_tr_cl                  false
% 1.17/0.98  --smt_preprocessing                     true
% 1.17/0.98  --smt_ac_axioms                         fast
% 1.17/0.98  --preprocessed_out                      false
% 1.17/0.98  --preprocessed_stats                    false
% 1.17/0.98  
% 1.17/0.98  ------ Abstraction refinement Options
% 1.17/0.98  
% 1.17/0.98  --abstr_ref                             []
% 1.17/0.98  --abstr_ref_prep                        false
% 1.17/0.98  --abstr_ref_until_sat                   false
% 1.17/0.98  --abstr_ref_sig_restrict                funpre
% 1.17/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.17/0.98  --abstr_ref_under                       []
% 1.17/0.98  
% 1.17/0.98  ------ SAT Options
% 1.17/0.98  
% 1.17/0.98  --sat_mode                              false
% 1.17/0.98  --sat_fm_restart_options                ""
% 1.17/0.98  --sat_gr_def                            false
% 1.17/0.98  --sat_epr_types                         true
% 1.17/0.98  --sat_non_cyclic_types                  false
% 1.17/0.98  --sat_finite_models                     false
% 1.17/0.98  --sat_fm_lemmas                         false
% 1.17/0.98  --sat_fm_prep                           false
% 1.17/0.98  --sat_fm_uc_incr                        true
% 1.17/0.98  --sat_out_model                         small
% 1.17/0.98  --sat_out_clauses                       false
% 1.17/0.98  
% 1.17/0.98  ------ QBF Options
% 1.17/0.98  
% 1.17/0.98  --qbf_mode                              false
% 1.17/0.98  --qbf_elim_univ                         false
% 1.17/0.98  --qbf_dom_inst                          none
% 1.17/0.98  --qbf_dom_pre_inst                      false
% 1.17/0.98  --qbf_sk_in                             false
% 1.17/0.98  --qbf_pred_elim                         true
% 1.17/0.98  --qbf_split                             512
% 1.17/0.98  
% 1.17/0.98  ------ BMC1 Options
% 1.17/0.98  
% 1.17/0.98  --bmc1_incremental                      false
% 1.17/0.98  --bmc1_axioms                           reachable_all
% 1.17/0.98  --bmc1_min_bound                        0
% 1.17/0.98  --bmc1_max_bound                        -1
% 1.17/0.98  --bmc1_max_bound_default                -1
% 1.17/0.98  --bmc1_symbol_reachability              true
% 1.17/0.98  --bmc1_property_lemmas                  false
% 1.17/0.98  --bmc1_k_induction                      false
% 1.17/0.98  --bmc1_non_equiv_states                 false
% 1.17/0.98  --bmc1_deadlock                         false
% 1.17/0.98  --bmc1_ucm                              false
% 1.17/0.98  --bmc1_add_unsat_core                   none
% 1.17/0.98  --bmc1_unsat_core_children              false
% 1.17/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.17/0.98  --bmc1_out_stat                         full
% 1.17/0.98  --bmc1_ground_init                      false
% 1.17/0.98  --bmc1_pre_inst_next_state              false
% 1.17/0.98  --bmc1_pre_inst_state                   false
% 1.17/0.98  --bmc1_pre_inst_reach_state             false
% 1.17/0.98  --bmc1_out_unsat_core                   false
% 1.17/0.98  --bmc1_aig_witness_out                  false
% 1.17/0.98  --bmc1_verbose                          false
% 1.17/0.98  --bmc1_dump_clauses_tptp                false
% 1.17/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.17/0.98  --bmc1_dump_file                        -
% 1.17/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.17/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.17/0.98  --bmc1_ucm_extend_mode                  1
% 1.17/0.98  --bmc1_ucm_init_mode                    2
% 1.17/0.98  --bmc1_ucm_cone_mode                    none
% 1.17/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.17/0.98  --bmc1_ucm_relax_model                  4
% 1.17/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.17/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.17/0.98  --bmc1_ucm_layered_model                none
% 1.17/0.98  --bmc1_ucm_max_lemma_size               10
% 1.17/0.98  
% 1.17/0.98  ------ AIG Options
% 1.17/0.98  
% 1.17/0.98  --aig_mode                              false
% 1.17/0.98  
% 1.17/0.98  ------ Instantiation Options
% 1.17/0.98  
% 1.17/0.98  --instantiation_flag                    true
% 1.17/0.98  --inst_sos_flag                         false
% 1.17/0.98  --inst_sos_phase                        true
% 1.17/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.17/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.17/0.98  --inst_lit_sel_side                     none
% 1.17/0.98  --inst_solver_per_active                1400
% 1.17/0.98  --inst_solver_calls_frac                1.
% 1.17/0.98  --inst_passive_queue_type               priority_queues
% 1.17/0.98  --inst_passive_queues                   [[-num_var];[+age;-num_symb]]
% 1.17/0.98  --inst_passive_queues_freq              [25;2]
% 1.17/0.98  --inst_dismatching                      true
% 1.17/0.98  --inst_eager_unprocessed_to_passive     true
% 1.17/0.98  --inst_prop_sim_given                   true
% 1.17/0.98  --inst_prop_sim_new                     false
% 1.17/0.98  --inst_subs_new                         false
% 1.17/0.98  --inst_eq_res_simp                      false
% 1.17/0.98  --inst_subs_given                       false
% 1.17/0.98  --inst_orphan_elimination               true
% 1.17/0.98  --inst_learning_loop_flag               true
% 1.17/0.98  --inst_learning_start                   3000
% 1.17/0.98  --inst_learning_factor                  2
% 1.17/0.98  --inst_start_prop_sim_after_learn       3
% 1.17/0.98  --inst_sel_renew                        solver
% 1.17/0.98  --inst_lit_activity_flag                true
% 1.17/0.98  --inst_restr_to_given                   false
% 1.17/0.98  --inst_activity_threshold               500
% 1.17/0.98  --inst_out_proof                        true
% 1.17/0.98  
% 1.17/0.98  ------ Resolution Options
% 1.17/0.98  
% 1.17/0.98  --resolution_flag                       false
% 1.17/0.98  --res_lit_sel                           adaptive
% 1.17/0.98  --res_lit_sel_side                      none
% 1.17/0.98  --res_ordering                          kbo
% 1.17/0.98  --res_to_prop_solver                    active
% 1.17/0.98  --res_prop_simpl_new                    false
% 1.17/0.98  --res_prop_simpl_given                  true
% 1.17/0.98  --res_passive_queue_type                priority_queues
% 1.17/0.98  --res_passive_queues                    [[-num_symb];[+age;-num_symb]]
% 1.17/0.98  --res_passive_queues_freq               [15;5]
% 1.17/0.98  --res_forward_subs                      full
% 1.17/0.98  --res_backward_subs                     full
% 1.17/0.98  --res_forward_subs_resolution           true
% 1.17/0.98  --res_backward_subs_resolution          true
% 1.17/0.98  --res_orphan_elimination                true
% 1.17/0.98  --res_time_limit                        2.
% 1.17/0.98  --res_out_proof                         true
% 1.17/0.98  
% 1.17/0.98  ------ Superposition Options
% 1.17/0.98  
% 1.17/0.98  --superposition_flag                    true
% 1.17/0.98  --sup_passive_queue_type                priority_queues
% 1.17/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.17/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.17/0.98  --demod_completeness_check              fast
% 1.17/0.98  --demod_use_ground                      true
% 1.17/0.98  --sup_to_prop_solver                    passive
% 1.17/0.98  --sup_prop_simpl_new                    true
% 1.17/0.98  --sup_prop_simpl_given                  true
% 1.17/0.98  --sup_fun_splitting                     false
% 1.17/0.98  --sup_smt_interval                      50000
% 1.17/0.98  
% 1.17/0.98  ------ Superposition Simplification Setup
% 1.17/0.98  
% 1.17/0.98  --sup_indices_passive                   []
% 1.17/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.17/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.17/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.17/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.17/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.17/0.98  --sup_full_bw                           [BwDemod]
% 1.17/0.98  --sup_immed_triv                        [TrivRules]
% 1.17/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.17/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.17/0.98  --sup_immed_bw_main                     []
% 1.17/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.17/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.17/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.17/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.17/0.98  
% 1.17/0.98  ------ Combination Options
% 1.17/0.98  
% 1.17/0.98  --comb_res_mult                         3
% 1.17/0.98  --comb_sup_mult                         2
% 1.17/0.98  --comb_inst_mult                        10
% 1.17/0.98  
% 1.17/0.98  ------ Debug Options
% 1.17/0.98  
% 1.17/0.98  --dbg_backtrace                         false
% 1.17/0.98  --dbg_dump_prop_clauses                 false
% 1.17/0.98  --dbg_dump_prop_clauses_file            -
% 1.17/0.98  --dbg_out_stat                          false
% 1.17/0.98  
% 1.17/0.98  
% 1.17/0.98  
% 1.17/0.98  
% 1.17/0.98  ------ Proving...
% 1.17/0.98  
% 1.17/0.98  
% 1.17/0.98  % SZS status Theorem for theBenchmark.p
% 1.17/0.98  
% 1.17/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 1.17/0.98  
% 1.17/0.98  fof(f2,axiom,(
% 1.17/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v8_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_compts_1(X1,X0) => (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_xboole_0(X3,X4) & r1_tarski(X1,X4) & r2_hidden(X2,X3) & v3_pre_topc(X4,X0) & v3_pre_topc(X3,X0)))) & r2_hidden(X2,k3_subset_1(u1_struct_0(X0),X1)))) | k1_xboole_0 = X1)))))),
% 1.17/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.17/0.98  
% 1.17/0.98  fof(f8,plain,(
% 1.17/0.98    ! [X0] : ((! [X1] : (((! [X2] : ((? [X3] : (? [X4] : ((r1_xboole_0(X3,X4) & r1_tarski(X1,X4) & r2_hidden(X2,X3) & v3_pre_topc(X4,X0) & v3_pre_topc(X3,X0)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | k1_xboole_0 = X1) | ~v2_compts_1(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~v8_pre_topc(X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.17/0.98    inference(ennf_transformation,[],[f2])).
% 1.17/0.98  
% 1.17/0.98  fof(f9,plain,(
% 1.17/0.98    ! [X0] : (! [X1] : (! [X2] : (? [X3] : (? [X4] : (r1_xboole_0(X3,X4) & r1_tarski(X1,X4) & r2_hidden(X2,X3) & v3_pre_topc(X4,X0) & v3_pre_topc(X3,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,k3_subset_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | k1_xboole_0 = X1 | ~v2_compts_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~v8_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.17/0.98    inference(flattening,[],[f8])).
% 1.17/0.98  
% 1.17/0.98  fof(f26,plain,(
% 1.17/0.98    ( ! [X3] : (! [X2,X1,X0] : (? [X4] : (r1_xboole_0(X3,X4) & r1_tarski(X1,X4) & r2_hidden(X2,X3) & v3_pre_topc(X4,X0) & v3_pre_topc(X3,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) => (r1_xboole_0(X3,sK7(X0,X1,X2)) & r1_tarski(X1,sK7(X0,X1,X2)) & r2_hidden(X2,X3) & v3_pre_topc(sK7(X0,X1,X2),X0) & v3_pre_topc(X3,X0) & m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))) )),
% 1.17/0.98    introduced(choice_axiom,[])).
% 1.17/0.98  
% 1.17/0.98  fof(f25,plain,(
% 1.17/0.98    ! [X2,X1,X0] : (? [X3] : (? [X4] : (r1_xboole_0(X3,X4) & r1_tarski(X1,X4) & r2_hidden(X2,X3) & v3_pre_topc(X4,X0) & v3_pre_topc(X3,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X4] : (r1_xboole_0(sK6(X0,X1,X2),X4) & r1_tarski(X1,X4) & r2_hidden(X2,sK6(X0,X1,X2)) & v3_pre_topc(X4,X0) & v3_pre_topc(sK6(X0,X1,X2),X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.17/0.98    introduced(choice_axiom,[])).
% 1.17/0.98  
% 1.17/0.98  fof(f27,plain,(
% 1.17/0.98    ! [X0] : (! [X1] : (! [X2] : (((r1_xboole_0(sK6(X0,X1,X2),sK7(X0,X1,X2)) & r1_tarski(X1,sK7(X0,X1,X2)) & r2_hidden(X2,sK6(X0,X1,X2)) & v3_pre_topc(sK7(X0,X1,X2),X0) & v3_pre_topc(sK6(X0,X1,X2),X0) & m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,k3_subset_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | k1_xboole_0 = X1 | ~v2_compts_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~v8_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.17/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f9,f26,f25])).
% 1.17/0.98  
% 1.17/0.98  fof(f51,plain,(
% 1.17/0.98    ( ! [X2,X0,X1] : (r1_tarski(X1,sK7(X0,X1,X2)) | ~r2_hidden(X2,k3_subset_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k1_xboole_0 = X1 | ~v2_compts_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v8_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.17/0.98    inference(cnf_transformation,[],[f27])).
% 1.17/0.98  
% 1.17/0.98  fof(f4,conjecture,(
% 1.17/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ((v1_compts_1(X0) & v8_pre_topc(X0)) => v9_pre_topc(X0)))),
% 1.17/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.17/0.98  
% 1.17/0.98  fof(f5,negated_conjecture,(
% 1.17/0.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ((v1_compts_1(X0) & v8_pre_topc(X0)) => v9_pre_topc(X0)))),
% 1.17/0.98    inference(negated_conjecture,[],[f4])).
% 1.17/0.98  
% 1.17/0.98  fof(f12,plain,(
% 1.17/0.98    ? [X0] : ((~v9_pre_topc(X0) & (v1_compts_1(X0) & v8_pre_topc(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.17/0.98    inference(ennf_transformation,[],[f5])).
% 1.17/0.98  
% 1.17/0.98  fof(f13,plain,(
% 1.17/0.98    ? [X0] : (~v9_pre_topc(X0) & v1_compts_1(X0) & v8_pre_topc(X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.17/0.98    inference(flattening,[],[f12])).
% 1.17/0.98  
% 1.17/0.98  fof(f28,plain,(
% 1.17/0.98    ? [X0] : (~v9_pre_topc(X0) & v1_compts_1(X0) & v8_pre_topc(X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (~v9_pre_topc(sK8) & v1_compts_1(sK8) & v8_pre_topc(sK8) & l1_pre_topc(sK8) & v2_pre_topc(sK8) & ~v2_struct_0(sK8))),
% 1.17/0.98    introduced(choice_axiom,[])).
% 1.17/0.98  
% 1.17/0.98  fof(f29,plain,(
% 1.17/0.98    ~v9_pre_topc(sK8) & v1_compts_1(sK8) & v8_pre_topc(sK8) & l1_pre_topc(sK8) & v2_pre_topc(sK8) & ~v2_struct_0(sK8)),
% 1.17/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f13,f28])).
% 1.17/0.98  
% 1.17/0.98  fof(f56,plain,(
% 1.17/0.98    l1_pre_topc(sK8)),
% 1.17/0.98    inference(cnf_transformation,[],[f29])).
% 1.17/0.98  
% 1.17/0.98  fof(f55,plain,(
% 1.17/0.98    v2_pre_topc(sK8)),
% 1.17/0.98    inference(cnf_transformation,[],[f29])).
% 1.17/0.98  
% 1.17/0.98  fof(f57,plain,(
% 1.17/0.98    v8_pre_topc(sK8)),
% 1.17/0.98    inference(cnf_transformation,[],[f29])).
% 1.17/0.98  
% 1.17/0.98  fof(f14,plain,(
% 1.17/0.98    ! [X0] : (sP0(X0) <=> ! [X1] : (! [X2] : (? [X3] : (? [X4] : (r1_xboole_0(X3,X4) & r1_tarski(X2,X4) & r2_hidden(X1,X3) & v3_pre_topc(X4,X0) & v3_pre_topc(X3,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k3_subset_1(u1_struct_0(X0),X2)) | ~v4_pre_topc(X2,X0) | k1_xboole_0 = X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))))),
% 1.17/0.98    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.17/0.98  
% 1.17/0.98  fof(f18,plain,(
% 1.17/0.98    ! [X0] : ((sP0(X0) | ? [X1] : (? [X2] : (! [X3] : (! [X4] : (~r1_xboole_0(X3,X4) | ~r1_tarski(X2,X4) | ~r2_hidden(X1,X3) | ~v3_pre_topc(X4,X0) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X1,k3_subset_1(u1_struct_0(X0),X2)) & v4_pre_topc(X2,X0) & k1_xboole_0 != X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (? [X3] : (? [X4] : (r1_xboole_0(X3,X4) & r1_tarski(X2,X4) & r2_hidden(X1,X3) & v3_pre_topc(X4,X0) & v3_pre_topc(X3,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k3_subset_1(u1_struct_0(X0),X2)) | ~v4_pre_topc(X2,X0) | k1_xboole_0 = X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~sP0(X0)))),
% 1.17/0.98    inference(nnf_transformation,[],[f14])).
% 1.17/0.98  
% 1.17/0.98  fof(f19,plain,(
% 1.17/0.98    ! [X0] : ((sP0(X0) | ? [X1] : (? [X2] : (! [X3] : (! [X4] : (~r1_xboole_0(X3,X4) | ~r1_tarski(X2,X4) | ~r2_hidden(X1,X3) | ~v3_pre_topc(X4,X0) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X1,k3_subset_1(u1_struct_0(X0),X2)) & v4_pre_topc(X2,X0) & k1_xboole_0 != X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X5] : (! [X6] : (? [X7] : (? [X8] : (r1_xboole_0(X7,X8) & r1_tarski(X6,X8) & r2_hidden(X5,X7) & v3_pre_topc(X8,X0) & v3_pre_topc(X7,X0) & m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X5,k3_subset_1(u1_struct_0(X0),X6)) | ~v4_pre_topc(X6,X0) | k1_xboole_0 = X6 | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~sP0(X0)))),
% 1.17/0.98    inference(rectify,[],[f18])).
% 1.17/0.98  
% 1.17/0.98  fof(f23,plain,(
% 1.17/0.98    ( ! [X7] : (! [X6,X5,X0] : (? [X8] : (r1_xboole_0(X7,X8) & r1_tarski(X6,X8) & r2_hidden(X5,X7) & v3_pre_topc(X8,X0) & v3_pre_topc(X7,X0) & m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X0)))) => (r1_xboole_0(X7,sK5(X0,X5,X6)) & r1_tarski(X6,sK5(X0,X5,X6)) & r2_hidden(X5,X7) & v3_pre_topc(sK5(X0,X5,X6),X0) & v3_pre_topc(X7,X0) & m1_subset_1(sK5(X0,X5,X6),k1_zfmisc_1(u1_struct_0(X0)))))) )),
% 1.17/0.98    introduced(choice_axiom,[])).
% 1.17/0.98  
% 1.17/0.98  fof(f22,plain,(
% 1.17/0.98    ! [X6,X5,X0] : (? [X7] : (? [X8] : (r1_xboole_0(X7,X8) & r1_tarski(X6,X8) & r2_hidden(X5,X7) & v3_pre_topc(X8,X0) & v3_pre_topc(X7,X0) & m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X8] : (r1_xboole_0(sK4(X0,X5,X6),X8) & r1_tarski(X6,X8) & r2_hidden(X5,sK4(X0,X5,X6)) & v3_pre_topc(X8,X0) & v3_pre_topc(sK4(X0,X5,X6),X0) & m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK4(X0,X5,X6),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.17/0.98    introduced(choice_axiom,[])).
% 1.17/0.98  
% 1.17/0.98  fof(f21,plain,(
% 1.17/0.98    ( ! [X1] : (! [X0] : (? [X2] : (! [X3] : (! [X4] : (~r1_xboole_0(X3,X4) | ~r1_tarski(X2,X4) | ~r2_hidden(X1,X3) | ~v3_pre_topc(X4,X0) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X1,k3_subset_1(u1_struct_0(X0),X2)) & v4_pre_topc(X2,X0) & k1_xboole_0 != X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (! [X3] : (! [X4] : (~r1_xboole_0(X3,X4) | ~r1_tarski(sK3(X0),X4) | ~r2_hidden(X1,X3) | ~v3_pre_topc(X4,X0) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X1,k3_subset_1(u1_struct_0(X0),sK3(X0))) & v4_pre_topc(sK3(X0),X0) & k1_xboole_0 != sK3(X0) & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))))) )),
% 1.17/0.98    introduced(choice_axiom,[])).
% 1.17/0.98  
% 1.17/0.98  fof(f20,plain,(
% 1.17/0.98    ! [X0] : (? [X1] : (? [X2] : (! [X3] : (! [X4] : (~r1_xboole_0(X3,X4) | ~r1_tarski(X2,X4) | ~r2_hidden(X1,X3) | ~v3_pre_topc(X4,X0) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X1,k3_subset_1(u1_struct_0(X0),X2)) & v4_pre_topc(X2,X0) & k1_xboole_0 != X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (! [X3] : (! [X4] : (~r1_xboole_0(X3,X4) | ~r1_tarski(X2,X4) | ~r2_hidden(sK2(X0),X3) | ~v3_pre_topc(X4,X0) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(sK2(X0),k3_subset_1(u1_struct_0(X0),X2)) & v4_pre_topc(X2,X0) & k1_xboole_0 != X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK2(X0),u1_struct_0(X0))))),
% 1.17/0.98    introduced(choice_axiom,[])).
% 1.17/0.98  
% 1.17/0.98  fof(f24,plain,(
% 1.17/0.98    ! [X0] : ((sP0(X0) | ((! [X3] : (! [X4] : (~r1_xboole_0(X3,X4) | ~r1_tarski(sK3(X0),X4) | ~r2_hidden(sK2(X0),X3) | ~v3_pre_topc(X4,X0) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(sK2(X0),k3_subset_1(u1_struct_0(X0),sK3(X0))) & v4_pre_topc(sK3(X0),X0) & k1_xboole_0 != sK3(X0) & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK2(X0),u1_struct_0(X0)))) & (! [X5] : (! [X6] : (((r1_xboole_0(sK4(X0,X5,X6),sK5(X0,X5,X6)) & r1_tarski(X6,sK5(X0,X5,X6)) & r2_hidden(X5,sK4(X0,X5,X6)) & v3_pre_topc(sK5(X0,X5,X6),X0) & v3_pre_topc(sK4(X0,X5,X6),X0) & m1_subset_1(sK5(X0,X5,X6),k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK4(X0,X5,X6),k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X5,k3_subset_1(u1_struct_0(X0),X6)) | ~v4_pre_topc(X6,X0) | k1_xboole_0 = X6 | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~sP0(X0)))),
% 1.17/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f19,f23,f22,f21,f20])).
% 1.17/0.98  
% 1.17/0.98  fof(f44,plain,(
% 1.17/0.98    ( ! [X4,X0,X3] : (sP0(X0) | ~r1_xboole_0(X3,X4) | ~r1_tarski(sK3(X0),X4) | ~r2_hidden(sK2(X0),X3) | ~v3_pre_topc(X4,X0) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 1.17/0.98    inference(cnf_transformation,[],[f24])).
% 1.17/0.98  
% 1.17/0.98  fof(f15,plain,(
% 1.17/0.98    ! [X0] : ((v9_pre_topc(X0) <=> sP0(X0)) | ~sP1(X0))),
% 1.17/0.98    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.17/0.98  
% 1.17/0.98  fof(f17,plain,(
% 1.17/0.98    ! [X0] : (((v9_pre_topc(X0) | ~sP0(X0)) & (sP0(X0) | ~v9_pre_topc(X0))) | ~sP1(X0))),
% 1.17/0.98    inference(nnf_transformation,[],[f15])).
% 1.17/0.98  
% 1.17/0.98  fof(f31,plain,(
% 1.17/0.98    ( ! [X0] : (v9_pre_topc(X0) | ~sP0(X0) | ~sP1(X0)) )),
% 1.17/0.98    inference(cnf_transformation,[],[f17])).
% 1.17/0.98  
% 1.17/0.98  fof(f1,axiom,(
% 1.17/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v9_pre_topc(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_xboole_0(X3,X4) & r1_tarski(X2,X4) & r2_hidden(X1,X3) & v3_pre_topc(X4,X0) & v3_pre_topc(X3,X0)))) & r2_hidden(X1,k3_subset_1(u1_struct_0(X0),X2)) & v4_pre_topc(X2,X0) & k1_xboole_0 != X2)))))),
% 1.17/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.17/0.98  
% 1.17/0.98  fof(f6,plain,(
% 1.17/0.98    ! [X0] : ((v9_pre_topc(X0) <=> ! [X1] : (! [X2] : ((? [X3] : (? [X4] : ((r1_xboole_0(X3,X4) & r1_tarski(X2,X4) & r2_hidden(X1,X3) & v3_pre_topc(X4,X0) & v3_pre_topc(X3,X0)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k3_subset_1(u1_struct_0(X0),X2)) | ~v4_pre_topc(X2,X0) | k1_xboole_0 = X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.17/0.98    inference(ennf_transformation,[],[f1])).
% 1.17/0.98  
% 1.17/0.98  fof(f7,plain,(
% 1.17/0.98    ! [X0] : ((v9_pre_topc(X0) <=> ! [X1] : (! [X2] : (? [X3] : (? [X4] : (r1_xboole_0(X3,X4) & r1_tarski(X2,X4) & r2_hidden(X1,X3) & v3_pre_topc(X4,X0) & v3_pre_topc(X3,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k3_subset_1(u1_struct_0(X0),X2)) | ~v4_pre_topc(X2,X0) | k1_xboole_0 = X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.17/0.98    inference(flattening,[],[f6])).
% 1.17/0.98  
% 1.17/0.98  fof(f16,plain,(
% 1.17/0.98    ! [X0] : (sP1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.17/0.98    inference(definition_folding,[],[f7,f15,f14])).
% 1.17/0.98  
% 1.17/0.98  fof(f45,plain,(
% 1.17/0.98    ( ! [X0] : (sP1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.17/0.98    inference(cnf_transformation,[],[f16])).
% 1.17/0.98  
% 1.17/0.98  fof(f54,plain,(
% 1.17/0.98    ~v2_struct_0(sK8)),
% 1.17/0.98    inference(cnf_transformation,[],[f29])).
% 1.17/0.98  
% 1.17/0.98  fof(f59,plain,(
% 1.17/0.98    ~v9_pre_topc(sK8)),
% 1.17/0.98    inference(cnf_transformation,[],[f29])).
% 1.17/0.98  
% 1.17/0.98  fof(f52,plain,(
% 1.17/0.98    ( ! [X2,X0,X1] : (r1_xboole_0(sK6(X0,X1,X2),sK7(X0,X1,X2)) | ~r2_hidden(X2,k3_subset_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k1_xboole_0 = X1 | ~v2_compts_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v8_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.17/0.98    inference(cnf_transformation,[],[f27])).
% 1.17/0.98  
% 1.17/0.98  fof(f46,plain,(
% 1.17/0.98    ( ! [X2,X0,X1] : (m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X2,k3_subset_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k1_xboole_0 = X1 | ~v2_compts_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v8_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.17/0.98    inference(cnf_transformation,[],[f27])).
% 1.17/0.98  
% 1.17/0.98  fof(f47,plain,(
% 1.17/0.98    ( ! [X2,X0,X1] : (m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X2,k3_subset_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k1_xboole_0 = X1 | ~v2_compts_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v8_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.17/0.98    inference(cnf_transformation,[],[f27])).
% 1.17/0.98  
% 1.17/0.98  fof(f48,plain,(
% 1.17/0.98    ( ! [X2,X0,X1] : (v3_pre_topc(sK6(X0,X1,X2),X0) | ~r2_hidden(X2,k3_subset_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k1_xboole_0 = X1 | ~v2_compts_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v8_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.17/0.98    inference(cnf_transformation,[],[f27])).
% 1.17/0.98  
% 1.17/0.98  fof(f49,plain,(
% 1.17/0.98    ( ! [X2,X0,X1] : (v3_pre_topc(sK7(X0,X1,X2),X0) | ~r2_hidden(X2,k3_subset_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k1_xboole_0 = X1 | ~v2_compts_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v8_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.17/0.98    inference(cnf_transformation,[],[f27])).
% 1.17/0.98  
% 1.17/0.98  fof(f42,plain,(
% 1.17/0.98    ( ! [X0] : (sP0(X0) | v4_pre_topc(sK3(X0),X0)) )),
% 1.17/0.98    inference(cnf_transformation,[],[f24])).
% 1.17/0.98  
% 1.17/0.98  fof(f3,axiom,(
% 1.17/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X1,X0) & v1_compts_1(X0)) => v2_compts_1(X1,X0))))),
% 1.17/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.17/0.98  
% 1.17/0.98  fof(f10,plain,(
% 1.17/0.98    ! [X0] : (! [X1] : ((v2_compts_1(X1,X0) | (~v4_pre_topc(X1,X0) | ~v1_compts_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.17/0.98    inference(ennf_transformation,[],[f3])).
% 1.17/0.98  
% 1.17/0.98  fof(f11,plain,(
% 1.17/0.98    ! [X0] : (! [X1] : (v2_compts_1(X1,X0) | ~v4_pre_topc(X1,X0) | ~v1_compts_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.17/0.98    inference(flattening,[],[f10])).
% 1.17/0.98  
% 1.17/0.98  fof(f53,plain,(
% 1.17/0.98    ( ! [X0,X1] : (v2_compts_1(X1,X0) | ~v4_pre_topc(X1,X0) | ~v1_compts_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.17/0.98    inference(cnf_transformation,[],[f11])).
% 1.17/0.98  
% 1.17/0.98  fof(f58,plain,(
% 1.17/0.98    v1_compts_1(sK8)),
% 1.17/0.98    inference(cnf_transformation,[],[f29])).
% 1.17/0.98  
% 1.17/0.98  fof(f40,plain,(
% 1.17/0.98    ( ! [X0] : (sP0(X0) | m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 1.17/0.98    inference(cnf_transformation,[],[f24])).
% 1.17/0.98  
% 1.17/0.98  fof(f41,plain,(
% 1.17/0.98    ( ! [X0] : (sP0(X0) | k1_xboole_0 != sK3(X0)) )),
% 1.17/0.98    inference(cnf_transformation,[],[f24])).
% 1.17/0.98  
% 1.17/0.98  fof(f50,plain,(
% 1.17/0.98    ( ! [X2,X0,X1] : (r2_hidden(X2,sK6(X0,X1,X2)) | ~r2_hidden(X2,k3_subset_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k1_xboole_0 = X1 | ~v2_compts_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v8_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.17/0.98    inference(cnf_transformation,[],[f27])).
% 1.17/0.98  
% 1.17/0.98  fof(f43,plain,(
% 1.17/0.98    ( ! [X0] : (sP0(X0) | r2_hidden(sK2(X0),k3_subset_1(u1_struct_0(X0),sK3(X0)))) )),
% 1.17/0.98    inference(cnf_transformation,[],[f24])).
% 1.17/0.98  
% 1.17/0.98  fof(f39,plain,(
% 1.17/0.98    ( ! [X0] : (sP0(X0) | m1_subset_1(sK2(X0),u1_struct_0(X0))) )),
% 1.17/0.98    inference(cnf_transformation,[],[f24])).
% 1.17/0.98  
% 1.17/0.98  cnf(c_1322,plain,( X0_54 = X0_54 ),theory(equality) ).
% 1.17/0.98  
% 1.17/0.98  cnf(c_1626,plain,
% 1.17/0.98      ( sK7(sK8,sK3(sK8),sK2(sK8)) = sK7(sK8,sK3(sK8),sK2(sK8)) ),
% 1.17/0.98      inference(instantiation,[status(thm)],[c_1322]) ).
% 1.17/0.98  
% 1.17/0.98  cnf(c_17,plain,
% 1.17/0.98      ( ~ v2_compts_1(X0,X1)
% 1.17/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.17/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.17/0.98      | ~ r2_hidden(X2,k3_subset_1(u1_struct_0(X1),X0))
% 1.17/0.98      | r1_tarski(X0,sK7(X1,X0,X2))
% 1.17/0.98      | ~ v8_pre_topc(X1)
% 1.17/0.98      | ~ v2_pre_topc(X1)
% 1.17/0.98      | ~ l1_pre_topc(X1)
% 1.17/0.98      | k1_xboole_0 = X0 ),
% 1.17/0.98      inference(cnf_transformation,[],[f51]) ).
% 1.17/0.98  
% 1.17/0.98  cnf(c_27,negated_conjecture,
% 1.17/0.98      ( l1_pre_topc(sK8) ),
% 1.17/0.98      inference(cnf_transformation,[],[f56]) ).
% 1.17/0.98  
% 1.17/0.98  cnf(c_928,plain,
% 1.17/0.98      ( ~ v2_compts_1(X0,X1)
% 1.17/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.17/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.17/0.98      | ~ r2_hidden(X2,k3_subset_1(u1_struct_0(X1),X0))
% 1.17/0.98      | r1_tarski(X0,sK7(X1,X0,X2))
% 1.17/0.98      | ~ v8_pre_topc(X1)
% 1.17/0.98      | ~ v2_pre_topc(X1)
% 1.17/0.98      | sK8 != X1
% 1.17/0.98      | k1_xboole_0 = X0 ),
% 1.17/0.98      inference(resolution_lifted,[status(thm)],[c_17,c_27]) ).
% 1.17/0.98  
% 1.17/0.98  cnf(c_929,plain,
% 1.17/0.98      ( ~ v2_compts_1(X0,sK8)
% 1.17/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
% 1.17/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 1.17/0.98      | ~ r2_hidden(X1,k3_subset_1(u1_struct_0(sK8),X0))
% 1.17/0.98      | r1_tarski(X0,sK7(sK8,X0,X1))
% 1.17/0.98      | ~ v8_pre_topc(sK8)
% 1.17/0.98      | ~ v2_pre_topc(sK8)
% 1.17/0.98      | k1_xboole_0 = X0 ),
% 1.17/0.98      inference(unflattening,[status(thm)],[c_928]) ).
% 1.17/0.98  
% 1.17/0.98  cnf(c_28,negated_conjecture,
% 1.17/0.98      ( v2_pre_topc(sK8) ),
% 1.17/0.98      inference(cnf_transformation,[],[f55]) ).
% 1.17/0.98  
% 1.17/0.98  cnf(c_26,negated_conjecture,
% 1.17/0.98      ( v8_pre_topc(sK8) ),
% 1.17/0.98      inference(cnf_transformation,[],[f57]) ).
% 1.17/0.98  
% 1.17/0.98  cnf(c_933,plain,
% 1.17/0.98      ( ~ v2_compts_1(X0,sK8)
% 1.17/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
% 1.17/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 1.17/0.98      | ~ r2_hidden(X1,k3_subset_1(u1_struct_0(sK8),X0))
% 1.17/0.98      | r1_tarski(X0,sK7(sK8,X0,X1))
% 1.17/0.98      | k1_xboole_0 = X0 ),
% 1.17/0.98      inference(global_propositional_subsumption,
% 1.17/0.98                [status(thm)],
% 1.17/0.98                [c_929,c_28,c_26]) ).
% 1.17/0.98  
% 1.17/0.98  cnf(c_2,plain,
% 1.17/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.17/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.17/0.98      | ~ v3_pre_topc(X0,X1)
% 1.17/0.98      | ~ v3_pre_topc(X2,X1)
% 1.17/0.98      | ~ r2_hidden(sK2(X1),X2)
% 1.17/0.98      | ~ r1_tarski(sK3(X1),X0)
% 1.17/0.98      | ~ r1_xboole_0(X2,X0)
% 1.17/0.98      | sP0(X1) ),
% 1.17/0.98      inference(cnf_transformation,[],[f44]) ).
% 1.17/0.98  
% 1.17/0.98  cnf(c_0,plain,
% 1.17/0.98      ( ~ sP1(X0) | ~ sP0(X0) | v9_pre_topc(X0) ),
% 1.17/0.98      inference(cnf_transformation,[],[f31]) ).
% 1.17/0.98  
% 1.17/0.98  cnf(c_15,plain,
% 1.17/0.98      ( v2_struct_0(X0)
% 1.17/0.98      | ~ v2_pre_topc(X0)
% 1.17/0.98      | ~ l1_pre_topc(X0)
% 1.17/0.98      | sP1(X0) ),
% 1.17/0.98      inference(cnf_transformation,[],[f45]) ).
% 1.17/0.98  
% 1.17/0.98  cnf(c_29,negated_conjecture,
% 1.17/0.98      ( ~ v2_struct_0(sK8) ),
% 1.17/0.98      inference(cnf_transformation,[],[f54]) ).
% 1.17/0.98  
% 1.17/0.98  cnf(c_340,plain,
% 1.17/0.98      ( ~ v2_pre_topc(X0) | ~ l1_pre_topc(X0) | sP1(X0) | sK8 != X0 ),
% 1.17/0.98      inference(resolution_lifted,[status(thm)],[c_15,c_29]) ).
% 1.17/0.98  
% 1.17/0.98  cnf(c_341,plain,
% 1.17/0.98      ( ~ v2_pre_topc(sK8) | ~ l1_pre_topc(sK8) | sP1(sK8) ),
% 1.17/0.98      inference(unflattening,[status(thm)],[c_340]) ).
% 1.17/0.98  
% 1.17/0.98  cnf(c_343,plain,
% 1.17/0.98      ( sP1(sK8) ),
% 1.17/0.98      inference(global_propositional_subsumption,
% 1.17/0.98                [status(thm)],
% 1.17/0.98                [c_341,c_28,c_27]) ).
% 1.17/0.98  
% 1.17/0.98  cnf(c_355,plain,
% 1.17/0.98      ( ~ sP0(X0) | v9_pre_topc(X0) | sK8 != X0 ),
% 1.17/0.98      inference(resolution_lifted,[status(thm)],[c_0,c_343]) ).
% 1.17/0.98  
% 1.17/0.98  cnf(c_356,plain,
% 1.17/0.98      ( ~ sP0(sK8) | v9_pre_topc(sK8) ),
% 1.17/0.98      inference(unflattening,[status(thm)],[c_355]) ).
% 1.17/0.98  
% 1.17/0.98  cnf(c_24,negated_conjecture,
% 1.17/0.98      ( ~ v9_pre_topc(sK8) ),
% 1.17/0.98      inference(cnf_transformation,[],[f59]) ).
% 1.17/0.98  
% 1.17/0.98  cnf(c_358,plain,
% 1.17/0.98      ( ~ sP0(sK8) ),
% 1.17/0.98      inference(global_propositional_subsumption,
% 1.17/0.98                [status(thm)],
% 1.17/0.98                [c_356,c_24]) ).
% 1.17/0.98  
% 1.17/0.98  cnf(c_638,plain,
% 1.17/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.17/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.17/0.98      | ~ v3_pre_topc(X0,X1)
% 1.17/0.98      | ~ v3_pre_topc(X2,X1)
% 1.17/0.98      | ~ r2_hidden(sK2(X1),X2)
% 1.17/0.98      | ~ r1_tarski(sK3(X1),X0)
% 1.17/0.98      | ~ r1_xboole_0(X2,X0)
% 1.17/0.98      | sK8 != X1 ),
% 1.17/0.98      inference(resolution_lifted,[status(thm)],[c_2,c_358]) ).
% 1.17/0.98  
% 1.17/0.98  cnf(c_639,plain,
% 1.17/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
% 1.17/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8)))
% 1.17/0.98      | ~ v3_pre_topc(X1,sK8)
% 1.17/0.98      | ~ v3_pre_topc(X0,sK8)
% 1.17/0.98      | ~ r2_hidden(sK2(sK8),X1)
% 1.17/0.98      | ~ r1_tarski(sK3(sK8),X0)
% 1.17/0.98      | ~ r1_xboole_0(X1,X0) ),
% 1.17/0.98      inference(unflattening,[status(thm)],[c_638]) ).
% 1.17/0.98  
% 1.17/0.98  cnf(c_16,plain,
% 1.17/0.98      ( ~ v2_compts_1(X0,X1)
% 1.17/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.17/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.17/0.98      | ~ r2_hidden(X2,k3_subset_1(u1_struct_0(X1),X0))
% 1.17/0.98      | r1_xboole_0(sK6(X1,X0,X2),sK7(X1,X0,X2))
% 1.17/0.98      | ~ v8_pre_topc(X1)
% 1.17/0.98      | ~ v2_pre_topc(X1)
% 1.17/0.98      | ~ l1_pre_topc(X1)
% 1.17/0.98      | k1_xboole_0 = X0 ),
% 1.17/0.98      inference(cnf_transformation,[],[f52]) ).
% 1.17/0.98  
% 1.17/0.98  cnf(c_958,plain,
% 1.17/0.98      ( ~ v2_compts_1(X0,X1)
% 1.17/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.17/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.17/0.98      | ~ r2_hidden(X2,k3_subset_1(u1_struct_0(X1),X0))
% 1.17/0.98      | r1_xboole_0(sK6(X1,X0,X2),sK7(X1,X0,X2))
% 1.17/0.98      | ~ v8_pre_topc(X1)
% 1.17/0.98      | ~ v2_pre_topc(X1)
% 1.17/0.98      | sK8 != X1
% 1.17/0.98      | k1_xboole_0 = X0 ),
% 1.17/0.98      inference(resolution_lifted,[status(thm)],[c_16,c_27]) ).
% 1.17/0.98  
% 1.17/0.98  cnf(c_959,plain,
% 1.17/0.98      ( ~ v2_compts_1(X0,sK8)
% 1.17/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
% 1.17/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 1.17/0.98      | ~ r2_hidden(X1,k3_subset_1(u1_struct_0(sK8),X0))
% 1.17/0.98      | r1_xboole_0(sK6(sK8,X0,X1),sK7(sK8,X0,X1))
% 1.17/0.98      | ~ v8_pre_topc(sK8)
% 1.17/0.98      | ~ v2_pre_topc(sK8)
% 1.17/0.98      | k1_xboole_0 = X0 ),
% 1.17/0.98      inference(unflattening,[status(thm)],[c_958]) ).
% 1.17/0.98  
% 1.17/0.98  cnf(c_963,plain,
% 1.17/0.98      ( ~ v2_compts_1(X0,sK8)
% 1.17/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
% 1.17/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 1.17/0.98      | ~ r2_hidden(X1,k3_subset_1(u1_struct_0(sK8),X0))
% 1.17/0.98      | r1_xboole_0(sK6(sK8,X0,X1),sK7(sK8,X0,X1))
% 1.17/0.98      | k1_xboole_0 = X0 ),
% 1.17/0.98      inference(global_propositional_subsumption,
% 1.17/0.98                [status(thm)],
% 1.17/0.98                [c_959,c_28,c_26]) ).
% 1.17/0.98  
% 1.17/0.98  cnf(c_1037,plain,
% 1.17/0.98      ( ~ v2_compts_1(X0,sK8)
% 1.17/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8)))
% 1.17/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK8)))
% 1.17/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
% 1.17/0.98      | ~ m1_subset_1(X3,u1_struct_0(sK8))
% 1.17/0.98      | ~ v3_pre_topc(X1,sK8)
% 1.17/0.98      | ~ v3_pre_topc(X2,sK8)
% 1.17/0.98      | ~ r2_hidden(X3,k3_subset_1(u1_struct_0(sK8),X0))
% 1.17/0.98      | ~ r2_hidden(sK2(sK8),X2)
% 1.17/0.98      | ~ r1_tarski(sK3(sK8),X1)
% 1.17/0.98      | sK7(sK8,X0,X3) != X1
% 1.17/0.98      | sK6(sK8,X0,X3) != X2
% 1.17/0.98      | k1_xboole_0 = X0 ),
% 1.17/0.98      inference(resolution_lifted,[status(thm)],[c_639,c_963]) ).
% 1.17/0.98  
% 1.17/0.98  cnf(c_1038,plain,
% 1.17/0.98      ( ~ v2_compts_1(X0,sK8)
% 1.17/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
% 1.17/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 1.17/0.98      | ~ m1_subset_1(sK7(sK8,X0,X1),k1_zfmisc_1(u1_struct_0(sK8)))
% 1.17/0.98      | ~ m1_subset_1(sK6(sK8,X0,X1),k1_zfmisc_1(u1_struct_0(sK8)))
% 1.17/0.98      | ~ v3_pre_topc(sK7(sK8,X0,X1),sK8)
% 1.17/0.98      | ~ v3_pre_topc(sK6(sK8,X0,X1),sK8)
% 1.17/0.98      | ~ r2_hidden(X1,k3_subset_1(u1_struct_0(sK8),X0))
% 1.17/0.98      | ~ r2_hidden(sK2(sK8),sK6(sK8,X0,X1))
% 1.17/0.98      | ~ r1_tarski(sK3(sK8),sK7(sK8,X0,X1))
% 1.17/0.98      | k1_xboole_0 = X0 ),
% 1.17/0.98      inference(unflattening,[status(thm)],[c_1037]) ).
% 1.17/0.98  
% 1.17/0.98  cnf(c_22,plain,
% 1.17/0.98      ( ~ v2_compts_1(X0,X1)
% 1.17/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.17/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.17/0.98      | m1_subset_1(sK6(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
% 1.17/0.98      | ~ r2_hidden(X2,k3_subset_1(u1_struct_0(X1),X0))
% 1.17/0.98      | ~ v8_pre_topc(X1)
% 1.17/0.98      | ~ v2_pre_topc(X1)
% 1.17/0.98      | ~ l1_pre_topc(X1)
% 1.17/0.98      | k1_xboole_0 = X0 ),
% 1.17/0.98      inference(cnf_transformation,[],[f46]) ).
% 1.17/0.98  
% 1.17/0.98  cnf(c_778,plain,
% 1.17/0.98      ( ~ v2_compts_1(X0,X1)
% 1.17/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.17/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.17/0.98      | m1_subset_1(sK6(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
% 1.17/0.98      | ~ r2_hidden(X2,k3_subset_1(u1_struct_0(X1),X0))
% 1.17/0.98      | ~ v8_pre_topc(X1)
% 1.17/0.98      | ~ v2_pre_topc(X1)
% 1.17/0.98      | sK8 != X1
% 1.17/0.98      | k1_xboole_0 = X0 ),
% 1.17/0.98      inference(resolution_lifted,[status(thm)],[c_22,c_27]) ).
% 1.17/0.98  
% 1.17/0.98  cnf(c_779,plain,
% 1.17/0.98      ( ~ v2_compts_1(X0,sK8)
% 1.17/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
% 1.17/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 1.17/0.98      | m1_subset_1(sK6(sK8,X0,X1),k1_zfmisc_1(u1_struct_0(sK8)))
% 1.17/0.98      | ~ r2_hidden(X1,k3_subset_1(u1_struct_0(sK8),X0))
% 1.17/0.98      | ~ v8_pre_topc(sK8)
% 1.17/0.98      | ~ v2_pre_topc(sK8)
% 1.17/0.98      | k1_xboole_0 = X0 ),
% 1.17/0.98      inference(unflattening,[status(thm)],[c_778]) ).
% 1.17/0.98  
% 1.17/0.98  cnf(c_783,plain,
% 1.17/0.98      ( ~ v2_compts_1(X0,sK8)
% 1.17/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
% 1.17/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 1.17/0.98      | m1_subset_1(sK6(sK8,X0,X1),k1_zfmisc_1(u1_struct_0(sK8)))
% 1.17/0.98      | ~ r2_hidden(X1,k3_subset_1(u1_struct_0(sK8),X0))
% 1.17/0.98      | k1_xboole_0 = X0 ),
% 1.17/0.98      inference(global_propositional_subsumption,
% 1.17/0.98                [status(thm)],
% 1.17/0.98                [c_779,c_28,c_26]) ).
% 1.17/0.98  
% 1.17/0.98  cnf(c_21,plain,
% 1.17/0.98      ( ~ v2_compts_1(X0,X1)
% 1.17/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.17/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.17/0.98      | m1_subset_1(sK7(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
% 1.17/0.98      | ~ r2_hidden(X2,k3_subset_1(u1_struct_0(X1),X0))
% 1.17/0.98      | ~ v8_pre_topc(X1)
% 1.17/0.98      | ~ v2_pre_topc(X1)
% 1.17/0.98      | ~ l1_pre_topc(X1)
% 1.17/0.98      | k1_xboole_0 = X0 ),
% 1.17/0.98      inference(cnf_transformation,[],[f47]) ).
% 1.17/0.98  
% 1.17/0.98  cnf(c_808,plain,
% 1.17/0.98      ( ~ v2_compts_1(X0,X1)
% 1.17/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.17/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.17/0.98      | m1_subset_1(sK7(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
% 1.17/0.98      | ~ r2_hidden(X2,k3_subset_1(u1_struct_0(X1),X0))
% 1.17/0.98      | ~ v8_pre_topc(X1)
% 1.17/0.98      | ~ v2_pre_topc(X1)
% 1.17/0.98      | sK8 != X1
% 1.17/0.98      | k1_xboole_0 = X0 ),
% 1.17/0.98      inference(resolution_lifted,[status(thm)],[c_21,c_27]) ).
% 1.17/0.98  
% 1.17/0.98  cnf(c_809,plain,
% 1.17/0.98      ( ~ v2_compts_1(X0,sK8)
% 1.17/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
% 1.17/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 1.17/0.98      | m1_subset_1(sK7(sK8,X0,X1),k1_zfmisc_1(u1_struct_0(sK8)))
% 1.17/0.98      | ~ r2_hidden(X1,k3_subset_1(u1_struct_0(sK8),X0))
% 1.17/0.98      | ~ v8_pre_topc(sK8)
% 1.17/0.98      | ~ v2_pre_topc(sK8)
% 1.17/0.98      | k1_xboole_0 = X0 ),
% 1.17/0.98      inference(unflattening,[status(thm)],[c_808]) ).
% 1.17/0.98  
% 1.17/0.98  cnf(c_813,plain,
% 1.17/0.98      ( ~ v2_compts_1(X0,sK8)
% 1.17/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
% 1.17/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 1.17/0.98      | m1_subset_1(sK7(sK8,X0,X1),k1_zfmisc_1(u1_struct_0(sK8)))
% 1.17/0.98      | ~ r2_hidden(X1,k3_subset_1(u1_struct_0(sK8),X0))
% 1.17/0.98      | k1_xboole_0 = X0 ),
% 1.17/0.98      inference(global_propositional_subsumption,
% 1.17/0.98                [status(thm)],
% 1.17/0.98                [c_809,c_28,c_26]) ).
% 1.17/0.98  
% 1.17/0.98  cnf(c_20,plain,
% 1.17/0.98      ( ~ v2_compts_1(X0,X1)
% 1.17/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.17/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.17/0.98      | v3_pre_topc(sK6(X1,X0,X2),X1)
% 1.17/0.98      | ~ r2_hidden(X2,k3_subset_1(u1_struct_0(X1),X0))
% 1.17/0.98      | ~ v8_pre_topc(X1)
% 1.17/0.98      | ~ v2_pre_topc(X1)
% 1.17/0.98      | ~ l1_pre_topc(X1)
% 1.17/0.98      | k1_xboole_0 = X0 ),
% 1.17/0.98      inference(cnf_transformation,[],[f48]) ).
% 1.17/0.98  
% 1.17/0.98  cnf(c_838,plain,
% 1.17/0.98      ( ~ v2_compts_1(X0,X1)
% 1.17/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.17/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.17/0.98      | v3_pre_topc(sK6(X1,X0,X2),X1)
% 1.17/0.98      | ~ r2_hidden(X2,k3_subset_1(u1_struct_0(X1),X0))
% 1.17/0.98      | ~ v8_pre_topc(X1)
% 1.17/0.98      | ~ v2_pre_topc(X1)
% 1.17/0.98      | sK8 != X1
% 1.17/0.98      | k1_xboole_0 = X0 ),
% 1.17/0.98      inference(resolution_lifted,[status(thm)],[c_20,c_27]) ).
% 1.17/0.98  
% 1.17/0.98  cnf(c_839,plain,
% 1.17/0.98      ( ~ v2_compts_1(X0,sK8)
% 1.17/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
% 1.17/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 1.17/0.98      | v3_pre_topc(sK6(sK8,X0,X1),sK8)
% 1.17/0.98      | ~ r2_hidden(X1,k3_subset_1(u1_struct_0(sK8),X0))
% 1.17/0.98      | ~ v8_pre_topc(sK8)
% 1.17/0.98      | ~ v2_pre_topc(sK8)
% 1.17/0.98      | k1_xboole_0 = X0 ),
% 1.17/0.98      inference(unflattening,[status(thm)],[c_838]) ).
% 1.17/0.98  
% 1.17/0.98  cnf(c_843,plain,
% 1.17/0.98      ( ~ v2_compts_1(X0,sK8)
% 1.17/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
% 1.17/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 1.17/0.98      | v3_pre_topc(sK6(sK8,X0,X1),sK8)
% 1.17/0.98      | ~ r2_hidden(X1,k3_subset_1(u1_struct_0(sK8),X0))
% 1.17/0.98      | k1_xboole_0 = X0 ),
% 1.17/0.98      inference(global_propositional_subsumption,
% 1.17/0.98                [status(thm)],
% 1.17/0.98                [c_839,c_28,c_26]) ).
% 1.17/0.98  
% 1.17/0.98  cnf(c_19,plain,
% 1.17/0.98      ( ~ v2_compts_1(X0,X1)
% 1.17/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.17/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.17/0.98      | v3_pre_topc(sK7(X1,X0,X2),X1)
% 1.17/0.98      | ~ r2_hidden(X2,k3_subset_1(u1_struct_0(X1),X0))
% 1.17/0.98      | ~ v8_pre_topc(X1)
% 1.17/0.98      | ~ v2_pre_topc(X1)
% 1.17/0.98      | ~ l1_pre_topc(X1)
% 1.17/0.98      | k1_xboole_0 = X0 ),
% 1.17/0.98      inference(cnf_transformation,[],[f49]) ).
% 1.17/0.98  
% 1.17/0.98  cnf(c_868,plain,
% 1.17/0.98      ( ~ v2_compts_1(X0,X1)
% 1.17/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.17/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.17/0.98      | v3_pre_topc(sK7(X1,X0,X2),X1)
% 1.17/0.98      | ~ r2_hidden(X2,k3_subset_1(u1_struct_0(X1),X0))
% 1.17/0.98      | ~ v8_pre_topc(X1)
% 1.17/0.98      | ~ v2_pre_topc(X1)
% 1.17/0.98      | sK8 != X1
% 1.17/0.98      | k1_xboole_0 = X0 ),
% 1.17/0.98      inference(resolution_lifted,[status(thm)],[c_19,c_27]) ).
% 1.17/0.98  
% 1.17/0.98  cnf(c_869,plain,
% 1.17/0.98      ( ~ v2_compts_1(X0,sK8)
% 1.17/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
% 1.17/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 1.17/0.98      | v3_pre_topc(sK7(sK8,X0,X1),sK8)
% 1.17/0.98      | ~ r2_hidden(X1,k3_subset_1(u1_struct_0(sK8),X0))
% 1.17/0.98      | ~ v8_pre_topc(sK8)
% 1.17/0.98      | ~ v2_pre_topc(sK8)
% 1.17/0.98      | k1_xboole_0 = X0 ),
% 1.17/0.98      inference(unflattening,[status(thm)],[c_868]) ).
% 1.17/0.98  
% 1.17/0.98  cnf(c_873,plain,
% 1.17/0.98      ( ~ v2_compts_1(X0,sK8)
% 1.17/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
% 1.17/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 1.17/0.98      | v3_pre_topc(sK7(sK8,X0,X1),sK8)
% 1.17/0.98      | ~ r2_hidden(X1,k3_subset_1(u1_struct_0(sK8),X0))
% 1.17/0.98      | k1_xboole_0 = X0 ),
% 1.17/0.98      inference(global_propositional_subsumption,
% 1.17/0.98                [status(thm)],
% 1.17/0.98                [c_869,c_28,c_26]) ).
% 1.17/0.98  
% 1.17/0.98  cnf(c_1042,plain,
% 1.17/0.98      ( ~ v2_compts_1(X0,sK8)
% 1.17/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
% 1.17/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 1.17/0.98      | ~ r2_hidden(X1,k3_subset_1(u1_struct_0(sK8),X0))
% 1.17/0.98      | ~ r2_hidden(sK2(sK8),sK6(sK8,X0,X1))
% 1.17/0.98      | ~ r1_tarski(sK3(sK8),sK7(sK8,X0,X1))
% 1.17/0.98      | k1_xboole_0 = X0 ),
% 1.17/0.98      inference(global_propositional_subsumption,
% 1.17/0.98                [status(thm)],
% 1.17/0.98                [c_1038,c_783,c_813,c_843,c_873]) ).
% 1.17/0.98  
% 1.17/0.98  cnf(c_1078,plain,
% 1.17/0.98      ( ~ v2_compts_1(X0,sK8)
% 1.17/0.98      | ~ v2_compts_1(X1,sK8)
% 1.17/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
% 1.17/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8)))
% 1.17/0.98      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 1.17/0.98      | ~ m1_subset_1(X3,u1_struct_0(sK8))
% 1.17/0.98      | ~ r2_hidden(X2,k3_subset_1(u1_struct_0(sK8),X0))
% 1.17/0.99      | ~ r2_hidden(X3,k3_subset_1(u1_struct_0(sK8),X1))
% 1.17/0.99      | ~ r2_hidden(sK2(sK8),sK6(sK8,X1,X3))
% 1.17/0.99      | sK7(sK8,X1,X3) != sK7(sK8,X0,X2)
% 1.17/0.99      | sK3(sK8) != X0
% 1.17/0.99      | k1_xboole_0 = X0
% 1.17/0.99      | k1_xboole_0 = X1 ),
% 1.17/0.99      inference(resolution_lifted,[status(thm)],[c_933,c_1042]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_1079,plain,
% 1.17/0.99      ( ~ v2_compts_1(X0,sK8)
% 1.17/0.99      | ~ v2_compts_1(sK3(sK8),sK8)
% 1.17/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
% 1.17/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 1.17/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 1.17/0.99      | ~ m1_subset_1(sK3(sK8),k1_zfmisc_1(u1_struct_0(sK8)))
% 1.17/0.99      | ~ r2_hidden(X2,k3_subset_1(u1_struct_0(sK8),X0))
% 1.17/0.99      | ~ r2_hidden(X1,k3_subset_1(u1_struct_0(sK8),sK3(sK8)))
% 1.17/0.99      | ~ r2_hidden(sK2(sK8),sK6(sK8,X0,X2))
% 1.17/0.99      | sK7(sK8,X0,X2) != sK7(sK8,sK3(sK8),X1)
% 1.17/0.99      | k1_xboole_0 = X0
% 1.17/0.99      | k1_xboole_0 = sK3(sK8) ),
% 1.17/0.99      inference(unflattening,[status(thm)],[c_1078]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_4,plain,
% 1.17/0.99      ( v4_pre_topc(sK3(X0),X0) | sP0(X0) ),
% 1.17/0.99      inference(cnf_transformation,[],[f42]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_23,plain,
% 1.17/0.99      ( v2_compts_1(X0,X1)
% 1.17/0.99      | ~ v4_pre_topc(X0,X1)
% 1.17/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.17/0.99      | ~ v1_compts_1(X1)
% 1.17/0.99      | ~ l1_pre_topc(X1) ),
% 1.17/0.99      inference(cnf_transformation,[],[f53]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_25,negated_conjecture,
% 1.17/0.99      ( v1_compts_1(sK8) ),
% 1.17/0.99      inference(cnf_transformation,[],[f58]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_368,plain,
% 1.17/0.99      ( v2_compts_1(X0,X1)
% 1.17/0.99      | ~ v4_pre_topc(X0,X1)
% 1.17/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.17/0.99      | ~ l1_pre_topc(X1)
% 1.17/0.99      | sK8 != X1 ),
% 1.17/0.99      inference(resolution_lifted,[status(thm)],[c_23,c_25]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_369,plain,
% 1.17/0.99      ( v2_compts_1(X0,sK8)
% 1.17/0.99      | ~ v4_pre_topc(X0,sK8)
% 1.17/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
% 1.17/0.99      | ~ l1_pre_topc(sK8) ),
% 1.17/0.99      inference(unflattening,[status(thm)],[c_368]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_373,plain,
% 1.17/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
% 1.17/0.99      | ~ v4_pre_topc(X0,sK8)
% 1.17/0.99      | v2_compts_1(X0,sK8) ),
% 1.17/0.99      inference(global_propositional_subsumption,
% 1.17/0.99                [status(thm)],
% 1.17/0.99                [c_369,c_27]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_374,plain,
% 1.17/0.99      ( v2_compts_1(X0,sK8)
% 1.17/0.99      | ~ v4_pre_topc(X0,sK8)
% 1.17/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) ),
% 1.17/0.99      inference(renaming,[status(thm)],[c_373]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_595,plain,
% 1.17/0.99      ( v2_compts_1(X0,sK8)
% 1.17/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
% 1.17/0.99      | sP0(X1)
% 1.17/0.99      | sK3(X1) != X0
% 1.17/0.99      | sK8 != X1 ),
% 1.17/0.99      inference(resolution_lifted,[status(thm)],[c_4,c_374]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_596,plain,
% 1.17/0.99      ( v2_compts_1(sK3(sK8),sK8)
% 1.17/0.99      | ~ m1_subset_1(sK3(sK8),k1_zfmisc_1(u1_struct_0(sK8)))
% 1.17/0.99      | sP0(sK8) ),
% 1.17/0.99      inference(unflattening,[status(thm)],[c_595]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_598,plain,
% 1.17/0.99      ( ~ m1_subset_1(sK3(sK8),k1_zfmisc_1(u1_struct_0(sK8)))
% 1.17/0.99      | v2_compts_1(sK3(sK8),sK8) ),
% 1.17/0.99      inference(global_propositional_subsumption,
% 1.17/0.99                [status(thm)],
% 1.17/0.99                [c_596,c_24,c_356]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_599,plain,
% 1.17/0.99      ( v2_compts_1(sK3(sK8),sK8)
% 1.17/0.99      | ~ m1_subset_1(sK3(sK8),k1_zfmisc_1(u1_struct_0(sK8))) ),
% 1.17/0.99      inference(renaming,[status(thm)],[c_598]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_6,plain,
% 1.17/0.99      ( m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) | sP0(X0) ),
% 1.17/0.99      inference(cnf_transformation,[],[f40]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_619,plain,
% 1.17/0.99      ( m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) | sK8 != X0 ),
% 1.17/0.99      inference(resolution_lifted,[status(thm)],[c_6,c_358]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_620,plain,
% 1.17/0.99      ( m1_subset_1(sK3(sK8),k1_zfmisc_1(u1_struct_0(sK8))) ),
% 1.17/0.99      inference(unflattening,[status(thm)],[c_619]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_1083,plain,
% 1.17/0.99      ( ~ m1_subset_1(X2,u1_struct_0(sK8))
% 1.17/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 1.17/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
% 1.17/0.99      | ~ v2_compts_1(X0,sK8)
% 1.17/0.99      | ~ r2_hidden(X2,k3_subset_1(u1_struct_0(sK8),X0))
% 1.17/0.99      | ~ r2_hidden(X1,k3_subset_1(u1_struct_0(sK8),sK3(sK8)))
% 1.17/0.99      | ~ r2_hidden(sK2(sK8),sK6(sK8,X0,X2))
% 1.17/0.99      | sK7(sK8,X0,X2) != sK7(sK8,sK3(sK8),X1)
% 1.17/0.99      | k1_xboole_0 = X0
% 1.17/0.99      | k1_xboole_0 = sK3(sK8) ),
% 1.17/0.99      inference(global_propositional_subsumption,
% 1.17/0.99                [status(thm)],
% 1.17/0.99                [c_1079,c_24,c_356,c_596,c_620]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_1084,plain,
% 1.17/0.99      ( ~ v2_compts_1(X0,sK8)
% 1.17/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
% 1.17/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 1.17/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 1.17/0.99      | ~ r2_hidden(X1,k3_subset_1(u1_struct_0(sK8),X0))
% 1.17/0.99      | ~ r2_hidden(X2,k3_subset_1(u1_struct_0(sK8),sK3(sK8)))
% 1.17/0.99      | ~ r2_hidden(sK2(sK8),sK6(sK8,X0,X1))
% 1.17/0.99      | sK7(sK8,X0,X1) != sK7(sK8,sK3(sK8),X2)
% 1.17/0.99      | k1_xboole_0 = X0
% 1.17/0.99      | k1_xboole_0 = sK3(sK8) ),
% 1.17/0.99      inference(renaming,[status(thm)],[c_1083]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_668,plain,
% 1.17/0.99      ( v2_compts_1(sK3(sK8),sK8) ),
% 1.17/0.99      inference(backward_subsumption_resolution,
% 1.17/0.99                [status(thm)],
% 1.17/0.99                [c_620,c_599]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_1131,plain,
% 1.17/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
% 1.17/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 1.17/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 1.17/0.99      | ~ r2_hidden(X2,k3_subset_1(u1_struct_0(sK8),X0))
% 1.17/0.99      | ~ r2_hidden(X1,k3_subset_1(u1_struct_0(sK8),sK3(sK8)))
% 1.17/0.99      | ~ r2_hidden(sK2(sK8),sK6(sK8,X0,X2))
% 1.17/0.99      | sK7(sK8,sK3(sK8),X1) != sK7(sK8,X0,X2)
% 1.17/0.99      | sK3(sK8) != X0
% 1.17/0.99      | sK3(sK8) = k1_xboole_0
% 1.17/0.99      | sK8 != sK8
% 1.17/0.99      | k1_xboole_0 = X0 ),
% 1.17/0.99      inference(resolution_lifted,[status(thm)],[c_1084,c_668]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_1132,plain,
% 1.17/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK8))
% 1.17/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 1.17/0.99      | ~ m1_subset_1(sK3(sK8),k1_zfmisc_1(u1_struct_0(sK8)))
% 1.17/0.99      | ~ r2_hidden(X0,k3_subset_1(u1_struct_0(sK8),sK3(sK8)))
% 1.17/0.99      | ~ r2_hidden(X1,k3_subset_1(u1_struct_0(sK8),sK3(sK8)))
% 1.17/0.99      | ~ r2_hidden(sK2(sK8),sK6(sK8,sK3(sK8),X0))
% 1.17/0.99      | sK7(sK8,sK3(sK8),X1) != sK7(sK8,sK3(sK8),X0)
% 1.17/0.99      | sK3(sK8) = k1_xboole_0
% 1.17/0.99      | k1_xboole_0 = sK3(sK8) ),
% 1.17/0.99      inference(unflattening,[status(thm)],[c_1131]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_5,plain,
% 1.17/0.99      ( sP0(X0) | sK3(X0) != k1_xboole_0 ),
% 1.17/0.99      inference(cnf_transformation,[],[f41]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_626,plain,
% 1.17/0.99      ( sK3(X0) != k1_xboole_0 | sK8 != X0 ),
% 1.17/0.99      inference(resolution_lifted,[status(thm)],[c_5,c_358]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_627,plain,
% 1.17/0.99      ( sK3(sK8) != k1_xboole_0 ),
% 1.17/0.99      inference(unflattening,[status(thm)],[c_626]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_1136,plain,
% 1.17/0.99      ( sK7(sK8,sK3(sK8),X1) != sK7(sK8,sK3(sK8),X0)
% 1.17/0.99      | ~ r2_hidden(sK2(sK8),sK6(sK8,sK3(sK8),X0))
% 1.17/0.99      | ~ r2_hidden(X1,k3_subset_1(u1_struct_0(sK8),sK3(sK8)))
% 1.17/0.99      | ~ r2_hidden(X0,k3_subset_1(u1_struct_0(sK8),sK3(sK8)))
% 1.17/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 1.17/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 1.17/0.99      | k1_xboole_0 = sK3(sK8) ),
% 1.17/0.99      inference(global_propositional_subsumption,
% 1.17/0.99                [status(thm)],
% 1.17/0.99                [c_1132,c_620,c_627]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_1137,plain,
% 1.17/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK8))
% 1.17/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 1.17/0.99      | ~ r2_hidden(X0,k3_subset_1(u1_struct_0(sK8),sK3(sK8)))
% 1.17/0.99      | ~ r2_hidden(X1,k3_subset_1(u1_struct_0(sK8),sK3(sK8)))
% 1.17/0.99      | ~ r2_hidden(sK2(sK8),sK6(sK8,sK3(sK8),X1))
% 1.17/0.99      | sK7(sK8,sK3(sK8),X0) != sK7(sK8,sK3(sK8),X1)
% 1.17/0.99      | k1_xboole_0 = sK3(sK8) ),
% 1.17/0.99      inference(renaming,[status(thm)],[c_1136]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_1316,plain,
% 1.17/0.99      ( ~ m1_subset_1(X0_54,u1_struct_0(sK8))
% 1.17/0.99      | ~ m1_subset_1(X1_54,u1_struct_0(sK8))
% 1.17/0.99      | ~ r2_hidden(X0_54,k3_subset_1(u1_struct_0(sK8),sK3(sK8)))
% 1.17/0.99      | ~ r2_hidden(X1_54,k3_subset_1(u1_struct_0(sK8),sK3(sK8)))
% 1.17/0.99      | ~ r2_hidden(sK2(sK8),sK6(sK8,sK3(sK8),X1_54))
% 1.17/0.99      | sK7(sK8,sK3(sK8),X0_54) != sK7(sK8,sK3(sK8),X1_54)
% 1.17/0.99      | k1_xboole_0 = sK3(sK8) ),
% 1.17/0.99      inference(subtyping,[status(esa)],[c_1137]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_1563,plain,
% 1.17/0.99      ( ~ m1_subset_1(X0_54,u1_struct_0(sK8))
% 1.17/0.99      | ~ m1_subset_1(sK2(sK8),u1_struct_0(sK8))
% 1.17/0.99      | ~ r2_hidden(X0_54,k3_subset_1(u1_struct_0(sK8),sK3(sK8)))
% 1.17/0.99      | ~ r2_hidden(sK2(sK8),sK6(sK8,sK3(sK8),X0_54))
% 1.17/0.99      | ~ r2_hidden(sK2(sK8),k3_subset_1(u1_struct_0(sK8),sK3(sK8)))
% 1.17/0.99      | sK7(sK8,sK3(sK8),sK2(sK8)) != sK7(sK8,sK3(sK8),X0_54)
% 1.17/0.99      | k1_xboole_0 = sK3(sK8) ),
% 1.17/0.99      inference(instantiation,[status(thm)],[c_1316]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_1616,plain,
% 1.17/0.99      ( ~ m1_subset_1(sK2(sK8),u1_struct_0(sK8))
% 1.17/0.99      | ~ r2_hidden(sK2(sK8),sK6(sK8,sK3(sK8),sK2(sK8)))
% 1.17/0.99      | ~ r2_hidden(sK2(sK8),k3_subset_1(u1_struct_0(sK8),sK3(sK8)))
% 1.17/0.99      | sK7(sK8,sK3(sK8),sK2(sK8)) != sK7(sK8,sK3(sK8),sK2(sK8))
% 1.17/0.99      | k1_xboole_0 = sK3(sK8) ),
% 1.17/0.99      inference(instantiation,[status(thm)],[c_1563]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_1589,plain,
% 1.17/0.99      ( sK3(sK8) = sK3(sK8) ),
% 1.17/0.99      inference(instantiation,[status(thm)],[c_1322]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_1323,plain,
% 1.17/0.99      ( X0_54 != X1_54 | X2_54 != X1_54 | X2_54 = X0_54 ),
% 1.17/0.99      theory(equality) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_1546,plain,
% 1.17/0.99      ( sK3(sK8) != X0_54
% 1.17/0.99      | sK3(sK8) = k1_xboole_0
% 1.17/0.99      | k1_xboole_0 != X0_54 ),
% 1.17/0.99      inference(instantiation,[status(thm)],[c_1323]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_1588,plain,
% 1.17/0.99      ( sK3(sK8) != sK3(sK8)
% 1.17/0.99      | sK3(sK8) = k1_xboole_0
% 1.17/0.99      | k1_xboole_0 != sK3(sK8) ),
% 1.17/0.99      inference(instantiation,[status(thm)],[c_1546]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_18,plain,
% 1.17/0.99      ( ~ v2_compts_1(X0,X1)
% 1.17/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.17/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.17/0.99      | r2_hidden(X2,sK6(X1,X0,X2))
% 1.17/0.99      | ~ r2_hidden(X2,k3_subset_1(u1_struct_0(X1),X0))
% 1.17/0.99      | ~ v8_pre_topc(X1)
% 1.17/0.99      | ~ v2_pre_topc(X1)
% 1.17/0.99      | ~ l1_pre_topc(X1)
% 1.17/0.99      | k1_xboole_0 = X0 ),
% 1.17/0.99      inference(cnf_transformation,[],[f50]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_898,plain,
% 1.17/0.99      ( ~ v2_compts_1(X0,X1)
% 1.17/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.17/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.17/0.99      | r2_hidden(X2,sK6(X1,X0,X2))
% 1.17/0.99      | ~ r2_hidden(X2,k3_subset_1(u1_struct_0(X1),X0))
% 1.17/0.99      | ~ v8_pre_topc(X1)
% 1.17/0.99      | ~ v2_pre_topc(X1)
% 1.17/0.99      | sK8 != X1
% 1.17/0.99      | k1_xboole_0 = X0 ),
% 1.17/0.99      inference(resolution_lifted,[status(thm)],[c_18,c_27]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_899,plain,
% 1.17/0.99      ( ~ v2_compts_1(X0,sK8)
% 1.17/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
% 1.17/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 1.17/0.99      | r2_hidden(X1,sK6(sK8,X0,X1))
% 1.17/0.99      | ~ r2_hidden(X1,k3_subset_1(u1_struct_0(sK8),X0))
% 1.17/0.99      | ~ v8_pre_topc(sK8)
% 1.17/0.99      | ~ v2_pre_topc(sK8)
% 1.17/0.99      | k1_xboole_0 = X0 ),
% 1.17/0.99      inference(unflattening,[status(thm)],[c_898]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_903,plain,
% 1.17/0.99      ( ~ v2_compts_1(X0,sK8)
% 1.17/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
% 1.17/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 1.17/0.99      | r2_hidden(X1,sK6(sK8,X0,X1))
% 1.17/0.99      | ~ r2_hidden(X1,k3_subset_1(u1_struct_0(sK8),X0))
% 1.17/0.99      | k1_xboole_0 = X0 ),
% 1.17/0.99      inference(global_propositional_subsumption,
% 1.17/0.99                [status(thm)],
% 1.17/0.99                [c_899,c_28,c_26]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_1164,plain,
% 1.17/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
% 1.17/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 1.17/0.99      | r2_hidden(X1,sK6(sK8,X0,X1))
% 1.17/0.99      | ~ r2_hidden(X1,k3_subset_1(u1_struct_0(sK8),X0))
% 1.17/0.99      | sK3(sK8) != X0
% 1.17/0.99      | sK8 != sK8
% 1.17/0.99      | k1_xboole_0 = X0 ),
% 1.17/0.99      inference(resolution_lifted,[status(thm)],[c_903,c_668]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_1165,plain,
% 1.17/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK8))
% 1.17/0.99      | ~ m1_subset_1(sK3(sK8),k1_zfmisc_1(u1_struct_0(sK8)))
% 1.17/0.99      | r2_hidden(X0,sK6(sK8,sK3(sK8),X0))
% 1.17/0.99      | ~ r2_hidden(X0,k3_subset_1(u1_struct_0(sK8),sK3(sK8)))
% 1.17/0.99      | k1_xboole_0 = sK3(sK8) ),
% 1.17/0.99      inference(unflattening,[status(thm)],[c_1164]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_1169,plain,
% 1.17/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK8))
% 1.17/0.99      | r2_hidden(X0,sK6(sK8,sK3(sK8),X0))
% 1.17/0.99      | ~ r2_hidden(X0,k3_subset_1(u1_struct_0(sK8),sK3(sK8)))
% 1.17/0.99      | k1_xboole_0 = sK3(sK8) ),
% 1.17/0.99      inference(global_propositional_subsumption,
% 1.17/0.99                [status(thm)],
% 1.17/0.99                [c_1165,c_620]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_1315,plain,
% 1.17/0.99      ( ~ m1_subset_1(X0_54,u1_struct_0(sK8))
% 1.17/0.99      | r2_hidden(X0_54,sK6(sK8,sK3(sK8),X0_54))
% 1.17/0.99      | ~ r2_hidden(X0_54,k3_subset_1(u1_struct_0(sK8),sK3(sK8)))
% 1.17/0.99      | k1_xboole_0 = sK3(sK8) ),
% 1.17/0.99      inference(subtyping,[status(esa)],[c_1169]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_1543,plain,
% 1.17/0.99      ( ~ m1_subset_1(sK2(sK8),u1_struct_0(sK8))
% 1.17/0.99      | r2_hidden(sK2(sK8),sK6(sK8,sK3(sK8),sK2(sK8)))
% 1.17/0.99      | ~ r2_hidden(sK2(sK8),k3_subset_1(u1_struct_0(sK8),sK3(sK8)))
% 1.17/0.99      | k1_xboole_0 = sK3(sK8) ),
% 1.17/0.99      inference(instantiation,[status(thm)],[c_1315]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_1318,plain,
% 1.17/0.99      ( sK3(sK8) != k1_xboole_0 ),
% 1.17/0.99      inference(subtyping,[status(esa)],[c_627]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_3,plain,
% 1.17/0.99      ( r2_hidden(sK2(X0),k3_subset_1(u1_struct_0(X0),sK3(X0)))
% 1.17/0.99      | sP0(X0) ),
% 1.17/0.99      inference(cnf_transformation,[],[f43]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_631,plain,
% 1.17/0.99      ( r2_hidden(sK2(X0),k3_subset_1(u1_struct_0(X0),sK3(X0)))
% 1.17/0.99      | sK8 != X0 ),
% 1.17/0.99      inference(resolution_lifted,[status(thm)],[c_3,c_358]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_632,plain,
% 1.17/0.99      ( r2_hidden(sK2(sK8),k3_subset_1(u1_struct_0(sK8),sK3(sK8))) ),
% 1.17/0.99      inference(unflattening,[status(thm)],[c_631]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_7,plain,
% 1.17/0.99      ( m1_subset_1(sK2(X0),u1_struct_0(X0)) | sP0(X0) ),
% 1.17/0.99      inference(cnf_transformation,[],[f39]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_612,plain,
% 1.17/0.99      ( m1_subset_1(sK2(X0),u1_struct_0(X0)) | sK8 != X0 ),
% 1.17/0.99      inference(resolution_lifted,[status(thm)],[c_7,c_358]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_613,plain,
% 1.17/0.99      ( m1_subset_1(sK2(sK8),u1_struct_0(sK8)) ),
% 1.17/0.99      inference(unflattening,[status(thm)],[c_612]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(contradiction,plain,
% 1.17/0.99      ( $false ),
% 1.17/0.99      inference(minisat,
% 1.17/0.99                [status(thm)],
% 1.17/0.99                [c_1626,c_1616,c_1589,c_1588,c_1543,c_1318,c_632,c_613]) ).
% 1.17/0.99  
% 1.17/0.99  
% 1.17/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 1.17/0.99  
% 1.17/0.99  ------                               Statistics
% 1.17/0.99  
% 1.17/0.99  ------ General
% 1.17/0.99  
% 1.17/0.99  abstr_ref_over_cycles:                  0
% 1.17/0.99  abstr_ref_under_cycles:                 0
% 1.17/0.99  gc_basic_clause_elim:                   0
% 1.17/0.99  forced_gc_time:                         0
% 1.17/0.99  parsing_time:                           0.011
% 1.17/0.99  unif_index_cands_time:                  0.
% 1.17/0.99  unif_index_add_time:                    0.
% 1.17/0.99  orderings_time:                         0.
% 1.17/0.99  out_proof_time:                         0.016
% 1.17/0.99  total_time:                             0.094
% 1.17/0.99  num_of_symbols:                         57
% 1.17/0.99  num_of_terms:                           1992
% 1.17/0.99  
% 1.17/0.99  ------ Preprocessing
% 1.17/0.99  
% 1.17/0.99  num_of_splits:                          0
% 1.17/0.99  num_of_split_atoms:                     0
% 1.17/0.99  num_of_reused_defs:                     0
% 1.17/0.99  num_eq_ax_congr_red:                    33
% 1.17/0.99  num_of_sem_filtered_clauses:            1
% 1.17/0.99  num_of_subtypes:                        3
% 1.17/0.99  monotx_restored_types:                  0
% 1.17/0.99  sat_num_of_epr_types:                   0
% 1.17/0.99  sat_num_of_non_cyclic_types:            0
% 1.17/0.99  sat_guarded_non_collapsed_types:        0
% 1.17/0.99  num_pure_diseq_elim:                    0
% 1.17/0.99  simp_replaced_by:                       0
% 1.17/0.99  res_preprocessed:                       69
% 1.17/0.99  prep_upred:                             0
% 1.17/0.99  prep_unflattend:                        51
% 1.17/0.99  smt_new_axioms:                         0
% 1.17/0.99  pred_elim_cands:                        2
% 1.17/0.99  pred_elim:                              13
% 1.17/0.99  pred_elim_cl:                           22
% 1.17/0.99  pred_elim_cycles:                       19
% 1.17/0.99  merged_defs:                            0
% 1.17/0.99  merged_defs_ncl:                        0
% 1.17/0.99  bin_hyper_res:                          0
% 1.17/0.99  prep_cycles:                            4
% 1.17/0.99  pred_elim_time:                         0.023
% 1.17/0.99  splitting_time:                         0.
% 1.17/0.99  sem_filter_time:                        0.
% 1.17/0.99  monotx_time:                            0.
% 1.17/0.99  subtype_inf_time:                       0.
% 1.17/0.99  
% 1.17/0.99  ------ Problem properties
% 1.17/0.99  
% 1.17/0.99  clauses:                                8
% 1.17/0.99  conjectures:                            0
% 1.17/0.99  epr:                                    0
% 1.17/0.99  horn:                                   5
% 1.17/0.99  ground:                                 4
% 1.17/0.99  unary:                                  4
% 1.17/0.99  binary:                                 0
% 1.17/0.99  lits:                                   23
% 1.17/0.99  lits_eq:                                6
% 1.17/0.99  fd_pure:                                0
% 1.17/0.99  fd_pseudo:                              0
% 1.17/0.99  fd_cond:                                0
% 1.17/0.99  fd_pseudo_cond:                         0
% 1.17/0.99  ac_symbols:                             0
% 1.17/0.99  
% 1.17/0.99  ------ Propositional Solver
% 1.17/0.99  
% 1.17/0.99  prop_solver_calls:                      24
% 1.17/0.99  prop_fast_solver_calls:                 824
% 1.17/0.99  smt_solver_calls:                       0
% 1.17/0.99  smt_fast_solver_calls:                  0
% 1.17/0.99  prop_num_of_clauses:                    348
% 1.17/0.99  prop_preprocess_simplified:             1872
% 1.17/0.99  prop_fo_subsumed:                       32
% 1.17/0.99  prop_solver_time:                       0.
% 1.17/0.99  smt_solver_time:                        0.
% 1.17/0.99  smt_fast_solver_time:                   0.
% 1.17/0.99  prop_fast_solver_time:                  0.
% 1.17/0.99  prop_unsat_core_time:                   0.
% 1.17/0.99  
% 1.17/0.99  ------ QBF
% 1.17/0.99  
% 1.17/0.99  qbf_q_res:                              0
% 1.17/0.99  qbf_num_tautologies:                    0
% 1.17/0.99  qbf_prep_cycles:                        0
% 1.17/0.99  
% 1.17/0.99  ------ BMC1
% 1.17/0.99  
% 1.17/0.99  bmc1_current_bound:                     -1
% 1.17/0.99  bmc1_last_solved_bound:                 -1
% 1.17/0.99  bmc1_unsat_core_size:                   -1
% 1.17/0.99  bmc1_unsat_core_parents_size:           -1
% 1.17/0.99  bmc1_merge_next_fun:                    0
% 1.17/0.99  bmc1_unsat_core_clauses_time:           0.
% 1.17/0.99  
% 1.17/0.99  ------ Instantiation
% 1.17/0.99  
% 1.17/0.99  inst_num_of_clauses:                    32
% 1.17/0.99  inst_num_in_passive:                    7
% 1.17/0.99  inst_num_in_active:                     24
% 1.17/0.99  inst_num_in_unprocessed:                0
% 1.17/0.99  inst_num_of_loops:                      26
% 1.17/0.99  inst_num_of_learning_restarts:          0
% 1.17/0.99  inst_num_moves_active_passive:          0
% 1.17/0.99  inst_lit_activity:                      0
% 1.17/0.99  inst_lit_activity_moves:                0
% 1.17/0.99  inst_num_tautologies:                   0
% 1.17/0.99  inst_num_prop_implied:                  0
% 1.17/0.99  inst_num_existing_simplified:           0
% 1.17/0.99  inst_num_eq_res_simplified:             0
% 1.17/0.99  inst_num_child_elim:                    0
% 1.17/0.99  inst_num_of_dismatching_blockings:      1
% 1.17/0.99  inst_num_of_non_proper_insts:           19
% 1.17/0.99  inst_num_of_duplicates:                 0
% 1.17/0.99  inst_inst_num_from_inst_to_res:         0
% 1.17/0.99  inst_dismatching_checking_time:         0.
% 1.17/0.99  
% 1.17/0.99  ------ Resolution
% 1.17/0.99  
% 1.17/0.99  res_num_of_clauses:                     0
% 1.17/0.99  res_num_in_passive:                     0
% 1.17/0.99  res_num_in_active:                      0
% 1.17/0.99  res_num_of_loops:                       73
% 1.17/0.99  res_forward_subset_subsumed:            4
% 1.17/0.99  res_backward_subset_subsumed:           0
% 1.17/0.99  res_forward_subsumed:                   0
% 1.17/0.99  res_backward_subsumed:                  0
% 1.17/0.99  res_forward_subsumption_resolution:     0
% 1.17/0.99  res_backward_subsumption_resolution:    1
% 1.17/0.99  res_clause_to_clause_subsumption:       73
% 1.17/0.99  res_orphan_elimination:                 0
% 1.17/0.99  res_tautology_del:                      7
% 1.17/0.99  res_num_eq_res_simplified:              0
% 1.17/0.99  res_num_sel_changes:                    0
% 1.17/0.99  res_moves_from_active_to_pass:          0
% 1.17/0.99  
% 1.17/0.99  ------ Superposition
% 1.17/0.99  
% 1.17/0.99  sup_time_total:                         0.
% 1.17/0.99  sup_time_generating:                    0.
% 1.17/0.99  sup_time_sim_full:                      0.
% 1.17/0.99  sup_time_sim_immed:                     0.
% 1.17/0.99  
% 1.17/0.99  sup_num_of_clauses:                     8
% 1.17/0.99  sup_num_in_active:                      4
% 1.17/0.99  sup_num_in_passive:                     4
% 1.17/0.99  sup_num_of_loops:                       4
% 1.17/0.99  sup_fw_superposition:                   0
% 1.17/0.99  sup_bw_superposition:                   0
% 1.17/0.99  sup_immediate_simplified:               0
% 1.17/0.99  sup_given_eliminated:                   0
% 1.17/0.99  comparisons_done:                       0
% 1.17/0.99  comparisons_avoided:                    0
% 1.17/0.99  
% 1.17/0.99  ------ Simplifications
% 1.17/0.99  
% 1.17/0.99  
% 1.17/0.99  sim_fw_subset_subsumed:                 0
% 1.17/0.99  sim_bw_subset_subsumed:                 0
% 1.17/0.99  sim_fw_subsumed:                        0
% 1.17/0.99  sim_bw_subsumed:                        0
% 1.17/0.99  sim_fw_subsumption_res:                 0
% 1.17/0.99  sim_bw_subsumption_res:                 0
% 1.17/0.99  sim_tautology_del:                      0
% 1.17/0.99  sim_eq_tautology_del:                   0
% 1.17/0.99  sim_eq_res_simp:                        0
% 1.17/0.99  sim_fw_demodulated:                     0
% 1.17/0.99  sim_bw_demodulated:                     0
% 1.17/0.99  sim_light_normalised:                   0
% 1.17/0.99  sim_joinable_taut:                      0
% 1.17/0.99  sim_joinable_simp:                      0
% 1.17/0.99  sim_ac_normalised:                      0
% 1.17/0.99  sim_smt_subsumption:                    0
% 1.17/0.99  
%------------------------------------------------------------------------------
