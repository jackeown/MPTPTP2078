%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1366+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:33 EST 2020

% Result     : Theorem 0.45s
% Output     : CNFRefutation 0.45s
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
