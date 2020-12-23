%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:50 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 392 expanded)
%              Number of leaves         :   11 ( 149 expanded)
%              Depth                    :   34
%              Number of atoms          :  873 (6238 expanded)
%              Number of equality atoms :   47 ( 361 expanded)
%              Maximal formula depth    :   23 (  11 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f142,plain,(
    $false ),
    inference(subsumption_resolution,[],[f141,f28])).

fof(f28,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ~ v9_pre_topc(sK0)
    & v1_compts_1(sK0)
    & v8_pre_topc(sK0)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f14])).

fof(f14,plain,
    ( ? [X0] :
        ( ~ v9_pre_topc(X0)
        & v1_compts_1(X0)
        & v8_pre_topc(X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ~ v9_pre_topc(sK0)
      & v1_compts_1(sK0)
      & v8_pre_topc(sK0)
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] :
      ( ~ v9_pre_topc(X0)
      & v1_compts_1(X0)
      & v8_pre_topc(X0)
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ~ v9_pre_topc(X0)
      & v1_compts_1(X0)
      & v8_pre_topc(X0)
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ( ( v1_compts_1(X0)
            & v8_pre_topc(X0) )
         => v9_pre_topc(X0) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( ( v1_compts_1(X0)
          & v8_pre_topc(X0) )
       => v9_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_compts_1)).

fof(f141,plain,(
    ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f140,f26])).

fof(f26,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f140,plain,
    ( v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f139,f31])).

fof(f31,plain,(
    ~ v9_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f139,plain,
    ( v9_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f138,f29])).

fof(f29,plain,(
    v8_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f138,plain,
    ( ~ v8_pre_topc(sK0)
    | v9_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f137,f27])).

fof(f27,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f137,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ v8_pre_topc(sK0)
    | v9_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f136,f30])).

fof(f30,plain,(
    v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f136,plain,(
    ! [X0] :
      ( ~ v1_compts_1(X0)
      | ~ v2_pre_topc(X0)
      | ~ v8_pre_topc(X0)
      | v9_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f135])).

fof(f135,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ v8_pre_topc(X0)
      | v9_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | v9_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f134,f55])).

fof(f55,plain,(
    ! [X0] :
      ( v2_compts_1(sK2(X0),X0)
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | v9_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f54,f43])).

fof(f43,plain,(
    ! [X0] :
      ( v4_pre_topc(sK2(X0),X0)
      | v9_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( ( v9_pre_topc(X0)
          | ( ! [X3] :
                ( ! [X4] :
                    ( ~ r1_xboole_0(X3,X4)
                    | ~ r1_tarski(sK2(X0),X4)
                    | ~ r2_hidden(sK1(X0),X3)
                    | ~ v3_pre_topc(X4,X0)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            & r2_hidden(sK1(X0),k3_subset_1(u1_struct_0(X0),sK2(X0)))
            & v4_pre_topc(sK2(X0),X0)
            & k1_xboole_0 != sK2(X0)
            & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
            & m1_subset_1(sK1(X0),u1_struct_0(X0)) ) )
        & ( ! [X5] :
              ( ! [X6] :
                  ( ( r1_xboole_0(sK3(X0,X5,X6),sK4(X0,X5,X6))
                    & r1_tarski(X6,sK4(X0,X5,X6))
                    & r2_hidden(X5,sK3(X0,X5,X6))
                    & v3_pre_topc(sK4(X0,X5,X6),X0)
                    & v3_pre_topc(sK3(X0,X5,X6),X0)
                    & m1_subset_1(sK4(X0,X5,X6),k1_zfmisc_1(u1_struct_0(X0)))
                    & m1_subset_1(sK3(X0,X5,X6),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X5,k3_subset_1(u1_struct_0(X0),X6))
                  | ~ v4_pre_topc(X6,X0)
                  | k1_xboole_0 = X6
                  | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X5,u1_struct_0(X0)) )
          | ~ v9_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f17,f21,f20,f19,f18])).

fof(f18,plain,(
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
                    | ~ r2_hidden(sK1(X0),X3)
                    | ~ v3_pre_topc(X4,X0)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            & r2_hidden(sK1(X0),k3_subset_1(u1_struct_0(X0),X2))
            & v4_pre_topc(X2,X0)
            & k1_xboole_0 != X2
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK1(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( ! [X4] :
                  ( ~ r1_xboole_0(X3,X4)
                  | ~ r1_tarski(X2,X4)
                  | ~ r2_hidden(sK1(X0),X3)
                  | ~ v3_pre_topc(X4,X0)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & r2_hidden(sK1(X0),k3_subset_1(u1_struct_0(X0),X2))
          & v4_pre_topc(X2,X0)
          & k1_xboole_0 != X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ! [X3] :
            ( ! [X4] :
                ( ~ r1_xboole_0(X3,X4)
                | ~ r1_tarski(sK2(X0),X4)
                | ~ r2_hidden(sK1(X0),X3)
                | ~ v3_pre_topc(X4,X0)
                | ~ v3_pre_topc(X3,X0)
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & r2_hidden(sK1(X0),k3_subset_1(u1_struct_0(X0),sK2(X0)))
        & v4_pre_topc(sK2(X0),X0)
        & k1_xboole_0 != sK2(X0)
        & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
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
            ( r1_xboole_0(sK3(X0,X5,X6),X8)
            & r1_tarski(X6,X8)
            & r2_hidden(X5,sK3(X0,X5,X6))
            & v3_pre_topc(X8,X0)
            & v3_pre_topc(sK3(X0,X5,X6),X0)
            & m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK3(X0,X5,X6),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X6,X5,X0] :
      ( ? [X8] :
          ( r1_xboole_0(sK3(X0,X5,X6),X8)
          & r1_tarski(X6,X8)
          & r2_hidden(X5,sK3(X0,X5,X6))
          & v3_pre_topc(X8,X0)
          & v3_pre_topc(sK3(X0,X5,X6),X0)
          & m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r1_xboole_0(sK3(X0,X5,X6),sK4(X0,X5,X6))
        & r1_tarski(X6,sK4(X0,X5,X6))
        & r2_hidden(X5,sK3(X0,X5,X6))
        & v3_pre_topc(sK4(X0,X5,X6),X0)
        & v3_pre_topc(sK3(X0,X5,X6),X0)
        & m1_subset_1(sK4(X0,X5,X6),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0] :
      ( ( ( v9_pre_topc(X0)
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
          | ~ v9_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( ( v9_pre_topc(X0)
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
          | ~ v9_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

fof(f10,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_compts_1)).

fof(f54,plain,(
    ! [X0] :
      ( ~ v4_pre_topc(sK2(X0),X0)
      | ~ v1_compts_1(X0)
      | v2_compts_1(sK2(X0),X0)
      | ~ l1_pre_topc(X0)
      | v9_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ~ v4_pre_topc(sK2(X0),X0)
      | ~ v1_compts_1(X0)
      | v2_compts_1(sK2(X0),X0)
      | ~ l1_pre_topc(X0)
      | v9_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f32,f41])).

fof(f41,plain,(
    ! [X0] :
      ( m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | v9_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ v1_compts_1(X0)
      | v2_compts_1(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_compts_1(X1,X0)
          | ~ v4_pre_topc(X1,X0)
          | ~ v1_compts_1(X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_compts_1(X1,X0)
          | ~ v4_pre_topc(X1,X0)
          | ~ v1_compts_1(X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v4_pre_topc(X1,X0)
              & v1_compts_1(X0) )
           => v2_compts_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_compts_1)).

fof(f134,plain,(
    ! [X0] :
      ( ~ v2_compts_1(sK2(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ v8_pre_topc(X0)
      | v9_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f133,f41])).

fof(f133,plain,(
    ! [X0] :
      ( ~ v8_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ v2_compts_1(sK2(X0),X0)
      | v9_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(subsumption_resolution,[],[f132,f42])).

fof(f42,plain,(
    ! [X0] :
      ( k1_xboole_0 != sK2(X0)
      | v9_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f132,plain,(
    ! [X0] :
      ( ~ v8_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ v2_compts_1(sK2(X0),X0)
      | v9_pre_topc(X0)
      | v2_struct_0(X0)
      | k1_xboole_0 = sK2(X0)
      | ~ m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(subsumption_resolution,[],[f131,f40])).

fof(f40,plain,(
    ! [X0] :
      ( m1_subset_1(sK1(X0),u1_struct_0(X0))
      | v9_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f131,plain,(
    ! [X0] :
      ( ~ v8_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ v2_compts_1(sK2(X0),X0)
      | v9_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(sK1(X0),u1_struct_0(X0))
      | k1_xboole_0 = sK2(X0)
      | ~ m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(subsumption_resolution,[],[f130,f44])).

fof(f44,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),k3_subset_1(u1_struct_0(X0),sK2(X0)))
      | v9_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f130,plain,(
    ! [X0] :
      ( ~ v8_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ v2_compts_1(sK2(X0),X0)
      | v9_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ r2_hidden(sK1(X0),k3_subset_1(u1_struct_0(X0),sK2(X0)))
      | ~ m1_subset_1(sK1(X0),u1_struct_0(X0))
      | k1_xboole_0 = sK2(X0)
      | ~ m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(subsumption_resolution,[],[f129,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X2,k3_subset_1(u1_struct_0(X0),X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k1_xboole_0 = X1
      | ~ v2_compts_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v8_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_xboole_0(sK5(X0,X1,X2),sK6(X0,X1,X2))
                & r1_tarski(X1,sK6(X0,X1,X2))
                & r2_hidden(X2,sK5(X0,X1,X2))
                & v3_pre_topc(sK6(X0,X1,X2),X0)
                & v3_pre_topc(sK5(X0,X1,X2),X0)
                & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
                & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X2,k3_subset_1(u1_struct_0(X0),X1))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | k1_xboole_0 = X1
          | ~ v2_compts_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ v8_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f13,f24,f23])).

fof(f23,plain,(
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
            ( r1_xboole_0(sK5(X0,X1,X2),X4)
            & r1_tarski(X1,X4)
            & r2_hidden(X2,sK5(X0,X1,X2))
            & v3_pre_topc(X4,X0)
            & v3_pre_topc(sK5(X0,X1,X2),X0)
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r1_xboole_0(sK5(X0,X1,X2),X4)
          & r1_tarski(X1,X4)
          & r2_hidden(X2,sK5(X0,X1,X2))
          & v3_pre_topc(X4,X0)
          & v3_pre_topc(sK5(X0,X1,X2),X0)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r1_xboole_0(sK5(X0,X1,X2),sK6(X0,X1,X2))
        & r1_tarski(X1,sK6(X0,X1,X2))
        & r2_hidden(X2,sK5(X0,X1,X2))
        & v3_pre_topc(sK6(X0,X1,X2),X0)
        & v3_pre_topc(sK5(X0,X1,X2),X0)
        & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f12,plain,(
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

% (23712)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_compts_1)).

fof(f129,plain,(
    ! [X0] :
      ( ~ v8_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ v2_compts_1(sK2(X0),X0)
      | v9_pre_topc(X0)
      | ~ m1_subset_1(sK5(X0,sK2(X0),sK1(X0)),k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0)
      | ~ r2_hidden(sK1(X0),k3_subset_1(u1_struct_0(X0),sK2(X0)))
      | ~ m1_subset_1(sK1(X0),u1_struct_0(X0))
      | k1_xboole_0 = sK2(X0)
      | ~ m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(subsumption_resolution,[],[f128,f60])).

fof(f60,plain,(
    ! [X0] :
      ( v3_pre_topc(sK5(X0,sK2(X0),sK1(X0)),X0)
      | ~ v2_compts_1(sK2(X0),X0)
      | ~ v8_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v9_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f59,f41])).

fof(f59,plain,(
    ! [X0] :
      ( v3_pre_topc(sK5(X0,sK2(X0),sK1(X0)),X0)
      | ~ v2_compts_1(sK2(X0),X0)
      | ~ m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v8_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v9_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f58,f42])).

fof(f58,plain,(
    ! [X0] :
      ( v3_pre_topc(sK5(X0,sK2(X0),sK1(X0)),X0)
      | k1_xboole_0 = sK2(X0)
      | ~ v2_compts_1(sK2(X0),X0)
      | ~ m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v8_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v9_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f57,f40])).

fof(f57,plain,(
    ! [X0] :
      ( v3_pre_topc(sK5(X0,sK2(X0),sK1(X0)),X0)
      | ~ m1_subset_1(sK1(X0),u1_struct_0(X0))
      | k1_xboole_0 = sK2(X0)
      | ~ v2_compts_1(sK2(X0),X0)
      | ~ m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v8_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v9_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( v3_pre_topc(sK5(X0,sK2(X0),sK1(X0)),X0)
      | ~ m1_subset_1(sK1(X0),u1_struct_0(X0))
      | k1_xboole_0 = sK2(X0)
      | ~ v2_compts_1(sK2(X0),X0)
      | ~ m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v8_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v9_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f48,f44])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_subset_1(u1_struct_0(X0),X1))
      | v3_pre_topc(sK5(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k1_xboole_0 = X1
      | ~ v2_compts_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v8_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f128,plain,(
    ! [X0] :
      ( ~ v8_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ v2_compts_1(sK2(X0),X0)
      | ~ v3_pre_topc(sK5(X0,sK2(X0),sK1(X0)),X0)
      | v9_pre_topc(X0)
      | ~ m1_subset_1(sK5(X0,sK2(X0),sK1(X0)),k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0)
      | ~ r2_hidden(sK1(X0),k3_subset_1(u1_struct_0(X0),sK2(X0)))
      | ~ m1_subset_1(sK1(X0),u1_struct_0(X0))
      | k1_xboole_0 = sK2(X0)
      | ~ m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(subsumption_resolution,[],[f127,f70])).

fof(f70,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),sK5(X0,sK2(X0),sK1(X0)))
      | ~ v2_compts_1(sK2(X0),X0)
      | ~ v8_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v9_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f69,f41])).

fof(f69,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),sK5(X0,sK2(X0),sK1(X0)))
      | ~ v2_compts_1(sK2(X0),X0)
      | ~ m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v8_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v9_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f68,f42])).

fof(f68,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),sK5(X0,sK2(X0),sK1(X0)))
      | k1_xboole_0 = sK2(X0)
      | ~ v2_compts_1(sK2(X0),X0)
      | ~ m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v8_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v9_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f67,f40])).

fof(f67,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),sK5(X0,sK2(X0),sK1(X0)))
      | ~ m1_subset_1(sK1(X0),u1_struct_0(X0))
      | k1_xboole_0 = sK2(X0)
      | ~ v2_compts_1(sK2(X0),X0)
      | ~ m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v8_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v9_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f66])).

fof(f66,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),sK5(X0,sK2(X0),sK1(X0)))
      | ~ m1_subset_1(sK1(X0),u1_struct_0(X0))
      | k1_xboole_0 = sK2(X0)
      | ~ v2_compts_1(sK2(X0),X0)
      | ~ m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v8_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v9_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f50,f44])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_subset_1(u1_struct_0(X0),X1))
      | r2_hidden(X2,sK5(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k1_xboole_0 = X1
      | ~ v2_compts_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v8_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f127,plain,(
    ! [X0] :
      ( ~ v8_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ v2_compts_1(sK2(X0),X0)
      | ~ r2_hidden(sK1(X0),sK5(X0,sK2(X0),sK1(X0)))
      | ~ v3_pre_topc(sK5(X0,sK2(X0),sK1(X0)),X0)
      | v9_pre_topc(X0)
      | ~ m1_subset_1(sK5(X0,sK2(X0),sK1(X0)),k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0)
      | ~ r2_hidden(sK1(X0),k3_subset_1(u1_struct_0(X0),sK2(X0)))
      | ~ m1_subset_1(sK1(X0),u1_struct_0(X0))
      | k1_xboole_0 = sK2(X0)
      | ~ m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(duplicate_literal_removal,[],[f126])).

fof(f126,plain,(
    ! [X0] :
      ( ~ v8_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ v2_compts_1(sK2(X0),X0)
      | ~ r2_hidden(sK1(X0),sK5(X0,sK2(X0),sK1(X0)))
      | ~ v3_pre_topc(sK5(X0,sK2(X0),sK1(X0)),X0)
      | v9_pre_topc(X0)
      | ~ m1_subset_1(sK5(X0,sK2(X0),sK1(X0)),k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0)
      | ~ r2_hidden(sK1(X0),k3_subset_1(u1_struct_0(X0),sK2(X0)))
      | ~ m1_subset_1(sK1(X0),u1_struct_0(X0))
      | k1_xboole_0 = sK2(X0)
      | ~ v2_compts_1(sK2(X0),X0)
      | ~ m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v8_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(resolution,[],[f125,f52])).

% (23716)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(sK5(X0,X1,X2),sK6(X0,X1,X2))
      | ~ r2_hidden(X2,k3_subset_1(u1_struct_0(X0),X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k1_xboole_0 = X1
      | ~ v2_compts_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v8_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f125,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,sK6(X0,sK2(X0),sK1(X0)))
      | ~ v8_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ v2_compts_1(sK2(X0),X0)
      | ~ r2_hidden(sK1(X0),X1)
      | ~ v3_pre_topc(X1,X0)
      | v9_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f124,f44])).

fof(f124,plain,(
    ! [X0,X1] :
      ( ~ v2_compts_1(sK2(X0),X0)
      | ~ v8_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ r1_xboole_0(X1,sK6(X0,sK2(X0),sK1(X0)))
      | ~ r2_hidden(sK1(X0),k3_subset_1(u1_struct_0(X0),sK2(X0)))
      | ~ r2_hidden(sK1(X0),X1)
      | ~ v3_pre_topc(X1,X0)
      | v9_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f123,f41])).

fof(f123,plain,(
    ! [X0,X1] :
      ( ~ v2_compts_1(sK2(X0),X0)
      | ~ m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v8_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ r1_xboole_0(X1,sK6(X0,sK2(X0),sK1(X0)))
      | ~ r2_hidden(sK1(X0),k3_subset_1(u1_struct_0(X0),sK2(X0)))
      | ~ r2_hidden(sK1(X0),X1)
      | ~ v3_pre_topc(X1,X0)
      | v9_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f122,f42])).

fof(f122,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = sK2(X0)
      | ~ v2_compts_1(sK2(X0),X0)
      | ~ m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v8_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ r1_xboole_0(X1,sK6(X0,sK2(X0),sK1(X0)))
      | ~ r2_hidden(sK1(X0),k3_subset_1(u1_struct_0(X0),sK2(X0)))
      | ~ r2_hidden(sK1(X0),X1)
      | ~ v3_pre_topc(X1,X0)
      | v9_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f121,f40])).

fof(f121,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK1(X0),u1_struct_0(X0))
      | k1_xboole_0 = sK2(X0)
      | ~ v2_compts_1(sK2(X0),X0)
      | ~ m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v8_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ r1_xboole_0(X1,sK6(X0,sK2(X0),sK1(X0)))
      | ~ r2_hidden(sK1(X0),k3_subset_1(u1_struct_0(X0),sK2(X0)))
      | ~ r2_hidden(sK1(X0),X1)
      | ~ v3_pre_topc(X1,X0)
      | v9_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f120])).

fof(f120,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK1(X0),u1_struct_0(X0))
      | k1_xboole_0 = sK2(X0)
      | ~ v2_compts_1(sK2(X0),X0)
      | ~ m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v8_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ r1_xboole_0(X1,sK6(X0,sK2(X0),sK1(X0)))
      | ~ r2_hidden(sK1(X0),k3_subset_1(u1_struct_0(X0),sK2(X0)))
      | ~ r2_hidden(sK1(X0),X1)
      | ~ v3_pre_topc(X1,X0)
      | v9_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0)
      | ~ v2_compts_1(sK2(X0),X0)
      | ~ v8_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v9_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f95,f75])).

fof(f75,plain,(
    ! [X0] :
      ( r1_tarski(sK2(X0),sK6(X0,sK2(X0),sK1(X0)))
      | ~ v2_compts_1(sK2(X0),X0)
      | ~ v8_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v9_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f74,f41])).

fof(f74,plain,(
    ! [X0] :
      ( r1_tarski(sK2(X0),sK6(X0,sK2(X0),sK1(X0)))
      | ~ v2_compts_1(sK2(X0),X0)
      | ~ m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v8_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v9_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f73,f42])).

fof(f73,plain,(
    ! [X0] :
      ( r1_tarski(sK2(X0),sK6(X0,sK2(X0),sK1(X0)))
      | k1_xboole_0 = sK2(X0)
      | ~ v2_compts_1(sK2(X0),X0)
      | ~ m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v8_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v9_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f72,f40])).

fof(f72,plain,(
    ! [X0] :
      ( r1_tarski(sK2(X0),sK6(X0,sK2(X0),sK1(X0)))
      | ~ m1_subset_1(sK1(X0),u1_struct_0(X0))
      | k1_xboole_0 = sK2(X0)
      | ~ v2_compts_1(sK2(X0),X0)
      | ~ m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v8_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v9_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f71])).

fof(f71,plain,(
    ! [X0] :
      ( r1_tarski(sK2(X0),sK6(X0,sK2(X0),sK1(X0)))
      | ~ m1_subset_1(sK1(X0),u1_struct_0(X0))
      | k1_xboole_0 = sK2(X0)
      | ~ v2_compts_1(sK2(X0),X0)
      | ~ m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v8_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v9_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f51,f44])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_subset_1(u1_struct_0(X0),X1))
      | r1_tarski(X1,sK6(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k1_xboole_0 = X1
      | ~ v2_compts_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v8_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f95,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(sK2(X1),sK6(X1,X2,X0))
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | k1_xboole_0 = X2
      | ~ v2_compts_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v8_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ r1_xboole_0(X3,sK6(X1,X2,X0))
      | ~ r2_hidden(X0,k3_subset_1(u1_struct_0(X1),X2))
      | ~ r2_hidden(sK1(X1),X3)
      | ~ v3_pre_topc(X3,X1)
      | v9_pre_topc(X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f94,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_subset_1(u1_struct_0(X0),X1))
      | v3_pre_topc(sK6(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k1_xboole_0 = X1
      | ~ v2_compts_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v8_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f94,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,k3_subset_1(u1_struct_0(X1),X2))
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | k1_xboole_0 = X2
      | ~ v2_compts_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v8_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ r1_xboole_0(X3,sK6(X1,X2,X0))
      | ~ r1_tarski(sK2(X1),sK6(X1,X2,X0))
      | ~ r2_hidden(sK1(X1),X3)
      | ~ v3_pre_topc(sK6(X1,X2,X0),X1)
      | ~ v3_pre_topc(X3,X1)
      | v9_pre_topc(X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | v2_struct_0(X1) ) ),
    inference(duplicate_literal_removal,[],[f91])).

fof(f91,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,k3_subset_1(u1_struct_0(X1),X2))
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | k1_xboole_0 = X2
      | ~ v2_compts_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v8_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ r1_xboole_0(X3,sK6(X1,X2,X0))
      | ~ r1_tarski(sK2(X1),sK6(X1,X2,X0))
      | ~ r2_hidden(sK1(X1),X3)
      | ~ v3_pre_topc(sK6(X1,X2,X0),X1)
      | ~ v3_pre_topc(X3,X1)
      | v9_pre_topc(X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f47,f45])).

fof(f45,plain,(
    ! [X4,X0,X3] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_xboole_0(X3,X4)
      | ~ r1_tarski(sK2(X0),X4)
      | ~ r2_hidden(sK1(X0),X3)
      | ~ v3_pre_topc(X4,X0)
      | ~ v3_pre_topc(X3,X0)
      | v9_pre_topc(X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f47,plain,(
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
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:19:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (23726)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.46  % (23718)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.47  % (23713)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.47  % (23713)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (23720)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.48  % (23731)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f142,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(subsumption_resolution,[],[f141,f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    l1_pre_topc(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ~v9_pre_topc(sK0) & v1_compts_1(sK0) & v8_pre_topc(sK0) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ? [X0] : (~v9_pre_topc(X0) & v1_compts_1(X0) & v8_pre_topc(X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (~v9_pre_topc(sK0) & v1_compts_1(sK0) & v8_pre_topc(sK0) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f7,plain,(
% 0.21/0.48    ? [X0] : (~v9_pre_topc(X0) & v1_compts_1(X0) & v8_pre_topc(X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f6])).
% 0.21/0.48  fof(f6,plain,(
% 0.21/0.48    ? [X0] : ((~v9_pre_topc(X0) & (v1_compts_1(X0) & v8_pre_topc(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,negated_conjecture,(
% 0.21/0.48    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ((v1_compts_1(X0) & v8_pre_topc(X0)) => v9_pre_topc(X0)))),
% 0.21/0.48    inference(negated_conjecture,[],[f4])).
% 0.21/0.48  fof(f4,conjecture,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ((v1_compts_1(X0) & v8_pre_topc(X0)) => v9_pre_topc(X0)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_compts_1)).
% 0.21/0.48  fof(f141,plain,(
% 0.21/0.48    ~l1_pre_topc(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f140,f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ~v2_struct_0(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f140,plain,(
% 0.21/0.48    v2_struct_0(sK0) | ~l1_pre_topc(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f139,f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ~v9_pre_topc(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f139,plain,(
% 0.21/0.48    v9_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f138,f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    v8_pre_topc(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f138,plain,(
% 0.21/0.48    ~v8_pre_topc(sK0) | v9_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f137,f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    v2_pre_topc(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f137,plain,(
% 0.21/0.48    ~v2_pre_topc(sK0) | ~v8_pre_topc(sK0) | v9_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK0)),
% 0.21/0.48    inference(resolution,[],[f136,f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    v1_compts_1(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f136,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_compts_1(X0) | ~v2_pre_topc(X0) | ~v8_pre_topc(X0) | v9_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f135])).
% 0.21/0.48  fof(f135,plain,(
% 0.21/0.48    ( ! [X0] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~v8_pre_topc(X0) | v9_pre_topc(X0) | v2_struct_0(X0) | ~v1_compts_1(X0) | ~l1_pre_topc(X0) | v9_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(resolution,[],[f134,f55])).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    ( ! [X0] : (v2_compts_1(sK2(X0),X0) | ~v1_compts_1(X0) | ~l1_pre_topc(X0) | v9_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f54,f43])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ( ! [X0] : (v4_pre_topc(sK2(X0),X0) | v9_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0] : (((v9_pre_topc(X0) | ((! [X3] : (! [X4] : (~r1_xboole_0(X3,X4) | ~r1_tarski(sK2(X0),X4) | ~r2_hidden(sK1(X0),X3) | ~v3_pre_topc(X4,X0) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(sK1(X0),k3_subset_1(u1_struct_0(X0),sK2(X0))) & v4_pre_topc(sK2(X0),X0) & k1_xboole_0 != sK2(X0) & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK1(X0),u1_struct_0(X0)))) & (! [X5] : (! [X6] : (((r1_xboole_0(sK3(X0,X5,X6),sK4(X0,X5,X6)) & r1_tarski(X6,sK4(X0,X5,X6)) & r2_hidden(X5,sK3(X0,X5,X6)) & v3_pre_topc(sK4(X0,X5,X6),X0) & v3_pre_topc(sK3(X0,X5,X6),X0) & m1_subset_1(sK4(X0,X5,X6),k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK3(X0,X5,X6),k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X5,k3_subset_1(u1_struct_0(X0),X6)) | ~v4_pre_topc(X6,X0) | k1_xboole_0 = X6 | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~v9_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f17,f21,f20,f19,f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0] : (? [X1] : (? [X2] : (! [X3] : (! [X4] : (~r1_xboole_0(X3,X4) | ~r1_tarski(X2,X4) | ~r2_hidden(X1,X3) | ~v3_pre_topc(X4,X0) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X1,k3_subset_1(u1_struct_0(X0),X2)) & v4_pre_topc(X2,X0) & k1_xboole_0 != X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (! [X3] : (! [X4] : (~r1_xboole_0(X3,X4) | ~r1_tarski(X2,X4) | ~r2_hidden(sK1(X0),X3) | ~v3_pre_topc(X4,X0) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(sK1(X0),k3_subset_1(u1_struct_0(X0),X2)) & v4_pre_topc(X2,X0) & k1_xboole_0 != X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK1(X0),u1_struct_0(X0))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0] : (? [X2] : (! [X3] : (! [X4] : (~r1_xboole_0(X3,X4) | ~r1_tarski(X2,X4) | ~r2_hidden(sK1(X0),X3) | ~v3_pre_topc(X4,X0) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(sK1(X0),k3_subset_1(u1_struct_0(X0),X2)) & v4_pre_topc(X2,X0) & k1_xboole_0 != X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (! [X3] : (! [X4] : (~r1_xboole_0(X3,X4) | ~r1_tarski(sK2(X0),X4) | ~r2_hidden(sK1(X0),X3) | ~v3_pre_topc(X4,X0) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(sK1(X0),k3_subset_1(u1_struct_0(X0),sK2(X0))) & v4_pre_topc(sK2(X0),X0) & k1_xboole_0 != sK2(X0) & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X6,X5,X0] : (? [X7] : (? [X8] : (r1_xboole_0(X7,X8) & r1_tarski(X6,X8) & r2_hidden(X5,X7) & v3_pre_topc(X8,X0) & v3_pre_topc(X7,X0) & m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X8] : (r1_xboole_0(sK3(X0,X5,X6),X8) & r1_tarski(X6,X8) & r2_hidden(X5,sK3(X0,X5,X6)) & v3_pre_topc(X8,X0) & v3_pre_topc(sK3(X0,X5,X6),X0) & m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK3(X0,X5,X6),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X6,X5,X0] : (? [X8] : (r1_xboole_0(sK3(X0,X5,X6),X8) & r1_tarski(X6,X8) & r2_hidden(X5,sK3(X0,X5,X6)) & v3_pre_topc(X8,X0) & v3_pre_topc(sK3(X0,X5,X6),X0) & m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X0)))) => (r1_xboole_0(sK3(X0,X5,X6),sK4(X0,X5,X6)) & r1_tarski(X6,sK4(X0,X5,X6)) & r2_hidden(X5,sK3(X0,X5,X6)) & v3_pre_topc(sK4(X0,X5,X6),X0) & v3_pre_topc(sK3(X0,X5,X6),X0) & m1_subset_1(sK4(X0,X5,X6),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0] : (((v9_pre_topc(X0) | ? [X1] : (? [X2] : (! [X3] : (! [X4] : (~r1_xboole_0(X3,X4) | ~r1_tarski(X2,X4) | ~r2_hidden(X1,X3) | ~v3_pre_topc(X4,X0) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X1,k3_subset_1(u1_struct_0(X0),X2)) & v4_pre_topc(X2,X0) & k1_xboole_0 != X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X5] : (! [X6] : (? [X7] : (? [X8] : (r1_xboole_0(X7,X8) & r1_tarski(X6,X8) & r2_hidden(X5,X7) & v3_pre_topc(X8,X0) & v3_pre_topc(X7,X0) & m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X5,k3_subset_1(u1_struct_0(X0),X6)) | ~v4_pre_topc(X6,X0) | k1_xboole_0 = X6 | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~v9_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(rectify,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0] : (((v9_pre_topc(X0) | ? [X1] : (? [X2] : (! [X3] : (! [X4] : (~r1_xboole_0(X3,X4) | ~r1_tarski(X2,X4) | ~r2_hidden(X1,X3) | ~v3_pre_topc(X4,X0) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X1,k3_subset_1(u1_struct_0(X0),X2)) & v4_pre_topc(X2,X0) & k1_xboole_0 != X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (? [X3] : (? [X4] : (r1_xboole_0(X3,X4) & r1_tarski(X2,X4) & r2_hidden(X1,X3) & v3_pre_topc(X4,X0) & v3_pre_topc(X3,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k3_subset_1(u1_struct_0(X0),X2)) | ~v4_pre_topc(X2,X0) | k1_xboole_0 = X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v9_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ! [X0] : ((v9_pre_topc(X0) <=> ! [X1] : (! [X2] : (? [X3] : (? [X4] : (r1_xboole_0(X3,X4) & r1_tarski(X2,X4) & r2_hidden(X1,X3) & v3_pre_topc(X4,X0) & v3_pre_topc(X3,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k3_subset_1(u1_struct_0(X0),X2)) | ~v4_pre_topc(X2,X0) | k1_xboole_0 = X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f10])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ! [X0] : ((v9_pre_topc(X0) <=> ! [X1] : (! [X2] : ((? [X3] : (? [X4] : ((r1_xboole_0(X3,X4) & r1_tarski(X2,X4) & r2_hidden(X1,X3) & v3_pre_topc(X4,X0) & v3_pre_topc(X3,X0)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k3_subset_1(u1_struct_0(X0),X2)) | ~v4_pre_topc(X2,X0) | k1_xboole_0 = X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v9_pre_topc(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_xboole_0(X3,X4) & r1_tarski(X2,X4) & r2_hidden(X1,X3) & v3_pre_topc(X4,X0) & v3_pre_topc(X3,X0)))) & r2_hidden(X1,k3_subset_1(u1_struct_0(X0),X2)) & v4_pre_topc(X2,X0) & k1_xboole_0 != X2)))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_compts_1)).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    ( ! [X0] : (~v4_pre_topc(sK2(X0),X0) | ~v1_compts_1(X0) | v2_compts_1(sK2(X0),X0) | ~l1_pre_topc(X0) | v9_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f53])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    ( ! [X0] : (~v4_pre_topc(sK2(X0),X0) | ~v1_compts_1(X0) | v2_compts_1(sK2(X0),X0) | ~l1_pre_topc(X0) | v9_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(resolution,[],[f32,f41])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ( ! [X0] : (m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) | v9_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f22])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | ~v1_compts_1(X0) | v2_compts_1(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (v2_compts_1(X1,X0) | ~v4_pre_topc(X1,X0) | ~v1_compts_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(flattening,[],[f8])).
% 0.21/0.49  fof(f8,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : ((v2_compts_1(X1,X0) | (~v4_pre_topc(X1,X0) | ~v1_compts_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X1,X0) & v1_compts_1(X0)) => v2_compts_1(X1,X0))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_compts_1)).
% 0.21/0.49  fof(f134,plain,(
% 0.21/0.49    ( ! [X0] : (~v2_compts_1(sK2(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~v8_pre_topc(X0) | v9_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f133,f41])).
% 0.21/0.49  fof(f133,plain,(
% 0.21/0.49    ( ! [X0] : (~v8_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~v2_compts_1(sK2(X0),X0) | v9_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f132,f42])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ( ! [X0] : (k1_xboole_0 != sK2(X0) | v9_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f22])).
% 0.21/0.49  fof(f132,plain,(
% 0.21/0.49    ( ! [X0] : (~v8_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~v2_compts_1(sK2(X0),X0) | v9_pre_topc(X0) | v2_struct_0(X0) | k1_xboole_0 = sK2(X0) | ~m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f131,f40])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ( ! [X0] : (m1_subset_1(sK1(X0),u1_struct_0(X0)) | v9_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f22])).
% 0.21/0.49  fof(f131,plain,(
% 0.21/0.49    ( ! [X0] : (~v8_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~v2_compts_1(sK2(X0),X0) | v9_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(sK1(X0),u1_struct_0(X0)) | k1_xboole_0 = sK2(X0) | ~m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f130,f44])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    ( ! [X0] : (r2_hidden(sK1(X0),k3_subset_1(u1_struct_0(X0),sK2(X0))) | v9_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f22])).
% 0.21/0.49  fof(f130,plain,(
% 0.21/0.49    ( ! [X0] : (~v8_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~v2_compts_1(sK2(X0),X0) | v9_pre_topc(X0) | v2_struct_0(X0) | ~r2_hidden(sK1(X0),k3_subset_1(u1_struct_0(X0),sK2(X0))) | ~m1_subset_1(sK1(X0),u1_struct_0(X0)) | k1_xboole_0 = sK2(X0) | ~m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f129,f46])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X2,k3_subset_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k1_xboole_0 = X1 | ~v2_compts_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v8_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (((r1_xboole_0(sK5(X0,X1,X2),sK6(X0,X1,X2)) & r1_tarski(X1,sK6(X0,X1,X2)) & r2_hidden(X2,sK5(X0,X1,X2)) & v3_pre_topc(sK6(X0,X1,X2),X0) & v3_pre_topc(sK5(X0,X1,X2),X0) & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,k3_subset_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | k1_xboole_0 = X1 | ~v2_compts_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~v8_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f13,f24,f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ! [X2,X1,X0] : (? [X3] : (? [X4] : (r1_xboole_0(X3,X4) & r1_tarski(X1,X4) & r2_hidden(X2,X3) & v3_pre_topc(X4,X0) & v3_pre_topc(X3,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X4] : (r1_xboole_0(sK5(X0,X1,X2),X4) & r1_tarski(X1,X4) & r2_hidden(X2,sK5(X0,X1,X2)) & v3_pre_topc(X4,X0) & v3_pre_topc(sK5(X0,X1,X2),X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X2,X1,X0] : (? [X4] : (r1_xboole_0(sK5(X0,X1,X2),X4) & r1_tarski(X1,X4) & r2_hidden(X2,sK5(X0,X1,X2)) & v3_pre_topc(X4,X0) & v3_pre_topc(sK5(X0,X1,X2),X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) => (r1_xboole_0(sK5(X0,X1,X2),sK6(X0,X1,X2)) & r1_tarski(X1,sK6(X0,X1,X2)) & r2_hidden(X2,sK5(X0,X1,X2)) & v3_pre_topc(sK6(X0,X1,X2),X0) & v3_pre_topc(sK5(X0,X1,X2),X0) & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (? [X3] : (? [X4] : (r1_xboole_0(X3,X4) & r1_tarski(X1,X4) & r2_hidden(X2,X3) & v3_pre_topc(X4,X0) & v3_pre_topc(X3,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,k3_subset_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | k1_xboole_0 = X1 | ~v2_compts_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~v8_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.49    inference(flattening,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ! [X0] : ((! [X1] : (((! [X2] : ((? [X3] : (? [X4] : ((r1_xboole_0(X3,X4) & r1_tarski(X1,X4) & r2_hidden(X2,X3) & v3_pre_topc(X4,X0) & v3_pre_topc(X3,X0)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | k1_xboole_0 = X1) | ~v2_compts_1(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~v8_pre_topc(X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  % (23712)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v8_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_compts_1(X1,X0) => (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_xboole_0(X3,X4) & r1_tarski(X1,X4) & r2_hidden(X2,X3) & v3_pre_topc(X4,X0) & v3_pre_topc(X3,X0)))) & r2_hidden(X2,k3_subset_1(u1_struct_0(X0),X1)))) | k1_xboole_0 = X1)))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_compts_1)).
% 0.21/0.49  fof(f129,plain,(
% 0.21/0.49    ( ! [X0] : (~v8_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~v2_compts_1(sK2(X0),X0) | v9_pre_topc(X0) | ~m1_subset_1(sK5(X0,sK2(X0),sK1(X0)),k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X0) | ~r2_hidden(sK1(X0),k3_subset_1(u1_struct_0(X0),sK2(X0))) | ~m1_subset_1(sK1(X0),u1_struct_0(X0)) | k1_xboole_0 = sK2(X0) | ~m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f128,f60])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    ( ! [X0] : (v3_pre_topc(sK5(X0,sK2(X0),sK1(X0)),X0) | ~v2_compts_1(sK2(X0),X0) | ~v8_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v9_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f59,f41])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    ( ! [X0] : (v3_pre_topc(sK5(X0,sK2(X0),sK1(X0)),X0) | ~v2_compts_1(sK2(X0),X0) | ~m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~v8_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v9_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f58,f42])).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    ( ! [X0] : (v3_pre_topc(sK5(X0,sK2(X0),sK1(X0)),X0) | k1_xboole_0 = sK2(X0) | ~v2_compts_1(sK2(X0),X0) | ~m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~v8_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v9_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f57,f40])).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    ( ! [X0] : (v3_pre_topc(sK5(X0,sK2(X0),sK1(X0)),X0) | ~m1_subset_1(sK1(X0),u1_struct_0(X0)) | k1_xboole_0 = sK2(X0) | ~v2_compts_1(sK2(X0),X0) | ~m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~v8_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v9_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f56])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    ( ! [X0] : (v3_pre_topc(sK5(X0,sK2(X0),sK1(X0)),X0) | ~m1_subset_1(sK1(X0),u1_struct_0(X0)) | k1_xboole_0 = sK2(X0) | ~v2_compts_1(sK2(X0),X0) | ~m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~v8_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v9_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(resolution,[],[f48,f44])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_subset_1(u1_struct_0(X0),X1)) | v3_pre_topc(sK5(X0,X1,X2),X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | k1_xboole_0 = X1 | ~v2_compts_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v8_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f25])).
% 0.21/0.49  fof(f128,plain,(
% 0.21/0.49    ( ! [X0] : (~v8_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~v2_compts_1(sK2(X0),X0) | ~v3_pre_topc(sK5(X0,sK2(X0),sK1(X0)),X0) | v9_pre_topc(X0) | ~m1_subset_1(sK5(X0,sK2(X0),sK1(X0)),k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X0) | ~r2_hidden(sK1(X0),k3_subset_1(u1_struct_0(X0),sK2(X0))) | ~m1_subset_1(sK1(X0),u1_struct_0(X0)) | k1_xboole_0 = sK2(X0) | ~m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f127,f70])).
% 0.21/0.49  fof(f70,plain,(
% 0.21/0.49    ( ! [X0] : (r2_hidden(sK1(X0),sK5(X0,sK2(X0),sK1(X0))) | ~v2_compts_1(sK2(X0),X0) | ~v8_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v9_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f69,f41])).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    ( ! [X0] : (r2_hidden(sK1(X0),sK5(X0,sK2(X0),sK1(X0))) | ~v2_compts_1(sK2(X0),X0) | ~m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~v8_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v9_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f68,f42])).
% 0.21/0.49  fof(f68,plain,(
% 0.21/0.49    ( ! [X0] : (r2_hidden(sK1(X0),sK5(X0,sK2(X0),sK1(X0))) | k1_xboole_0 = sK2(X0) | ~v2_compts_1(sK2(X0),X0) | ~m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~v8_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v9_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f67,f40])).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    ( ! [X0] : (r2_hidden(sK1(X0),sK5(X0,sK2(X0),sK1(X0))) | ~m1_subset_1(sK1(X0),u1_struct_0(X0)) | k1_xboole_0 = sK2(X0) | ~v2_compts_1(sK2(X0),X0) | ~m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~v8_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v9_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f66])).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    ( ! [X0] : (r2_hidden(sK1(X0),sK5(X0,sK2(X0),sK1(X0))) | ~m1_subset_1(sK1(X0),u1_struct_0(X0)) | k1_xboole_0 = sK2(X0) | ~v2_compts_1(sK2(X0),X0) | ~m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~v8_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v9_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(resolution,[],[f50,f44])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_subset_1(u1_struct_0(X0),X1)) | r2_hidden(X2,sK5(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k1_xboole_0 = X1 | ~v2_compts_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v8_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f25])).
% 0.21/0.49  fof(f127,plain,(
% 0.21/0.49    ( ! [X0] : (~v8_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~v2_compts_1(sK2(X0),X0) | ~r2_hidden(sK1(X0),sK5(X0,sK2(X0),sK1(X0))) | ~v3_pre_topc(sK5(X0,sK2(X0),sK1(X0)),X0) | v9_pre_topc(X0) | ~m1_subset_1(sK5(X0,sK2(X0),sK1(X0)),k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X0) | ~r2_hidden(sK1(X0),k3_subset_1(u1_struct_0(X0),sK2(X0))) | ~m1_subset_1(sK1(X0),u1_struct_0(X0)) | k1_xboole_0 = sK2(X0) | ~m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f126])).
% 0.21/0.49  fof(f126,plain,(
% 0.21/0.49    ( ! [X0] : (~v8_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~v2_compts_1(sK2(X0),X0) | ~r2_hidden(sK1(X0),sK5(X0,sK2(X0),sK1(X0))) | ~v3_pre_topc(sK5(X0,sK2(X0),sK1(X0)),X0) | v9_pre_topc(X0) | ~m1_subset_1(sK5(X0,sK2(X0),sK1(X0)),k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X0) | ~r2_hidden(sK1(X0),k3_subset_1(u1_struct_0(X0),sK2(X0))) | ~m1_subset_1(sK1(X0),u1_struct_0(X0)) | k1_xboole_0 = sK2(X0) | ~v2_compts_1(sK2(X0),X0) | ~m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~v8_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.49    inference(resolution,[],[f125,f52])).
% 0.21/0.49  % (23716)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r1_xboole_0(sK5(X0,X1,X2),sK6(X0,X1,X2)) | ~r2_hidden(X2,k3_subset_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k1_xboole_0 = X1 | ~v2_compts_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v8_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f25])).
% 0.21/0.49  fof(f125,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r1_xboole_0(X1,sK6(X0,sK2(X0),sK1(X0))) | ~v8_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~v2_compts_1(sK2(X0),X0) | ~r2_hidden(sK1(X0),X1) | ~v3_pre_topc(X1,X0) | v9_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f124,f44])).
% 0.21/0.49  fof(f124,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v2_compts_1(sK2(X0),X0) | ~v8_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~r1_xboole_0(X1,sK6(X0,sK2(X0),sK1(X0))) | ~r2_hidden(sK1(X0),k3_subset_1(u1_struct_0(X0),sK2(X0))) | ~r2_hidden(sK1(X0),X1) | ~v3_pre_topc(X1,X0) | v9_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f123,f41])).
% 0.21/0.49  fof(f123,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v2_compts_1(sK2(X0),X0) | ~m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~v8_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~r1_xboole_0(X1,sK6(X0,sK2(X0),sK1(X0))) | ~r2_hidden(sK1(X0),k3_subset_1(u1_struct_0(X0),sK2(X0))) | ~r2_hidden(sK1(X0),X1) | ~v3_pre_topc(X1,X0) | v9_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f122,f42])).
% 0.21/0.49  fof(f122,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k1_xboole_0 = sK2(X0) | ~v2_compts_1(sK2(X0),X0) | ~m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~v8_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~r1_xboole_0(X1,sK6(X0,sK2(X0),sK1(X0))) | ~r2_hidden(sK1(X0),k3_subset_1(u1_struct_0(X0),sK2(X0))) | ~r2_hidden(sK1(X0),X1) | ~v3_pre_topc(X1,X0) | v9_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f121,f40])).
% 0.21/0.49  fof(f121,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(sK1(X0),u1_struct_0(X0)) | k1_xboole_0 = sK2(X0) | ~v2_compts_1(sK2(X0),X0) | ~m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~v8_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~r1_xboole_0(X1,sK6(X0,sK2(X0),sK1(X0))) | ~r2_hidden(sK1(X0),k3_subset_1(u1_struct_0(X0),sK2(X0))) | ~r2_hidden(sK1(X0),X1) | ~v3_pre_topc(X1,X0) | v9_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f120])).
% 0.21/0.49  fof(f120,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(sK1(X0),u1_struct_0(X0)) | k1_xboole_0 = sK2(X0) | ~v2_compts_1(sK2(X0),X0) | ~m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~v8_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~r1_xboole_0(X1,sK6(X0,sK2(X0),sK1(X0))) | ~r2_hidden(sK1(X0),k3_subset_1(u1_struct_0(X0),sK2(X0))) | ~r2_hidden(sK1(X0),X1) | ~v3_pre_topc(X1,X0) | v9_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X0) | ~v2_compts_1(sK2(X0),X0) | ~v8_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v9_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(resolution,[],[f95,f75])).
% 0.21/0.49  fof(f75,plain,(
% 0.21/0.49    ( ! [X0] : (r1_tarski(sK2(X0),sK6(X0,sK2(X0),sK1(X0))) | ~v2_compts_1(sK2(X0),X0) | ~v8_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v9_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f74,f41])).
% 0.21/0.49  fof(f74,plain,(
% 0.21/0.49    ( ! [X0] : (r1_tarski(sK2(X0),sK6(X0,sK2(X0),sK1(X0))) | ~v2_compts_1(sK2(X0),X0) | ~m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~v8_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v9_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f73,f42])).
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    ( ! [X0] : (r1_tarski(sK2(X0),sK6(X0,sK2(X0),sK1(X0))) | k1_xboole_0 = sK2(X0) | ~v2_compts_1(sK2(X0),X0) | ~m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~v8_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v9_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f72,f40])).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    ( ! [X0] : (r1_tarski(sK2(X0),sK6(X0,sK2(X0),sK1(X0))) | ~m1_subset_1(sK1(X0),u1_struct_0(X0)) | k1_xboole_0 = sK2(X0) | ~v2_compts_1(sK2(X0),X0) | ~m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~v8_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v9_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f71])).
% 0.21/0.49  fof(f71,plain,(
% 0.21/0.49    ( ! [X0] : (r1_tarski(sK2(X0),sK6(X0,sK2(X0),sK1(X0))) | ~m1_subset_1(sK1(X0),u1_struct_0(X0)) | k1_xboole_0 = sK2(X0) | ~v2_compts_1(sK2(X0),X0) | ~m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~v8_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v9_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(resolution,[],[f51,f44])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_subset_1(u1_struct_0(X0),X1)) | r1_tarski(X1,sK6(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k1_xboole_0 = X1 | ~v2_compts_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v8_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f25])).
% 0.21/0.49  fof(f95,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~r1_tarski(sK2(X1),sK6(X1,X2,X0)) | ~m1_subset_1(X0,u1_struct_0(X1)) | k1_xboole_0 = X2 | ~v2_compts_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~v8_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~r1_xboole_0(X3,sK6(X1,X2,X0)) | ~r2_hidden(X0,k3_subset_1(u1_struct_0(X1),X2)) | ~r2_hidden(sK1(X1),X3) | ~v3_pre_topc(X3,X1) | v9_pre_topc(X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | v2_struct_0(X1)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f94,f49])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_subset_1(u1_struct_0(X0),X1)) | v3_pre_topc(sK6(X0,X1,X2),X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | k1_xboole_0 = X1 | ~v2_compts_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v8_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f25])).
% 0.21/0.49  fof(f94,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,k3_subset_1(u1_struct_0(X1),X2)) | ~m1_subset_1(X0,u1_struct_0(X1)) | k1_xboole_0 = X2 | ~v2_compts_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~v8_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~r1_xboole_0(X3,sK6(X1,X2,X0)) | ~r1_tarski(sK2(X1),sK6(X1,X2,X0)) | ~r2_hidden(sK1(X1),X3) | ~v3_pre_topc(sK6(X1,X2,X0),X1) | ~v3_pre_topc(X3,X1) | v9_pre_topc(X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | v2_struct_0(X1)) )),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f91])).
% 0.21/0.49  fof(f91,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,k3_subset_1(u1_struct_0(X1),X2)) | ~m1_subset_1(X0,u1_struct_0(X1)) | k1_xboole_0 = X2 | ~v2_compts_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~v8_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~r1_xboole_0(X3,sK6(X1,X2,X0)) | ~r1_tarski(sK2(X1),sK6(X1,X2,X0)) | ~r2_hidden(sK1(X1),X3) | ~v3_pre_topc(sK6(X1,X2,X0),X1) | ~v3_pre_topc(X3,X1) | v9_pre_topc(X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 0.21/0.49    inference(resolution,[],[f47,f45])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    ( ! [X4,X0,X3] : (~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_xboole_0(X3,X4) | ~r1_tarski(sK2(X0),X4) | ~r2_hidden(sK1(X0),X3) | ~v3_pre_topc(X4,X0) | ~v3_pre_topc(X3,X0) | v9_pre_topc(X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f22])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X2,k3_subset_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k1_xboole_0 = X1 | ~v2_compts_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v8_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f25])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (23713)------------------------------
% 0.21/0.49  % (23713)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (23713)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (23713)Memory used [KB]: 10746
% 0.21/0.49  % (23713)Time elapsed: 0.067 s
% 0.21/0.49  % (23713)------------------------------
% 0.21/0.49  % (23713)------------------------------
% 0.21/0.49  % (23712)Refutation not found, incomplete strategy% (23712)------------------------------
% 0.21/0.49  % (23712)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (23712)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (23712)Memory used [KB]: 10618
% 0.21/0.49  % (23712)Time elapsed: 0.079 s
% 0.21/0.49  % (23712)------------------------------
% 0.21/0.49  % (23712)------------------------------
% 0.21/0.49  % (23714)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.49  % (23710)Success in time 0.134 s
%------------------------------------------------------------------------------
