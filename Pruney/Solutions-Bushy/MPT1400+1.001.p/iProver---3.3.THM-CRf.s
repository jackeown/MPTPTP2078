%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1400+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:38 EST 2020

% Result     : Theorem 28.12s
% Output     : CNFRefutation 28.12s
% Verified   : 
% Statistics : Number of formulae       :  211 (19534 expanded)
%              Number of clauses        :  133 (4973 expanded)
%              Number of leaves         :   20 (5333 expanded)
%              Depth                    :   28
%              Number of atoms          : 1092 (118480 expanded)
%              Number of equality atoms :  339 (13171 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   24 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r2_hidden(X1,k1_connsp_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => r2_hidden(X1,k1_connsp_2(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(X1,k1_connsp_2(X0,X1))
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(X1,k1_connsp_2(X0,X1))
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f50,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(X1,k1_connsp_2(X0,X1))
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ~ r2_hidden(sK9,k1_connsp_2(X0,sK9))
        & m1_subset_1(sK9,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r2_hidden(X1,k1_connsp_2(X0,X1))
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ r2_hidden(X1,k1_connsp_2(sK8,X1))
          & m1_subset_1(X1,u1_struct_0(sK8)) )
      & l1_pre_topc(sK8)
      & v2_pre_topc(sK8)
      & ~ v2_struct_0(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ~ r2_hidden(sK9,k1_connsp_2(sK8,sK9))
    & m1_subset_1(sK9,u1_struct_0(sK8))
    & l1_pre_topc(sK8)
    & v2_pre_topc(sK8)
    & ~ v2_struct_0(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f27,f50,f49])).

fof(f88,plain,(
    m1_subset_1(sK9,u1_struct_0(sK8)) ),
    inference(cnf_transformation,[],[f51])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = X0
       => ( k1_setfam_1(X0) = X1
        <=> k1_xboole_0 = X1 ) )
      & ( k1_xboole_0 != X0
       => ( k1_setfam_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ! [X3] :
                  ( r2_hidden(X3,X0)
                 => r2_hidden(X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( ( k1_setfam_1(X0) = X1
        <=> k1_xboole_0 = X1 )
        | k1_xboole_0 != X0 )
      & ( ( k1_setfam_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ! [X3] :
                  ( r2_hidden(X2,X3)
                  | ~ r2_hidden(X3,X0) ) ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_setfam_1(X0) = X1
            | k1_xboole_0 != X1 )
          & ( k1_xboole_0 = X1
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 != X0 )
      & ( ( ( k1_setfam_1(X0) = X1
            | ? [X2] :
                ( ( ? [X3] :
                      ( ~ r2_hidden(X2,X3)
                      & r2_hidden(X3,X0) )
                  | ~ r2_hidden(X2,X1) )
                & ( ! [X3] :
                      ( r2_hidden(X2,X3)
                      | ~ r2_hidden(X3,X0) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ? [X3] :
                      ( ~ r2_hidden(X2,X3)
                      & r2_hidden(X3,X0) ) )
                & ( ! [X3] :
                      ( r2_hidden(X2,X3)
                      | ~ r2_hidden(X3,X0) )
                  | ~ r2_hidden(X2,X1) ) )
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_setfam_1(X0) = X1
            | k1_xboole_0 != X1 )
          & ( k1_xboole_0 = X1
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 != X0 )
      & ( ( ( k1_setfam_1(X0) = X1
            | ? [X2] :
                ( ( ? [X3] :
                      ( ~ r2_hidden(X2,X3)
                      & r2_hidden(X3,X0) )
                  | ~ r2_hidden(X2,X1) )
                & ( ! [X4] :
                      ( r2_hidden(X2,X4)
                      | ~ r2_hidden(X4,X0) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ? [X6] :
                      ( ~ r2_hidden(X5,X6)
                      & r2_hidden(X6,X0) ) )
                & ( ! [X7] :
                      ( r2_hidden(X5,X7)
                      | ~ r2_hidden(X7,X0) )
                  | ~ r2_hidden(X5,X1) ) )
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(rectify,[],[f31])).

fof(f35,plain,(
    ! [X5,X0] :
      ( ? [X6] :
          ( ~ r2_hidden(X5,X6)
          & r2_hidden(X6,X0) )
     => ( ~ r2_hidden(X5,sK4(X0,X5))
        & r2_hidden(sK4(X0,X5),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X2,X3)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(X2,sK3(X0,X1))
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ? [X3] :
                ( ~ r2_hidden(X2,X3)
                & r2_hidden(X3,X0) )
            | ~ r2_hidden(X2,X1) )
          & ( ! [X4] :
                ( r2_hidden(X2,X4)
                | ~ r2_hidden(X4,X0) )
            | r2_hidden(X2,X1) ) )
     => ( ( ? [X3] :
              ( ~ r2_hidden(sK2(X0,X1),X3)
              & r2_hidden(X3,X0) )
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( ! [X4] :
              ( r2_hidden(sK2(X0,X1),X4)
              | ~ r2_hidden(X4,X0) )
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_setfam_1(X0) = X1
            | k1_xboole_0 != X1 )
          & ( k1_xboole_0 = X1
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 != X0 )
      & ( ( ( k1_setfam_1(X0) = X1
            | ( ( ( ~ r2_hidden(sK2(X0,X1),sK3(X0,X1))
                  & r2_hidden(sK3(X0,X1),X0) )
                | ~ r2_hidden(sK2(X0,X1),X1) )
              & ( ! [X4] :
                    ( r2_hidden(sK2(X0,X1),X4)
                    | ~ r2_hidden(X4,X0) )
                | r2_hidden(sK2(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ( ~ r2_hidden(X5,sK4(X0,X5))
                    & r2_hidden(sK4(X0,X5),X0) ) )
                & ( ! [X7] :
                      ( r2_hidden(X5,X7)
                      | ~ r2_hidden(X7,X0) )
                  | ~ r2_hidden(X5,X1) ) )
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f32,f35,f34,f33])).

fof(f53,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | r2_hidden(sK4(X0,X5),X0)
      | k1_setfam_1(X0) != X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f95,plain,(
    ! [X0,X5] :
      ( r2_hidden(X5,k1_setfam_1(X0))
      | r2_hidden(sK4(X0,X5),X0)
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f53])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f74,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f87,plain,(
    l1_pre_topc(sK8) ),
    inference(cnf_transformation,[],[f51])).

fof(f85,plain,(
    ~ v2_struct_0(sK8) ),
    inference(cnf_transformation,[],[f51])).

fof(f86,plain,(
    v2_pre_topc(sK8) ),
    inference(cnf_transformation,[],[f51])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f29,plain,(
    ! [X1,X0,X2] :
      ( ( k1_connsp_2(X0,X1) = X2
      <=> sP0(X2,X0,X1) )
      | ~ sP1(X1,X0,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f37,plain,(
    ! [X1,X0,X2] :
      ( ( ( k1_connsp_2(X0,X1) = X2
          | ~ sP0(X2,X0,X1) )
        & ( sP0(X2,X0,X1)
          | k1_connsp_2(X0,X1) != X2 ) )
      | ~ sP1(X1,X0,X2) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_connsp_2(X1,X0) = X2
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | k1_connsp_2(X1,X0) != X2 ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f37])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X1,X0)
      | k1_connsp_2(X1,X0) != X2
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f97,plain,(
    ! [X0,X1] :
      ( sP0(k1_connsp_2(X1,X0),X1,X0)
      | ~ sP1(X0,X1,k1_connsp_2(X1,X0)) ) ),
    inference(equality_resolution,[],[f60])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( k1_connsp_2(X0,X1) = X2
              <=> ? [X3] :
                    ( k6_setfam_1(u1_struct_0(X0),X3) = X2
                    & ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                       => ( r2_hidden(X4,X3)
                        <=> ( r2_hidden(X1,X4)
                            & v4_pre_topc(X4,X0)
                            & v3_pre_topc(X4,X0) ) ) )
                    & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_connsp_2(X0,X1) = X2
              <=> ? [X3] :
                    ( k6_setfam_1(u1_struct_0(X0),X3) = X2
                    & ! [X4] :
                        ( ( r2_hidden(X4,X3)
                        <=> ( r2_hidden(X1,X4)
                            & v4_pre_topc(X4,X0)
                            & v3_pre_topc(X4,X0) ) )
                        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                    & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_connsp_2(X0,X1) = X2
              <=> ? [X3] :
                    ( k6_setfam_1(u1_struct_0(X0),X3) = X2
                    & ! [X4] :
                        ( ( r2_hidden(X4,X3)
                        <=> ( r2_hidden(X1,X4)
                            & v4_pre_topc(X4,X0)
                            & v3_pre_topc(X4,X0) ) )
                        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                    & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X0,X1)
    <=> ? [X3] :
          ( k6_setfam_1(u1_struct_0(X0),X3) = X2
          & ! [X4] :
              ( ( r2_hidden(X4,X3)
              <=> ( r2_hidden(X1,X4)
                  & v4_pre_topc(X4,X0)
                  & v3_pre_topc(X4,X0) ) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP1(X1,X0,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f14,f29,f28])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( sP1(X1,X0,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ( sP0(X2,X0,X1)
        | ! [X3] :
            ( k6_setfam_1(u1_struct_0(X0),X3) != X2
            | ? [X4] :
                ( ( ~ r2_hidden(X1,X4)
                  | ~ v4_pre_topc(X4,X0)
                  | ~ v3_pre_topc(X4,X0)
                  | ~ r2_hidden(X4,X3) )
                & ( ( r2_hidden(X1,X4)
                    & v4_pre_topc(X4,X0)
                    & v3_pre_topc(X4,X0) )
                  | r2_hidden(X4,X3) )
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
      & ( ? [X3] :
            ( k6_setfam_1(u1_struct_0(X0),X3) = X2
            & ! [X4] :
                ( ( ( r2_hidden(X4,X3)
                    | ~ r2_hidden(X1,X4)
                    | ~ v4_pre_topc(X4,X0)
                    | ~ v3_pre_topc(X4,X0) )
                  & ( ( r2_hidden(X1,X4)
                      & v4_pre_topc(X4,X0)
                      & v3_pre_topc(X4,X0) )
                    | ~ r2_hidden(X4,X3) ) )
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        | ~ sP0(X2,X0,X1) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ( sP0(X2,X0,X1)
        | ! [X3] :
            ( k6_setfam_1(u1_struct_0(X0),X3) != X2
            | ? [X4] :
                ( ( ~ r2_hidden(X1,X4)
                  | ~ v4_pre_topc(X4,X0)
                  | ~ v3_pre_topc(X4,X0)
                  | ~ r2_hidden(X4,X3) )
                & ( ( r2_hidden(X1,X4)
                    & v4_pre_topc(X4,X0)
                    & v3_pre_topc(X4,X0) )
                  | r2_hidden(X4,X3) )
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
      & ( ? [X3] :
            ( k6_setfam_1(u1_struct_0(X0),X3) = X2
            & ! [X4] :
                ( ( ( r2_hidden(X4,X3)
                    | ~ r2_hidden(X1,X4)
                    | ~ v4_pre_topc(X4,X0)
                    | ~ v3_pre_topc(X4,X0) )
                  & ( ( r2_hidden(X1,X4)
                      & v4_pre_topc(X4,X0)
                      & v3_pre_topc(X4,X0) )
                    | ~ r2_hidden(X4,X3) ) )
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        | ~ sP0(X2,X0,X1) ) ) ),
    inference(flattening,[],[f39])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3] :
            ( k6_setfam_1(u1_struct_0(X1),X3) != X0
            | ? [X4] :
                ( ( ~ r2_hidden(X2,X4)
                  | ~ v4_pre_topc(X4,X1)
                  | ~ v3_pre_topc(X4,X1)
                  | ~ r2_hidden(X4,X3) )
                & ( ( r2_hidden(X2,X4)
                    & v4_pre_topc(X4,X1)
                    & v3_pre_topc(X4,X1) )
                  | r2_hidden(X4,X3) )
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
            | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) )
      & ( ? [X5] :
            ( k6_setfam_1(u1_struct_0(X1),X5) = X0
            & ! [X6] :
                ( ( ( r2_hidden(X6,X5)
                    | ~ r2_hidden(X2,X6)
                    | ~ v4_pre_topc(X6,X1)
                    | ~ v3_pre_topc(X6,X1) )
                  & ( ( r2_hidden(X2,X6)
                      & v4_pre_topc(X6,X1)
                      & v3_pre_topc(X6,X1) )
                    | ~ r2_hidden(X6,X5) ) )
                | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))) )
            & m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f40])).

fof(f43,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( k6_setfam_1(u1_struct_0(X1),X5) = X0
          & ! [X6] :
              ( ( ( r2_hidden(X6,X5)
                  | ~ r2_hidden(X2,X6)
                  | ~ v4_pre_topc(X6,X1)
                  | ~ v3_pre_topc(X6,X1) )
                & ( ( r2_hidden(X2,X6)
                    & v4_pre_topc(X6,X1)
                    & v3_pre_topc(X6,X1) )
                  | ~ r2_hidden(X6,X5) ) )
              | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
     => ( k6_setfam_1(u1_struct_0(X1),sK6(X0,X1,X2)) = X0
        & ! [X6] :
            ( ( ( r2_hidden(X6,sK6(X0,X1,X2))
                | ~ r2_hidden(X2,X6)
                | ~ v4_pre_topc(X6,X1)
                | ~ v3_pre_topc(X6,X1) )
              & ( ( r2_hidden(X2,X6)
                  & v4_pre_topc(X6,X1)
                  & v3_pre_topc(X6,X1) )
                | ~ r2_hidden(X6,sK6(X0,X1,X2)) ) )
            | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))) )
        & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X3,X2,X1] :
      ( ? [X4] :
          ( ( ~ r2_hidden(X2,X4)
            | ~ v4_pre_topc(X4,X1)
            | ~ v3_pre_topc(X4,X1)
            | ~ r2_hidden(X4,X3) )
          & ( ( r2_hidden(X2,X4)
              & v4_pre_topc(X4,X1)
              & v3_pre_topc(X4,X1) )
            | r2_hidden(X4,X3) )
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ( ~ r2_hidden(X2,sK5(X1,X2,X3))
          | ~ v4_pre_topc(sK5(X1,X2,X3),X1)
          | ~ v3_pre_topc(sK5(X1,X2,X3),X1)
          | ~ r2_hidden(sK5(X1,X2,X3),X3) )
        & ( ( r2_hidden(X2,sK5(X1,X2,X3))
            & v4_pre_topc(sK5(X1,X2,X3),X1)
            & v3_pre_topc(sK5(X1,X2,X3),X1) )
          | r2_hidden(sK5(X1,X2,X3),X3) )
        & m1_subset_1(sK5(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3] :
            ( k6_setfam_1(u1_struct_0(X1),X3) != X0
            | ( ( ~ r2_hidden(X2,sK5(X1,X2,X3))
                | ~ v4_pre_topc(sK5(X1,X2,X3),X1)
                | ~ v3_pre_topc(sK5(X1,X2,X3),X1)
                | ~ r2_hidden(sK5(X1,X2,X3),X3) )
              & ( ( r2_hidden(X2,sK5(X1,X2,X3))
                  & v4_pre_topc(sK5(X1,X2,X3),X1)
                  & v3_pre_topc(sK5(X1,X2,X3),X1) )
                | r2_hidden(sK5(X1,X2,X3),X3) )
              & m1_subset_1(sK5(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1))) )
            | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) )
      & ( ( k6_setfam_1(u1_struct_0(X1),sK6(X0,X1,X2)) = X0
          & ! [X6] :
              ( ( ( r2_hidden(X6,sK6(X0,X1,X2))
                  | ~ r2_hidden(X2,X6)
                  | ~ v4_pre_topc(X6,X1)
                  | ~ v3_pre_topc(X6,X1) )
                & ( ( r2_hidden(X2,X6)
                    & v4_pre_topc(X6,X1)
                    & v3_pre_topc(X6,X1) )
                  | ~ r2_hidden(X6,sK6(X0,X1,X2)) ) )
              | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f41,f43,f42])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k6_setfam_1(u1_struct_0(X1),sK6(X0,X1,X2)) = X0
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f55,plain,(
    ! [X4,X0,X1] :
      ( k1_setfam_1(X0) = X1
      | r2_hidden(sK2(X0,X1),X4)
      | ~ r2_hidden(X4,X0)
      | r2_hidden(sK2(X0,X1),X1)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k1_setfam_1(X1) = k6_setfam_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(X1) = k6_setfam_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(X1) = k6_setfam_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f52,plain,(
    ! [X0,X7,X5,X1] :
      ( r2_hidden(X5,X7)
      | ~ r2_hidden(X7,X0)
      | ~ r2_hidden(X5,X1)
      | k1_setfam_1(X0) != X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f96,plain,(
    ! [X0,X7,X5] :
      ( r2_hidden(X5,X7)
      | ~ r2_hidden(X7,X0)
      | ~ r2_hidden(X5,k1_setfam_1(X0))
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f52])).

fof(f89,plain,(
    ~ r2_hidden(sK9,k1_connsp_2(sK8,sK9)) ),
    inference(cnf_transformation,[],[f51])).

fof(f65,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(X2,X6)
      | ~ r2_hidden(X6,sK6(X0,X1,X2))
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f54,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(X5,sK4(X0,X5))
      | k1_setfam_1(X0) != X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f94,plain,(
    ! [X0,X5] :
      ( r2_hidden(X5,k1_setfam_1(X0))
      | ~ r2_hidden(X5,sK4(X0,X5))
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f54])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ~ ( k1_xboole_0 = X2
                  & ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                     => ( r2_hidden(X3,X2)
                      <=> ( r2_hidden(X1,X3)
                          & v4_pre_topc(X3,X0)
                          & v3_pre_topc(X3,X0) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_xboole_0 != X2
              | ? [X3] :
                  ( ( r2_hidden(X3,X2)
                  <~> ( r2_hidden(X1,X3)
                      & v4_pre_topc(X3,X0)
                      & v3_pre_topc(X3,X0) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_xboole_0 != X2
              | ? [X3] :
                  ( ( r2_hidden(X3,X2)
                  <~> ( r2_hidden(X1,X3)
                      & v4_pre_topc(X3,X0)
                      & v3_pre_topc(X3,X0) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_xboole_0 != X2
              | ? [X3] :
                  ( ( ~ r2_hidden(X1,X3)
                    | ~ v4_pre_topc(X3,X0)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ r2_hidden(X3,X2) )
                  & ( ( r2_hidden(X1,X3)
                      & v4_pre_topc(X3,X0)
                      & v3_pre_topc(X3,X0) )
                    | r2_hidden(X3,X2) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_xboole_0 != X2
              | ? [X3] :
                  ( ( ~ r2_hidden(X1,X3)
                    | ~ v4_pre_topc(X3,X0)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ r2_hidden(X3,X2) )
                  & ( ( r2_hidden(X1,X3)
                      & v4_pre_topc(X3,X0)
                      & v3_pre_topc(X3,X0) )
                    | r2_hidden(X3,X2) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f47,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X1,X3)
            | ~ v4_pre_topc(X3,X0)
            | ~ v3_pre_topc(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X1,X3)
              & v4_pre_topc(X3,X0)
              & v3_pre_topc(X3,X0) )
            | r2_hidden(X3,X2) )
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ~ r2_hidden(X1,sK7(X0,X1,X2))
          | ~ v4_pre_topc(sK7(X0,X1,X2),X0)
          | ~ v3_pre_topc(sK7(X0,X1,X2),X0)
          | ~ r2_hidden(sK7(X0,X1,X2),X2) )
        & ( ( r2_hidden(X1,sK7(X0,X1,X2))
            & v4_pre_topc(sK7(X0,X1,X2),X0)
            & v3_pre_topc(sK7(X0,X1,X2),X0) )
          | r2_hidden(sK7(X0,X1,X2),X2) )
        & m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_xboole_0 != X2
              | ( ( ~ r2_hidden(X1,sK7(X0,X1,X2))
                  | ~ v4_pre_topc(sK7(X0,X1,X2),X0)
                  | ~ v3_pre_topc(sK7(X0,X1,X2),X0)
                  | ~ r2_hidden(sK7(X0,X1,X2),X2) )
                & ( ( r2_hidden(X1,sK7(X0,X1,X2))
                    & v4_pre_topc(sK7(X0,X1,X2),X0)
                    & v3_pre_topc(sK7(X0,X1,X2),X0) )
                  | r2_hidden(sK7(X0,X1,X2),X2) )
                & m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f46,f47])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X2
      | r2_hidden(X1,sK7(X0,X1,X2))
      | r2_hidden(sK7(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f104,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,sK7(X0,X1,k1_xboole_0))
      | r2_hidden(sK7(X0,X1,k1_xboole_0),k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f80])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X2
      | m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f107,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK7(X0,X1,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f77])).

fof(f66,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(X6,sK6(X0,X1,X2))
      | ~ r2_hidden(X2,X6)
      | ~ v4_pre_topc(X6,X1)
      | ~ v3_pre_topc(X6,X1)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X2
      | v3_pre_topc(sK7(X0,X1,X2),X0)
      | r2_hidden(sK7(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f106,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(sK7(X0,X1,k1_xboole_0),X0)
      | r2_hidden(sK7(X0,X1,k1_xboole_0),k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f78])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X2
      | v4_pre_topc(sK7(X0,X1,X2),X0)
      | r2_hidden(sK7(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f105,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(sK7(X0,X1,k1_xboole_0),X0)
      | r2_hidden(sK7(X0,X1,k1_xboole_0),k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f79])).

fof(f64,plain,(
    ! [X6,X2,X0,X1] :
      ( v4_pre_topc(X6,X1)
      | ~ r2_hidden(X6,sK6(X0,X1,X2))
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f63,plain,(
    ! [X6,X2,X0,X1] :
      ( v3_pre_topc(X6,X1)
      | ~ r2_hidden(X6,sK6(X0,X1,X2))
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X2
      | ~ r2_hidden(X1,sK7(X0,X1,X2))
      | ~ v4_pre_topc(sK7(X0,X1,X2),X0)
      | ~ v3_pre_topc(sK7(X0,X1,X2),X0)
      | ~ r2_hidden(sK7(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,sK7(X0,X1,k1_xboole_0))
      | ~ v4_pre_topc(sK7(X0,X1,k1_xboole_0),X0)
      | ~ v3_pre_topc(sK7(X0,X1,k1_xboole_0),X0)
      | ~ r2_hidden(sK7(X0,X1,k1_xboole_0),k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f81])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK9,u1_struct_0(sK8)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_4782,plain,
    ( m1_subset_1(sK9,u1_struct_0(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_6,plain,
    ( r2_hidden(X0,k1_setfam_1(X1))
    | r2_hidden(sK4(X1,X0),X1)
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_4801,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(X1,k1_setfam_1(X0)) = iProver_top
    | r2_hidden(sK4(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k1_connsp_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_35,negated_conjecture,
    ( l1_pre_topc(sK8) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_612,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k1_connsp_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_35])).

cnf(c_613,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | m1_subset_1(k1_connsp_2(sK8,X0),k1_zfmisc_1(u1_struct_0(sK8)))
    | v2_struct_0(sK8)
    | ~ v2_pre_topc(sK8) ),
    inference(unflattening,[status(thm)],[c_612])).

cnf(c_37,negated_conjecture,
    ( ~ v2_struct_0(sK8) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_36,negated_conjecture,
    ( v2_pre_topc(sK8) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_617,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | m1_subset_1(k1_connsp_2(sK8,X0),k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_613,c_37,c_36])).

cnf(c_4776,plain,
    ( m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(k1_connsp_2(sK8,X0),k1_zfmisc_1(u1_struct_0(sK8))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_617])).

cnf(c_31,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_4785,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_5797,plain,
    ( m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK8)) = iProver_top
    | r2_hidden(X1,k1_connsp_2(sK8,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4776,c_4785])).

cnf(c_6244,plain,
    ( k1_connsp_2(sK8,X0) = k1_xboole_0
    | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK4(k1_connsp_2(sK8,X0),X1),u1_struct_0(sK8)) = iProver_top
    | r2_hidden(X1,k1_setfam_1(k1_connsp_2(sK8,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4801,c_5797])).

cnf(c_9,plain,
    ( ~ sP1(X0,X1,k1_connsp_2(X1,X0))
    | sP0(k1_connsp_2(X1,X0),X1,X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_21,plain,
    ( sP1(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_630,plain,
    ( sP1(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_35])).

cnf(c_631,plain,
    ( sP1(X0,sK8,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | v2_struct_0(sK8)
    | ~ v2_pre_topc(sK8) ),
    inference(unflattening,[status(thm)],[c_630])).

cnf(c_635,plain,
    ( sP1(X0,sK8,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ m1_subset_1(X0,u1_struct_0(sK8)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_631,c_37,c_36])).

cnf(c_702,plain,
    ( sP0(k1_connsp_2(X0,X1),X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ m1_subset_1(X3,u1_struct_0(sK8))
    | X3 != X1
    | k1_connsp_2(X0,X1) != X2
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_635])).

cnf(c_703,plain,
    ( sP0(k1_connsp_2(sK8,X0),sK8,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(k1_connsp_2(sK8,X0),k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(unflattening,[status(thm)],[c_702])).

cnf(c_707,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | sP0(k1_connsp_2(sK8,X0),sK8,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_703,c_37,c_36,c_613])).

cnf(c_708,plain,
    ( sP0(k1_connsp_2(sK8,X0),sK8,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK8)) ),
    inference(renaming,[status(thm)],[c_707])).

cnf(c_4774,plain,
    ( sP0(k1_connsp_2(sK8,X0),sK8,X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_708])).

cnf(c_15,plain,
    ( ~ sP0(X0,X1,X2)
    | k6_setfam_1(u1_struct_0(X1),sK6(X0,X1,X2)) = X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_4794,plain,
    ( k6_setfam_1(u1_struct_0(X0),sK6(X1,X0,X2)) = X1
    | sP0(X1,X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_5685,plain,
    ( k6_setfam_1(u1_struct_0(sK8),sK6(k1_connsp_2(sK8,X0),sK8,X0)) = k1_connsp_2(sK8,X0)
    | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4774,c_4794])).

cnf(c_6527,plain,
    ( k6_setfam_1(u1_struct_0(sK8),sK6(k1_connsp_2(sK8,sK4(k1_connsp_2(sK8,X0),X1)),sK8,sK4(k1_connsp_2(sK8,X0),X1))) = k1_connsp_2(sK8,sK4(k1_connsp_2(sK8,X0),X1))
    | k1_connsp_2(sK8,X0) = k1_xboole_0
    | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
    | r2_hidden(X1,k1_setfam_1(k1_connsp_2(sK8,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_6244,c_5685])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK2(X1,X2),X2)
    | r2_hidden(sK2(X1,X2),X0)
    | k1_setfam_1(X1) = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_4803,plain,
    ( k1_setfam_1(X0) = X1
    | k1_xboole_0 = X0
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(sK2(X0,X1),X1) = iProver_top
    | r2_hidden(sK2(X0,X1),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_6952,plain,
    ( k1_setfam_1(X0) = X1
    | k1_xboole_0 = X0
    | m1_subset_1(X2,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK2(X0,X1),u1_struct_0(sK8)) = iProver_top
    | r2_hidden(k1_connsp_2(sK8,X2),X0) != iProver_top
    | r2_hidden(sK2(X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_4803,c_5797])).

cnf(c_7310,plain,
    ( k6_setfam_1(u1_struct_0(sK8),sK6(k1_connsp_2(sK8,sK4(k1_connsp_2(sK8,X0),k1_connsp_2(sK8,X1))),sK8,sK4(k1_connsp_2(sK8,X0),k1_connsp_2(sK8,X1)))) = k1_connsp_2(sK8,sK4(k1_connsp_2(sK8,X0),k1_connsp_2(sK8,X1)))
    | k1_connsp_2(sK8,X0) = k1_xboole_0
    | k1_setfam_1(k1_connsp_2(sK8,X0)) = k1_xboole_0
    | k1_setfam_1(k1_setfam_1(k1_connsp_2(sK8,X0))) = X2
    | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK2(k1_setfam_1(k1_connsp_2(sK8,X0)),X2),u1_struct_0(sK8)) = iProver_top
    | r2_hidden(sK2(k1_setfam_1(k1_connsp_2(sK8,X0)),X2),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_6527,c_6952])).

cnf(c_67846,plain,
    ( k6_setfam_1(u1_struct_0(sK8),sK6(k1_connsp_2(sK8,sK4(k1_connsp_2(sK8,X0),k1_connsp_2(sK8,sK9))),sK8,sK4(k1_connsp_2(sK8,X0),k1_connsp_2(sK8,sK9)))) = k1_connsp_2(sK8,sK4(k1_connsp_2(sK8,X0),k1_connsp_2(sK8,sK9)))
    | k1_connsp_2(sK8,X0) = k1_xboole_0
    | k1_setfam_1(k1_connsp_2(sK8,X0)) = k1_xboole_0
    | k1_setfam_1(k1_setfam_1(k1_connsp_2(sK8,X0))) = X1
    | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK2(k1_setfam_1(k1_connsp_2(sK8,X0)),X1),u1_struct_0(sK8)) = iProver_top
    | r2_hidden(sK2(k1_setfam_1(k1_connsp_2(sK8,X0)),X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_4782,c_7310])).

cnf(c_20,plain,
    ( ~ sP0(X0,X1,X2)
    | m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_4789,plain,
    ( sP0(X0,X1,X2) != iProver_top
    | m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k6_setfam_1(X1,X0) = k1_setfam_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_4788,plain,
    ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_5782,plain,
    ( k6_setfam_1(u1_struct_0(X0),sK6(X1,X0,X2)) = k1_setfam_1(sK6(X1,X0,X2))
    | sP0(X1,X0,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4789,c_4788])).

cnf(c_11645,plain,
    ( k6_setfam_1(u1_struct_0(sK8),sK6(k1_connsp_2(sK8,X0),sK8,X0)) = k1_setfam_1(sK6(k1_connsp_2(sK8,X0),sK8,X0))
    | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4774,c_5782])).

cnf(c_12077,plain,
    ( k6_setfam_1(u1_struct_0(sK8),sK6(k1_connsp_2(sK8,sK9),sK8,sK9)) = k1_setfam_1(sK6(k1_connsp_2(sK8,sK9),sK8,sK9)) ),
    inference(superposition,[status(thm)],[c_4782,c_11645])).

cnf(c_5690,plain,
    ( k6_setfam_1(u1_struct_0(sK8),sK6(k1_connsp_2(sK8,sK9),sK8,sK9)) = k1_connsp_2(sK8,sK9) ),
    inference(superposition,[status(thm)],[c_4782,c_5685])).

cnf(c_12207,plain,
    ( k1_setfam_1(sK6(k1_connsp_2(sK8,sK9),sK8,sK9)) = k1_connsp_2(sK8,sK9) ),
    inference(light_normalisation,[status(thm)],[c_12077,c_5690])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X0)
    | ~ r2_hidden(X2,k1_setfam_1(X1))
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_4800,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(X1,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top
    | r2_hidden(X2,k1_setfam_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_12408,plain,
    ( sK6(k1_connsp_2(sK8,sK9),sK8,sK9) = k1_xboole_0
    | r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X1,sK6(k1_connsp_2(sK8,sK9),sK8,sK9)) != iProver_top
    | r2_hidden(X0,k1_connsp_2(sK8,sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12207,c_4800])).

cnf(c_69799,plain,
    ( sK6(k1_connsp_2(sK8,sK9),sK8,sK9) = k1_setfam_1(k1_setfam_1(k1_connsp_2(sK8,X0)))
    | sK6(k1_connsp_2(sK8,sK9),sK8,sK9) = k1_xboole_0
    | k6_setfam_1(u1_struct_0(sK8),sK6(k1_connsp_2(sK8,sK4(k1_connsp_2(sK8,X0),k1_connsp_2(sK8,sK9))),sK8,sK4(k1_connsp_2(sK8,X0),k1_connsp_2(sK8,sK9)))) = k1_connsp_2(sK8,sK4(k1_connsp_2(sK8,X0),k1_connsp_2(sK8,sK9)))
    | k1_connsp_2(sK8,X0) = k1_xboole_0
    | k1_setfam_1(k1_connsp_2(sK8,X0)) = k1_xboole_0
    | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK2(k1_setfam_1(k1_connsp_2(sK8,X0)),sK6(k1_connsp_2(sK8,sK9),sK8,sK9)),u1_struct_0(sK8)) = iProver_top
    | r2_hidden(X1,k1_connsp_2(sK8,sK9)) != iProver_top
    | r2_hidden(X1,sK2(k1_setfam_1(k1_connsp_2(sK8,X0)),sK6(k1_connsp_2(sK8,sK9),sK8,sK9))) = iProver_top ),
    inference(superposition,[status(thm)],[c_67846,c_12408])).

cnf(c_41,plain,
    ( m1_subset_1(sK9,u1_struct_0(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,negated_conjecture,
    ( ~ r2_hidden(sK9,k1_connsp_2(sK8,sK9)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_42,plain,
    ( r2_hidden(sK9,k1_connsp_2(sK8,sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_5098,plain,
    ( sP0(k1_connsp_2(sK8,sK9),sK8,sK9)
    | ~ m1_subset_1(sK9,u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_708])).

cnf(c_5099,plain,
    ( sP0(k1_connsp_2(sK8,sK9),sK8,sK9) = iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5098])).

cnf(c_17,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X2,X3)
    | ~ r2_hidden(X3,sK6(X0,X1,X2)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_4792,plain,
    ( sP0(X0,X1,X2) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r2_hidden(X2,X3) = iProver_top
    | r2_hidden(X3,sK6(X0,X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_88,plain,
    ( sP0(X0,X1,X2) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r2_hidden(X2,X3) = iProver_top
    | r2_hidden(X3,sK6(X0,X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_5795,plain,
    ( sP0(X0,X1,X2) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | r2_hidden(X3,sK6(X0,X1,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4789,c_4785])).

cnf(c_8532,plain,
    ( sP0(X0,X1,X2) != iProver_top
    | r2_hidden(X2,X3) = iProver_top
    | r2_hidden(X3,sK6(X0,X1,X2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4792,c_88,c_5795])).

cnf(c_8543,plain,
    ( sK6(X0,X1,X2) = k1_xboole_0
    | sP0(X0,X1,X2) != iProver_top
    | r2_hidden(X2,sK4(sK6(X0,X1,X2),X3)) = iProver_top
    | r2_hidden(X3,k1_setfam_1(sK6(X0,X1,X2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4801,c_8532])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,sK4(X1,X0))
    | r2_hidden(X0,k1_setfam_1(X1))
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_4802,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(X1,sK4(X0,X1)) != iProver_top
    | r2_hidden(X1,k1_setfam_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_94139,plain,
    ( sK6(X0,X1,X2) = k1_xboole_0
    | sP0(X0,X1,X2) != iProver_top
    | r2_hidden(X2,k1_setfam_1(sK6(X0,X1,X2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_8543,c_4802])).

cnf(c_94547,plain,
    ( sK6(k1_connsp_2(sK8,sK9),sK8,sK9) = k1_xboole_0
    | sP0(k1_connsp_2(sK8,sK9),sK8,sK9) != iProver_top
    | r2_hidden(sK9,k1_connsp_2(sK8,sK9)) = iProver_top ),
    inference(superposition,[status(thm)],[c_12207,c_94139])).

cnf(c_105273,plain,
    ( sK6(k1_connsp_2(sK8,sK9),sK8,sK9) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_69799,c_41,c_42,c_5099,c_94547])).

cnf(c_105520,plain,
    ( sP0(k1_connsp_2(sK8,sK9),sK8,sK9) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_105273,c_4789])).

cnf(c_4221,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_4246,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4221])).

cnf(c_5172,plain,
    ( ~ sP0(k1_connsp_2(sK8,sK9),sK8,sK9)
    | m1_subset_1(sK6(k1_connsp_2(sK8,sK9),sK8,sK9),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8)))) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_5173,plain,
    ( sP0(k1_connsp_2(sK8,sK9),sK8,sK9) != iProver_top
    | m1_subset_1(sK6(k1_connsp_2(sK8,sK9),sK8,sK9),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5172])).

cnf(c_4232,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_5268,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(sK6(k1_connsp_2(sK8,sK9),sK8,sK9),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8))))
    | X0 != sK6(k1_connsp_2(sK8,sK9),sK8,sK9)
    | X1 != k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(instantiation,[status(thm)],[c_4232])).

cnf(c_5754,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8))))
    | ~ m1_subset_1(sK6(k1_connsp_2(sK8,sK9),sK8,sK9),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8))))
    | X0 != sK6(k1_connsp_2(sK8,sK9),sK8,sK9)
    | k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8))) != k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(instantiation,[status(thm)],[c_5268])).

cnf(c_5756,plain,
    ( X0 != sK6(k1_connsp_2(sK8,sK9),sK8,sK9)
    | k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8))) != k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8)))
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8)))) = iProver_top
    | m1_subset_1(sK6(k1_connsp_2(sK8,sK9),sK8,sK9),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5754])).

cnf(c_5758,plain,
    ( k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8))) != k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8)))
    | k1_xboole_0 != sK6(k1_connsp_2(sK8,sK9),sK8,sK9)
    | m1_subset_1(sK6(k1_connsp_2(sK8,sK9),sK8,sK9),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8)))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8)))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_5756])).

cnf(c_5755,plain,
    ( k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8))) = k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(instantiation,[status(thm)],[c_4221])).

cnf(c_4222,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_12541,plain,
    ( X0 != X1
    | X0 = sK6(k1_connsp_2(sK8,sK9),sK8,sK9)
    | sK6(k1_connsp_2(sK8,sK9),sK8,sK9) != X1 ),
    inference(instantiation,[status(thm)],[c_4222])).

cnf(c_12542,plain,
    ( sK6(k1_connsp_2(sK8,sK9),sK8,sK9) != k1_xboole_0
    | k1_xboole_0 = sK6(k1_connsp_2(sK8,sK9),sK8,sK9)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_12541])).

cnf(c_117661,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_105520,c_41,c_42,c_4246,c_5099,c_5173,c_5758,c_5755,c_12542,c_94547])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | r2_hidden(X0,sK7(X1,X0,k1_xboole_0))
    | r2_hidden(sK7(X1,X0,k1_xboole_0),k1_xboole_0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_558,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | r2_hidden(X0,sK7(X1,X0,k1_xboole_0))
    | r2_hidden(sK7(X1,X0,k1_xboole_0),k1_xboole_0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_35])).

cnf(c_559,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8))))
    | r2_hidden(X0,sK7(sK8,X0,k1_xboole_0))
    | r2_hidden(sK7(sK8,X0,k1_xboole_0),k1_xboole_0)
    | v2_struct_0(sK8)
    | ~ v2_pre_topc(sK8) ),
    inference(unflattening,[status(thm)],[c_558])).

cnf(c_563,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8))))
    | r2_hidden(X0,sK7(sK8,X0,k1_xboole_0))
    | r2_hidden(sK7(sK8,X0,k1_xboole_0),k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_559,c_37,c_36])).

cnf(c_4778,plain,
    ( m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8)))) != iProver_top
    | r2_hidden(X0,sK7(sK8,X0,k1_xboole_0)) = iProver_top
    | r2_hidden(sK7(sK8,X0,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_563])).

cnf(c_117672,plain,
    ( m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
    | r2_hidden(X0,sK7(sK8,X0,k1_xboole_0)) = iProver_top
    | r2_hidden(sK7(sK8,X0,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_117661,c_4778])).

cnf(c_29,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(sK7(X1,X0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_489,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(sK7(X1,X0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_35])).

cnf(c_490,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | m1_subset_1(sK7(sK8,X0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8))))
    | v2_struct_0(sK8)
    | ~ v2_pre_topc(sK8) ),
    inference(unflattening,[status(thm)],[c_489])).

cnf(c_494,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | m1_subset_1(sK7(sK8,X0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_490,c_37,c_36])).

cnf(c_4781,plain,
    ( m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK7(sK8,X0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK8))) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_494])).

cnf(c_16,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X3,X1)
    | ~ v4_pre_topc(X3,X1)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(X3,sK6(X0,X1,X2)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_4793,plain,
    ( sP0(X0,X1,X2) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v3_pre_topc(X3,X1) != iProver_top
    | v4_pre_topc(X3,X1) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r2_hidden(X3,sK6(X0,X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_105516,plain,
    ( sP0(k1_connsp_2(sK8,sK9),sK8,sK9) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | v3_pre_topc(X0,sK8) != iProver_top
    | v4_pre_topc(X0,sK8) != iProver_top
    | r2_hidden(X0,k1_xboole_0) = iProver_top
    | r2_hidden(sK9,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_105273,c_4793])).

cnf(c_127166,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | v3_pre_topc(X0,sK8) != iProver_top
    | v4_pre_topc(X0,sK8) != iProver_top
    | r2_hidden(X0,k1_xboole_0) = iProver_top
    | r2_hidden(sK9,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_105516,c_41,c_5099])).

cnf(c_127176,plain,
    ( m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8)))) != iProver_top
    | v3_pre_topc(sK7(sK8,X0,k1_xboole_0),sK8) != iProver_top
    | v4_pre_topc(sK7(sK8,X0,k1_xboole_0),sK8) != iProver_top
    | r2_hidden(sK7(sK8,X0,k1_xboole_0),k1_xboole_0) = iProver_top
    | r2_hidden(sK9,sK7(sK8,X0,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4781,c_127166])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | v3_pre_topc(sK7(X1,X0,k1_xboole_0),X1)
    | r2_hidden(sK7(X1,X0,k1_xboole_0),k1_xboole_0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_510,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | v3_pre_topc(sK7(X1,X0,k1_xboole_0),X1)
    | r2_hidden(sK7(X1,X0,k1_xboole_0),k1_xboole_0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_35])).

cnf(c_511,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8))))
    | v3_pre_topc(sK7(sK8,X0,k1_xboole_0),sK8)
    | r2_hidden(sK7(sK8,X0,k1_xboole_0),k1_xboole_0)
    | v2_struct_0(sK8)
    | ~ v2_pre_topc(sK8) ),
    inference(unflattening,[status(thm)],[c_510])).

cnf(c_515,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8))))
    | v3_pre_topc(sK7(sK8,X0,k1_xboole_0),sK8)
    | r2_hidden(sK7(sK8,X0,k1_xboole_0),k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_511,c_37,c_36])).

cnf(c_517,plain,
    ( m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8)))) != iProver_top
    | v3_pre_topc(sK7(sK8,X0,k1_xboole_0),sK8) = iProver_top
    | r2_hidden(sK7(sK8,X0,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_515])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | v4_pre_topc(sK7(X1,X0,k1_xboole_0),X1)
    | r2_hidden(sK7(X1,X0,k1_xboole_0),k1_xboole_0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_534,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | v4_pre_topc(sK7(X1,X0,k1_xboole_0),X1)
    | r2_hidden(sK7(X1,X0,k1_xboole_0),k1_xboole_0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_35])).

cnf(c_535,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8))))
    | v4_pre_topc(sK7(sK8,X0,k1_xboole_0),sK8)
    | r2_hidden(sK7(sK8,X0,k1_xboole_0),k1_xboole_0)
    | v2_struct_0(sK8)
    | ~ v2_pre_topc(sK8) ),
    inference(unflattening,[status(thm)],[c_534])).

cnf(c_539,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8))))
    | v4_pre_topc(sK7(sK8,X0,k1_xboole_0),sK8)
    | r2_hidden(sK7(sK8,X0,k1_xboole_0),k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_535,c_37,c_36])).

cnf(c_4779,plain,
    ( m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8)))) != iProver_top
    | v4_pre_topc(sK7(sK8,X0,k1_xboole_0),sK8) = iProver_top
    | r2_hidden(sK7(sK8,X0,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_539])).

cnf(c_117671,plain,
    ( m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
    | v4_pre_topc(sK7(sK8,X0,k1_xboole_0),sK8) = iProver_top
    | r2_hidden(sK7(sK8,X0,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_117661,c_4779])).

cnf(c_127885,plain,
    ( m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
    | r2_hidden(sK7(sK8,X0,k1_xboole_0),k1_xboole_0) = iProver_top
    | r2_hidden(sK9,sK7(sK8,X0,k1_xboole_0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_127176,c_41,c_42,c_517,c_4246,c_5099,c_5173,c_5758,c_5755,c_12542,c_94547,c_117671])).

cnf(c_127895,plain,
    ( m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top
    | r2_hidden(sK7(sK8,sK9,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_117672,c_127885])).

cnf(c_127934,plain,
    ( r2_hidden(sK7(sK8,sK9,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_127895,c_41])).

cnf(c_105517,plain,
    ( sP0(k1_connsp_2(sK8,sK9),sK8,sK9) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top
    | r2_hidden(sK9,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_105273,c_8532])).

cnf(c_118846,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | r2_hidden(sK9,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_105517,c_41,c_5099])).

cnf(c_127952,plain,
    ( r2_hidden(sK9,sK7(sK8,sK9,k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_127934,c_118846])).

cnf(c_18,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | v4_pre_topc(X3,X1)
    | ~ r2_hidden(X3,sK6(X0,X1,X2)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_4791,plain,
    ( sP0(X0,X1,X2) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v4_pre_topc(X3,X1) = iProver_top
    | r2_hidden(X3,sK6(X0,X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_85,plain,
    ( sP0(X0,X1,X2) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v4_pre_topc(X3,X1) = iProver_top
    | r2_hidden(X3,sK6(X0,X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_8450,plain,
    ( sP0(X0,X1,X2) != iProver_top
    | v4_pre_topc(X3,X1) = iProver_top
    | r2_hidden(X3,sK6(X0,X1,X2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4791,c_85,c_5795])).

cnf(c_105518,plain,
    ( sP0(k1_connsp_2(sK8,sK9),sK8,sK9) != iProver_top
    | v4_pre_topc(X0,sK8) = iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_105273,c_8450])).

cnf(c_119777,plain,
    ( v4_pre_topc(X0,sK8) = iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_105518,c_41,c_5099])).

cnf(c_127951,plain,
    ( v4_pre_topc(sK7(sK8,sK9,k1_xboole_0),sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_127934,c_119777])).

cnf(c_19,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | v3_pre_topc(X3,X1)
    | ~ r2_hidden(X3,sK6(X0,X1,X2)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_4790,plain,
    ( sP0(X0,X1,X2) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v3_pre_topc(X3,X1) = iProver_top
    | r2_hidden(X3,sK6(X0,X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_82,plain,
    ( sP0(X0,X1,X2) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v3_pre_topc(X3,X1) = iProver_top
    | r2_hidden(X3,sK6(X0,X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_6772,plain,
    ( sP0(X0,X1,X2) != iProver_top
    | v3_pre_topc(X3,X1) = iProver_top
    | r2_hidden(X3,sK6(X0,X1,X2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4790,c_82,c_5795])).

cnf(c_105519,plain,
    ( sP0(k1_connsp_2(sK8,sK9),sK8,sK9) != iProver_top
    | v3_pre_topc(X0,sK8) = iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_105273,c_6772])).

cnf(c_120403,plain,
    ( v3_pre_topc(X0,sK8) = iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_105519,c_41,c_5099])).

cnf(c_127950,plain,
    ( v3_pre_topc(sK7(sK8,sK9,k1_xboole_0),sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_127934,c_120403])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ v3_pre_topc(sK7(X1,X0,k1_xboole_0),X1)
    | ~ v4_pre_topc(sK7(X1,X0,k1_xboole_0),X1)
    | ~ r2_hidden(X0,sK7(X1,X0,k1_xboole_0))
    | ~ r2_hidden(sK7(X1,X0,k1_xboole_0),k1_xboole_0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_582,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ v3_pre_topc(sK7(X1,X0,k1_xboole_0),X1)
    | ~ v4_pre_topc(sK7(X1,X0,k1_xboole_0),X1)
    | ~ r2_hidden(X0,sK7(X1,X0,k1_xboole_0))
    | ~ r2_hidden(sK7(X1,X0,k1_xboole_0),k1_xboole_0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_35])).

cnf(c_583,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8))))
    | ~ v3_pre_topc(sK7(sK8,X0,k1_xboole_0),sK8)
    | ~ v4_pre_topc(sK7(sK8,X0,k1_xboole_0),sK8)
    | ~ r2_hidden(X0,sK7(sK8,X0,k1_xboole_0))
    | ~ r2_hidden(sK7(sK8,X0,k1_xboole_0),k1_xboole_0)
    | v2_struct_0(sK8)
    | ~ v2_pre_topc(sK8) ),
    inference(unflattening,[status(thm)],[c_582])).

cnf(c_587,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8))))
    | ~ v3_pre_topc(sK7(sK8,X0,k1_xboole_0),sK8)
    | ~ v4_pre_topc(sK7(sK8,X0,k1_xboole_0),sK8)
    | ~ r2_hidden(X0,sK7(sK8,X0,k1_xboole_0))
    | ~ r2_hidden(sK7(sK8,X0,k1_xboole_0),k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_583,c_37,c_36])).

cnf(c_45878,plain,
    ( ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8))))
    | ~ v3_pre_topc(sK7(sK8,sK9,k1_xboole_0),sK8)
    | ~ v4_pre_topc(sK7(sK8,sK9,k1_xboole_0),sK8)
    | ~ r2_hidden(sK7(sK8,sK9,k1_xboole_0),k1_xboole_0)
    | ~ r2_hidden(sK9,sK7(sK8,sK9,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_587])).

cnf(c_45879,plain,
    ( m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8)))) != iProver_top
    | v3_pre_topc(sK7(sK8,sK9,k1_xboole_0),sK8) != iProver_top
    | v4_pre_topc(sK7(sK8,sK9,k1_xboole_0),sK8) != iProver_top
    | r2_hidden(sK7(sK8,sK9,k1_xboole_0),k1_xboole_0) != iProver_top
    | r2_hidden(sK9,sK7(sK8,sK9,k1_xboole_0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45878])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_127952,c_127951,c_127950,c_127895,c_94547,c_45879,c_12542,c_5755,c_5758,c_5173,c_5099,c_4246,c_42,c_41])).


%------------------------------------------------------------------------------
