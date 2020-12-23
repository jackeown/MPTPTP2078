%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:28:49 EST 2020

% Result     : Theorem 3.57s
% Output     : CNFRefutation 3.57s
% Verified   : 
% Statistics : Number of formulae       :  185 (1222 expanded)
%              Number of clauses        :   96 ( 288 expanded)
%              Number of leaves         :   25 ( 418 expanded)
%              Depth                    :   20
%              Number of atoms          :  751 (6780 expanded)
%              Number of equality atoms :  120 ( 265 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f47])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f48])).

fof(f50,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            & ~ r2_hidden(sK2(X0,X1,X2),X0) )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( r2_hidden(sK2(X0,X1,X2),X1)
          | r2_hidden(sK2(X0,X1,X2),X0)
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
              & ~ r2_hidden(sK2(X0,X1,X2),X0) )
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( r2_hidden(sK2(X0,X1,X2),X1)
            | r2_hidden(sK2(X0,X1,X2),X0)
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f49,f50])).

fof(f66,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f97,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k3_tarski(k2_tarski(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f66,f71])).

fof(f104,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k2_tarski(X0,X1)))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f97])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))
                 => m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))
                   => m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))
                  & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
              & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))
                  & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
              & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))
          & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
     => ( ~ m1_subset_1(k2_xboole_0(X2,sK6),u1_struct_0(k9_yellow_6(X0,X1)))
        & m1_subset_1(sK6,u1_struct_0(k9_yellow_6(X0,X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))
              & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
          & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
     => ( ? [X3] :
            ( ~ m1_subset_1(k2_xboole_0(sK5,X3),u1_struct_0(k9_yellow_6(X0,X1)))
            & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
        & m1_subset_1(sK5,u1_struct_0(k9_yellow_6(X0,X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))
                  & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
              & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ~ m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,sK4)))
                & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,sK4))) )
            & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,sK4))) )
        & m1_subset_1(sK4,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))
                    & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
                & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK3,X1)))
                  & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK3,X1))) )
              & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK3,X1))) )
          & m1_subset_1(X1,u1_struct_0(sK3)) )
      & l1_pre_topc(sK3)
      & v2_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK5,sK6),u1_struct_0(k9_yellow_6(sK3,sK4)))
    & m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4)))
    & m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK3,sK4)))
    & m1_subset_1(sK4,u1_struct_0(sK3))
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f40,f58,f57,f56,f55])).

fof(f92,plain,(
    m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4))) ),
    inference(cnf_transformation,[],[f59])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
             => m1_connsp_2(X2,X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X2,X0,X1)
              | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X2,X0,X1)
              | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f87,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f59])).

fof(f88,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f59])).

fof(f89,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f59])).

fof(f90,plain,(
    m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f59])).

fof(f91,plain,(
    m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK3,sK4))) ),
    inference(cnf_transformation,[],[f59])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f24])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k2_tarski(X1,X2)) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f77,f71])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f22])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
              <=> ( v3_pre_topc(X2,X0)
                  & r2_hidden(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
              <=> ( v3_pre_topc(X2,X0)
                  & r2_hidden(X1,X2) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
              <=> ( v3_pre_topc(X2,X0)
                  & r2_hidden(X1,X2) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
                  | ~ v3_pre_topc(X2,X0)
                  | ~ r2_hidden(X1,X2) )
                & ( ( v3_pre_topc(X2,X0)
                    & r2_hidden(X1,X2) )
                  | ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
                  | ~ v3_pre_topc(X2,X0)
                  | ~ r2_hidden(X1,X2) )
                & ( ( v3_pre_topc(X2,X0)
                    & r2_hidden(X1,X2) )
                  | ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f53])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ v3_pre_topc(X2,X0)
      | ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f29])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f78,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f93,plain,(
    ~ m1_subset_1(k2_xboole_0(sK5,sK6),u1_struct_0(k9_yellow_6(sK3,sK4))) ),
    inference(cnf_transformation,[],[f59])).

fof(f103,plain,(
    ~ m1_subset_1(k3_tarski(k2_tarski(sK5,sK6)),u1_struct_0(k9_yellow_6(sK3,sK4))) ),
    inference(definition_unfolding,[],[f93,f71])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(X2,X0)
      | ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f45,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f45])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f100,plain,(
    ! [X0,X1] :
      ( k3_tarski(k2_tarski(X0,X1)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f70,f71])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f74,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f42,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f41])).

fof(f43,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f42,f43])).

fof(f60,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_pre_topc(X2,X0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_xboole_0(X1,X2),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v3_pre_topc(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v3_pre_topc(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(k3_tarski(k2_tarski(X1,X2)),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(definition_unfolding,[],[f81,f71])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k3_tarski(k2_tarski(X2,X1))) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_1197,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k3_tarski(k2_tarski(X2,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4))) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1186,plain,
    ( m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_25,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(X1,X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_21,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_385,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(resolution,[status(thm)],[c_25,c_21])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_415,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_385,c_32])).

cnf(c_416,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK3,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_415])).

cnf(c_31,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_30,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_420,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK3,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_416,c_31,c_30])).

cnf(c_1181,plain,
    ( m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK3,X1))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_420])).

cnf(c_1487,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1186,c_1181])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_36,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_1500,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1487,c_36])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK3,sK4))) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1185,plain,
    ( m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_1488,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1185,c_1181])).

cnf(c_1545,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1488,c_36])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X2,X0) = k3_tarski(k2_tarski(X2,X0)) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_1190,plain,
    ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3411,plain,
    ( k4_subset_1(u1_struct_0(sK3),sK5,X0) = k3_tarski(k2_tarski(sK5,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1545,c_1190])).

cnf(c_4011,plain,
    ( k4_subset_1(u1_struct_0(sK3),sK5,sK6) = k3_tarski(k2_tarski(sK5,sK6)) ),
    inference(superposition,[status(thm)],[c_1500,c_3411])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | m1_subset_1(k4_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1191,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k4_subset_1(X1,X0,X2),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_5053,plain,
    ( m1_subset_1(k3_tarski(k2_tarski(sK5,sK6)),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4011,c_1191])).

cnf(c_10362,plain,
    ( m1_subset_1(k3_tarski(k2_tarski(sK5,sK6)),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5053,c_36,c_1487,c_1488])).

cnf(c_22,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_484,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_32])).

cnf(c_485,plain,
    ( ~ v3_pre_topc(X0,sK3)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X1,X0)
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK3,X1)))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_484])).

cnf(c_489,plain,
    ( ~ v3_pre_topc(X0,sK3)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X1,X0)
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK3,X1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_485,c_31,c_30])).

cnf(c_19,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_505,plain,
    ( ~ v3_pre_topc(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X1,X0)
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK3,X1))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_489,c_19])).

cnf(c_1178,plain,
    ( v3_pre_topc(X0,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(X1,X0) != iProver_top
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK3,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_505])).

cnf(c_17,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1189,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1934,plain,
    ( v3_pre_topc(X0,sK3) != iProver_top
    | m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK3,X1))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1178,c_1189])).

cnf(c_26,negated_conjecture,
    ( ~ m1_subset_1(k3_tarski(k2_tarski(sK5,sK6)),u1_struct_0(k9_yellow_6(sK3,sK4))) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1187,plain,
    ( m1_subset_1(k3_tarski(k2_tarski(sK5,sK6)),u1_struct_0(k9_yellow_6(sK3,sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_2311,plain,
    ( v3_pre_topc(k3_tarski(k2_tarski(sK5,sK6)),sK3) != iProver_top
    | m1_subset_1(k3_tarski(k2_tarski(sK5,sK6)),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(sK4,k3_tarski(k2_tarski(sK5,sK6))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1934,c_1187])).

cnf(c_10374,plain,
    ( v3_pre_topc(k3_tarski(k2_tarski(sK5,sK6)),sK3) != iProver_top
    | r2_hidden(sK4,k3_tarski(k2_tarski(sK5,sK6))) != iProver_top ),
    inference(superposition,[status(thm)],[c_10362,c_2311])).

cnf(c_37,plain,
    ( m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_38,plain,
    ( m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_740,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1564,plain,
    ( u1_struct_0(k9_yellow_6(sK3,sK4)) = u1_struct_0(k9_yellow_6(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_740])).

cnf(c_23,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_460,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_32])).

cnf(c_461,plain,
    ( v3_pre_topc(X0,sK3)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(sK3,X1)))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_460])).

cnf(c_465,plain,
    ( v3_pre_topc(X0,sK3)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(sK3,X1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_461,c_31,c_30])).

cnf(c_1401,plain,
    ( v3_pre_topc(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(sK3,sK4))) ),
    inference(instantiation,[status(thm)],[c_465])).

cnf(c_1661,plain,
    ( v3_pre_topc(sK6,sK3)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(sK6,u1_struct_0(k9_yellow_6(sK3,sK4))) ),
    inference(instantiation,[status(thm)],[c_1401])).

cnf(c_1662,plain,
    ( v3_pre_topc(sK6,sK3) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(sK6,u1_struct_0(k9_yellow_6(sK3,sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1661])).

cnf(c_1682,plain,
    ( v3_pre_topc(sK5,sK3)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(sK5,u1_struct_0(k9_yellow_6(sK3,sK4))) ),
    inference(instantiation,[status(thm)],[c_1401])).

cnf(c_1683,plain,
    ( v3_pre_topc(sK5,sK3) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(sK5,u1_struct_0(k9_yellow_6(sK3,sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1682])).

cnf(c_745,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1468,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k3_tarski(k2_tarski(sK5,sK6)),u1_struct_0(k9_yellow_6(sK3,sK4)))
    | u1_struct_0(k9_yellow_6(sK3,sK4)) != X1
    | k3_tarski(k2_tarski(sK5,sK6)) != X0 ),
    inference(instantiation,[status(thm)],[c_745])).

cnf(c_1563,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK3,sK4)))
    | m1_subset_1(k3_tarski(k2_tarski(sK5,sK6)),u1_struct_0(k9_yellow_6(sK3,sK4)))
    | u1_struct_0(k9_yellow_6(sK3,sK4)) != u1_struct_0(k9_yellow_6(sK3,sK4))
    | k3_tarski(k2_tarski(sK5,sK6)) != X0 ),
    inference(instantiation,[status(thm)],[c_1468])).

cnf(c_1724,plain,
    ( m1_subset_1(k3_tarski(k2_tarski(sK5,sK6)),u1_struct_0(k9_yellow_6(sK3,sK4)))
    | ~ m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4)))
    | u1_struct_0(k9_yellow_6(sK3,sK4)) != u1_struct_0(k9_yellow_6(sK3,sK4))
    | k3_tarski(k2_tarski(sK5,sK6)) != sK6 ),
    inference(instantiation,[status(thm)],[c_1563])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_tarski(k2_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f100])).

cnf(c_357,plain,
    ( r2_hidden(sK1(X0,X1),X0)
    | k3_tarski(k2_tarski(X0,X1)) = X1 ),
    inference(resolution,[status(thm)],[c_3,c_10])).

cnf(c_1765,plain,
    ( r2_hidden(sK1(sK5,sK6),sK5)
    | k3_tarski(k2_tarski(sK5,sK6)) = sK6 ),
    inference(instantiation,[status(thm)],[c_357])).

cnf(c_1770,plain,
    ( k3_tarski(k2_tarski(sK5,sK6)) = sK6
    | r2_hidden(sK1(sK5,sK6),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1765])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1513,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK3,sK4)))
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK3,sK4)))
    | v1_xboole_0(u1_struct_0(k9_yellow_6(sK3,sK4))) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_2370,plain,
    ( ~ m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4)))
    | r2_hidden(sK6,u1_struct_0(k9_yellow_6(sK3,sK4)))
    | v1_xboole_0(u1_struct_0(k9_yellow_6(sK3,sK4))) ),
    inference(instantiation,[status(thm)],[c_1513])).

cnf(c_2371,plain,
    ( m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4))) != iProver_top
    | r2_hidden(sK6,u1_struct_0(k9_yellow_6(sK3,sK4))) = iProver_top
    | v1_xboole_0(u1_struct_0(k9_yellow_6(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2370])).

cnf(c_2373,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK3,sK4)))
    | r2_hidden(sK5,u1_struct_0(k9_yellow_6(sK3,sK4)))
    | v1_xboole_0(u1_struct_0(k9_yellow_6(sK3,sK4))) ),
    inference(instantiation,[status(thm)],[c_1513])).

cnf(c_2374,plain,
    ( m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK3,sK4))) != iProver_top
    | r2_hidden(sK5,u1_struct_0(k9_yellow_6(sK3,sK4))) = iProver_top
    | v1_xboole_0(u1_struct_0(k9_yellow_6(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2373])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1193,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2510,plain,
    ( v1_xboole_0(u1_struct_0(k9_yellow_6(sK3,sK4))) != iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1185,c_1193])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2604,plain,
    ( ~ r2_hidden(sK1(sK5,sK6),sK5)
    | ~ v1_xboole_0(sK5) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2605,plain,
    ( r2_hidden(sK1(sK5,sK6),sK5) != iProver_top
    | v1_xboole_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2604])).

cnf(c_20,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ v3_pre_topc(X2,X1)
    | v3_pre_topc(k3_tarski(k2_tarski(X2,X0)),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_532,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ v3_pre_topc(X2,X1)
    | v3_pre_topc(k3_tarski(k2_tarski(X2,X0)),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_30])).

cnf(c_533,plain,
    ( ~ v3_pre_topc(X0,sK3)
    | ~ v3_pre_topc(X1,sK3)
    | v3_pre_topc(k3_tarski(k2_tarski(X1,X0)),sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_532])).

cnf(c_537,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v3_pre_topc(k3_tarski(k2_tarski(X1,X0)),sK3)
    | ~ v3_pre_topc(X1,sK3)
    | ~ v3_pre_topc(X0,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_533,c_31])).

cnf(c_538,plain,
    ( ~ v3_pre_topc(X0,sK3)
    | ~ v3_pre_topc(X1,sK3)
    | v3_pre_topc(k3_tarski(k2_tarski(X1,X0)),sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(renaming,[status(thm)],[c_537])).

cnf(c_3555,plain,
    ( ~ v3_pre_topc(X0,sK3)
    | v3_pre_topc(k3_tarski(k2_tarski(X0,sK6)),sK3)
    | ~ v3_pre_topc(sK6,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_538])).

cnf(c_6927,plain,
    ( v3_pre_topc(k3_tarski(k2_tarski(sK5,sK6)),sK3)
    | ~ v3_pre_topc(sK6,sK3)
    | ~ v3_pre_topc(sK5,sK3)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_3555])).

cnf(c_6928,plain,
    ( v3_pre_topc(k3_tarski(k2_tarski(sK5,sK6)),sK3) = iProver_top
    | v3_pre_topc(sK6,sK3) != iProver_top
    | v3_pre_topc(sK5,sK3) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6927])).

cnf(c_10455,plain,
    ( r2_hidden(sK4,k3_tarski(k2_tarski(sK5,sK6))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10374,c_36,c_37,c_27,c_38,c_26,c_1487,c_1488,c_1564,c_1662,c_1683,c_1724,c_1770,c_2311,c_2371,c_2374,c_2510,c_2605,c_5053,c_6928])).

cnf(c_10460,plain,
    ( r2_hidden(sK4,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1197,c_10455])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(X1,X0)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_436,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(X1,X0)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_32])).

cnf(c_437,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | r2_hidden(X0,X1)
    | ~ r2_hidden(X1,u1_struct_0(k9_yellow_6(sK3,X0)))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_436])).

cnf(c_441,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | r2_hidden(X0,X1)
    | ~ r2_hidden(X1,u1_struct_0(k9_yellow_6(sK3,X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_437,c_31,c_30])).

cnf(c_1406,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(sK3,sK4)))
    | r2_hidden(sK4,X0) ),
    inference(instantiation,[status(thm)],[c_441])).

cnf(c_1660,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3)))
    | r2_hidden(sK4,sK6)
    | ~ r2_hidden(sK6,u1_struct_0(k9_yellow_6(sK3,sK4))) ),
    inference(instantiation,[status(thm)],[c_1406])).

cnf(c_1664,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(sK4,sK6) = iProver_top
    | r2_hidden(sK6,u1_struct_0(k9_yellow_6(sK3,sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1660])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10460,c_2605,c_2510,c_2371,c_1770,c_1724,c_1664,c_1564,c_1487,c_26,c_38,c_27,c_36])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:53:26 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 3.57/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.57/0.98  
% 3.57/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.57/0.98  
% 3.57/0.98  ------  iProver source info
% 3.57/0.98  
% 3.57/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.57/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.57/0.98  git: non_committed_changes: false
% 3.57/0.98  git: last_make_outside_of_git: false
% 3.57/0.98  
% 3.57/0.98  ------ 
% 3.57/0.98  
% 3.57/0.98  ------ Input Options
% 3.57/0.98  
% 3.57/0.98  --out_options                           all
% 3.57/0.98  --tptp_safe_out                         true
% 3.57/0.98  --problem_path                          ""
% 3.57/0.98  --include_path                          ""
% 3.57/0.98  --clausifier                            res/vclausify_rel
% 3.57/0.98  --clausifier_options                    --mode clausify
% 3.57/0.98  --stdin                                 false
% 3.57/0.98  --stats_out                             all
% 3.57/0.98  
% 3.57/0.98  ------ General Options
% 3.57/0.98  
% 3.57/0.98  --fof                                   false
% 3.57/0.98  --time_out_real                         305.
% 3.57/0.98  --time_out_virtual                      -1.
% 3.57/0.98  --symbol_type_check                     false
% 3.57/0.98  --clausify_out                          false
% 3.57/0.98  --sig_cnt_out                           false
% 3.57/0.98  --trig_cnt_out                          false
% 3.57/0.98  --trig_cnt_out_tolerance                1.
% 3.57/0.98  --trig_cnt_out_sk_spl                   false
% 3.57/0.98  --abstr_cl_out                          false
% 3.57/0.98  
% 3.57/0.98  ------ Global Options
% 3.57/0.98  
% 3.57/0.98  --schedule                              default
% 3.57/0.98  --add_important_lit                     false
% 3.57/0.98  --prop_solver_per_cl                    1000
% 3.57/0.98  --min_unsat_core                        false
% 3.57/0.98  --soft_assumptions                      false
% 3.57/0.98  --soft_lemma_size                       3
% 3.57/0.98  --prop_impl_unit_size                   0
% 3.57/0.98  --prop_impl_unit                        []
% 3.57/0.98  --share_sel_clauses                     true
% 3.57/0.98  --reset_solvers                         false
% 3.57/0.98  --bc_imp_inh                            [conj_cone]
% 3.57/0.98  --conj_cone_tolerance                   3.
% 3.57/0.98  --extra_neg_conj                        none
% 3.57/0.98  --large_theory_mode                     true
% 3.57/0.98  --prolific_symb_bound                   200
% 3.57/0.98  --lt_threshold                          2000
% 3.57/0.98  --clause_weak_htbl                      true
% 3.57/0.98  --gc_record_bc_elim                     false
% 3.57/0.98  
% 3.57/0.98  ------ Preprocessing Options
% 3.57/0.98  
% 3.57/0.98  --preprocessing_flag                    true
% 3.57/0.98  --time_out_prep_mult                    0.1
% 3.57/0.98  --splitting_mode                        input
% 3.57/0.98  --splitting_grd                         true
% 3.57/0.98  --splitting_cvd                         false
% 3.57/0.98  --splitting_cvd_svl                     false
% 3.57/0.98  --splitting_nvd                         32
% 3.57/0.98  --sub_typing                            true
% 3.57/0.98  --prep_gs_sim                           true
% 3.57/0.98  --prep_unflatten                        true
% 3.57/0.98  --prep_res_sim                          true
% 3.57/0.98  --prep_upred                            true
% 3.57/0.98  --prep_sem_filter                       exhaustive
% 3.57/0.98  --prep_sem_filter_out                   false
% 3.57/0.98  --pred_elim                             true
% 3.57/0.98  --res_sim_input                         true
% 3.57/0.98  --eq_ax_congr_red                       true
% 3.57/0.98  --pure_diseq_elim                       true
% 3.57/0.98  --brand_transform                       false
% 3.57/0.98  --non_eq_to_eq                          false
% 3.57/0.98  --prep_def_merge                        true
% 3.57/0.98  --prep_def_merge_prop_impl              false
% 3.57/0.98  --prep_def_merge_mbd                    true
% 3.57/0.98  --prep_def_merge_tr_red                 false
% 3.57/0.98  --prep_def_merge_tr_cl                  false
% 3.57/0.98  --smt_preprocessing                     true
% 3.57/0.98  --smt_ac_axioms                         fast
% 3.57/0.98  --preprocessed_out                      false
% 3.57/0.98  --preprocessed_stats                    false
% 3.57/0.98  
% 3.57/0.98  ------ Abstraction refinement Options
% 3.57/0.98  
% 3.57/0.98  --abstr_ref                             []
% 3.57/0.98  --abstr_ref_prep                        false
% 3.57/0.98  --abstr_ref_until_sat                   false
% 3.57/0.98  --abstr_ref_sig_restrict                funpre
% 3.57/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.57/0.98  --abstr_ref_under                       []
% 3.57/0.98  
% 3.57/0.98  ------ SAT Options
% 3.57/0.98  
% 3.57/0.98  --sat_mode                              false
% 3.57/0.98  --sat_fm_restart_options                ""
% 3.57/0.98  --sat_gr_def                            false
% 3.57/0.98  --sat_epr_types                         true
% 3.57/0.98  --sat_non_cyclic_types                  false
% 3.57/0.98  --sat_finite_models                     false
% 3.57/0.98  --sat_fm_lemmas                         false
% 3.57/0.98  --sat_fm_prep                           false
% 3.57/0.98  --sat_fm_uc_incr                        true
% 3.57/0.98  --sat_out_model                         small
% 3.57/0.98  --sat_out_clauses                       false
% 3.57/0.98  
% 3.57/0.98  ------ QBF Options
% 3.57/0.98  
% 3.57/0.98  --qbf_mode                              false
% 3.57/0.98  --qbf_elim_univ                         false
% 3.57/0.98  --qbf_dom_inst                          none
% 3.57/0.98  --qbf_dom_pre_inst                      false
% 3.57/0.98  --qbf_sk_in                             false
% 3.57/0.98  --qbf_pred_elim                         true
% 3.57/0.98  --qbf_split                             512
% 3.57/0.98  
% 3.57/0.98  ------ BMC1 Options
% 3.57/0.98  
% 3.57/0.98  --bmc1_incremental                      false
% 3.57/0.98  --bmc1_axioms                           reachable_all
% 3.57/0.98  --bmc1_min_bound                        0
% 3.57/0.98  --bmc1_max_bound                        -1
% 3.57/0.98  --bmc1_max_bound_default                -1
% 3.57/0.98  --bmc1_symbol_reachability              true
% 3.57/0.98  --bmc1_property_lemmas                  false
% 3.57/0.98  --bmc1_k_induction                      false
% 3.57/0.98  --bmc1_non_equiv_states                 false
% 3.57/0.98  --bmc1_deadlock                         false
% 3.57/0.98  --bmc1_ucm                              false
% 3.57/0.98  --bmc1_add_unsat_core                   none
% 3.57/0.98  --bmc1_unsat_core_children              false
% 3.57/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.57/0.98  --bmc1_out_stat                         full
% 3.57/0.98  --bmc1_ground_init                      false
% 3.57/0.98  --bmc1_pre_inst_next_state              false
% 3.57/0.98  --bmc1_pre_inst_state                   false
% 3.57/0.98  --bmc1_pre_inst_reach_state             false
% 3.57/0.98  --bmc1_out_unsat_core                   false
% 3.57/0.98  --bmc1_aig_witness_out                  false
% 3.57/0.98  --bmc1_verbose                          false
% 3.57/0.98  --bmc1_dump_clauses_tptp                false
% 3.57/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.57/0.98  --bmc1_dump_file                        -
% 3.57/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.57/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.57/0.98  --bmc1_ucm_extend_mode                  1
% 3.57/0.98  --bmc1_ucm_init_mode                    2
% 3.57/0.98  --bmc1_ucm_cone_mode                    none
% 3.57/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.57/0.98  --bmc1_ucm_relax_model                  4
% 3.57/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.57/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.57/0.98  --bmc1_ucm_layered_model                none
% 3.57/0.98  --bmc1_ucm_max_lemma_size               10
% 3.57/0.98  
% 3.57/0.98  ------ AIG Options
% 3.57/0.98  
% 3.57/0.98  --aig_mode                              false
% 3.57/0.98  
% 3.57/0.98  ------ Instantiation Options
% 3.57/0.98  
% 3.57/0.98  --instantiation_flag                    true
% 3.57/0.98  --inst_sos_flag                         false
% 3.57/0.98  --inst_sos_phase                        true
% 3.57/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.57/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.57/0.98  --inst_lit_sel_side                     num_symb
% 3.57/0.98  --inst_solver_per_active                1400
% 3.57/0.98  --inst_solver_calls_frac                1.
% 3.57/0.98  --inst_passive_queue_type               priority_queues
% 3.57/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.57/0.98  --inst_passive_queues_freq              [25;2]
% 3.57/0.98  --inst_dismatching                      true
% 3.57/0.98  --inst_eager_unprocessed_to_passive     true
% 3.57/0.98  --inst_prop_sim_given                   true
% 3.57/0.98  --inst_prop_sim_new                     false
% 3.57/0.98  --inst_subs_new                         false
% 3.57/0.98  --inst_eq_res_simp                      false
% 3.57/0.98  --inst_subs_given                       false
% 3.57/0.98  --inst_orphan_elimination               true
% 3.57/0.98  --inst_learning_loop_flag               true
% 3.57/0.98  --inst_learning_start                   3000
% 3.57/0.98  --inst_learning_factor                  2
% 3.57/0.98  --inst_start_prop_sim_after_learn       3
% 3.57/0.98  --inst_sel_renew                        solver
% 3.57/0.98  --inst_lit_activity_flag                true
% 3.57/0.98  --inst_restr_to_given                   false
% 3.57/0.98  --inst_activity_threshold               500
% 3.57/0.98  --inst_out_proof                        true
% 3.57/0.98  
% 3.57/0.98  ------ Resolution Options
% 3.57/0.98  
% 3.57/0.98  --resolution_flag                       true
% 3.57/0.98  --res_lit_sel                           adaptive
% 3.57/0.98  --res_lit_sel_side                      none
% 3.57/0.98  --res_ordering                          kbo
% 3.57/0.98  --res_to_prop_solver                    active
% 3.57/0.98  --res_prop_simpl_new                    false
% 3.57/0.98  --res_prop_simpl_given                  true
% 3.57/0.98  --res_passive_queue_type                priority_queues
% 3.57/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.57/0.98  --res_passive_queues_freq               [15;5]
% 3.57/0.98  --res_forward_subs                      full
% 3.57/0.98  --res_backward_subs                     full
% 3.57/0.98  --res_forward_subs_resolution           true
% 3.57/0.98  --res_backward_subs_resolution          true
% 3.57/0.98  --res_orphan_elimination                true
% 3.57/0.98  --res_time_limit                        2.
% 3.57/0.98  --res_out_proof                         true
% 3.57/0.98  
% 3.57/0.98  ------ Superposition Options
% 3.57/0.98  
% 3.57/0.98  --superposition_flag                    true
% 3.57/0.98  --sup_passive_queue_type                priority_queues
% 3.57/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.57/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.57/0.98  --demod_completeness_check              fast
% 3.57/0.98  --demod_use_ground                      true
% 3.57/0.98  --sup_to_prop_solver                    passive
% 3.57/0.98  --sup_prop_simpl_new                    true
% 3.57/0.98  --sup_prop_simpl_given                  true
% 3.57/0.98  --sup_fun_splitting                     false
% 3.57/0.98  --sup_smt_interval                      50000
% 3.57/0.98  
% 3.57/0.98  ------ Superposition Simplification Setup
% 3.57/0.98  
% 3.57/0.98  --sup_indices_passive                   []
% 3.57/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.57/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.57/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.57/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.57/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.57/0.98  --sup_full_bw                           [BwDemod]
% 3.57/0.98  --sup_immed_triv                        [TrivRules]
% 3.57/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.57/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.57/0.98  --sup_immed_bw_main                     []
% 3.57/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.57/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.57/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.57/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.57/0.98  
% 3.57/0.98  ------ Combination Options
% 3.57/0.98  
% 3.57/0.98  --comb_res_mult                         3
% 3.57/0.98  --comb_sup_mult                         2
% 3.57/0.98  --comb_inst_mult                        10
% 3.57/0.98  
% 3.57/0.98  ------ Debug Options
% 3.57/0.98  
% 3.57/0.98  --dbg_backtrace                         false
% 3.57/0.98  --dbg_dump_prop_clauses                 false
% 3.57/0.98  --dbg_dump_prop_clauses_file            -
% 3.57/0.98  --dbg_out_stat                          false
% 3.57/0.98  ------ Parsing...
% 3.57/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.57/0.98  
% 3.57/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.57/0.98  
% 3.57/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.57/0.98  
% 3.57/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.57/0.98  ------ Proving...
% 3.57/0.98  ------ Problem Properties 
% 3.57/0.98  
% 3.57/0.98  
% 3.57/0.98  clauses                                 26
% 3.57/0.98  conjectures                             4
% 3.57/0.98  EPR                                     5
% 3.57/0.98  Horn                                    21
% 3.57/0.98  unary                                   4
% 3.57/0.98  binary                                  7
% 3.57/0.98  lits                                    69
% 3.57/0.98  lits eq                                 6
% 3.57/0.98  fd_pure                                 0
% 3.57/0.98  fd_pseudo                               0
% 3.57/0.98  fd_cond                                 0
% 3.57/0.98  fd_pseudo_cond                          3
% 3.57/0.98  AC symbols                              0
% 3.57/0.98  
% 3.57/0.98  ------ Schedule dynamic 5 is on 
% 3.57/0.98  
% 3.57/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.57/0.98  
% 3.57/0.98  
% 3.57/0.98  ------ 
% 3.57/0.98  Current options:
% 3.57/0.98  ------ 
% 3.57/0.98  
% 3.57/0.98  ------ Input Options
% 3.57/0.98  
% 3.57/0.98  --out_options                           all
% 3.57/0.98  --tptp_safe_out                         true
% 3.57/0.98  --problem_path                          ""
% 3.57/0.98  --include_path                          ""
% 3.57/0.98  --clausifier                            res/vclausify_rel
% 3.57/0.98  --clausifier_options                    --mode clausify
% 3.57/0.98  --stdin                                 false
% 3.57/0.98  --stats_out                             all
% 3.57/0.98  
% 3.57/0.98  ------ General Options
% 3.57/0.98  
% 3.57/0.98  --fof                                   false
% 3.57/0.98  --time_out_real                         305.
% 3.57/0.98  --time_out_virtual                      -1.
% 3.57/0.98  --symbol_type_check                     false
% 3.57/0.98  --clausify_out                          false
% 3.57/0.98  --sig_cnt_out                           false
% 3.57/0.98  --trig_cnt_out                          false
% 3.57/0.98  --trig_cnt_out_tolerance                1.
% 3.57/0.98  --trig_cnt_out_sk_spl                   false
% 3.57/0.98  --abstr_cl_out                          false
% 3.57/0.98  
% 3.57/0.98  ------ Global Options
% 3.57/0.98  
% 3.57/0.98  --schedule                              default
% 3.57/0.98  --add_important_lit                     false
% 3.57/0.98  --prop_solver_per_cl                    1000
% 3.57/0.98  --min_unsat_core                        false
% 3.57/0.98  --soft_assumptions                      false
% 3.57/0.98  --soft_lemma_size                       3
% 3.57/0.98  --prop_impl_unit_size                   0
% 3.57/0.98  --prop_impl_unit                        []
% 3.57/0.98  --share_sel_clauses                     true
% 3.57/0.98  --reset_solvers                         false
% 3.57/0.98  --bc_imp_inh                            [conj_cone]
% 3.57/0.98  --conj_cone_tolerance                   3.
% 3.57/0.98  --extra_neg_conj                        none
% 3.57/0.98  --large_theory_mode                     true
% 3.57/0.98  --prolific_symb_bound                   200
% 3.57/0.98  --lt_threshold                          2000
% 3.57/0.98  --clause_weak_htbl                      true
% 3.57/0.98  --gc_record_bc_elim                     false
% 3.57/0.98  
% 3.57/0.98  ------ Preprocessing Options
% 3.57/0.98  
% 3.57/0.98  --preprocessing_flag                    true
% 3.57/0.98  --time_out_prep_mult                    0.1
% 3.57/0.98  --splitting_mode                        input
% 3.57/0.98  --splitting_grd                         true
% 3.57/0.98  --splitting_cvd                         false
% 3.57/0.98  --splitting_cvd_svl                     false
% 3.57/0.98  --splitting_nvd                         32
% 3.57/0.98  --sub_typing                            true
% 3.57/0.98  --prep_gs_sim                           true
% 3.57/0.98  --prep_unflatten                        true
% 3.57/0.98  --prep_res_sim                          true
% 3.57/0.98  --prep_upred                            true
% 3.57/0.98  --prep_sem_filter                       exhaustive
% 3.57/0.98  --prep_sem_filter_out                   false
% 3.57/0.98  --pred_elim                             true
% 3.57/0.98  --res_sim_input                         true
% 3.57/0.98  --eq_ax_congr_red                       true
% 3.57/0.98  --pure_diseq_elim                       true
% 3.57/0.98  --brand_transform                       false
% 3.57/0.98  --non_eq_to_eq                          false
% 3.57/0.98  --prep_def_merge                        true
% 3.57/0.98  --prep_def_merge_prop_impl              false
% 3.57/0.98  --prep_def_merge_mbd                    true
% 3.57/0.98  --prep_def_merge_tr_red                 false
% 3.57/0.98  --prep_def_merge_tr_cl                  false
% 3.57/0.98  --smt_preprocessing                     true
% 3.57/0.98  --smt_ac_axioms                         fast
% 3.57/0.98  --preprocessed_out                      false
% 3.57/0.98  --preprocessed_stats                    false
% 3.57/0.98  
% 3.57/0.98  ------ Abstraction refinement Options
% 3.57/0.98  
% 3.57/0.98  --abstr_ref                             []
% 3.57/0.98  --abstr_ref_prep                        false
% 3.57/0.98  --abstr_ref_until_sat                   false
% 3.57/0.98  --abstr_ref_sig_restrict                funpre
% 3.57/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.57/0.98  --abstr_ref_under                       []
% 3.57/0.98  
% 3.57/0.98  ------ SAT Options
% 3.57/0.98  
% 3.57/0.98  --sat_mode                              false
% 3.57/0.98  --sat_fm_restart_options                ""
% 3.57/0.98  --sat_gr_def                            false
% 3.57/0.98  --sat_epr_types                         true
% 3.57/0.98  --sat_non_cyclic_types                  false
% 3.57/0.98  --sat_finite_models                     false
% 3.57/0.98  --sat_fm_lemmas                         false
% 3.57/0.98  --sat_fm_prep                           false
% 3.57/0.98  --sat_fm_uc_incr                        true
% 3.57/0.98  --sat_out_model                         small
% 3.57/0.98  --sat_out_clauses                       false
% 3.57/0.98  
% 3.57/0.98  ------ QBF Options
% 3.57/0.98  
% 3.57/0.98  --qbf_mode                              false
% 3.57/0.98  --qbf_elim_univ                         false
% 3.57/0.98  --qbf_dom_inst                          none
% 3.57/0.98  --qbf_dom_pre_inst                      false
% 3.57/0.98  --qbf_sk_in                             false
% 3.57/0.98  --qbf_pred_elim                         true
% 3.57/0.98  --qbf_split                             512
% 3.57/0.98  
% 3.57/0.98  ------ BMC1 Options
% 3.57/0.98  
% 3.57/0.98  --bmc1_incremental                      false
% 3.57/0.98  --bmc1_axioms                           reachable_all
% 3.57/0.98  --bmc1_min_bound                        0
% 3.57/0.98  --bmc1_max_bound                        -1
% 3.57/0.98  --bmc1_max_bound_default                -1
% 3.57/0.98  --bmc1_symbol_reachability              true
% 3.57/0.98  --bmc1_property_lemmas                  false
% 3.57/0.98  --bmc1_k_induction                      false
% 3.57/0.98  --bmc1_non_equiv_states                 false
% 3.57/0.98  --bmc1_deadlock                         false
% 3.57/0.98  --bmc1_ucm                              false
% 3.57/0.98  --bmc1_add_unsat_core                   none
% 3.57/0.98  --bmc1_unsat_core_children              false
% 3.57/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.57/0.98  --bmc1_out_stat                         full
% 3.57/0.98  --bmc1_ground_init                      false
% 3.57/0.98  --bmc1_pre_inst_next_state              false
% 3.57/0.98  --bmc1_pre_inst_state                   false
% 3.57/0.98  --bmc1_pre_inst_reach_state             false
% 3.57/0.98  --bmc1_out_unsat_core                   false
% 3.57/0.98  --bmc1_aig_witness_out                  false
% 3.57/0.98  --bmc1_verbose                          false
% 3.57/0.98  --bmc1_dump_clauses_tptp                false
% 3.57/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.57/0.98  --bmc1_dump_file                        -
% 3.57/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.57/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.57/0.98  --bmc1_ucm_extend_mode                  1
% 3.57/0.98  --bmc1_ucm_init_mode                    2
% 3.57/0.98  --bmc1_ucm_cone_mode                    none
% 3.57/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.57/0.98  --bmc1_ucm_relax_model                  4
% 3.57/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.57/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.57/0.98  --bmc1_ucm_layered_model                none
% 3.57/0.98  --bmc1_ucm_max_lemma_size               10
% 3.57/0.98  
% 3.57/0.98  ------ AIG Options
% 3.57/0.98  
% 3.57/0.98  --aig_mode                              false
% 3.57/0.98  
% 3.57/0.98  ------ Instantiation Options
% 3.57/0.98  
% 3.57/0.98  --instantiation_flag                    true
% 3.57/0.98  --inst_sos_flag                         false
% 3.57/0.98  --inst_sos_phase                        true
% 3.57/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.57/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.57/0.98  --inst_lit_sel_side                     none
% 3.57/0.98  --inst_solver_per_active                1400
% 3.57/0.98  --inst_solver_calls_frac                1.
% 3.57/0.98  --inst_passive_queue_type               priority_queues
% 3.57/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.57/0.98  --inst_passive_queues_freq              [25;2]
% 3.57/0.98  --inst_dismatching                      true
% 3.57/0.98  --inst_eager_unprocessed_to_passive     true
% 3.57/0.98  --inst_prop_sim_given                   true
% 3.57/0.98  --inst_prop_sim_new                     false
% 3.57/0.98  --inst_subs_new                         false
% 3.57/0.98  --inst_eq_res_simp                      false
% 3.57/0.98  --inst_subs_given                       false
% 3.57/0.98  --inst_orphan_elimination               true
% 3.57/0.98  --inst_learning_loop_flag               true
% 3.57/0.98  --inst_learning_start                   3000
% 3.57/0.98  --inst_learning_factor                  2
% 3.57/0.98  --inst_start_prop_sim_after_learn       3
% 3.57/0.98  --inst_sel_renew                        solver
% 3.57/0.98  --inst_lit_activity_flag                true
% 3.57/0.98  --inst_restr_to_given                   false
% 3.57/0.98  --inst_activity_threshold               500
% 3.57/0.98  --inst_out_proof                        true
% 3.57/0.98  
% 3.57/0.98  ------ Resolution Options
% 3.57/0.98  
% 3.57/0.98  --resolution_flag                       false
% 3.57/0.98  --res_lit_sel                           adaptive
% 3.57/0.98  --res_lit_sel_side                      none
% 3.57/0.98  --res_ordering                          kbo
% 3.57/0.98  --res_to_prop_solver                    active
% 3.57/0.98  --res_prop_simpl_new                    false
% 3.57/0.98  --res_prop_simpl_given                  true
% 3.57/0.98  --res_passive_queue_type                priority_queues
% 3.57/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.57/0.98  --res_passive_queues_freq               [15;5]
% 3.57/0.98  --res_forward_subs                      full
% 3.57/0.98  --res_backward_subs                     full
% 3.57/0.98  --res_forward_subs_resolution           true
% 3.57/0.98  --res_backward_subs_resolution          true
% 3.57/0.98  --res_orphan_elimination                true
% 3.57/0.98  --res_time_limit                        2.
% 3.57/0.98  --res_out_proof                         true
% 3.57/0.98  
% 3.57/0.98  ------ Superposition Options
% 3.57/0.98  
% 3.57/0.98  --superposition_flag                    true
% 3.57/0.98  --sup_passive_queue_type                priority_queues
% 3.57/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.57/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.57/0.98  --demod_completeness_check              fast
% 3.57/0.98  --demod_use_ground                      true
% 3.57/0.98  --sup_to_prop_solver                    passive
% 3.57/0.98  --sup_prop_simpl_new                    true
% 3.57/0.98  --sup_prop_simpl_given                  true
% 3.57/0.98  --sup_fun_splitting                     false
% 3.57/0.98  --sup_smt_interval                      50000
% 3.57/0.98  
% 3.57/0.98  ------ Superposition Simplification Setup
% 3.57/0.98  
% 3.57/0.98  --sup_indices_passive                   []
% 3.57/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.57/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.57/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.57/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.57/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.57/0.98  --sup_full_bw                           [BwDemod]
% 3.57/0.98  --sup_immed_triv                        [TrivRules]
% 3.57/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.57/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.57/0.98  --sup_immed_bw_main                     []
% 3.57/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.57/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.57/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.57/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.57/0.98  
% 3.57/0.98  ------ Combination Options
% 3.57/0.98  
% 3.57/0.98  --comb_res_mult                         3
% 3.57/0.98  --comb_sup_mult                         2
% 3.57/0.98  --comb_inst_mult                        10
% 3.57/0.98  
% 3.57/0.98  ------ Debug Options
% 3.57/0.98  
% 3.57/0.98  --dbg_backtrace                         false
% 3.57/0.98  --dbg_dump_prop_clauses                 false
% 3.57/0.98  --dbg_dump_prop_clauses_file            -
% 3.57/0.98  --dbg_out_stat                          false
% 3.57/0.98  
% 3.57/0.98  
% 3.57/0.98  
% 3.57/0.98  
% 3.57/0.98  ------ Proving...
% 3.57/0.98  
% 3.57/0.98  
% 3.57/0.98  % SZS status Theorem for theBenchmark.p
% 3.57/0.98  
% 3.57/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.57/0.98  
% 3.57/0.98  fof(f3,axiom,(
% 3.57/0.98    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 3.57/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.57/0.98  
% 3.57/0.98  fof(f47,plain,(
% 3.57/0.98    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.57/0.98    inference(nnf_transformation,[],[f3])).
% 3.57/0.98  
% 3.57/0.98  fof(f48,plain,(
% 3.57/0.98    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.57/0.98    inference(flattening,[],[f47])).
% 3.57/0.98  
% 3.57/0.98  fof(f49,plain,(
% 3.57/0.98    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.57/0.98    inference(rectify,[],[f48])).
% 3.57/0.98  
% 3.57/0.98  fof(f50,plain,(
% 3.57/0.98    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK2(X0,X1,X2),X1) & ~r2_hidden(sK2(X0,X1,X2),X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 3.57/0.98    introduced(choice_axiom,[])).
% 3.57/0.98  
% 3.57/0.98  fof(f51,plain,(
% 3.57/0.98    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK2(X0,X1,X2),X1) & ~r2_hidden(sK2(X0,X1,X2),X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.57/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f49,f50])).
% 3.57/0.98  
% 3.57/0.98  fof(f66,plain,(
% 3.57/0.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 3.57/0.98    inference(cnf_transformation,[],[f51])).
% 3.57/0.98  
% 3.57/0.98  fof(f5,axiom,(
% 3.57/0.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.57/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.57/0.98  
% 3.57/0.98  fof(f71,plain,(
% 3.57/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.57/0.98    inference(cnf_transformation,[],[f5])).
% 3.57/0.98  
% 3.57/0.98  fof(f97,plain,(
% 3.57/0.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k3_tarski(k2_tarski(X0,X1)) != X2) )),
% 3.57/0.98    inference(definition_unfolding,[],[f66,f71])).
% 3.57/0.98  
% 3.57/0.98  fof(f104,plain,(
% 3.57/0.98    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k2_tarski(X0,X1))) | ~r2_hidden(X4,X1)) )),
% 3.57/0.98    inference(equality_resolution,[],[f97])).
% 3.57/0.98  
% 3.57/0.98  fof(f16,conjecture,(
% 3.57/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) => m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))))))),
% 3.57/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.57/0.98  
% 3.57/0.98  fof(f17,negated_conjecture,(
% 3.57/0.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) => m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))))))),
% 3.57/0.98    inference(negated_conjecture,[],[f16])).
% 3.57/0.98  
% 3.57/0.98  fof(f39,plain,(
% 3.57/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.57/0.98    inference(ennf_transformation,[],[f17])).
% 3.57/0.98  
% 3.57/0.98  fof(f40,plain,(
% 3.57/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.57/0.98    inference(flattening,[],[f39])).
% 3.57/0.98  
% 3.57/0.98  fof(f58,plain,(
% 3.57/0.98    ( ! [X2,X0,X1] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) => (~m1_subset_1(k2_xboole_0(X2,sK6),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(sK6,u1_struct_0(k9_yellow_6(X0,X1))))) )),
% 3.57/0.98    introduced(choice_axiom,[])).
% 3.57/0.98  
% 3.57/0.98  fof(f57,plain,(
% 3.57/0.98    ( ! [X0,X1] : (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) => (? [X3] : (~m1_subset_1(k2_xboole_0(sK5,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(sK5,u1_struct_0(k9_yellow_6(X0,X1))))) )),
% 3.57/0.98    introduced(choice_axiom,[])).
% 3.57/0.98  
% 3.57/0.98  fof(f56,plain,(
% 3.57/0.98    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,sK4))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,sK4)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,sK4)))) & m1_subset_1(sK4,u1_struct_0(X0)))) )),
% 3.57/0.98    introduced(choice_axiom,[])).
% 3.57/0.98  
% 3.57/0.98  fof(f55,plain,(
% 3.57/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK3,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK3,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK3,X1)))) & m1_subset_1(X1,u1_struct_0(sK3))) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 3.57/0.98    introduced(choice_axiom,[])).
% 3.57/0.98  
% 3.57/0.98  fof(f59,plain,(
% 3.57/0.98    (((~m1_subset_1(k2_xboole_0(sK5,sK6),u1_struct_0(k9_yellow_6(sK3,sK4))) & m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4)))) & m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK3,sK4)))) & m1_subset_1(sK4,u1_struct_0(sK3))) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 3.57/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f40,f58,f57,f56,f55])).
% 3.57/0.98  
% 3.57/0.98  fof(f92,plain,(
% 3.57/0.98    m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4)))),
% 3.57/0.98    inference(cnf_transformation,[],[f59])).
% 3.57/0.98  
% 3.57/0.98  fof(f15,axiom,(
% 3.57/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => m1_connsp_2(X2,X0,X1))))),
% 3.57/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.57/0.98  
% 3.57/0.98  fof(f37,plain,(
% 3.57/0.98    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.57/0.98    inference(ennf_transformation,[],[f15])).
% 3.57/0.98  
% 3.57/0.98  fof(f38,plain,(
% 3.57/0.98    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.57/0.98    inference(flattening,[],[f37])).
% 3.57/0.98  
% 3.57/0.98  fof(f86,plain,(
% 3.57/0.98    ( ! [X2,X0,X1] : (m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.57/0.98    inference(cnf_transformation,[],[f38])).
% 3.57/0.98  
% 3.57/0.98  fof(f13,axiom,(
% 3.57/0.98    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.57/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.57/0.98  
% 3.57/0.98  fof(f33,plain,(
% 3.57/0.98    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.57/0.98    inference(ennf_transformation,[],[f13])).
% 3.57/0.98  
% 3.57/0.98  fof(f34,plain,(
% 3.57/0.98    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.57/0.98    inference(flattening,[],[f33])).
% 3.57/0.98  
% 3.57/0.98  fof(f82,plain,(
% 3.57/0.98    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.57/0.98    inference(cnf_transformation,[],[f34])).
% 3.57/0.98  
% 3.57/0.98  fof(f87,plain,(
% 3.57/0.98    ~v2_struct_0(sK3)),
% 3.57/0.98    inference(cnf_transformation,[],[f59])).
% 3.57/0.98  
% 3.57/0.98  fof(f88,plain,(
% 3.57/0.98    v2_pre_topc(sK3)),
% 3.57/0.98    inference(cnf_transformation,[],[f59])).
% 3.57/0.98  
% 3.57/0.98  fof(f89,plain,(
% 3.57/0.98    l1_pre_topc(sK3)),
% 3.57/0.98    inference(cnf_transformation,[],[f59])).
% 3.57/0.98  
% 3.57/0.98  fof(f90,plain,(
% 3.57/0.98    m1_subset_1(sK4,u1_struct_0(sK3))),
% 3.57/0.98    inference(cnf_transformation,[],[f59])).
% 3.57/0.98  
% 3.57/0.98  fof(f91,plain,(
% 3.57/0.98    m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK3,sK4)))),
% 3.57/0.98    inference(cnf_transformation,[],[f59])).
% 3.57/0.98  
% 3.57/0.98  fof(f8,axiom,(
% 3.57/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 3.57/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.57/0.98  
% 3.57/0.98  fof(f24,plain,(
% 3.57/0.98    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 3.57/0.98    inference(ennf_transformation,[],[f8])).
% 3.57/0.98  
% 3.57/0.98  fof(f25,plain,(
% 3.57/0.98    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.57/0.98    inference(flattening,[],[f24])).
% 3.57/0.98  
% 3.57/0.98  fof(f77,plain,(
% 3.57/0.98    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.57/0.98    inference(cnf_transformation,[],[f25])).
% 3.57/0.98  
% 3.57/0.98  fof(f101,plain,(
% 3.57/0.98    ( ! [X2,X0,X1] : (k3_tarski(k2_tarski(X1,X2)) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.57/0.98    inference(definition_unfolding,[],[f77,f71])).
% 3.57/0.98  
% 3.57/0.98  fof(f7,axiom,(
% 3.57/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 3.57/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.57/0.98  
% 3.57/0.98  fof(f22,plain,(
% 3.57/0.98    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 3.57/0.98    inference(ennf_transformation,[],[f7])).
% 3.57/0.98  
% 3.57/0.98  fof(f23,plain,(
% 3.57/0.98    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.57/0.98    inference(flattening,[],[f22])).
% 3.57/0.98  
% 3.57/0.98  fof(f76,plain,(
% 3.57/0.98    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.57/0.98    inference(cnf_transformation,[],[f23])).
% 3.57/0.98  
% 3.57/0.98  fof(f14,axiom,(
% 3.57/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))))))),
% 3.57/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.57/0.98  
% 3.57/0.98  fof(f35,plain,(
% 3.57/0.98    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.57/0.98    inference(ennf_transformation,[],[f14])).
% 3.57/0.98  
% 3.57/0.98  fof(f36,plain,(
% 3.57/0.98    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.57/0.98    inference(flattening,[],[f35])).
% 3.57/0.98  
% 3.57/0.98  fof(f53,plain,(
% 3.57/0.98    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | (~v3_pre_topc(X2,X0) | ~r2_hidden(X1,X2))) & ((v3_pre_topc(X2,X0) & r2_hidden(X1,X2)) | ~r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.57/0.98    inference(nnf_transformation,[],[f36])).
% 3.57/0.98  
% 3.57/0.98  fof(f54,plain,(
% 3.57/0.98    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~v3_pre_topc(X2,X0) | ~r2_hidden(X1,X2)) & ((v3_pre_topc(X2,X0) & r2_hidden(X1,X2)) | ~r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.57/0.98    inference(flattening,[],[f53])).
% 3.57/0.98  
% 3.57/0.98  fof(f85,plain,(
% 3.57/0.98    ( ! [X2,X0,X1] : (r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~v3_pre_topc(X2,X0) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.57/0.98    inference(cnf_transformation,[],[f54])).
% 3.57/0.98  
% 3.57/0.98  fof(f11,axiom,(
% 3.57/0.98    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 3.57/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.57/0.98  
% 3.57/0.98  fof(f29,plain,(
% 3.57/0.98    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 3.57/0.98    inference(ennf_transformation,[],[f11])).
% 3.57/0.98  
% 3.57/0.98  fof(f30,plain,(
% 3.57/0.98    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.57/0.98    inference(flattening,[],[f29])).
% 3.57/0.98  
% 3.57/0.98  fof(f80,plain,(
% 3.57/0.98    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.57/0.98    inference(cnf_transformation,[],[f30])).
% 3.57/0.98  
% 3.57/0.98  fof(f9,axiom,(
% 3.57/0.98    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 3.57/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.57/0.98  
% 3.57/0.98  fof(f26,plain,(
% 3.57/0.98    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 3.57/0.98    inference(ennf_transformation,[],[f9])).
% 3.57/0.98  
% 3.57/0.98  fof(f78,plain,(
% 3.57/0.98    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 3.57/0.98    inference(cnf_transformation,[],[f26])).
% 3.57/0.98  
% 3.57/0.98  fof(f93,plain,(
% 3.57/0.98    ~m1_subset_1(k2_xboole_0(sK5,sK6),u1_struct_0(k9_yellow_6(sK3,sK4)))),
% 3.57/0.98    inference(cnf_transformation,[],[f59])).
% 3.57/0.98  
% 3.57/0.98  fof(f103,plain,(
% 3.57/0.98    ~m1_subset_1(k3_tarski(k2_tarski(sK5,sK6)),u1_struct_0(k9_yellow_6(sK3,sK4)))),
% 3.57/0.98    inference(definition_unfolding,[],[f93,f71])).
% 3.57/0.98  
% 3.57/0.98  fof(f84,plain,(
% 3.57/0.98    ( ! [X2,X0,X1] : (v3_pre_topc(X2,X0) | ~r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.57/0.98    inference(cnf_transformation,[],[f54])).
% 3.57/0.98  
% 3.57/0.98  fof(f2,axiom,(
% 3.57/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.57/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.57/0.98  
% 3.57/0.98  fof(f18,plain,(
% 3.57/0.98    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 3.57/0.98    inference(unused_predicate_definition_removal,[],[f2])).
% 3.57/0.98  
% 3.57/0.98  fof(f19,plain,(
% 3.57/0.98    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 3.57/0.98    inference(ennf_transformation,[],[f18])).
% 3.57/0.98  
% 3.57/0.98  fof(f45,plain,(
% 3.57/0.98    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 3.57/0.98    introduced(choice_axiom,[])).
% 3.57/0.98  
% 3.57/0.98  fof(f46,plain,(
% 3.57/0.98    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 3.57/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f45])).
% 3.57/0.98  
% 3.57/0.98  fof(f62,plain,(
% 3.57/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 3.57/0.98    inference(cnf_transformation,[],[f46])).
% 3.57/0.98  
% 3.57/0.98  fof(f4,axiom,(
% 3.57/0.98    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 3.57/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.57/0.98  
% 3.57/0.98  fof(f20,plain,(
% 3.57/0.98    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 3.57/0.98    inference(ennf_transformation,[],[f4])).
% 3.57/0.98  
% 3.57/0.98  fof(f70,plain,(
% 3.57/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 3.57/0.98    inference(cnf_transformation,[],[f20])).
% 3.57/0.98  
% 3.57/0.98  fof(f100,plain,(
% 3.57/0.98    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = X1 | ~r1_tarski(X0,X1)) )),
% 3.57/0.98    inference(definition_unfolding,[],[f70,f71])).
% 3.57/0.98  
% 3.57/0.98  fof(f10,axiom,(
% 3.57/0.98    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 3.57/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.57/0.98  
% 3.57/0.98  fof(f27,plain,(
% 3.57/0.98    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 3.57/0.98    inference(ennf_transformation,[],[f10])).
% 3.57/0.98  
% 3.57/0.98  fof(f28,plain,(
% 3.57/0.98    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 3.57/0.98    inference(flattening,[],[f27])).
% 3.57/0.98  
% 3.57/0.98  fof(f79,plain,(
% 3.57/0.98    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 3.57/0.98    inference(cnf_transformation,[],[f28])).
% 3.57/0.98  
% 3.57/0.98  fof(f6,axiom,(
% 3.57/0.98    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 3.57/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.57/0.98  
% 3.57/0.98  fof(f21,plain,(
% 3.57/0.98    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 3.57/0.98    inference(ennf_transformation,[],[f6])).
% 3.57/0.98  
% 3.57/0.98  fof(f52,plain,(
% 3.57/0.98    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 3.57/0.98    inference(nnf_transformation,[],[f21])).
% 3.57/0.98  
% 3.57/0.98  fof(f74,plain,(
% 3.57/0.98    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,X0) | ~v1_xboole_0(X0)) )),
% 3.57/0.98    inference(cnf_transformation,[],[f52])).
% 3.57/0.98  
% 3.57/0.98  fof(f1,axiom,(
% 3.57/0.98    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.57/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.57/0.98  
% 3.57/0.98  fof(f41,plain,(
% 3.57/0.98    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.57/0.98    inference(nnf_transformation,[],[f1])).
% 3.57/0.98  
% 3.57/0.98  fof(f42,plain,(
% 3.57/0.98    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.57/0.98    inference(rectify,[],[f41])).
% 3.57/0.98  
% 3.57/0.98  fof(f43,plain,(
% 3.57/0.98    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.57/0.98    introduced(choice_axiom,[])).
% 3.57/0.98  
% 3.57/0.98  fof(f44,plain,(
% 3.57/0.98    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.57/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f42,f43])).
% 3.57/0.98  
% 3.57/0.98  fof(f60,plain,(
% 3.57/0.98    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 3.57/0.98    inference(cnf_transformation,[],[f44])).
% 3.57/0.98  
% 3.57/0.98  fof(f12,axiom,(
% 3.57/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X2,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_xboole_0(X1,X2),X0))),
% 3.57/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.57/0.98  
% 3.57/0.98  fof(f31,plain,(
% 3.57/0.98    ! [X0,X1,X2] : (v3_pre_topc(k2_xboole_0(X1,X2),X0) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.57/0.98    inference(ennf_transformation,[],[f12])).
% 3.57/0.98  
% 3.57/0.98  fof(f32,plain,(
% 3.57/0.98    ! [X0,X1,X2] : (v3_pre_topc(k2_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.57/0.98    inference(flattening,[],[f31])).
% 3.57/0.98  
% 3.57/0.98  fof(f81,plain,(
% 3.57/0.98    ( ! [X2,X0,X1] : (v3_pre_topc(k2_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.57/0.98    inference(cnf_transformation,[],[f32])).
% 3.57/0.98  
% 3.57/0.98  fof(f102,plain,(
% 3.57/0.98    ( ! [X2,X0,X1] : (v3_pre_topc(k3_tarski(k2_tarski(X1,X2)),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.57/0.98    inference(definition_unfolding,[],[f81,f71])).
% 3.57/0.98  
% 3.57/0.98  fof(f83,plain,(
% 3.57/0.98    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.57/0.98    inference(cnf_transformation,[],[f54])).
% 3.57/0.98  
% 3.57/0.98  cnf(c_7,plain,
% 3.57/0.98      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,k3_tarski(k2_tarski(X2,X1))) ),
% 3.57/0.98      inference(cnf_transformation,[],[f104]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1197,plain,
% 3.57/0.98      ( r2_hidden(X0,X1) != iProver_top
% 3.57/0.98      | r2_hidden(X0,k3_tarski(k2_tarski(X2,X1))) = iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_27,negated_conjecture,
% 3.57/0.98      ( m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4))) ),
% 3.57/0.98      inference(cnf_transformation,[],[f92]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1186,plain,
% 3.57/0.98      ( m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4))) = iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_25,plain,
% 3.57/0.98      ( m1_connsp_2(X0,X1,X2)
% 3.57/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.57/0.98      | ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(X1,X2)))
% 3.57/0.98      | v2_struct_0(X1)
% 3.57/0.98      | ~ v2_pre_topc(X1)
% 3.57/0.98      | ~ l1_pre_topc(X1) ),
% 3.57/0.98      inference(cnf_transformation,[],[f86]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_21,plain,
% 3.57/0.98      ( ~ m1_connsp_2(X0,X1,X2)
% 3.57/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.57/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.57/0.98      | v2_struct_0(X1)
% 3.57/0.98      | ~ v2_pre_topc(X1)
% 3.57/0.98      | ~ l1_pre_topc(X1) ),
% 3.57/0.98      inference(cnf_transformation,[],[f82]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_385,plain,
% 3.57/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.57/0.98      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
% 3.57/0.98      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.57/0.98      | v2_struct_0(X1)
% 3.57/0.98      | ~ v2_pre_topc(X1)
% 3.57/0.98      | ~ l1_pre_topc(X1) ),
% 3.57/0.98      inference(resolution,[status(thm)],[c_25,c_21]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_32,negated_conjecture,
% 3.57/0.98      ( ~ v2_struct_0(sK3) ),
% 3.57/0.98      inference(cnf_transformation,[],[f87]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_415,plain,
% 3.57/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.57/0.98      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
% 3.57/0.98      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.57/0.98      | ~ v2_pre_topc(X1)
% 3.57/0.98      | ~ l1_pre_topc(X1)
% 3.57/0.98      | sK3 != X1 ),
% 3.57/0.98      inference(resolution_lifted,[status(thm)],[c_385,c_32]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_416,plain,
% 3.57/0.98      ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK3,X1)))
% 3.57/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 3.57/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.57/0.98      | ~ v2_pre_topc(sK3)
% 3.57/0.98      | ~ l1_pre_topc(sK3) ),
% 3.57/0.98      inference(unflattening,[status(thm)],[c_415]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_31,negated_conjecture,
% 3.57/0.98      ( v2_pre_topc(sK3) ),
% 3.57/0.98      inference(cnf_transformation,[],[f88]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_30,negated_conjecture,
% 3.57/0.98      ( l1_pre_topc(sK3) ),
% 3.57/0.98      inference(cnf_transformation,[],[f89]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_420,plain,
% 3.57/0.98      ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK3,X1)))
% 3.57/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 3.57/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 3.57/0.98      inference(global_propositional_subsumption,
% 3.57/0.98                [status(thm)],
% 3.57/0.98                [c_416,c_31,c_30]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1181,plain,
% 3.57/0.98      ( m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK3,X1))) != iProver_top
% 3.57/0.98      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
% 3.57/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_420]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1487,plain,
% 3.57/0.98      ( m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 3.57/0.98      | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 3.57/0.98      inference(superposition,[status(thm)],[c_1186,c_1181]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_29,negated_conjecture,
% 3.57/0.98      ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 3.57/0.98      inference(cnf_transformation,[],[f90]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_36,plain,
% 3.57/0.98      ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1500,plain,
% 3.57/0.98      ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 3.57/0.98      inference(global_propositional_subsumption,
% 3.57/0.98                [status(thm)],
% 3.57/0.98                [c_1487,c_36]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_28,negated_conjecture,
% 3.57/0.98      ( m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK3,sK4))) ),
% 3.57/0.98      inference(cnf_transformation,[],[f91]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1185,plain,
% 3.57/0.98      ( m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK3,sK4))) = iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1488,plain,
% 3.57/0.98      ( m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 3.57/0.98      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 3.57/0.98      inference(superposition,[status(thm)],[c_1185,c_1181]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1545,plain,
% 3.57/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 3.57/0.98      inference(global_propositional_subsumption,
% 3.57/0.98                [status(thm)],
% 3.57/0.98                [c_1488,c_36]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_16,plain,
% 3.57/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.57/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.57/0.98      | k4_subset_1(X1,X2,X0) = k3_tarski(k2_tarski(X2,X0)) ),
% 3.57/0.98      inference(cnf_transformation,[],[f101]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1190,plain,
% 3.57/0.98      ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
% 3.57/0.98      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 3.57/0.98      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_3411,plain,
% 3.57/0.98      ( k4_subset_1(u1_struct_0(sK3),sK5,X0) = k3_tarski(k2_tarski(sK5,X0))
% 3.57/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 3.57/0.98      inference(superposition,[status(thm)],[c_1545,c_1190]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_4011,plain,
% 3.57/0.98      ( k4_subset_1(u1_struct_0(sK3),sK5,sK6) = k3_tarski(k2_tarski(sK5,sK6)) ),
% 3.57/0.98      inference(superposition,[status(thm)],[c_1500,c_3411]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_15,plain,
% 3.57/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.57/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.57/0.98      | m1_subset_1(k4_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 3.57/0.98      inference(cnf_transformation,[],[f76]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1191,plain,
% 3.57/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.57/0.98      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 3.57/0.98      | m1_subset_1(k4_subset_1(X1,X0,X2),k1_zfmisc_1(X1)) = iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_5053,plain,
% 3.57/0.98      ( m1_subset_1(k3_tarski(k2_tarski(sK5,sK6)),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 3.57/0.98      | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.57/0.98      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 3.57/0.98      inference(superposition,[status(thm)],[c_4011,c_1191]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_10362,plain,
% 3.57/0.98      ( m1_subset_1(k3_tarski(k2_tarski(sK5,sK6)),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 3.57/0.98      inference(global_propositional_subsumption,
% 3.57/0.98                [status(thm)],
% 3.57/0.98                [c_5053,c_36,c_1487,c_1488]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_22,plain,
% 3.57/0.98      ( ~ v3_pre_topc(X0,X1)
% 3.57/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.57/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.57/0.98      | ~ r2_hidden(X2,X0)
% 3.57/0.98      | r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
% 3.57/0.98      | v2_struct_0(X1)
% 3.57/0.98      | ~ v2_pre_topc(X1)
% 3.57/0.98      | ~ l1_pre_topc(X1) ),
% 3.57/0.98      inference(cnf_transformation,[],[f85]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_484,plain,
% 3.57/0.98      ( ~ v3_pre_topc(X0,X1)
% 3.57/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.57/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.57/0.98      | ~ r2_hidden(X2,X0)
% 3.57/0.98      | r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
% 3.57/0.98      | ~ v2_pre_topc(X1)
% 3.57/0.98      | ~ l1_pre_topc(X1)
% 3.57/0.98      | sK3 != X1 ),
% 3.57/0.98      inference(resolution_lifted,[status(thm)],[c_22,c_32]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_485,plain,
% 3.57/0.98      ( ~ v3_pre_topc(X0,sK3)
% 3.57/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 3.57/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.57/0.98      | ~ r2_hidden(X1,X0)
% 3.57/0.98      | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK3,X1)))
% 3.57/0.98      | ~ v2_pre_topc(sK3)
% 3.57/0.98      | ~ l1_pre_topc(sK3) ),
% 3.57/0.98      inference(unflattening,[status(thm)],[c_484]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_489,plain,
% 3.57/0.98      ( ~ v3_pre_topc(X0,sK3)
% 3.57/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 3.57/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.57/0.98      | ~ r2_hidden(X1,X0)
% 3.57/0.98      | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK3,X1))) ),
% 3.57/0.98      inference(global_propositional_subsumption,
% 3.57/0.98                [status(thm)],
% 3.57/0.98                [c_485,c_31,c_30]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_19,plain,
% 3.57/0.98      ( m1_subset_1(X0,X1)
% 3.57/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.57/0.98      | ~ r2_hidden(X0,X2) ),
% 3.57/0.98      inference(cnf_transformation,[],[f80]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_505,plain,
% 3.57/0.98      ( ~ v3_pre_topc(X0,sK3)
% 3.57/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.57/0.98      | ~ r2_hidden(X1,X0)
% 3.57/0.98      | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK3,X1))) ),
% 3.57/0.98      inference(forward_subsumption_resolution,
% 3.57/0.98                [status(thm)],
% 3.57/0.98                [c_489,c_19]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1178,plain,
% 3.57/0.98      ( v3_pre_topc(X0,sK3) != iProver_top
% 3.57/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.57/0.98      | r2_hidden(X1,X0) != iProver_top
% 3.57/0.98      | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK3,X1))) = iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_505]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_17,plain,
% 3.57/0.98      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 3.57/0.98      inference(cnf_transformation,[],[f78]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1189,plain,
% 3.57/0.98      ( m1_subset_1(X0,X1) = iProver_top
% 3.57/0.98      | r2_hidden(X0,X1) != iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1934,plain,
% 3.57/0.98      ( v3_pre_topc(X0,sK3) != iProver_top
% 3.57/0.98      | m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK3,X1))) = iProver_top
% 3.57/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.57/0.98      | r2_hidden(X1,X0) != iProver_top ),
% 3.57/0.98      inference(superposition,[status(thm)],[c_1178,c_1189]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_26,negated_conjecture,
% 3.57/0.98      ( ~ m1_subset_1(k3_tarski(k2_tarski(sK5,sK6)),u1_struct_0(k9_yellow_6(sK3,sK4))) ),
% 3.57/0.98      inference(cnf_transformation,[],[f103]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1187,plain,
% 3.57/0.98      ( m1_subset_1(k3_tarski(k2_tarski(sK5,sK6)),u1_struct_0(k9_yellow_6(sK3,sK4))) != iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_2311,plain,
% 3.57/0.98      ( v3_pre_topc(k3_tarski(k2_tarski(sK5,sK6)),sK3) != iProver_top
% 3.57/0.98      | m1_subset_1(k3_tarski(k2_tarski(sK5,sK6)),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.57/0.98      | r2_hidden(sK4,k3_tarski(k2_tarski(sK5,sK6))) != iProver_top ),
% 3.57/0.98      inference(superposition,[status(thm)],[c_1934,c_1187]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_10374,plain,
% 3.57/0.98      ( v3_pre_topc(k3_tarski(k2_tarski(sK5,sK6)),sK3) != iProver_top
% 3.57/0.98      | r2_hidden(sK4,k3_tarski(k2_tarski(sK5,sK6))) != iProver_top ),
% 3.57/0.98      inference(superposition,[status(thm)],[c_10362,c_2311]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_37,plain,
% 3.57/0.98      ( m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK3,sK4))) = iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_38,plain,
% 3.57/0.98      ( m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4))) = iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_740,plain,( X0 = X0 ),theory(equality) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1564,plain,
% 3.57/0.98      ( u1_struct_0(k9_yellow_6(sK3,sK4)) = u1_struct_0(k9_yellow_6(sK3,sK4)) ),
% 3.57/0.98      inference(instantiation,[status(thm)],[c_740]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_23,plain,
% 3.57/0.98      ( v3_pre_topc(X0,X1)
% 3.57/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.57/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.57/0.98      | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
% 3.57/0.98      | v2_struct_0(X1)
% 3.57/0.98      | ~ v2_pre_topc(X1)
% 3.57/0.98      | ~ l1_pre_topc(X1) ),
% 3.57/0.98      inference(cnf_transformation,[],[f84]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_460,plain,
% 3.57/0.98      ( v3_pre_topc(X0,X1)
% 3.57/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.57/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.57/0.98      | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
% 3.57/0.98      | ~ v2_pre_topc(X1)
% 3.57/0.98      | ~ l1_pre_topc(X1)
% 3.57/0.98      | sK3 != X1 ),
% 3.57/0.98      inference(resolution_lifted,[status(thm)],[c_23,c_32]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_461,plain,
% 3.57/0.98      ( v3_pre_topc(X0,sK3)
% 3.57/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 3.57/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.57/0.98      | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(sK3,X1)))
% 3.57/0.98      | ~ v2_pre_topc(sK3)
% 3.57/0.98      | ~ l1_pre_topc(sK3) ),
% 3.57/0.98      inference(unflattening,[status(thm)],[c_460]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_465,plain,
% 3.57/0.98      ( v3_pre_topc(X0,sK3)
% 3.57/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 3.57/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.57/0.98      | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(sK3,X1))) ),
% 3.57/0.98      inference(global_propositional_subsumption,
% 3.57/0.98                [status(thm)],
% 3.57/0.98                [c_461,c_31,c_30]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1401,plain,
% 3.57/0.98      ( v3_pre_topc(X0,sK3)
% 3.57/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.57/0.98      | ~ m1_subset_1(sK4,u1_struct_0(sK3))
% 3.57/0.98      | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(sK3,sK4))) ),
% 3.57/0.98      inference(instantiation,[status(thm)],[c_465]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1661,plain,
% 3.57/0.98      ( v3_pre_topc(sK6,sK3)
% 3.57/0.98      | ~ m1_subset_1(sK4,u1_struct_0(sK3))
% 3.57/0.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.57/0.98      | ~ r2_hidden(sK6,u1_struct_0(k9_yellow_6(sK3,sK4))) ),
% 3.57/0.98      inference(instantiation,[status(thm)],[c_1401]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1662,plain,
% 3.57/0.98      ( v3_pre_topc(sK6,sK3) = iProver_top
% 3.57/0.98      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 3.57/0.98      | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.57/0.98      | r2_hidden(sK6,u1_struct_0(k9_yellow_6(sK3,sK4))) != iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_1661]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1682,plain,
% 3.57/0.98      ( v3_pre_topc(sK5,sK3)
% 3.57/0.98      | ~ m1_subset_1(sK4,u1_struct_0(sK3))
% 3.57/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.57/0.98      | ~ r2_hidden(sK5,u1_struct_0(k9_yellow_6(sK3,sK4))) ),
% 3.57/0.98      inference(instantiation,[status(thm)],[c_1401]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1683,plain,
% 3.57/0.98      ( v3_pre_topc(sK5,sK3) = iProver_top
% 3.57/0.98      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 3.57/0.98      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.57/0.98      | r2_hidden(sK5,u1_struct_0(k9_yellow_6(sK3,sK4))) != iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_1682]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_745,plain,
% 3.57/0.98      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.57/0.98      theory(equality) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1468,plain,
% 3.57/0.98      ( ~ m1_subset_1(X0,X1)
% 3.57/0.98      | m1_subset_1(k3_tarski(k2_tarski(sK5,sK6)),u1_struct_0(k9_yellow_6(sK3,sK4)))
% 3.57/0.98      | u1_struct_0(k9_yellow_6(sK3,sK4)) != X1
% 3.57/0.98      | k3_tarski(k2_tarski(sK5,sK6)) != X0 ),
% 3.57/0.98      inference(instantiation,[status(thm)],[c_745]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1563,plain,
% 3.57/0.98      ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK3,sK4)))
% 3.57/0.98      | m1_subset_1(k3_tarski(k2_tarski(sK5,sK6)),u1_struct_0(k9_yellow_6(sK3,sK4)))
% 3.57/0.98      | u1_struct_0(k9_yellow_6(sK3,sK4)) != u1_struct_0(k9_yellow_6(sK3,sK4))
% 3.57/0.98      | k3_tarski(k2_tarski(sK5,sK6)) != X0 ),
% 3.57/0.98      inference(instantiation,[status(thm)],[c_1468]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1724,plain,
% 3.57/0.98      ( m1_subset_1(k3_tarski(k2_tarski(sK5,sK6)),u1_struct_0(k9_yellow_6(sK3,sK4)))
% 3.57/0.98      | ~ m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4)))
% 3.57/0.98      | u1_struct_0(k9_yellow_6(sK3,sK4)) != u1_struct_0(k9_yellow_6(sK3,sK4))
% 3.57/0.98      | k3_tarski(k2_tarski(sK5,sK6)) != sK6 ),
% 3.57/0.98      inference(instantiation,[status(thm)],[c_1563]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_3,plain,
% 3.57/0.98      ( r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 3.57/0.98      inference(cnf_transformation,[],[f62]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_10,plain,
% 3.57/0.98      ( ~ r1_tarski(X0,X1) | k3_tarski(k2_tarski(X0,X1)) = X1 ),
% 3.57/0.98      inference(cnf_transformation,[],[f100]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_357,plain,
% 3.57/0.98      ( r2_hidden(sK1(X0,X1),X0) | k3_tarski(k2_tarski(X0,X1)) = X1 ),
% 3.57/0.98      inference(resolution,[status(thm)],[c_3,c_10]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1765,plain,
% 3.57/0.98      ( r2_hidden(sK1(sK5,sK6),sK5)
% 3.57/0.98      | k3_tarski(k2_tarski(sK5,sK6)) = sK6 ),
% 3.57/0.98      inference(instantiation,[status(thm)],[c_357]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1770,plain,
% 3.57/0.98      ( k3_tarski(k2_tarski(sK5,sK6)) = sK6
% 3.57/0.98      | r2_hidden(sK1(sK5,sK6),sK5) = iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_1765]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_18,plain,
% 3.57/0.98      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.57/0.98      inference(cnf_transformation,[],[f79]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1513,plain,
% 3.57/0.98      ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK3,sK4)))
% 3.57/0.98      | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK3,sK4)))
% 3.57/0.98      | v1_xboole_0(u1_struct_0(k9_yellow_6(sK3,sK4))) ),
% 3.57/0.98      inference(instantiation,[status(thm)],[c_18]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_2370,plain,
% 3.57/0.98      ( ~ m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4)))
% 3.57/0.98      | r2_hidden(sK6,u1_struct_0(k9_yellow_6(sK3,sK4)))
% 3.57/0.98      | v1_xboole_0(u1_struct_0(k9_yellow_6(sK3,sK4))) ),
% 3.57/0.98      inference(instantiation,[status(thm)],[c_1513]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_2371,plain,
% 3.57/0.98      ( m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4))) != iProver_top
% 3.57/0.98      | r2_hidden(sK6,u1_struct_0(k9_yellow_6(sK3,sK4))) = iProver_top
% 3.57/0.98      | v1_xboole_0(u1_struct_0(k9_yellow_6(sK3,sK4))) = iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_2370]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_2373,plain,
% 3.57/0.98      ( ~ m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK3,sK4)))
% 3.57/0.98      | r2_hidden(sK5,u1_struct_0(k9_yellow_6(sK3,sK4)))
% 3.57/0.98      | v1_xboole_0(u1_struct_0(k9_yellow_6(sK3,sK4))) ),
% 3.57/0.98      inference(instantiation,[status(thm)],[c_1513]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_2374,plain,
% 3.57/0.98      ( m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK3,sK4))) != iProver_top
% 3.57/0.98      | r2_hidden(sK5,u1_struct_0(k9_yellow_6(sK3,sK4))) = iProver_top
% 3.57/0.98      | v1_xboole_0(u1_struct_0(k9_yellow_6(sK3,sK4))) = iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_2373]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_12,plain,
% 3.57/0.98      ( ~ m1_subset_1(X0,X1) | ~ v1_xboole_0(X1) | v1_xboole_0(X0) ),
% 3.57/0.98      inference(cnf_transformation,[],[f74]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1193,plain,
% 3.57/0.98      ( m1_subset_1(X0,X1) != iProver_top
% 3.57/0.98      | v1_xboole_0(X1) != iProver_top
% 3.57/0.98      | v1_xboole_0(X0) = iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_2510,plain,
% 3.57/0.98      ( v1_xboole_0(u1_struct_0(k9_yellow_6(sK3,sK4))) != iProver_top
% 3.57/0.98      | v1_xboole_0(sK5) = iProver_top ),
% 3.57/0.98      inference(superposition,[status(thm)],[c_1185,c_1193]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1,plain,
% 3.57/0.98      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.57/0.98      inference(cnf_transformation,[],[f60]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_2604,plain,
% 3.57/0.98      ( ~ r2_hidden(sK1(sK5,sK6),sK5) | ~ v1_xboole_0(sK5) ),
% 3.57/0.98      inference(instantiation,[status(thm)],[c_1]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_2605,plain,
% 3.57/0.98      ( r2_hidden(sK1(sK5,sK6),sK5) != iProver_top
% 3.57/0.98      | v1_xboole_0(sK5) != iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_2604]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_20,plain,
% 3.57/0.98      ( ~ v3_pre_topc(X0,X1)
% 3.57/0.98      | ~ v3_pre_topc(X2,X1)
% 3.57/0.98      | v3_pre_topc(k3_tarski(k2_tarski(X2,X0)),X1)
% 3.57/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.57/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.57/0.98      | ~ v2_pre_topc(X1)
% 3.57/0.99      | ~ l1_pre_topc(X1) ),
% 3.57/0.99      inference(cnf_transformation,[],[f102]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_532,plain,
% 3.57/0.99      ( ~ v3_pre_topc(X0,X1)
% 3.57/0.99      | ~ v3_pre_topc(X2,X1)
% 3.57/0.99      | v3_pre_topc(k3_tarski(k2_tarski(X2,X0)),X1)
% 3.57/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.57/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.57/0.99      | ~ v2_pre_topc(X1)
% 3.57/0.99      | sK3 != X1 ),
% 3.57/0.99      inference(resolution_lifted,[status(thm)],[c_20,c_30]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_533,plain,
% 3.57/0.99      ( ~ v3_pre_topc(X0,sK3)
% 3.57/0.99      | ~ v3_pre_topc(X1,sK3)
% 3.57/0.99      | v3_pre_topc(k3_tarski(k2_tarski(X1,X0)),sK3)
% 3.57/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.57/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.57/0.99      | ~ v2_pre_topc(sK3) ),
% 3.57/0.99      inference(unflattening,[status(thm)],[c_532]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_537,plain,
% 3.57/0.99      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.57/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.57/0.99      | v3_pre_topc(k3_tarski(k2_tarski(X1,X0)),sK3)
% 3.57/0.99      | ~ v3_pre_topc(X1,sK3)
% 3.57/0.99      | ~ v3_pre_topc(X0,sK3) ),
% 3.57/0.99      inference(global_propositional_subsumption,
% 3.57/0.99                [status(thm)],
% 3.57/0.99                [c_533,c_31]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_538,plain,
% 3.57/0.99      ( ~ v3_pre_topc(X0,sK3)
% 3.57/0.99      | ~ v3_pre_topc(X1,sK3)
% 3.57/0.99      | v3_pre_topc(k3_tarski(k2_tarski(X1,X0)),sK3)
% 3.57/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.57/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 3.57/0.99      inference(renaming,[status(thm)],[c_537]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_3555,plain,
% 3.57/0.99      ( ~ v3_pre_topc(X0,sK3)
% 3.57/0.99      | v3_pre_topc(k3_tarski(k2_tarski(X0,sK6)),sK3)
% 3.57/0.99      | ~ v3_pre_topc(sK6,sK3)
% 3.57/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.57/0.99      | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 3.57/0.99      inference(instantiation,[status(thm)],[c_538]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_6927,plain,
% 3.57/0.99      ( v3_pre_topc(k3_tarski(k2_tarski(sK5,sK6)),sK3)
% 3.57/0.99      | ~ v3_pre_topc(sK6,sK3)
% 3.57/0.99      | ~ v3_pre_topc(sK5,sK3)
% 3.57/0.99      | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.57/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 3.57/0.99      inference(instantiation,[status(thm)],[c_3555]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_6928,plain,
% 3.57/0.99      ( v3_pre_topc(k3_tarski(k2_tarski(sK5,sK6)),sK3) = iProver_top
% 3.57/0.99      | v3_pre_topc(sK6,sK3) != iProver_top
% 3.57/0.99      | v3_pre_topc(sK5,sK3) != iProver_top
% 3.57/0.99      | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.57/0.99      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 3.57/0.99      inference(predicate_to_equality,[status(thm)],[c_6927]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_10455,plain,
% 3.57/0.99      ( r2_hidden(sK4,k3_tarski(k2_tarski(sK5,sK6))) != iProver_top ),
% 3.57/0.99      inference(global_propositional_subsumption,
% 3.57/0.99                [status(thm)],
% 3.57/0.99                [c_10374,c_36,c_37,c_27,c_38,c_26,c_1487,c_1488,c_1564,
% 3.57/0.99                 c_1662,c_1683,c_1724,c_1770,c_2311,c_2371,c_2374,c_2510,
% 3.57/0.99                 c_2605,c_5053,c_6928]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_10460,plain,
% 3.57/0.99      ( r2_hidden(sK4,sK6) != iProver_top ),
% 3.57/0.99      inference(superposition,[status(thm)],[c_1197,c_10455]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_24,plain,
% 3.57/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.57/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.57/0.99      | r2_hidden(X0,X2)
% 3.57/0.99      | ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(X1,X0)))
% 3.57/0.99      | v2_struct_0(X1)
% 3.57/0.99      | ~ v2_pre_topc(X1)
% 3.57/0.99      | ~ l1_pre_topc(X1) ),
% 3.57/0.99      inference(cnf_transformation,[],[f83]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_436,plain,
% 3.57/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.57/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.57/0.99      | r2_hidden(X0,X2)
% 3.57/0.99      | ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(X1,X0)))
% 3.57/0.99      | ~ v2_pre_topc(X1)
% 3.57/0.99      | ~ l1_pre_topc(X1)
% 3.57/0.99      | sK3 != X1 ),
% 3.57/0.99      inference(resolution_lifted,[status(thm)],[c_24,c_32]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_437,plain,
% 3.57/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.57/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.57/0.99      | r2_hidden(X0,X1)
% 3.57/0.99      | ~ r2_hidden(X1,u1_struct_0(k9_yellow_6(sK3,X0)))
% 3.57/0.99      | ~ v2_pre_topc(sK3)
% 3.57/0.99      | ~ l1_pre_topc(sK3) ),
% 3.57/0.99      inference(unflattening,[status(thm)],[c_436]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_441,plain,
% 3.57/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.57/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.57/0.99      | r2_hidden(X0,X1)
% 3.57/0.99      | ~ r2_hidden(X1,u1_struct_0(k9_yellow_6(sK3,X0))) ),
% 3.57/0.99      inference(global_propositional_subsumption,
% 3.57/0.99                [status(thm)],
% 3.57/0.99                [c_437,c_31,c_30]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_1406,plain,
% 3.57/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.57/0.99      | ~ m1_subset_1(sK4,u1_struct_0(sK3))
% 3.57/0.99      | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(sK3,sK4)))
% 3.57/0.99      | r2_hidden(sK4,X0) ),
% 3.57/0.99      inference(instantiation,[status(thm)],[c_441]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_1660,plain,
% 3.57/0.99      ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
% 3.57/0.99      | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.57/0.99      | r2_hidden(sK4,sK6)
% 3.57/0.99      | ~ r2_hidden(sK6,u1_struct_0(k9_yellow_6(sK3,sK4))) ),
% 3.57/0.99      inference(instantiation,[status(thm)],[c_1406]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_1664,plain,
% 3.57/0.99      ( m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 3.57/0.99      | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.57/0.99      | r2_hidden(sK4,sK6) = iProver_top
% 3.57/0.99      | r2_hidden(sK6,u1_struct_0(k9_yellow_6(sK3,sK4))) != iProver_top ),
% 3.57/0.99      inference(predicate_to_equality,[status(thm)],[c_1660]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(contradiction,plain,
% 3.57/0.99      ( $false ),
% 3.57/0.99      inference(minisat,
% 3.57/0.99                [status(thm)],
% 3.57/0.99                [c_10460,c_2605,c_2510,c_2371,c_1770,c_1724,c_1664,
% 3.57/0.99                 c_1564,c_1487,c_26,c_38,c_27,c_36]) ).
% 3.57/0.99  
% 3.57/0.99  
% 3.57/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.57/0.99  
% 3.57/0.99  ------                               Statistics
% 3.57/0.99  
% 3.57/0.99  ------ General
% 3.57/0.99  
% 3.57/0.99  abstr_ref_over_cycles:                  0
% 3.57/0.99  abstr_ref_under_cycles:                 0
% 3.57/0.99  gc_basic_clause_elim:                   0
% 3.57/0.99  forced_gc_time:                         0
% 3.57/0.99  parsing_time:                           0.009
% 3.57/0.99  unif_index_cands_time:                  0.
% 3.57/0.99  unif_index_add_time:                    0.
% 3.57/0.99  orderings_time:                         0.
% 3.57/0.99  out_proof_time:                         0.013
% 3.57/0.99  total_time:                             0.304
% 3.57/0.99  num_of_symbols:                         53
% 3.57/0.99  num_of_terms:                           8976
% 3.57/0.99  
% 3.57/0.99  ------ Preprocessing
% 3.57/0.99  
% 3.57/0.99  num_of_splits:                          0
% 3.57/0.99  num_of_split_atoms:                     0
% 3.57/0.99  num_of_reused_defs:                     0
% 3.57/0.99  num_eq_ax_congr_red:                    36
% 3.57/0.99  num_of_sem_filtered_clauses:            1
% 3.57/0.99  num_of_subtypes:                        0
% 3.57/0.99  monotx_restored_types:                  0
% 3.57/0.99  sat_num_of_epr_types:                   0
% 3.57/0.99  sat_num_of_non_cyclic_types:            0
% 3.57/0.99  sat_guarded_non_collapsed_types:        0
% 3.57/0.99  num_pure_diseq_elim:                    0
% 3.57/0.99  simp_replaced_by:                       0
% 3.57/0.99  res_preprocessed:                       130
% 3.57/0.99  prep_upred:                             0
% 3.57/0.99  prep_unflattend:                        5
% 3.57/0.99  smt_new_axioms:                         0
% 3.57/0.99  pred_elim_cands:                        4
% 3.57/0.99  pred_elim:                              5
% 3.57/0.99  pred_elim_cl:                           5
% 3.57/0.99  pred_elim_cycles:                       7
% 3.57/0.99  merged_defs:                            0
% 3.57/0.99  merged_defs_ncl:                        0
% 3.57/0.99  bin_hyper_res:                          0
% 3.57/0.99  prep_cycles:                            4
% 3.57/0.99  pred_elim_time:                         0.013
% 3.57/0.99  splitting_time:                         0.
% 3.57/0.99  sem_filter_time:                        0.
% 3.57/0.99  monotx_time:                            0.001
% 3.57/0.99  subtype_inf_time:                       0.
% 3.57/0.99  
% 3.57/0.99  ------ Problem properties
% 3.57/0.99  
% 3.57/0.99  clauses:                                26
% 3.57/0.99  conjectures:                            4
% 3.57/0.99  epr:                                    5
% 3.57/0.99  horn:                                   21
% 3.57/0.99  ground:                                 4
% 3.57/0.99  unary:                                  4
% 3.57/0.99  binary:                                 7
% 3.57/0.99  lits:                                   69
% 3.57/0.99  lits_eq:                                6
% 3.57/0.99  fd_pure:                                0
% 3.57/0.99  fd_pseudo:                              0
% 3.57/0.99  fd_cond:                                0
% 3.57/0.99  fd_pseudo_cond:                         3
% 3.57/0.99  ac_symbols:                             0
% 3.57/0.99  
% 3.57/0.99  ------ Propositional Solver
% 3.57/0.99  
% 3.57/0.99  prop_solver_calls:                      30
% 3.57/0.99  prop_fast_solver_calls:                 1050
% 3.57/0.99  smt_solver_calls:                       0
% 3.57/0.99  smt_fast_solver_calls:                  0
% 3.57/0.99  prop_num_of_clauses:                    4414
% 3.57/0.99  prop_preprocess_simplified:             11569
% 3.57/0.99  prop_fo_subsumed:                       34
% 3.57/0.99  prop_solver_time:                       0.
% 3.57/0.99  smt_solver_time:                        0.
% 3.57/0.99  smt_fast_solver_time:                   0.
% 3.57/0.99  prop_fast_solver_time:                  0.
% 3.57/0.99  prop_unsat_core_time:                   0.
% 3.57/0.99  
% 3.57/0.99  ------ QBF
% 3.57/0.99  
% 3.57/0.99  qbf_q_res:                              0
% 3.57/0.99  qbf_num_tautologies:                    0
% 3.57/0.99  qbf_prep_cycles:                        0
% 3.57/0.99  
% 3.57/0.99  ------ BMC1
% 3.57/0.99  
% 3.57/0.99  bmc1_current_bound:                     -1
% 3.57/0.99  bmc1_last_solved_bound:                 -1
% 3.57/0.99  bmc1_unsat_core_size:                   -1
% 3.57/0.99  bmc1_unsat_core_parents_size:           -1
% 3.57/0.99  bmc1_merge_next_fun:                    0
% 3.57/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.57/0.99  
% 3.57/0.99  ------ Instantiation
% 3.57/0.99  
% 3.57/0.99  inst_num_of_clauses:                    1314
% 3.57/0.99  inst_num_in_passive:                    928
% 3.57/0.99  inst_num_in_active:                     354
% 3.57/0.99  inst_num_in_unprocessed:                32
% 3.57/0.99  inst_num_of_loops:                      480
% 3.57/0.99  inst_num_of_learning_restarts:          0
% 3.57/0.99  inst_num_moves_active_passive:          124
% 3.57/0.99  inst_lit_activity:                      0
% 3.57/0.99  inst_lit_activity_moves:                1
% 3.57/0.99  inst_num_tautologies:                   0
% 3.57/0.99  inst_num_prop_implied:                  0
% 3.57/0.99  inst_num_existing_simplified:           0
% 3.57/0.99  inst_num_eq_res_simplified:             0
% 3.57/0.99  inst_num_child_elim:                    0
% 3.57/0.99  inst_num_of_dismatching_blockings:      391
% 3.57/0.99  inst_num_of_non_proper_insts:           1014
% 3.57/0.99  inst_num_of_duplicates:                 0
% 3.57/0.99  inst_inst_num_from_inst_to_res:         0
% 3.57/0.99  inst_dismatching_checking_time:         0.
% 3.57/0.99  
% 3.57/0.99  ------ Resolution
% 3.57/0.99  
% 3.57/0.99  res_num_of_clauses:                     0
% 3.57/0.99  res_num_in_passive:                     0
% 3.57/0.99  res_num_in_active:                      0
% 3.57/0.99  res_num_of_loops:                       134
% 3.57/0.99  res_forward_subset_subsumed:            50
% 3.57/0.99  res_backward_subset_subsumed:           0
% 3.57/0.99  res_forward_subsumed:                   0
% 3.57/0.99  res_backward_subsumed:                  0
% 3.57/0.99  res_forward_subsumption_resolution:     1
% 3.57/0.99  res_backward_subsumption_resolution:    0
% 3.57/0.99  res_clause_to_clause_subsumption:       734
% 3.57/0.99  res_orphan_elimination:                 0
% 3.57/0.99  res_tautology_del:                      20
% 3.57/0.99  res_num_eq_res_simplified:              0
% 3.57/0.99  res_num_sel_changes:                    0
% 3.57/0.99  res_moves_from_active_to_pass:          0
% 3.57/0.99  
% 3.57/0.99  ------ Superposition
% 3.57/0.99  
% 3.57/0.99  sup_time_total:                         0.
% 3.57/0.99  sup_time_generating:                    0.
% 3.57/0.99  sup_time_sim_full:                      0.
% 3.57/0.99  sup_time_sim_immed:                     0.
% 3.57/0.99  
% 3.57/0.99  sup_num_of_clauses:                     190
% 3.57/0.99  sup_num_in_active:                      94
% 3.57/0.99  sup_num_in_passive:                     96
% 3.57/0.99  sup_num_of_loops:                       94
% 3.57/0.99  sup_fw_superposition:                   73
% 3.57/0.99  sup_bw_superposition:                   157
% 3.57/0.99  sup_immediate_simplified:               35
% 3.57/0.99  sup_given_eliminated:                   0
% 3.57/0.99  comparisons_done:                       0
% 3.57/0.99  comparisons_avoided:                    0
% 3.57/0.99  
% 3.57/0.99  ------ Simplifications
% 3.57/0.99  
% 3.57/0.99  
% 3.57/0.99  sim_fw_subset_subsumed:                 30
% 3.57/0.99  sim_bw_subset_subsumed:                 6
% 3.57/0.99  sim_fw_subsumed:                        6
% 3.57/0.99  sim_bw_subsumed:                        0
% 3.57/0.99  sim_fw_subsumption_res:                 2
% 3.57/0.99  sim_bw_subsumption_res:                 0
% 3.57/0.99  sim_tautology_del:                      16
% 3.57/0.99  sim_eq_tautology_del:                   0
% 3.57/0.99  sim_eq_res_simp:                        6
% 3.57/0.99  sim_fw_demodulated:                     0
% 3.57/0.99  sim_bw_demodulated:                     0
% 3.57/0.99  sim_light_normalised:                   0
% 3.57/0.99  sim_joinable_taut:                      0
% 3.57/0.99  sim_joinable_simp:                      0
% 3.57/0.99  sim_ac_normalised:                      0
% 3.57/0.99  sim_smt_subsumption:                    0
% 3.57/0.99  
%------------------------------------------------------------------------------
