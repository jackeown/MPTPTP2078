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
% DateTime   : Thu Dec  3 12:28:45 EST 2020

% Result     : Theorem 3.54s
% Output     : CNFRefutation 3.54s
% Verified   : 
% Statistics : Number of formulae       :  162 ( 958 expanded)
%              Number of clauses        :   86 ( 221 expanded)
%              Number of leaves         :   21 ( 330 expanded)
%              Depth                    :   20
%              Number of atoms          :  684 (5527 expanded)
%              Number of equality atoms :  129 ( 249 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f43])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f44])).

fof(f46,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X0)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(sK2(X0,X1,X2),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            | ~ r2_hidden(sK2(X0,X1,X2),X0)
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK2(X0,X1,X2),X1)
              & r2_hidden(sK2(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f45,f46])).

fof(f62,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f93,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k1_setfam_1(k2_tarski(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f62,f74])).

fof(f100,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k1_setfam_1(k2_tarski(X0,X1)))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f93])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_pre_topc(X2,X0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k3_xboole_0(X1,X2),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v3_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v3_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(k1_setfam_1(k2_tarski(X1,X2)),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(definition_unfolding,[],[f77,f74])).

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
                 => m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
                   => m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))
                  & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
              & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))
                  & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
              & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))
          & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
     => ( ~ m1_subset_1(k3_xboole_0(X2,sK6),u1_struct_0(k9_yellow_6(X0,X1)))
        & m1_subset_1(sK6,u1_struct_0(k9_yellow_6(X0,X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))
              & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
          & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
     => ( ? [X3] :
            ( ~ m1_subset_1(k3_xboole_0(sK5,X3),u1_struct_0(k9_yellow_6(X0,X1)))
            & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
        & m1_subset_1(sK5,u1_struct_0(k9_yellow_6(X0,X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))
                  & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
              & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ~ m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,sK4)))
                & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,sK4))) )
            & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,sK4))) )
        & m1_subset_1(sK4,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))
                    & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
                & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK3,X1)))
                  & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK3,X1))) )
              & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK3,X1))) )
          & m1_subset_1(X1,u1_struct_0(sK3)) )
      & l1_pre_topc(sK3)
      & v2_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK5,sK6),u1_struct_0(k9_yellow_6(sK3,sK4)))
    & m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4)))
    & m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK3,sK4)))
    & m1_subset_1(sK4,u1_struct_0(sK3))
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f36,f54,f53,f52,f51])).

fof(f85,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f55])).

fof(f84,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f55])).

fof(f88,plain,(
    m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4))) ),
    inference(cnf_transformation,[],[f55])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
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

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X2,X0,X1)
              | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f83,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f55])).

fof(f86,plain,(
    m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f55])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f73,f74])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
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

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f49,plain,(
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
    inference(nnf_transformation,[],[f32])).

fof(f50,plain,(
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
    inference(flattening,[],[f49])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ v3_pre_topc(X2,X0)
      | ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f75,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f89,plain,(
    ~ m1_subset_1(k3_xboole_0(sK5,sK6),u1_struct_0(k9_yellow_6(sK3,sK4))) ),
    inference(cnf_transformation,[],[f55])).

fof(f99,plain,(
    ~ m1_subset_1(k1_setfam_1(k2_tarski(sK5,sK6)),u1_struct_0(k9_yellow_6(sK3,sK4))) ),
    inference(definition_unfolding,[],[f89,f74])).

fof(f87,plain,(
    m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK3,sK4))) ),
    inference(cnf_transformation,[],[f55])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f48,plain,(
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

fof(f68,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(X2,X0)
      | ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( k1_setfam_1(k2_tarski(X0,X1)) = X2
      | r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f64,f74])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f38,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f37])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f38,f39])).

fof(f56,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k1_setfam_1(k2_tarski(X2,X1))) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1206,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X0,k1_setfam_1(k2_tarski(X1,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_20,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ v3_pre_topc(X2,X1)
    | v3_pre_topc(k1_setfam_1(k2_tarski(X2,X0)),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_30,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_532,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ v3_pre_topc(X2,X1)
    | v3_pre_topc(k1_setfam_1(k2_tarski(X2,X0)),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_30])).

cnf(c_533,plain,
    ( ~ v3_pre_topc(X0,sK3)
    | ~ v3_pre_topc(X1,sK3)
    | v3_pre_topc(k1_setfam_1(k2_tarski(X1,X0)),sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_532])).

cnf(c_31,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_537,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v3_pre_topc(k1_setfam_1(k2_tarski(X1,X0)),sK3)
    | ~ v3_pre_topc(X1,sK3)
    | ~ v3_pre_topc(X0,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_533,c_31])).

cnf(c_538,plain,
    ( ~ v3_pre_topc(X0,sK3)
    | ~ v3_pre_topc(X1,sK3)
    | v3_pre_topc(k1_setfam_1(k2_tarski(X1,X0)),sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(renaming,[status(thm)],[c_537])).

cnf(c_1186,plain,
    ( v3_pre_topc(X0,sK3) != iProver_top
    | v3_pre_topc(X1,sK3) != iProver_top
    | v3_pre_topc(k1_setfam_1(k2_tarski(X1,X0)),sK3) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_538])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4))) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1195,plain,
    ( m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_25,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(X1,X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_21,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f78])).

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
    inference(cnf_transformation,[],[f83])).

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

cnf(c_420,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK3,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_416,c_31,c_30])).

cnf(c_1190,plain,
    ( m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK3,X1))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_420])).

cnf(c_1493,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1195,c_1190])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_36,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_1506,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1493,c_36])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1199,plain,
    ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2335,plain,
    ( k9_subset_1(u1_struct_0(sK3),X0,sK6) = k1_setfam_1(k2_tarski(X0,sK6)) ),
    inference(superposition,[status(thm)],[c_1506,c_1199])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1200,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2664,plain,
    ( m1_subset_1(k1_setfam_1(k2_tarski(X0,sK6)),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2335,c_1200])).

cnf(c_8437,plain,
    ( m1_subset_1(k1_setfam_1(k2_tarski(X0,sK6)),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2664,c_36,c_1493])).

cnf(c_22,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f81])).

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
    inference(cnf_transformation,[],[f76])).

cnf(c_505,plain,
    ( ~ v3_pre_topc(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X1,X0)
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK3,X1))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_489,c_19])).

cnf(c_1187,plain,
    ( v3_pre_topc(X0,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(X1,X0) != iProver_top
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK3,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_505])).

cnf(c_18,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1198,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1894,plain,
    ( v3_pre_topc(X0,sK3) != iProver_top
    | m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK3,X1))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1187,c_1198])).

cnf(c_26,negated_conjecture,
    ( ~ m1_subset_1(k1_setfam_1(k2_tarski(sK5,sK6)),u1_struct_0(k9_yellow_6(sK3,sK4))) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1196,plain,
    ( m1_subset_1(k1_setfam_1(k2_tarski(sK5,sK6)),u1_struct_0(k9_yellow_6(sK3,sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_6597,plain,
    ( v3_pre_topc(k1_setfam_1(k2_tarski(sK5,sK6)),sK3) != iProver_top
    | m1_subset_1(k1_setfam_1(k2_tarski(sK5,sK6)),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(sK4,k1_setfam_1(k2_tarski(sK5,sK6))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1894,c_1196])).

cnf(c_8449,plain,
    ( v3_pre_topc(k1_setfam_1(k2_tarski(sK5,sK6)),sK3) != iProver_top
    | r2_hidden(sK4,k1_setfam_1(k2_tarski(sK5,sK6))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8437,c_6597])).

cnf(c_9315,plain,
    ( v3_pre_topc(sK6,sK3) != iProver_top
    | v3_pre_topc(sK5,sK3) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(sK4,k1_setfam_1(k2_tarski(sK5,sK6))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1186,c_8449])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK3,sK4))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1194,plain,
    ( m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_1494,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1194,c_1190])).

cnf(c_743,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1570,plain,
    ( u1_struct_0(k9_yellow_6(sK3,sK4)) = u1_struct_0(k9_yellow_6(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_743])).

cnf(c_749,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1478,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k1_setfam_1(k2_tarski(sK5,sK6)),u1_struct_0(k9_yellow_6(sK3,sK4)))
    | u1_struct_0(k9_yellow_6(sK3,sK4)) != X1
    | k1_setfam_1(k2_tarski(sK5,sK6)) != X0 ),
    inference(instantiation,[status(thm)],[c_749])).

cnf(c_1569,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK3,sK4)))
    | m1_subset_1(k1_setfam_1(k2_tarski(sK5,sK6)),u1_struct_0(k9_yellow_6(sK3,sK4)))
    | u1_struct_0(k9_yellow_6(sK3,sK4)) != u1_struct_0(k9_yellow_6(sK3,sK4))
    | k1_setfam_1(k2_tarski(sK5,sK6)) != X0 ),
    inference(instantiation,[status(thm)],[c_1478])).

cnf(c_1725,plain,
    ( m1_subset_1(k1_setfam_1(k2_tarski(sK5,sK6)),u1_struct_0(k9_yellow_6(sK3,sK4)))
    | ~ m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4)))
    | u1_struct_0(k9_yellow_6(sK3,sK4)) != u1_struct_0(k9_yellow_6(sK3,sK4))
    | k1_setfam_1(k2_tarski(sK5,sK6)) != sK6 ),
    inference(instantiation,[status(thm)],[c_1569])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1201,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2419,plain,
    ( r2_hidden(sK6,u1_struct_0(k9_yellow_6(sK3,sK4))) = iProver_top
    | v1_xboole_0(u1_struct_0(k9_yellow_6(sK3,sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1195,c_1201])).

cnf(c_23,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f80])).

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

cnf(c_1188,plain,
    ( v3_pre_topc(X0,sK3) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK3,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_465])).

cnf(c_2505,plain,
    ( v3_pre_topc(sK6,sK3) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v1_xboole_0(u1_struct_0(k9_yellow_6(sK3,sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2419,c_1188])).

cnf(c_2420,plain,
    ( r2_hidden(sK5,u1_struct_0(k9_yellow_6(sK3,sK4))) = iProver_top
    | v1_xboole_0(u1_struct_0(k9_yellow_6(sK3,sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1194,c_1201])).

cnf(c_2644,plain,
    ( v3_pre_topc(sK5,sK3) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v1_xboole_0(u1_struct_0(k9_yellow_6(sK3,sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2420,c_1188])).

cnf(c_5,plain,
    ( r2_hidden(sK2(X0,X1,X2),X1)
    | r2_hidden(sK2(X0,X1,X2),X2)
    | k1_setfam_1(k2_tarski(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1751,plain,
    ( r2_hidden(sK2(sK5,sK6,X0),X0)
    | r2_hidden(sK2(sK5,sK6,X0),sK6)
    | k1_setfam_1(k2_tarski(sK5,sK6)) = X0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2739,plain,
    ( r2_hidden(sK2(sK5,sK6,sK6),sK6)
    | k1_setfam_1(k2_tarski(sK5,sK6)) = sK6 ),
    inference(instantiation,[status(thm)],[c_1751])).

cnf(c_2740,plain,
    ( k1_setfam_1(k2_tarski(sK5,sK6)) = sK6
    | r2_hidden(sK2(sK5,sK6,sK6),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2739])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1202,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2965,plain,
    ( v1_xboole_0(u1_struct_0(k9_yellow_6(sK3,sK4))) != iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_1195,c_1202])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_3712,plain,
    ( ~ r2_hidden(sK2(sK5,sK6,sK6),sK6)
    | ~ v1_xboole_0(sK6) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3713,plain,
    ( r2_hidden(sK2(sK5,sK6,sK6),sK6) != iProver_top
    | v1_xboole_0(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3712])).

cnf(c_9340,plain,
    ( r2_hidden(sK4,k1_setfam_1(k2_tarski(sK5,sK6))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9315,c_36,c_27,c_26,c_1493,c_1494,c_1570,c_1725,c_2505,c_2644,c_2740,c_2965,c_3713])).

cnf(c_9345,plain,
    ( r2_hidden(sK4,sK6) != iProver_top
    | r2_hidden(sK4,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1206,c_9340])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(X1,X0)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f79])).

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

cnf(c_1189,plain,
    ( m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X1,u1_struct_0(k9_yellow_6(sK3,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_441])).

cnf(c_2643,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(sK4,sK5) = iProver_top
    | v1_xboole_0(u1_struct_0(k9_yellow_6(sK3,sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2420,c_1189])).

cnf(c_2504,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(sK4,sK6) = iProver_top
    | v1_xboole_0(u1_struct_0(k9_yellow_6(sK3,sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2419,c_1189])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9345,c_3713,c_2965,c_2740,c_2643,c_2504,c_1725,c_1570,c_1494,c_1493,c_26,c_27,c_36])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : iproveropt_run.sh %d %s
% 0.15/0.35  % Computer   : n010.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 10:28:44 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running in FOF mode
% 3.54/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.54/1.00  
% 3.54/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.54/1.00  
% 3.54/1.00  ------  iProver source info
% 3.54/1.00  
% 3.54/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.54/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.54/1.00  git: non_committed_changes: false
% 3.54/1.00  git: last_make_outside_of_git: false
% 3.54/1.00  
% 3.54/1.00  ------ 
% 3.54/1.00  
% 3.54/1.00  ------ Input Options
% 3.54/1.00  
% 3.54/1.00  --out_options                           all
% 3.54/1.00  --tptp_safe_out                         true
% 3.54/1.00  --problem_path                          ""
% 3.54/1.00  --include_path                          ""
% 3.54/1.00  --clausifier                            res/vclausify_rel
% 3.54/1.00  --clausifier_options                    --mode clausify
% 3.54/1.00  --stdin                                 false
% 3.54/1.00  --stats_out                             all
% 3.54/1.00  
% 3.54/1.00  ------ General Options
% 3.54/1.00  
% 3.54/1.00  --fof                                   false
% 3.54/1.00  --time_out_real                         305.
% 3.54/1.00  --time_out_virtual                      -1.
% 3.54/1.00  --symbol_type_check                     false
% 3.54/1.00  --clausify_out                          false
% 3.54/1.00  --sig_cnt_out                           false
% 3.54/1.00  --trig_cnt_out                          false
% 3.54/1.00  --trig_cnt_out_tolerance                1.
% 3.54/1.00  --trig_cnt_out_sk_spl                   false
% 3.54/1.00  --abstr_cl_out                          false
% 3.54/1.00  
% 3.54/1.00  ------ Global Options
% 3.54/1.00  
% 3.54/1.00  --schedule                              default
% 3.54/1.00  --add_important_lit                     false
% 3.54/1.00  --prop_solver_per_cl                    1000
% 3.54/1.00  --min_unsat_core                        false
% 3.54/1.00  --soft_assumptions                      false
% 3.54/1.00  --soft_lemma_size                       3
% 3.54/1.00  --prop_impl_unit_size                   0
% 3.54/1.00  --prop_impl_unit                        []
% 3.54/1.00  --share_sel_clauses                     true
% 3.54/1.00  --reset_solvers                         false
% 3.54/1.00  --bc_imp_inh                            [conj_cone]
% 3.54/1.00  --conj_cone_tolerance                   3.
% 3.54/1.00  --extra_neg_conj                        none
% 3.54/1.00  --large_theory_mode                     true
% 3.54/1.00  --prolific_symb_bound                   200
% 3.54/1.00  --lt_threshold                          2000
% 3.54/1.00  --clause_weak_htbl                      true
% 3.54/1.00  --gc_record_bc_elim                     false
% 3.54/1.00  
% 3.54/1.00  ------ Preprocessing Options
% 3.54/1.00  
% 3.54/1.00  --preprocessing_flag                    true
% 3.54/1.00  --time_out_prep_mult                    0.1
% 3.54/1.00  --splitting_mode                        input
% 3.54/1.00  --splitting_grd                         true
% 3.54/1.00  --splitting_cvd                         false
% 3.54/1.00  --splitting_cvd_svl                     false
% 3.54/1.00  --splitting_nvd                         32
% 3.54/1.00  --sub_typing                            true
% 3.54/1.00  --prep_gs_sim                           true
% 3.54/1.00  --prep_unflatten                        true
% 3.54/1.00  --prep_res_sim                          true
% 3.54/1.00  --prep_upred                            true
% 3.54/1.00  --prep_sem_filter                       exhaustive
% 3.54/1.00  --prep_sem_filter_out                   false
% 3.54/1.00  --pred_elim                             true
% 3.54/1.00  --res_sim_input                         true
% 3.54/1.00  --eq_ax_congr_red                       true
% 3.54/1.00  --pure_diseq_elim                       true
% 3.54/1.00  --brand_transform                       false
% 3.54/1.00  --non_eq_to_eq                          false
% 3.54/1.00  --prep_def_merge                        true
% 3.54/1.00  --prep_def_merge_prop_impl              false
% 3.54/1.00  --prep_def_merge_mbd                    true
% 3.54/1.00  --prep_def_merge_tr_red                 false
% 3.54/1.00  --prep_def_merge_tr_cl                  false
% 3.54/1.00  --smt_preprocessing                     true
% 3.54/1.00  --smt_ac_axioms                         fast
% 3.54/1.00  --preprocessed_out                      false
% 3.54/1.00  --preprocessed_stats                    false
% 3.54/1.00  
% 3.54/1.00  ------ Abstraction refinement Options
% 3.54/1.00  
% 3.54/1.00  --abstr_ref                             []
% 3.54/1.00  --abstr_ref_prep                        false
% 3.54/1.00  --abstr_ref_until_sat                   false
% 3.54/1.00  --abstr_ref_sig_restrict                funpre
% 3.54/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.54/1.00  --abstr_ref_under                       []
% 3.54/1.00  
% 3.54/1.00  ------ SAT Options
% 3.54/1.00  
% 3.54/1.00  --sat_mode                              false
% 3.54/1.00  --sat_fm_restart_options                ""
% 3.54/1.00  --sat_gr_def                            false
% 3.54/1.00  --sat_epr_types                         true
% 3.54/1.00  --sat_non_cyclic_types                  false
% 3.54/1.00  --sat_finite_models                     false
% 3.54/1.00  --sat_fm_lemmas                         false
% 3.54/1.00  --sat_fm_prep                           false
% 3.54/1.00  --sat_fm_uc_incr                        true
% 3.54/1.00  --sat_out_model                         small
% 3.54/1.00  --sat_out_clauses                       false
% 3.54/1.00  
% 3.54/1.00  ------ QBF Options
% 3.54/1.00  
% 3.54/1.00  --qbf_mode                              false
% 3.54/1.00  --qbf_elim_univ                         false
% 3.54/1.00  --qbf_dom_inst                          none
% 3.54/1.00  --qbf_dom_pre_inst                      false
% 3.54/1.00  --qbf_sk_in                             false
% 3.54/1.00  --qbf_pred_elim                         true
% 3.54/1.00  --qbf_split                             512
% 3.54/1.00  
% 3.54/1.00  ------ BMC1 Options
% 3.54/1.00  
% 3.54/1.00  --bmc1_incremental                      false
% 3.54/1.00  --bmc1_axioms                           reachable_all
% 3.54/1.00  --bmc1_min_bound                        0
% 3.54/1.00  --bmc1_max_bound                        -1
% 3.54/1.00  --bmc1_max_bound_default                -1
% 3.54/1.00  --bmc1_symbol_reachability              true
% 3.54/1.00  --bmc1_property_lemmas                  false
% 3.54/1.00  --bmc1_k_induction                      false
% 3.54/1.00  --bmc1_non_equiv_states                 false
% 3.54/1.00  --bmc1_deadlock                         false
% 3.54/1.00  --bmc1_ucm                              false
% 3.54/1.00  --bmc1_add_unsat_core                   none
% 3.54/1.00  --bmc1_unsat_core_children              false
% 3.54/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.54/1.00  --bmc1_out_stat                         full
% 3.54/1.00  --bmc1_ground_init                      false
% 3.54/1.00  --bmc1_pre_inst_next_state              false
% 3.54/1.00  --bmc1_pre_inst_state                   false
% 3.54/1.00  --bmc1_pre_inst_reach_state             false
% 3.54/1.00  --bmc1_out_unsat_core                   false
% 3.54/1.00  --bmc1_aig_witness_out                  false
% 3.54/1.00  --bmc1_verbose                          false
% 3.54/1.00  --bmc1_dump_clauses_tptp                false
% 3.54/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.54/1.00  --bmc1_dump_file                        -
% 3.54/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.54/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.54/1.00  --bmc1_ucm_extend_mode                  1
% 3.54/1.00  --bmc1_ucm_init_mode                    2
% 3.54/1.00  --bmc1_ucm_cone_mode                    none
% 3.54/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.54/1.00  --bmc1_ucm_relax_model                  4
% 3.54/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.54/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.54/1.00  --bmc1_ucm_layered_model                none
% 3.54/1.00  --bmc1_ucm_max_lemma_size               10
% 3.54/1.00  
% 3.54/1.00  ------ AIG Options
% 3.54/1.00  
% 3.54/1.00  --aig_mode                              false
% 3.54/1.00  
% 3.54/1.00  ------ Instantiation Options
% 3.54/1.00  
% 3.54/1.00  --instantiation_flag                    true
% 3.54/1.00  --inst_sos_flag                         false
% 3.54/1.00  --inst_sos_phase                        true
% 3.54/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.54/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.54/1.00  --inst_lit_sel_side                     num_symb
% 3.54/1.00  --inst_solver_per_active                1400
% 3.54/1.00  --inst_solver_calls_frac                1.
% 3.54/1.00  --inst_passive_queue_type               priority_queues
% 3.54/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.54/1.00  --inst_passive_queues_freq              [25;2]
% 3.54/1.00  --inst_dismatching                      true
% 3.54/1.00  --inst_eager_unprocessed_to_passive     true
% 3.54/1.00  --inst_prop_sim_given                   true
% 3.54/1.00  --inst_prop_sim_new                     false
% 3.54/1.00  --inst_subs_new                         false
% 3.54/1.00  --inst_eq_res_simp                      false
% 3.54/1.00  --inst_subs_given                       false
% 3.54/1.00  --inst_orphan_elimination               true
% 3.54/1.00  --inst_learning_loop_flag               true
% 3.54/1.00  --inst_learning_start                   3000
% 3.54/1.00  --inst_learning_factor                  2
% 3.54/1.00  --inst_start_prop_sim_after_learn       3
% 3.54/1.00  --inst_sel_renew                        solver
% 3.54/1.00  --inst_lit_activity_flag                true
% 3.54/1.00  --inst_restr_to_given                   false
% 3.54/1.00  --inst_activity_threshold               500
% 3.54/1.00  --inst_out_proof                        true
% 3.54/1.00  
% 3.54/1.00  ------ Resolution Options
% 3.54/1.00  
% 3.54/1.00  --resolution_flag                       true
% 3.54/1.00  --res_lit_sel                           adaptive
% 3.54/1.00  --res_lit_sel_side                      none
% 3.54/1.00  --res_ordering                          kbo
% 3.54/1.00  --res_to_prop_solver                    active
% 3.54/1.00  --res_prop_simpl_new                    false
% 3.54/1.00  --res_prop_simpl_given                  true
% 3.54/1.00  --res_passive_queue_type                priority_queues
% 3.54/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.54/1.00  --res_passive_queues_freq               [15;5]
% 3.54/1.00  --res_forward_subs                      full
% 3.54/1.00  --res_backward_subs                     full
% 3.54/1.00  --res_forward_subs_resolution           true
% 3.54/1.00  --res_backward_subs_resolution          true
% 3.54/1.00  --res_orphan_elimination                true
% 3.54/1.00  --res_time_limit                        2.
% 3.54/1.00  --res_out_proof                         true
% 3.54/1.00  
% 3.54/1.00  ------ Superposition Options
% 3.54/1.00  
% 3.54/1.00  --superposition_flag                    true
% 3.54/1.00  --sup_passive_queue_type                priority_queues
% 3.54/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.54/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.54/1.00  --demod_completeness_check              fast
% 3.54/1.00  --demod_use_ground                      true
% 3.54/1.00  --sup_to_prop_solver                    passive
% 3.54/1.00  --sup_prop_simpl_new                    true
% 3.54/1.00  --sup_prop_simpl_given                  true
% 3.54/1.00  --sup_fun_splitting                     false
% 3.54/1.00  --sup_smt_interval                      50000
% 3.54/1.00  
% 3.54/1.00  ------ Superposition Simplification Setup
% 3.54/1.00  
% 3.54/1.00  --sup_indices_passive                   []
% 3.54/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.54/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.54/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.54/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.54/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.54/1.00  --sup_full_bw                           [BwDemod]
% 3.54/1.00  --sup_immed_triv                        [TrivRules]
% 3.54/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.54/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.54/1.00  --sup_immed_bw_main                     []
% 3.54/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.54/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.54/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.54/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.54/1.00  
% 3.54/1.00  ------ Combination Options
% 3.54/1.00  
% 3.54/1.00  --comb_res_mult                         3
% 3.54/1.00  --comb_sup_mult                         2
% 3.54/1.00  --comb_inst_mult                        10
% 3.54/1.00  
% 3.54/1.00  ------ Debug Options
% 3.54/1.00  
% 3.54/1.00  --dbg_backtrace                         false
% 3.54/1.00  --dbg_dump_prop_clauses                 false
% 3.54/1.00  --dbg_dump_prop_clauses_file            -
% 3.54/1.00  --dbg_out_stat                          false
% 3.54/1.00  ------ Parsing...
% 3.54/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.54/1.00  
% 3.54/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.54/1.00  
% 3.54/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.54/1.00  
% 3.54/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.54/1.00  ------ Proving...
% 3.54/1.00  ------ Problem Properties 
% 3.54/1.00  
% 3.54/1.00  
% 3.54/1.00  clauses                                 27
% 3.54/1.00  conjectures                             4
% 3.54/1.00  EPR                                     5
% 3.54/1.00  Horn                                    22
% 3.54/1.00  unary                                   5
% 3.54/1.00  binary                                  9
% 3.54/1.00  lits                                    68
% 3.54/1.00  lits eq                                 7
% 3.54/1.00  fd_pure                                 0
% 3.54/1.00  fd_pseudo                               0
% 3.54/1.00  fd_cond                                 0
% 3.54/1.00  fd_pseudo_cond                          3
% 3.54/1.00  AC symbols                              0
% 3.54/1.00  
% 3.54/1.00  ------ Schedule dynamic 5 is on 
% 3.54/1.00  
% 3.54/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.54/1.00  
% 3.54/1.00  
% 3.54/1.00  ------ 
% 3.54/1.00  Current options:
% 3.54/1.00  ------ 
% 3.54/1.00  
% 3.54/1.00  ------ Input Options
% 3.54/1.00  
% 3.54/1.00  --out_options                           all
% 3.54/1.00  --tptp_safe_out                         true
% 3.54/1.00  --problem_path                          ""
% 3.54/1.00  --include_path                          ""
% 3.54/1.00  --clausifier                            res/vclausify_rel
% 3.54/1.00  --clausifier_options                    --mode clausify
% 3.54/1.00  --stdin                                 false
% 3.54/1.00  --stats_out                             all
% 3.54/1.00  
% 3.54/1.00  ------ General Options
% 3.54/1.00  
% 3.54/1.00  --fof                                   false
% 3.54/1.00  --time_out_real                         305.
% 3.54/1.00  --time_out_virtual                      -1.
% 3.54/1.00  --symbol_type_check                     false
% 3.54/1.00  --clausify_out                          false
% 3.54/1.00  --sig_cnt_out                           false
% 3.54/1.00  --trig_cnt_out                          false
% 3.54/1.00  --trig_cnt_out_tolerance                1.
% 3.54/1.00  --trig_cnt_out_sk_spl                   false
% 3.54/1.00  --abstr_cl_out                          false
% 3.54/1.00  
% 3.54/1.00  ------ Global Options
% 3.54/1.00  
% 3.54/1.00  --schedule                              default
% 3.54/1.00  --add_important_lit                     false
% 3.54/1.00  --prop_solver_per_cl                    1000
% 3.54/1.00  --min_unsat_core                        false
% 3.54/1.00  --soft_assumptions                      false
% 3.54/1.00  --soft_lemma_size                       3
% 3.54/1.00  --prop_impl_unit_size                   0
% 3.54/1.00  --prop_impl_unit                        []
% 3.54/1.00  --share_sel_clauses                     true
% 3.54/1.00  --reset_solvers                         false
% 3.54/1.00  --bc_imp_inh                            [conj_cone]
% 3.54/1.00  --conj_cone_tolerance                   3.
% 3.54/1.00  --extra_neg_conj                        none
% 3.54/1.00  --large_theory_mode                     true
% 3.54/1.00  --prolific_symb_bound                   200
% 3.54/1.00  --lt_threshold                          2000
% 3.54/1.00  --clause_weak_htbl                      true
% 3.54/1.00  --gc_record_bc_elim                     false
% 3.54/1.00  
% 3.54/1.00  ------ Preprocessing Options
% 3.54/1.00  
% 3.54/1.00  --preprocessing_flag                    true
% 3.54/1.00  --time_out_prep_mult                    0.1
% 3.54/1.00  --splitting_mode                        input
% 3.54/1.00  --splitting_grd                         true
% 3.54/1.00  --splitting_cvd                         false
% 3.54/1.00  --splitting_cvd_svl                     false
% 3.54/1.00  --splitting_nvd                         32
% 3.54/1.00  --sub_typing                            true
% 3.54/1.00  --prep_gs_sim                           true
% 3.54/1.00  --prep_unflatten                        true
% 3.54/1.00  --prep_res_sim                          true
% 3.54/1.00  --prep_upred                            true
% 3.54/1.00  --prep_sem_filter                       exhaustive
% 3.54/1.00  --prep_sem_filter_out                   false
% 3.54/1.00  --pred_elim                             true
% 3.54/1.00  --res_sim_input                         true
% 3.54/1.00  --eq_ax_congr_red                       true
% 3.54/1.00  --pure_diseq_elim                       true
% 3.54/1.00  --brand_transform                       false
% 3.54/1.00  --non_eq_to_eq                          false
% 3.54/1.00  --prep_def_merge                        true
% 3.54/1.00  --prep_def_merge_prop_impl              false
% 3.54/1.00  --prep_def_merge_mbd                    true
% 3.54/1.00  --prep_def_merge_tr_red                 false
% 3.54/1.00  --prep_def_merge_tr_cl                  false
% 3.54/1.00  --smt_preprocessing                     true
% 3.54/1.00  --smt_ac_axioms                         fast
% 3.54/1.00  --preprocessed_out                      false
% 3.54/1.00  --preprocessed_stats                    false
% 3.54/1.00  
% 3.54/1.00  ------ Abstraction refinement Options
% 3.54/1.00  
% 3.54/1.00  --abstr_ref                             []
% 3.54/1.00  --abstr_ref_prep                        false
% 3.54/1.00  --abstr_ref_until_sat                   false
% 3.54/1.00  --abstr_ref_sig_restrict                funpre
% 3.54/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.54/1.00  --abstr_ref_under                       []
% 3.54/1.00  
% 3.54/1.00  ------ SAT Options
% 3.54/1.00  
% 3.54/1.00  --sat_mode                              false
% 3.54/1.00  --sat_fm_restart_options                ""
% 3.54/1.00  --sat_gr_def                            false
% 3.54/1.00  --sat_epr_types                         true
% 3.54/1.00  --sat_non_cyclic_types                  false
% 3.54/1.00  --sat_finite_models                     false
% 3.54/1.00  --sat_fm_lemmas                         false
% 3.54/1.00  --sat_fm_prep                           false
% 3.54/1.00  --sat_fm_uc_incr                        true
% 3.54/1.00  --sat_out_model                         small
% 3.54/1.00  --sat_out_clauses                       false
% 3.54/1.00  
% 3.54/1.00  ------ QBF Options
% 3.54/1.00  
% 3.54/1.00  --qbf_mode                              false
% 3.54/1.00  --qbf_elim_univ                         false
% 3.54/1.00  --qbf_dom_inst                          none
% 3.54/1.00  --qbf_dom_pre_inst                      false
% 3.54/1.00  --qbf_sk_in                             false
% 3.54/1.00  --qbf_pred_elim                         true
% 3.54/1.00  --qbf_split                             512
% 3.54/1.00  
% 3.54/1.00  ------ BMC1 Options
% 3.54/1.00  
% 3.54/1.00  --bmc1_incremental                      false
% 3.54/1.00  --bmc1_axioms                           reachable_all
% 3.54/1.00  --bmc1_min_bound                        0
% 3.54/1.00  --bmc1_max_bound                        -1
% 3.54/1.00  --bmc1_max_bound_default                -1
% 3.54/1.00  --bmc1_symbol_reachability              true
% 3.54/1.00  --bmc1_property_lemmas                  false
% 3.54/1.00  --bmc1_k_induction                      false
% 3.54/1.00  --bmc1_non_equiv_states                 false
% 3.54/1.00  --bmc1_deadlock                         false
% 3.54/1.00  --bmc1_ucm                              false
% 3.54/1.00  --bmc1_add_unsat_core                   none
% 3.54/1.00  --bmc1_unsat_core_children              false
% 3.54/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.54/1.00  --bmc1_out_stat                         full
% 3.54/1.00  --bmc1_ground_init                      false
% 3.54/1.00  --bmc1_pre_inst_next_state              false
% 3.54/1.00  --bmc1_pre_inst_state                   false
% 3.54/1.00  --bmc1_pre_inst_reach_state             false
% 3.54/1.00  --bmc1_out_unsat_core                   false
% 3.54/1.00  --bmc1_aig_witness_out                  false
% 3.54/1.00  --bmc1_verbose                          false
% 3.54/1.00  --bmc1_dump_clauses_tptp                false
% 3.54/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.54/1.00  --bmc1_dump_file                        -
% 3.54/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.54/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.54/1.00  --bmc1_ucm_extend_mode                  1
% 3.54/1.00  --bmc1_ucm_init_mode                    2
% 3.54/1.00  --bmc1_ucm_cone_mode                    none
% 3.54/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.54/1.00  --bmc1_ucm_relax_model                  4
% 3.54/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.54/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.54/1.00  --bmc1_ucm_layered_model                none
% 3.54/1.00  --bmc1_ucm_max_lemma_size               10
% 3.54/1.00  
% 3.54/1.00  ------ AIG Options
% 3.54/1.00  
% 3.54/1.00  --aig_mode                              false
% 3.54/1.00  
% 3.54/1.00  ------ Instantiation Options
% 3.54/1.00  
% 3.54/1.00  --instantiation_flag                    true
% 3.54/1.00  --inst_sos_flag                         false
% 3.54/1.00  --inst_sos_phase                        true
% 3.54/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.54/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.54/1.00  --inst_lit_sel_side                     none
% 3.54/1.00  --inst_solver_per_active                1400
% 3.54/1.00  --inst_solver_calls_frac                1.
% 3.54/1.00  --inst_passive_queue_type               priority_queues
% 3.54/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.54/1.00  --inst_passive_queues_freq              [25;2]
% 3.54/1.00  --inst_dismatching                      true
% 3.54/1.00  --inst_eager_unprocessed_to_passive     true
% 3.54/1.00  --inst_prop_sim_given                   true
% 3.54/1.00  --inst_prop_sim_new                     false
% 3.54/1.00  --inst_subs_new                         false
% 3.54/1.00  --inst_eq_res_simp                      false
% 3.54/1.00  --inst_subs_given                       false
% 3.54/1.00  --inst_orphan_elimination               true
% 3.54/1.00  --inst_learning_loop_flag               true
% 3.54/1.00  --inst_learning_start                   3000
% 3.54/1.00  --inst_learning_factor                  2
% 3.54/1.00  --inst_start_prop_sim_after_learn       3
% 3.54/1.00  --inst_sel_renew                        solver
% 3.54/1.00  --inst_lit_activity_flag                true
% 3.54/1.00  --inst_restr_to_given                   false
% 3.54/1.00  --inst_activity_threshold               500
% 3.54/1.00  --inst_out_proof                        true
% 3.54/1.00  
% 3.54/1.00  ------ Resolution Options
% 3.54/1.00  
% 3.54/1.00  --resolution_flag                       false
% 3.54/1.00  --res_lit_sel                           adaptive
% 3.54/1.00  --res_lit_sel_side                      none
% 3.54/1.00  --res_ordering                          kbo
% 3.54/1.00  --res_to_prop_solver                    active
% 3.54/1.00  --res_prop_simpl_new                    false
% 3.54/1.00  --res_prop_simpl_given                  true
% 3.54/1.00  --res_passive_queue_type                priority_queues
% 3.54/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.54/1.00  --res_passive_queues_freq               [15;5]
% 3.54/1.00  --res_forward_subs                      full
% 3.54/1.00  --res_backward_subs                     full
% 3.54/1.00  --res_forward_subs_resolution           true
% 3.54/1.00  --res_backward_subs_resolution          true
% 3.54/1.00  --res_orphan_elimination                true
% 3.54/1.00  --res_time_limit                        2.
% 3.54/1.00  --res_out_proof                         true
% 3.54/1.00  
% 3.54/1.00  ------ Superposition Options
% 3.54/1.00  
% 3.54/1.00  --superposition_flag                    true
% 3.54/1.00  --sup_passive_queue_type                priority_queues
% 3.54/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.54/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.54/1.00  --demod_completeness_check              fast
% 3.54/1.00  --demod_use_ground                      true
% 3.54/1.00  --sup_to_prop_solver                    passive
% 3.54/1.00  --sup_prop_simpl_new                    true
% 3.54/1.00  --sup_prop_simpl_given                  true
% 3.54/1.00  --sup_fun_splitting                     false
% 3.54/1.00  --sup_smt_interval                      50000
% 3.54/1.00  
% 3.54/1.00  ------ Superposition Simplification Setup
% 3.54/1.00  
% 3.54/1.00  --sup_indices_passive                   []
% 3.54/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.54/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.54/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.54/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.54/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.54/1.00  --sup_full_bw                           [BwDemod]
% 3.54/1.00  --sup_immed_triv                        [TrivRules]
% 3.54/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.54/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.54/1.00  --sup_immed_bw_main                     []
% 3.54/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.54/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.54/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.54/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.54/1.00  
% 3.54/1.00  ------ Combination Options
% 3.54/1.00  
% 3.54/1.00  --comb_res_mult                         3
% 3.54/1.00  --comb_sup_mult                         2
% 3.54/1.00  --comb_inst_mult                        10
% 3.54/1.00  
% 3.54/1.00  ------ Debug Options
% 3.54/1.00  
% 3.54/1.00  --dbg_backtrace                         false
% 3.54/1.00  --dbg_dump_prop_clauses                 false
% 3.54/1.00  --dbg_dump_prop_clauses_file            -
% 3.54/1.00  --dbg_out_stat                          false
% 3.54/1.00  
% 3.54/1.00  
% 3.54/1.00  
% 3.54/1.00  
% 3.54/1.00  ------ Proving...
% 3.54/1.00  
% 3.54/1.00  
% 3.54/1.00  % SZS status Theorem for theBenchmark.p
% 3.54/1.00  
% 3.54/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.54/1.00  
% 3.54/1.00  fof(f3,axiom,(
% 3.54/1.00    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.54/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/1.00  
% 3.54/1.00  fof(f43,plain,(
% 3.54/1.00    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.54/1.00    inference(nnf_transformation,[],[f3])).
% 3.54/1.00  
% 3.54/1.00  fof(f44,plain,(
% 3.54/1.00    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.54/1.00    inference(flattening,[],[f43])).
% 3.54/1.00  
% 3.54/1.00  fof(f45,plain,(
% 3.54/1.00    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.54/1.00    inference(rectify,[],[f44])).
% 3.54/1.00  
% 3.54/1.00  fof(f46,plain,(
% 3.54/1.00    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 3.54/1.00    introduced(choice_axiom,[])).
% 3.54/1.00  
% 3.54/1.00  fof(f47,plain,(
% 3.54/1.00    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.54/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f45,f46])).
% 3.54/1.00  
% 3.54/1.00  fof(f62,plain,(
% 3.54/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k3_xboole_0(X0,X1) != X2) )),
% 3.54/1.00    inference(cnf_transformation,[],[f47])).
% 3.54/1.00  
% 3.54/1.00  fof(f9,axiom,(
% 3.54/1.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.54/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/1.00  
% 3.54/1.00  fof(f74,plain,(
% 3.54/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.54/1.00    inference(cnf_transformation,[],[f9])).
% 3.54/1.00  
% 3.54/1.00  fof(f93,plain,(
% 3.54/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k1_setfam_1(k2_tarski(X0,X1)) != X2) )),
% 3.54/1.00    inference(definition_unfolding,[],[f62,f74])).
% 3.54/1.00  
% 3.54/1.00  fof(f100,plain,(
% 3.54/1.00    ( ! [X4,X0,X1] : (r2_hidden(X4,k1_setfam_1(k2_tarski(X0,X1))) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 3.54/1.00    inference(equality_resolution,[],[f93])).
% 3.54/1.00  
% 3.54/1.00  fof(f12,axiom,(
% 3.54/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X2,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k3_xboole_0(X1,X2),X0))),
% 3.54/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/1.00  
% 3.54/1.00  fof(f27,plain,(
% 3.54/1.00    ! [X0,X1,X2] : (v3_pre_topc(k3_xboole_0(X1,X2),X0) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.54/1.00    inference(ennf_transformation,[],[f12])).
% 3.54/1.00  
% 3.54/1.00  fof(f28,plain,(
% 3.54/1.00    ! [X0,X1,X2] : (v3_pre_topc(k3_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.54/1.00    inference(flattening,[],[f27])).
% 3.54/1.00  
% 3.54/1.00  fof(f77,plain,(
% 3.54/1.00    ( ! [X2,X0,X1] : (v3_pre_topc(k3_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.54/1.00    inference(cnf_transformation,[],[f28])).
% 3.54/1.00  
% 3.54/1.00  fof(f98,plain,(
% 3.54/1.00    ( ! [X2,X0,X1] : (v3_pre_topc(k1_setfam_1(k2_tarski(X1,X2)),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.54/1.00    inference(definition_unfolding,[],[f77,f74])).
% 3.54/1.00  
% 3.54/1.00  fof(f16,conjecture,(
% 3.54/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) => m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))))))),
% 3.54/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/1.00  
% 3.54/1.00  fof(f17,negated_conjecture,(
% 3.54/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) => m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))))))),
% 3.54/1.00    inference(negated_conjecture,[],[f16])).
% 3.54/1.00  
% 3.54/1.00  fof(f35,plain,(
% 3.54/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.54/1.00    inference(ennf_transformation,[],[f17])).
% 3.54/1.00  
% 3.54/1.00  fof(f36,plain,(
% 3.54/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.54/1.00    inference(flattening,[],[f35])).
% 3.54/1.00  
% 3.54/1.00  fof(f54,plain,(
% 3.54/1.00    ( ! [X2,X0,X1] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) => (~m1_subset_1(k3_xboole_0(X2,sK6),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(sK6,u1_struct_0(k9_yellow_6(X0,X1))))) )),
% 3.54/1.00    introduced(choice_axiom,[])).
% 3.54/1.00  
% 3.54/1.00  fof(f53,plain,(
% 3.54/1.00    ( ! [X0,X1] : (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) => (? [X3] : (~m1_subset_1(k3_xboole_0(sK5,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(sK5,u1_struct_0(k9_yellow_6(X0,X1))))) )),
% 3.54/1.00    introduced(choice_axiom,[])).
% 3.54/1.00  
% 3.54/1.00  fof(f52,plain,(
% 3.54/1.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,sK4))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,sK4)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,sK4)))) & m1_subset_1(sK4,u1_struct_0(X0)))) )),
% 3.54/1.00    introduced(choice_axiom,[])).
% 3.54/1.00  
% 3.54/1.00  fof(f51,plain,(
% 3.54/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK3,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK3,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK3,X1)))) & m1_subset_1(X1,u1_struct_0(sK3))) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 3.54/1.00    introduced(choice_axiom,[])).
% 3.54/1.00  
% 3.54/1.00  fof(f55,plain,(
% 3.54/1.00    (((~m1_subset_1(k3_xboole_0(sK5,sK6),u1_struct_0(k9_yellow_6(sK3,sK4))) & m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4)))) & m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK3,sK4)))) & m1_subset_1(sK4,u1_struct_0(sK3))) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 3.54/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f36,f54,f53,f52,f51])).
% 3.54/1.00  
% 3.54/1.00  fof(f85,plain,(
% 3.54/1.00    l1_pre_topc(sK3)),
% 3.54/1.00    inference(cnf_transformation,[],[f55])).
% 3.54/1.00  
% 3.54/1.00  fof(f84,plain,(
% 3.54/1.00    v2_pre_topc(sK3)),
% 3.54/1.00    inference(cnf_transformation,[],[f55])).
% 3.54/1.00  
% 3.54/1.00  fof(f88,plain,(
% 3.54/1.00    m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4)))),
% 3.54/1.00    inference(cnf_transformation,[],[f55])).
% 3.54/1.00  
% 3.54/1.00  fof(f15,axiom,(
% 3.54/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => m1_connsp_2(X2,X0,X1))))),
% 3.54/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/1.00  
% 3.54/1.00  fof(f33,plain,(
% 3.54/1.00    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.54/1.00    inference(ennf_transformation,[],[f15])).
% 3.54/1.00  
% 3.54/1.00  fof(f34,plain,(
% 3.54/1.00    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.54/1.00    inference(flattening,[],[f33])).
% 3.54/1.00  
% 3.54/1.00  fof(f82,plain,(
% 3.54/1.00    ( ! [X2,X0,X1] : (m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.54/1.00    inference(cnf_transformation,[],[f34])).
% 3.54/1.00  
% 3.54/1.00  fof(f13,axiom,(
% 3.54/1.00    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.54/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/1.00  
% 3.54/1.00  fof(f29,plain,(
% 3.54/1.00    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.54/1.00    inference(ennf_transformation,[],[f13])).
% 3.54/1.00  
% 3.54/1.00  fof(f30,plain,(
% 3.54/1.00    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.54/1.00    inference(flattening,[],[f29])).
% 3.54/1.00  
% 3.54/1.00  fof(f78,plain,(
% 3.54/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.54/1.00    inference(cnf_transformation,[],[f30])).
% 3.54/1.00  
% 3.54/1.00  fof(f83,plain,(
% 3.54/1.00    ~v2_struct_0(sK3)),
% 3.54/1.00    inference(cnf_transformation,[],[f55])).
% 3.54/1.00  
% 3.54/1.00  fof(f86,plain,(
% 3.54/1.00    m1_subset_1(sK4,u1_struct_0(sK3))),
% 3.54/1.00    inference(cnf_transformation,[],[f55])).
% 3.54/1.00  
% 3.54/1.00  fof(f8,axiom,(
% 3.54/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 3.54/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/1.00  
% 3.54/1.00  fof(f23,plain,(
% 3.54/1.00    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 3.54/1.00    inference(ennf_transformation,[],[f8])).
% 3.54/1.00  
% 3.54/1.00  fof(f73,plain,(
% 3.54/1.00    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.54/1.00    inference(cnf_transformation,[],[f23])).
% 3.54/1.00  
% 3.54/1.00  fof(f97,plain,(
% 3.54/1.00    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.54/1.00    inference(definition_unfolding,[],[f73,f74])).
% 3.54/1.00  
% 3.54/1.00  fof(f7,axiom,(
% 3.54/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 3.54/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/1.00  
% 3.54/1.00  fof(f22,plain,(
% 3.54/1.00    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 3.54/1.00    inference(ennf_transformation,[],[f7])).
% 3.54/1.00  
% 3.54/1.00  fof(f72,plain,(
% 3.54/1.00    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.54/1.00    inference(cnf_transformation,[],[f22])).
% 3.54/1.00  
% 3.54/1.00  fof(f14,axiom,(
% 3.54/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))))))),
% 3.54/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/1.00  
% 3.54/1.00  fof(f31,plain,(
% 3.54/1.00    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.54/1.00    inference(ennf_transformation,[],[f14])).
% 3.54/1.00  
% 3.54/1.00  fof(f32,plain,(
% 3.54/1.00    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.54/1.00    inference(flattening,[],[f31])).
% 3.54/1.00  
% 3.54/1.00  fof(f49,plain,(
% 3.54/1.00    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | (~v3_pre_topc(X2,X0) | ~r2_hidden(X1,X2))) & ((v3_pre_topc(X2,X0) & r2_hidden(X1,X2)) | ~r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.54/1.00    inference(nnf_transformation,[],[f32])).
% 3.54/1.00  
% 3.54/1.00  fof(f50,plain,(
% 3.54/1.00    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~v3_pre_topc(X2,X0) | ~r2_hidden(X1,X2)) & ((v3_pre_topc(X2,X0) & r2_hidden(X1,X2)) | ~r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.54/1.00    inference(flattening,[],[f49])).
% 3.54/1.00  
% 3.54/1.00  fof(f81,plain,(
% 3.54/1.00    ( ! [X2,X0,X1] : (r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~v3_pre_topc(X2,X0) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.54/1.00    inference(cnf_transformation,[],[f50])).
% 3.54/1.00  
% 3.54/1.00  fof(f11,axiom,(
% 3.54/1.00    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 3.54/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/1.00  
% 3.54/1.00  fof(f25,plain,(
% 3.54/1.00    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 3.54/1.00    inference(ennf_transformation,[],[f11])).
% 3.54/1.00  
% 3.54/1.00  fof(f26,plain,(
% 3.54/1.00    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.54/1.00    inference(flattening,[],[f25])).
% 3.54/1.00  
% 3.54/1.00  fof(f76,plain,(
% 3.54/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.54/1.00    inference(cnf_transformation,[],[f26])).
% 3.54/1.00  
% 3.54/1.00  fof(f10,axiom,(
% 3.54/1.00    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 3.54/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/1.00  
% 3.54/1.00  fof(f24,plain,(
% 3.54/1.00    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 3.54/1.00    inference(ennf_transformation,[],[f10])).
% 3.54/1.00  
% 3.54/1.00  fof(f75,plain,(
% 3.54/1.00    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 3.54/1.00    inference(cnf_transformation,[],[f24])).
% 3.54/1.00  
% 3.54/1.00  fof(f89,plain,(
% 3.54/1.00    ~m1_subset_1(k3_xboole_0(sK5,sK6),u1_struct_0(k9_yellow_6(sK3,sK4)))),
% 3.54/1.00    inference(cnf_transformation,[],[f55])).
% 3.54/1.00  
% 3.54/1.00  fof(f99,plain,(
% 3.54/1.00    ~m1_subset_1(k1_setfam_1(k2_tarski(sK5,sK6)),u1_struct_0(k9_yellow_6(sK3,sK4)))),
% 3.54/1.00    inference(definition_unfolding,[],[f89,f74])).
% 3.54/1.00  
% 3.54/1.00  fof(f87,plain,(
% 3.54/1.00    m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK3,sK4)))),
% 3.54/1.00    inference(cnf_transformation,[],[f55])).
% 3.54/1.00  
% 3.54/1.00  fof(f6,axiom,(
% 3.54/1.00    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 3.54/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/1.00  
% 3.54/1.00  fof(f21,plain,(
% 3.54/1.00    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 3.54/1.00    inference(ennf_transformation,[],[f6])).
% 3.54/1.00  
% 3.54/1.00  fof(f48,plain,(
% 3.54/1.00    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 3.54/1.00    inference(nnf_transformation,[],[f21])).
% 3.54/1.00  
% 3.54/1.00  fof(f68,plain,(
% 3.54/1.00    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.54/1.00    inference(cnf_transformation,[],[f48])).
% 3.54/1.00  
% 3.54/1.00  fof(f80,plain,(
% 3.54/1.00    ( ! [X2,X0,X1] : (v3_pre_topc(X2,X0) | ~r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.54/1.00    inference(cnf_transformation,[],[f50])).
% 3.54/1.00  
% 3.54/1.00  fof(f64,plain,(
% 3.54/1.00    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 3.54/1.00    inference(cnf_transformation,[],[f47])).
% 3.54/1.00  
% 3.54/1.00  fof(f91,plain,(
% 3.54/1.00    ( ! [X2,X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = X2 | r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 3.54/1.00    inference(definition_unfolding,[],[f64,f74])).
% 3.54/1.00  
% 3.54/1.00  fof(f70,plain,(
% 3.54/1.00    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,X0) | ~v1_xboole_0(X0)) )),
% 3.54/1.00    inference(cnf_transformation,[],[f48])).
% 3.54/1.00  
% 3.54/1.00  fof(f1,axiom,(
% 3.54/1.00    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.54/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/1.00  
% 3.54/1.00  fof(f37,plain,(
% 3.54/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.54/1.00    inference(nnf_transformation,[],[f1])).
% 3.54/1.00  
% 3.54/1.00  fof(f38,plain,(
% 3.54/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.54/1.00    inference(rectify,[],[f37])).
% 3.54/1.00  
% 3.54/1.00  fof(f39,plain,(
% 3.54/1.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.54/1.00    introduced(choice_axiom,[])).
% 3.54/1.00  
% 3.54/1.00  fof(f40,plain,(
% 3.54/1.00    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.54/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f38,f39])).
% 3.54/1.00  
% 3.54/1.00  fof(f56,plain,(
% 3.54/1.00    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 3.54/1.00    inference(cnf_transformation,[],[f40])).
% 3.54/1.00  
% 3.54/1.00  fof(f79,plain,(
% 3.54/1.00    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.54/1.00    inference(cnf_transformation,[],[f50])).
% 3.54/1.00  
% 3.54/1.00  cnf(c_7,plain,
% 3.54/1.00      ( ~ r2_hidden(X0,X1)
% 3.54/1.00      | ~ r2_hidden(X0,X2)
% 3.54/1.00      | r2_hidden(X0,k1_setfam_1(k2_tarski(X2,X1))) ),
% 3.54/1.00      inference(cnf_transformation,[],[f100]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_1206,plain,
% 3.54/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.54/1.00      | r2_hidden(X0,X2) != iProver_top
% 3.54/1.00      | r2_hidden(X0,k1_setfam_1(k2_tarski(X1,X2))) = iProver_top ),
% 3.54/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_20,plain,
% 3.54/1.00      ( ~ v3_pre_topc(X0,X1)
% 3.54/1.00      | ~ v3_pre_topc(X2,X1)
% 3.54/1.00      | v3_pre_topc(k1_setfam_1(k2_tarski(X2,X0)),X1)
% 3.54/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.54/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.54/1.00      | ~ v2_pre_topc(X1)
% 3.54/1.00      | ~ l1_pre_topc(X1) ),
% 3.54/1.00      inference(cnf_transformation,[],[f98]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_30,negated_conjecture,
% 3.54/1.00      ( l1_pre_topc(sK3) ),
% 3.54/1.00      inference(cnf_transformation,[],[f85]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_532,plain,
% 3.54/1.00      ( ~ v3_pre_topc(X0,X1)
% 3.54/1.00      | ~ v3_pre_topc(X2,X1)
% 3.54/1.00      | v3_pre_topc(k1_setfam_1(k2_tarski(X2,X0)),X1)
% 3.54/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.54/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.54/1.00      | ~ v2_pre_topc(X1)
% 3.54/1.00      | sK3 != X1 ),
% 3.54/1.00      inference(resolution_lifted,[status(thm)],[c_20,c_30]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_533,plain,
% 3.54/1.00      ( ~ v3_pre_topc(X0,sK3)
% 3.54/1.00      | ~ v3_pre_topc(X1,sK3)
% 3.54/1.00      | v3_pre_topc(k1_setfam_1(k2_tarski(X1,X0)),sK3)
% 3.54/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.54/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.54/1.00      | ~ v2_pre_topc(sK3) ),
% 3.54/1.00      inference(unflattening,[status(thm)],[c_532]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_31,negated_conjecture,
% 3.54/1.00      ( v2_pre_topc(sK3) ),
% 3.54/1.00      inference(cnf_transformation,[],[f84]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_537,plain,
% 3.54/1.00      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.54/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.54/1.00      | v3_pre_topc(k1_setfam_1(k2_tarski(X1,X0)),sK3)
% 3.54/1.00      | ~ v3_pre_topc(X1,sK3)
% 3.54/1.00      | ~ v3_pre_topc(X0,sK3) ),
% 3.54/1.00      inference(global_propositional_subsumption,
% 3.54/1.00                [status(thm)],
% 3.54/1.00                [c_533,c_31]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_538,plain,
% 3.54/1.00      ( ~ v3_pre_topc(X0,sK3)
% 3.54/1.00      | ~ v3_pre_topc(X1,sK3)
% 3.54/1.00      | v3_pre_topc(k1_setfam_1(k2_tarski(X1,X0)),sK3)
% 3.54/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.54/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 3.54/1.00      inference(renaming,[status(thm)],[c_537]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_1186,plain,
% 3.54/1.00      ( v3_pre_topc(X0,sK3) != iProver_top
% 3.54/1.00      | v3_pre_topc(X1,sK3) != iProver_top
% 3.54/1.00      | v3_pre_topc(k1_setfam_1(k2_tarski(X1,X0)),sK3) = iProver_top
% 3.54/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.54/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 3.54/1.00      inference(predicate_to_equality,[status(thm)],[c_538]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_27,negated_conjecture,
% 3.54/1.00      ( m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4))) ),
% 3.54/1.00      inference(cnf_transformation,[],[f88]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_1195,plain,
% 3.54/1.00      ( m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4))) = iProver_top ),
% 3.54/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_25,plain,
% 3.54/1.00      ( m1_connsp_2(X0,X1,X2)
% 3.54/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.54/1.00      | ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(X1,X2)))
% 3.54/1.00      | v2_struct_0(X1)
% 3.54/1.00      | ~ v2_pre_topc(X1)
% 3.54/1.00      | ~ l1_pre_topc(X1) ),
% 3.54/1.00      inference(cnf_transformation,[],[f82]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_21,plain,
% 3.54/1.00      ( ~ m1_connsp_2(X0,X1,X2)
% 3.54/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.54/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.54/1.00      | v2_struct_0(X1)
% 3.54/1.00      | ~ v2_pre_topc(X1)
% 3.54/1.00      | ~ l1_pre_topc(X1) ),
% 3.54/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_385,plain,
% 3.54/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.54/1.00      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
% 3.54/1.00      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.54/1.00      | v2_struct_0(X1)
% 3.54/1.00      | ~ v2_pre_topc(X1)
% 3.54/1.00      | ~ l1_pre_topc(X1) ),
% 3.54/1.00      inference(resolution,[status(thm)],[c_25,c_21]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_32,negated_conjecture,
% 3.54/1.00      ( ~ v2_struct_0(sK3) ),
% 3.54/1.00      inference(cnf_transformation,[],[f83]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_415,plain,
% 3.54/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.54/1.00      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
% 3.54/1.00      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.54/1.00      | ~ v2_pre_topc(X1)
% 3.54/1.00      | ~ l1_pre_topc(X1)
% 3.54/1.00      | sK3 != X1 ),
% 3.54/1.00      inference(resolution_lifted,[status(thm)],[c_385,c_32]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_416,plain,
% 3.54/1.00      ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK3,X1)))
% 3.54/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 3.54/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.54/1.00      | ~ v2_pre_topc(sK3)
% 3.54/1.00      | ~ l1_pre_topc(sK3) ),
% 3.54/1.00      inference(unflattening,[status(thm)],[c_415]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_420,plain,
% 3.54/1.00      ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK3,X1)))
% 3.54/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 3.54/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 3.54/1.00      inference(global_propositional_subsumption,
% 3.54/1.00                [status(thm)],
% 3.54/1.00                [c_416,c_31,c_30]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_1190,plain,
% 3.54/1.00      ( m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK3,X1))) != iProver_top
% 3.54/1.00      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
% 3.54/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 3.54/1.00      inference(predicate_to_equality,[status(thm)],[c_420]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_1493,plain,
% 3.54/1.00      ( m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 3.54/1.00      | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 3.54/1.00      inference(superposition,[status(thm)],[c_1195,c_1190]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_29,negated_conjecture,
% 3.54/1.00      ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 3.54/1.00      inference(cnf_transformation,[],[f86]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_36,plain,
% 3.54/1.00      ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
% 3.54/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_1506,plain,
% 3.54/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 3.54/1.00      inference(global_propositional_subsumption,
% 3.54/1.00                [status(thm)],
% 3.54/1.00                [c_1493,c_36]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_17,plain,
% 3.54/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.54/1.00      | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
% 3.54/1.00      inference(cnf_transformation,[],[f97]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_1199,plain,
% 3.54/1.00      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
% 3.54/1.00      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 3.54/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_2335,plain,
% 3.54/1.00      ( k9_subset_1(u1_struct_0(sK3),X0,sK6) = k1_setfam_1(k2_tarski(X0,sK6)) ),
% 3.54/1.00      inference(superposition,[status(thm)],[c_1506,c_1199]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_16,plain,
% 3.54/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.54/1.00      | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 3.54/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_1200,plain,
% 3.54/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.54/1.00      | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 3.54/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_2664,plain,
% 3.54/1.00      ( m1_subset_1(k1_setfam_1(k2_tarski(X0,sK6)),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 3.54/1.00      | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 3.54/1.00      inference(superposition,[status(thm)],[c_2335,c_1200]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_8437,plain,
% 3.54/1.00      ( m1_subset_1(k1_setfam_1(k2_tarski(X0,sK6)),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 3.54/1.00      inference(global_propositional_subsumption,
% 3.54/1.00                [status(thm)],
% 3.54/1.00                [c_2664,c_36,c_1493]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_22,plain,
% 3.54/1.00      ( ~ v3_pre_topc(X0,X1)
% 3.54/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.54/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.54/1.00      | ~ r2_hidden(X2,X0)
% 3.54/1.00      | r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
% 3.54/1.00      | v2_struct_0(X1)
% 3.54/1.00      | ~ v2_pre_topc(X1)
% 3.54/1.00      | ~ l1_pre_topc(X1) ),
% 3.54/1.00      inference(cnf_transformation,[],[f81]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_484,plain,
% 3.54/1.00      ( ~ v3_pre_topc(X0,X1)
% 3.54/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.54/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.54/1.00      | ~ r2_hidden(X2,X0)
% 3.54/1.00      | r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
% 3.54/1.00      | ~ v2_pre_topc(X1)
% 3.54/1.00      | ~ l1_pre_topc(X1)
% 3.54/1.00      | sK3 != X1 ),
% 3.54/1.00      inference(resolution_lifted,[status(thm)],[c_22,c_32]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_485,plain,
% 3.54/1.00      ( ~ v3_pre_topc(X0,sK3)
% 3.54/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 3.54/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.54/1.00      | ~ r2_hidden(X1,X0)
% 3.54/1.00      | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK3,X1)))
% 3.54/1.00      | ~ v2_pre_topc(sK3)
% 3.54/1.00      | ~ l1_pre_topc(sK3) ),
% 3.54/1.00      inference(unflattening,[status(thm)],[c_484]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_489,plain,
% 3.54/1.00      ( ~ v3_pre_topc(X0,sK3)
% 3.54/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 3.54/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.54/1.00      | ~ r2_hidden(X1,X0)
% 3.54/1.00      | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK3,X1))) ),
% 3.54/1.00      inference(global_propositional_subsumption,
% 3.54/1.00                [status(thm)],
% 3.54/1.00                [c_485,c_31,c_30]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_19,plain,
% 3.54/1.00      ( m1_subset_1(X0,X1)
% 3.54/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.54/1.00      | ~ r2_hidden(X0,X2) ),
% 3.54/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_505,plain,
% 3.54/1.00      ( ~ v3_pre_topc(X0,sK3)
% 3.54/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.54/1.00      | ~ r2_hidden(X1,X0)
% 3.54/1.00      | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK3,X1))) ),
% 3.54/1.00      inference(forward_subsumption_resolution,
% 3.54/1.00                [status(thm)],
% 3.54/1.00                [c_489,c_19]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_1187,plain,
% 3.54/1.00      ( v3_pre_topc(X0,sK3) != iProver_top
% 3.54/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.54/1.00      | r2_hidden(X1,X0) != iProver_top
% 3.54/1.00      | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK3,X1))) = iProver_top ),
% 3.54/1.00      inference(predicate_to_equality,[status(thm)],[c_505]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_18,plain,
% 3.54/1.00      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 3.54/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_1198,plain,
% 3.54/1.00      ( m1_subset_1(X0,X1) = iProver_top
% 3.54/1.00      | r2_hidden(X0,X1) != iProver_top ),
% 3.54/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_1894,plain,
% 3.54/1.00      ( v3_pre_topc(X0,sK3) != iProver_top
% 3.54/1.00      | m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK3,X1))) = iProver_top
% 3.54/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.54/1.00      | r2_hidden(X1,X0) != iProver_top ),
% 3.54/1.00      inference(superposition,[status(thm)],[c_1187,c_1198]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_26,negated_conjecture,
% 3.54/1.00      ( ~ m1_subset_1(k1_setfam_1(k2_tarski(sK5,sK6)),u1_struct_0(k9_yellow_6(sK3,sK4))) ),
% 3.54/1.00      inference(cnf_transformation,[],[f99]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_1196,plain,
% 3.54/1.00      ( m1_subset_1(k1_setfam_1(k2_tarski(sK5,sK6)),u1_struct_0(k9_yellow_6(sK3,sK4))) != iProver_top ),
% 3.54/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_6597,plain,
% 3.54/1.00      ( v3_pre_topc(k1_setfam_1(k2_tarski(sK5,sK6)),sK3) != iProver_top
% 3.54/1.00      | m1_subset_1(k1_setfam_1(k2_tarski(sK5,sK6)),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.54/1.00      | r2_hidden(sK4,k1_setfam_1(k2_tarski(sK5,sK6))) != iProver_top ),
% 3.54/1.00      inference(superposition,[status(thm)],[c_1894,c_1196]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_8449,plain,
% 3.54/1.00      ( v3_pre_topc(k1_setfam_1(k2_tarski(sK5,sK6)),sK3) != iProver_top
% 3.54/1.00      | r2_hidden(sK4,k1_setfam_1(k2_tarski(sK5,sK6))) != iProver_top ),
% 3.54/1.00      inference(superposition,[status(thm)],[c_8437,c_6597]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_9315,plain,
% 3.54/1.00      ( v3_pre_topc(sK6,sK3) != iProver_top
% 3.54/1.00      | v3_pre_topc(sK5,sK3) != iProver_top
% 3.54/1.00      | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.54/1.00      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.54/1.00      | r2_hidden(sK4,k1_setfam_1(k2_tarski(sK5,sK6))) != iProver_top ),
% 3.54/1.00      inference(superposition,[status(thm)],[c_1186,c_8449]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_28,negated_conjecture,
% 3.54/1.00      ( m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK3,sK4))) ),
% 3.54/1.00      inference(cnf_transformation,[],[f87]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_1194,plain,
% 3.54/1.00      ( m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK3,sK4))) = iProver_top ),
% 3.54/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_1494,plain,
% 3.54/1.00      ( m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 3.54/1.00      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 3.54/1.00      inference(superposition,[status(thm)],[c_1194,c_1190]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_743,plain,( X0 = X0 ),theory(equality) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_1570,plain,
% 3.54/1.00      ( u1_struct_0(k9_yellow_6(sK3,sK4)) = u1_struct_0(k9_yellow_6(sK3,sK4)) ),
% 3.54/1.00      inference(instantiation,[status(thm)],[c_743]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_749,plain,
% 3.54/1.00      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.54/1.00      theory(equality) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_1478,plain,
% 3.54/1.00      ( ~ m1_subset_1(X0,X1)
% 3.54/1.00      | m1_subset_1(k1_setfam_1(k2_tarski(sK5,sK6)),u1_struct_0(k9_yellow_6(sK3,sK4)))
% 3.54/1.00      | u1_struct_0(k9_yellow_6(sK3,sK4)) != X1
% 3.54/1.00      | k1_setfam_1(k2_tarski(sK5,sK6)) != X0 ),
% 3.54/1.00      inference(instantiation,[status(thm)],[c_749]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_1569,plain,
% 3.54/1.00      ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK3,sK4)))
% 3.54/1.00      | m1_subset_1(k1_setfam_1(k2_tarski(sK5,sK6)),u1_struct_0(k9_yellow_6(sK3,sK4)))
% 3.54/1.00      | u1_struct_0(k9_yellow_6(sK3,sK4)) != u1_struct_0(k9_yellow_6(sK3,sK4))
% 3.54/1.00      | k1_setfam_1(k2_tarski(sK5,sK6)) != X0 ),
% 3.54/1.00      inference(instantiation,[status(thm)],[c_1478]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_1725,plain,
% 3.54/1.00      ( m1_subset_1(k1_setfam_1(k2_tarski(sK5,sK6)),u1_struct_0(k9_yellow_6(sK3,sK4)))
% 3.54/1.00      | ~ m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4)))
% 3.54/1.00      | u1_struct_0(k9_yellow_6(sK3,sK4)) != u1_struct_0(k9_yellow_6(sK3,sK4))
% 3.54/1.00      | k1_setfam_1(k2_tarski(sK5,sK6)) != sK6 ),
% 3.54/1.00      inference(instantiation,[status(thm)],[c_1569]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_15,plain,
% 3.54/1.00      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.54/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_1201,plain,
% 3.54/1.00      ( m1_subset_1(X0,X1) != iProver_top
% 3.54/1.00      | r2_hidden(X0,X1) = iProver_top
% 3.54/1.00      | v1_xboole_0(X1) = iProver_top ),
% 3.54/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_2419,plain,
% 3.54/1.00      ( r2_hidden(sK6,u1_struct_0(k9_yellow_6(sK3,sK4))) = iProver_top
% 3.54/1.00      | v1_xboole_0(u1_struct_0(k9_yellow_6(sK3,sK4))) = iProver_top ),
% 3.54/1.00      inference(superposition,[status(thm)],[c_1195,c_1201]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_23,plain,
% 3.54/1.00      ( v3_pre_topc(X0,X1)
% 3.54/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.54/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.54/1.00      | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
% 3.54/1.00      | v2_struct_0(X1)
% 3.54/1.00      | ~ v2_pre_topc(X1)
% 3.54/1.00      | ~ l1_pre_topc(X1) ),
% 3.54/1.00      inference(cnf_transformation,[],[f80]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_460,plain,
% 3.54/1.00      ( v3_pre_topc(X0,X1)
% 3.54/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.54/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.54/1.00      | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
% 3.54/1.00      | ~ v2_pre_topc(X1)
% 3.54/1.00      | ~ l1_pre_topc(X1)
% 3.54/1.00      | sK3 != X1 ),
% 3.54/1.00      inference(resolution_lifted,[status(thm)],[c_23,c_32]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_461,plain,
% 3.54/1.00      ( v3_pre_topc(X0,sK3)
% 3.54/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 3.54/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.54/1.00      | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(sK3,X1)))
% 3.54/1.00      | ~ v2_pre_topc(sK3)
% 3.54/1.00      | ~ l1_pre_topc(sK3) ),
% 3.54/1.00      inference(unflattening,[status(thm)],[c_460]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_465,plain,
% 3.54/1.00      ( v3_pre_topc(X0,sK3)
% 3.54/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 3.54/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.54/1.00      | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(sK3,X1))) ),
% 3.54/1.00      inference(global_propositional_subsumption,
% 3.54/1.00                [status(thm)],
% 3.54/1.00                [c_461,c_31,c_30]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_1188,plain,
% 3.54/1.00      ( v3_pre_topc(X0,sK3) = iProver_top
% 3.54/1.00      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
% 3.54/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.54/1.00      | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK3,X1))) != iProver_top ),
% 3.54/1.00      inference(predicate_to_equality,[status(thm)],[c_465]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_2505,plain,
% 3.54/1.00      ( v3_pre_topc(sK6,sK3) = iProver_top
% 3.54/1.00      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 3.54/1.00      | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.54/1.00      | v1_xboole_0(u1_struct_0(k9_yellow_6(sK3,sK4))) = iProver_top ),
% 3.54/1.00      inference(superposition,[status(thm)],[c_2419,c_1188]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_2420,plain,
% 3.54/1.00      ( r2_hidden(sK5,u1_struct_0(k9_yellow_6(sK3,sK4))) = iProver_top
% 3.54/1.00      | v1_xboole_0(u1_struct_0(k9_yellow_6(sK3,sK4))) = iProver_top ),
% 3.54/1.00      inference(superposition,[status(thm)],[c_1194,c_1201]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_2644,plain,
% 3.54/1.00      ( v3_pre_topc(sK5,sK3) = iProver_top
% 3.54/1.00      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 3.54/1.00      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.54/1.00      | v1_xboole_0(u1_struct_0(k9_yellow_6(sK3,sK4))) = iProver_top ),
% 3.54/1.00      inference(superposition,[status(thm)],[c_2420,c_1188]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_5,plain,
% 3.54/1.00      ( r2_hidden(sK2(X0,X1,X2),X1)
% 3.54/1.00      | r2_hidden(sK2(X0,X1,X2),X2)
% 3.54/1.00      | k1_setfam_1(k2_tarski(X0,X1)) = X2 ),
% 3.54/1.00      inference(cnf_transformation,[],[f91]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_1751,plain,
% 3.54/1.00      ( r2_hidden(sK2(sK5,sK6,X0),X0)
% 3.54/1.00      | r2_hidden(sK2(sK5,sK6,X0),sK6)
% 3.54/1.00      | k1_setfam_1(k2_tarski(sK5,sK6)) = X0 ),
% 3.54/1.00      inference(instantiation,[status(thm)],[c_5]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_2739,plain,
% 3.54/1.00      ( r2_hidden(sK2(sK5,sK6,sK6),sK6)
% 3.54/1.00      | k1_setfam_1(k2_tarski(sK5,sK6)) = sK6 ),
% 3.54/1.00      inference(instantiation,[status(thm)],[c_1751]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_2740,plain,
% 3.54/1.00      ( k1_setfam_1(k2_tarski(sK5,sK6)) = sK6
% 3.54/1.00      | r2_hidden(sK2(sK5,sK6,sK6),sK6) = iProver_top ),
% 3.54/1.00      inference(predicate_to_equality,[status(thm)],[c_2739]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_13,plain,
% 3.54/1.00      ( ~ m1_subset_1(X0,X1) | ~ v1_xboole_0(X1) | v1_xboole_0(X0) ),
% 3.54/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_1202,plain,
% 3.54/1.00      ( m1_subset_1(X0,X1) != iProver_top
% 3.54/1.00      | v1_xboole_0(X1) != iProver_top
% 3.54/1.00      | v1_xboole_0(X0) = iProver_top ),
% 3.54/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_2965,plain,
% 3.54/1.00      ( v1_xboole_0(u1_struct_0(k9_yellow_6(sK3,sK4))) != iProver_top
% 3.54/1.00      | v1_xboole_0(sK6) = iProver_top ),
% 3.54/1.00      inference(superposition,[status(thm)],[c_1195,c_1202]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_1,plain,
% 3.54/1.00      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.54/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_3712,plain,
% 3.54/1.00      ( ~ r2_hidden(sK2(sK5,sK6,sK6),sK6) | ~ v1_xboole_0(sK6) ),
% 3.54/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_3713,plain,
% 3.54/1.00      ( r2_hidden(sK2(sK5,sK6,sK6),sK6) != iProver_top
% 3.54/1.00      | v1_xboole_0(sK6) != iProver_top ),
% 3.54/1.00      inference(predicate_to_equality,[status(thm)],[c_3712]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_9340,plain,
% 3.54/1.00      ( r2_hidden(sK4,k1_setfam_1(k2_tarski(sK5,sK6))) != iProver_top ),
% 3.54/1.00      inference(global_propositional_subsumption,
% 3.54/1.00                [status(thm)],
% 3.54/1.00                [c_9315,c_36,c_27,c_26,c_1493,c_1494,c_1570,c_1725,
% 3.54/1.00                 c_2505,c_2644,c_2740,c_2965,c_3713]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_9345,plain,
% 3.54/1.00      ( r2_hidden(sK4,sK6) != iProver_top
% 3.54/1.00      | r2_hidden(sK4,sK5) != iProver_top ),
% 3.54/1.00      inference(superposition,[status(thm)],[c_1206,c_9340]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_24,plain,
% 3.54/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.54/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.54/1.00      | r2_hidden(X0,X2)
% 3.54/1.00      | ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(X1,X0)))
% 3.54/1.00      | v2_struct_0(X1)
% 3.54/1.00      | ~ v2_pre_topc(X1)
% 3.54/1.00      | ~ l1_pre_topc(X1) ),
% 3.54/1.00      inference(cnf_transformation,[],[f79]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_436,plain,
% 3.54/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.54/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.54/1.00      | r2_hidden(X0,X2)
% 3.54/1.00      | ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(X1,X0)))
% 3.54/1.00      | ~ v2_pre_topc(X1)
% 3.54/1.00      | ~ l1_pre_topc(X1)
% 3.54/1.00      | sK3 != X1 ),
% 3.54/1.00      inference(resolution_lifted,[status(thm)],[c_24,c_32]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_437,plain,
% 3.54/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.54/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.54/1.00      | r2_hidden(X0,X1)
% 3.54/1.00      | ~ r2_hidden(X1,u1_struct_0(k9_yellow_6(sK3,X0)))
% 3.54/1.00      | ~ v2_pre_topc(sK3)
% 3.54/1.00      | ~ l1_pre_topc(sK3) ),
% 3.54/1.00      inference(unflattening,[status(thm)],[c_436]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_441,plain,
% 3.54/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.54/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.54/1.00      | r2_hidden(X0,X1)
% 3.54/1.00      | ~ r2_hidden(X1,u1_struct_0(k9_yellow_6(sK3,X0))) ),
% 3.54/1.00      inference(global_propositional_subsumption,
% 3.54/1.00                [status(thm)],
% 3.54/1.00                [c_437,c_31,c_30]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_1189,plain,
% 3.54/1.00      ( m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 3.54/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.54/1.00      | r2_hidden(X0,X1) = iProver_top
% 3.54/1.00      | r2_hidden(X1,u1_struct_0(k9_yellow_6(sK3,X0))) != iProver_top ),
% 3.54/1.00      inference(predicate_to_equality,[status(thm)],[c_441]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_2643,plain,
% 3.54/1.00      ( m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 3.54/1.00      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.54/1.00      | r2_hidden(sK4,sK5) = iProver_top
% 3.54/1.00      | v1_xboole_0(u1_struct_0(k9_yellow_6(sK3,sK4))) = iProver_top ),
% 3.54/1.00      inference(superposition,[status(thm)],[c_2420,c_1189]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_2504,plain,
% 3.54/1.00      ( m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 3.54/1.00      | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.54/1.00      | r2_hidden(sK4,sK6) = iProver_top
% 3.54/1.00      | v1_xboole_0(u1_struct_0(k9_yellow_6(sK3,sK4))) = iProver_top ),
% 3.54/1.00      inference(superposition,[status(thm)],[c_2419,c_1189]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(contradiction,plain,
% 3.54/1.00      ( $false ),
% 3.54/1.00      inference(minisat,
% 3.54/1.00                [status(thm)],
% 3.54/1.00                [c_9345,c_3713,c_2965,c_2740,c_2643,c_2504,c_1725,c_1570,
% 3.54/1.00                 c_1494,c_1493,c_26,c_27,c_36]) ).
% 3.54/1.00  
% 3.54/1.00  
% 3.54/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.54/1.00  
% 3.54/1.00  ------                               Statistics
% 3.54/1.00  
% 3.54/1.00  ------ General
% 3.54/1.00  
% 3.54/1.00  abstr_ref_over_cycles:                  0
% 3.54/1.00  abstr_ref_under_cycles:                 0
% 3.54/1.00  gc_basic_clause_elim:                   0
% 3.54/1.00  forced_gc_time:                         0
% 3.54/1.01  parsing_time:                           0.024
% 3.54/1.01  unif_index_cands_time:                  0.
% 3.54/1.01  unif_index_add_time:                    0.
% 3.54/1.01  orderings_time:                         0.
% 3.54/1.01  out_proof_time:                         0.012
% 3.54/1.01  total_time:                             0.298
% 3.54/1.01  num_of_symbols:                         54
% 3.54/1.01  num_of_terms:                           10428
% 3.54/1.01  
% 3.54/1.01  ------ Preprocessing
% 3.54/1.01  
% 3.54/1.01  num_of_splits:                          0
% 3.54/1.01  num_of_split_atoms:                     0
% 3.54/1.01  num_of_reused_defs:                     0
% 3.54/1.01  num_eq_ax_congr_red:                    39
% 3.54/1.01  num_of_sem_filtered_clauses:            1
% 3.54/1.01  num_of_subtypes:                        0
% 3.54/1.01  monotx_restored_types:                  0
% 3.54/1.01  sat_num_of_epr_types:                   0
% 3.54/1.01  sat_num_of_non_cyclic_types:            0
% 3.54/1.01  sat_guarded_non_collapsed_types:        0
% 3.54/1.01  num_pure_diseq_elim:                    0
% 3.54/1.01  simp_replaced_by:                       0
% 3.54/1.01  res_preprocessed:                       136
% 3.54/1.01  prep_upred:                             0
% 3.54/1.01  prep_unflattend:                        5
% 3.54/1.01  smt_new_axioms:                         0
% 3.54/1.01  pred_elim_cands:                        4
% 3.54/1.01  pred_elim:                              5
% 3.54/1.01  pred_elim_cl:                           5
% 3.54/1.01  pred_elim_cycles:                       7
% 3.54/1.01  merged_defs:                            0
% 3.54/1.01  merged_defs_ncl:                        0
% 3.54/1.01  bin_hyper_res:                          0
% 3.54/1.01  prep_cycles:                            4
% 3.54/1.01  pred_elim_time:                         0.008
% 3.54/1.01  splitting_time:                         0.
% 3.54/1.01  sem_filter_time:                        0.
% 3.54/1.01  monotx_time:                            0.
% 3.54/1.01  subtype_inf_time:                       0.
% 3.54/1.01  
% 3.54/1.01  ------ Problem properties
% 3.54/1.01  
% 3.54/1.01  clauses:                                27
% 3.54/1.01  conjectures:                            4
% 3.54/1.01  epr:                                    5
% 3.54/1.01  horn:                                   22
% 3.54/1.01  ground:                                 4
% 3.54/1.01  unary:                                  5
% 3.54/1.01  binary:                                 9
% 3.54/1.01  lits:                                   68
% 3.54/1.01  lits_eq:                                7
% 3.54/1.01  fd_pure:                                0
% 3.54/1.01  fd_pseudo:                              0
% 3.54/1.01  fd_cond:                                0
% 3.54/1.01  fd_pseudo_cond:                         3
% 3.54/1.01  ac_symbols:                             0
% 3.54/1.01  
% 3.54/1.01  ------ Propositional Solver
% 3.54/1.01  
% 3.54/1.01  prop_solver_calls:                      29
% 3.54/1.01  prop_fast_solver_calls:                 1045
% 3.54/1.01  smt_solver_calls:                       0
% 3.54/1.01  smt_fast_solver_calls:                  0
% 3.54/1.01  prop_num_of_clauses:                    4225
% 3.54/1.01  prop_preprocess_simplified:             9743
% 3.54/1.01  prop_fo_subsumed:                       32
% 3.54/1.01  prop_solver_time:                       0.
% 3.54/1.01  smt_solver_time:                        0.
% 3.54/1.01  smt_fast_solver_time:                   0.
% 3.54/1.01  prop_fast_solver_time:                  0.
% 3.54/1.01  prop_unsat_core_time:                   0.
% 3.54/1.01  
% 3.54/1.01  ------ QBF
% 3.54/1.01  
% 3.54/1.01  qbf_q_res:                              0
% 3.54/1.01  qbf_num_tautologies:                    0
% 3.54/1.01  qbf_prep_cycles:                        0
% 3.54/1.01  
% 3.54/1.01  ------ BMC1
% 3.54/1.01  
% 3.54/1.01  bmc1_current_bound:                     -1
% 3.54/1.01  bmc1_last_solved_bound:                 -1
% 3.54/1.01  bmc1_unsat_core_size:                   -1
% 3.54/1.01  bmc1_unsat_core_parents_size:           -1
% 3.54/1.01  bmc1_merge_next_fun:                    0
% 3.54/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.54/1.01  
% 3.54/1.01  ------ Instantiation
% 3.54/1.01  
% 3.54/1.01  inst_num_of_clauses:                    1136
% 3.54/1.01  inst_num_in_passive:                    352
% 3.54/1.01  inst_num_in_active:                     322
% 3.54/1.01  inst_num_in_unprocessed:                462
% 3.54/1.01  inst_num_of_loops:                      450
% 3.54/1.01  inst_num_of_learning_restarts:          0
% 3.54/1.01  inst_num_moves_active_passive:          125
% 3.54/1.01  inst_lit_activity:                      0
% 3.54/1.01  inst_lit_activity_moves:                0
% 3.54/1.01  inst_num_tautologies:                   0
% 3.54/1.01  inst_num_prop_implied:                  0
% 3.54/1.01  inst_num_existing_simplified:           0
% 3.54/1.01  inst_num_eq_res_simplified:             0
% 3.54/1.01  inst_num_child_elim:                    0
% 3.54/1.01  inst_num_of_dismatching_blockings:      266
% 3.54/1.01  inst_num_of_non_proper_insts:           701
% 3.54/1.01  inst_num_of_duplicates:                 0
% 3.54/1.01  inst_inst_num_from_inst_to_res:         0
% 3.54/1.01  inst_dismatching_checking_time:         0.
% 3.54/1.01  
% 3.54/1.01  ------ Resolution
% 3.54/1.01  
% 3.54/1.01  res_num_of_clauses:                     0
% 3.54/1.01  res_num_in_passive:                     0
% 3.54/1.01  res_num_in_active:                      0
% 3.54/1.01  res_num_of_loops:                       140
% 3.54/1.01  res_forward_subset_subsumed:            64
% 3.54/1.01  res_backward_subset_subsumed:           0
% 3.54/1.01  res_forward_subsumed:                   0
% 3.54/1.01  res_backward_subsumed:                  0
% 3.54/1.01  res_forward_subsumption_resolution:     1
% 3.54/1.01  res_backward_subsumption_resolution:    0
% 3.54/1.01  res_clause_to_clause_subsumption:       680
% 3.54/1.01  res_orphan_elimination:                 0
% 3.54/1.01  res_tautology_del:                      23
% 3.54/1.01  res_num_eq_res_simplified:              0
% 3.54/1.01  res_num_sel_changes:                    0
% 3.54/1.01  res_moves_from_active_to_pass:          0
% 3.54/1.01  
% 3.54/1.01  ------ Superposition
% 3.54/1.01  
% 3.54/1.01  sup_time_total:                         0.
% 3.54/1.01  sup_time_generating:                    0.
% 3.54/1.01  sup_time_sim_full:                      0.
% 3.54/1.01  sup_time_sim_immed:                     0.
% 3.54/1.01  
% 3.54/1.01  sup_num_of_clauses:                     178
% 3.54/1.01  sup_num_in_active:                      88
% 3.54/1.01  sup_num_in_passive:                     90
% 3.54/1.01  sup_num_of_loops:                       88
% 3.54/1.01  sup_fw_superposition:                   72
% 3.54/1.01  sup_bw_superposition:                   137
% 3.54/1.01  sup_immediate_simplified:               37
% 3.54/1.01  sup_given_eliminated:                   0
% 3.54/1.01  comparisons_done:                       0
% 3.54/1.01  comparisons_avoided:                    0
% 3.54/1.01  
% 3.54/1.01  ------ Simplifications
% 3.54/1.01  
% 3.54/1.01  
% 3.54/1.01  sim_fw_subset_subsumed:                 30
% 3.54/1.01  sim_bw_subset_subsumed:                 6
% 3.54/1.01  sim_fw_subsumed:                        5
% 3.54/1.01  sim_bw_subsumed:                        0
% 3.54/1.01  sim_fw_subsumption_res:                 2
% 3.54/1.01  sim_bw_subsumption_res:                 0
% 3.54/1.01  sim_tautology_del:                      17
% 3.54/1.01  sim_eq_tautology_del:                   0
% 3.54/1.01  sim_eq_res_simp:                        2
% 3.54/1.01  sim_fw_demodulated:                     0
% 3.54/1.01  sim_bw_demodulated:                     0
% 3.54/1.01  sim_light_normalised:                   0
% 3.54/1.01  sim_joinable_taut:                      0
% 3.54/1.01  sim_joinable_simp:                      0
% 3.54/1.01  sim_ac_normalised:                      0
% 3.54/1.01  sim_smt_subsumption:                    0
% 3.54/1.01  
%------------------------------------------------------------------------------
