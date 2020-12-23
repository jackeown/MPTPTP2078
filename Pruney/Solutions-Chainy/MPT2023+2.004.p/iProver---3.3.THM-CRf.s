%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:28:46 EST 2020

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :  172 ( 965 expanded)
%              Number of clauses        :   88 ( 224 expanded)
%              Number of leaves         :   24 ( 332 expanded)
%              Depth                    :   19
%              Number of atoms          :  709 (5428 expanded)
%              Number of equality atoms :  126 ( 230 expanded)
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

fof(f42,plain,(
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
    inference(flattening,[],[f42])).

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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f43])).

fof(f45,plain,(
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

fof(f46,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f44,f45])).

fof(f61,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f91,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k1_setfam_1(k2_tarski(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f61,f72])).

fof(f98,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k1_setfam_1(k2_tarski(X0,X1)))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f91])).

fof(f15,conjecture,(
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

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f16])).

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
    inference(flattening,[],[f34])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))
          & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
     => ( ~ m1_subset_1(k3_xboole_0(X2,sK6),u1_struct_0(k9_yellow_6(X0,X1)))
        & m1_subset_1(sK6,u1_struct_0(k9_yellow_6(X0,X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
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

fof(f51,plain,(
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

fof(f50,plain,
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

fof(f54,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK5,sK6),u1_struct_0(k9_yellow_6(sK3,sK4)))
    & m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4)))
    & m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK3,sK4)))
    & m1_subset_1(sK4,u1_struct_0(sK3))
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f35,f53,f52,f51,f50])).

fof(f86,plain,(
    m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4))) ),
    inference(cnf_transformation,[],[f54])).

fof(f14,axiom,(
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

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X2,X0,X1)
              | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

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
    inference(flattening,[],[f32])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f81,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f54])).

fof(f82,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f54])).

fof(f83,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f54])).

fof(f84,plain,(
    m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f54])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f71,f72])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f13,axiom,(
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

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f13])).

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
    inference(flattening,[],[f30])).

fof(f48,plain,(
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
    inference(nnf_transformation,[],[f31])).

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
    inference(flattening,[],[f48])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ v3_pre_topc(X2,X0)
      | ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f73,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f87,plain,(
    ~ m1_subset_1(k3_xboole_0(sK5,sK6),u1_struct_0(k9_yellow_6(sK3,sK4))) ),
    inference(cnf_transformation,[],[f54])).

fof(f97,plain,(
    ~ m1_subset_1(k1_setfam_1(k2_tarski(sK5,sK6)),u1_struct_0(k9_yellow_6(sK3,sK4))) ),
    inference(definition_unfolding,[],[f87,f72])).

fof(f85,plain,(
    m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK3,sK4))) ),
    inference(cnf_transformation,[],[f54])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f17])).

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
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f18,f40])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f94,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_tarski(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f65,f72])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f36])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f38])).

fof(f55,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f47,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(X2,X0)
      | ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_pre_topc(X2,X0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k3_xboole_0(X1,X2),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v3_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v3_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(k1_setfam_1(k2_tarski(X1,X2)),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(definition_unfolding,[],[f75,f72])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k1_setfam_1(k2_tarski(X2,X1))) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1200,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X0,k1_setfam_1(k2_tarski(X1,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1189,plain,
    ( m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_24,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(X1,X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_20,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_382,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(resolution,[status(thm)],[c_24,c_20])).

cnf(c_31,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_412,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_382,c_31])).

cnf(c_413,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK3,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_412])).

cnf(c_30,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_29,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_417,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK3,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_413,c_30,c_29])).

cnf(c_1184,plain,
    ( m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK3,X1))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_417])).

cnf(c_1485,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1189,c_1184])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_35,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_1498,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1485,c_35])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1193,plain,
    ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2299,plain,
    ( k9_subset_1(u1_struct_0(sK3),X0,sK6) = k1_setfam_1(k2_tarski(X0,sK6)) ),
    inference(superposition,[status(thm)],[c_1498,c_1193])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1194,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2680,plain,
    ( m1_subset_1(k1_setfam_1(k2_tarski(X0,sK6)),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2299,c_1194])).

cnf(c_8556,plain,
    ( m1_subset_1(k1_setfam_1(k2_tarski(X0,sK6)),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2680,c_35,c_1485])).

cnf(c_21,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_481,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_31])).

cnf(c_482,plain,
    ( ~ v3_pre_topc(X0,sK3)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X1,X0)
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK3,X1)))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_481])).

cnf(c_486,plain,
    ( ~ v3_pre_topc(X0,sK3)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X1,X0)
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK3,X1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_482,c_30,c_29])).

cnf(c_18,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_502,plain,
    ( ~ v3_pre_topc(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X1,X0)
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK3,X1))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_486,c_18])).

cnf(c_1181,plain,
    ( v3_pre_topc(X0,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(X1,X0) != iProver_top
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK3,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_502])).

cnf(c_17,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1192,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1920,plain,
    ( v3_pre_topc(X0,sK3) != iProver_top
    | m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK3,X1))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1181,c_1192])).

cnf(c_25,negated_conjecture,
    ( ~ m1_subset_1(k1_setfam_1(k2_tarski(sK5,sK6)),u1_struct_0(k9_yellow_6(sK3,sK4))) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1190,plain,
    ( m1_subset_1(k1_setfam_1(k2_tarski(sK5,sK6)),u1_struct_0(k9_yellow_6(sK3,sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2222,plain,
    ( v3_pre_topc(k1_setfam_1(k2_tarski(sK5,sK6)),sK3) != iProver_top
    | m1_subset_1(k1_setfam_1(k2_tarski(sK5,sK6)),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(sK4,k1_setfam_1(k2_tarski(sK5,sK6))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1920,c_1190])).

cnf(c_8568,plain,
    ( v3_pre_topc(k1_setfam_1(k2_tarski(sK5,sK6)),sK3) != iProver_top
    | r2_hidden(sK4,k1_setfam_1(k2_tarski(sK5,sK6))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8556,c_2222])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK3,sK4))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1188,plain,
    ( m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_1486,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1188,c_1184])).

cnf(c_739,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1562,plain,
    ( u1_struct_0(k9_yellow_6(sK3,sK4)) = u1_struct_0(k9_yellow_6(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_739])).

cnf(c_744,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1470,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k1_setfam_1(k2_tarski(sK5,sK6)),u1_struct_0(k9_yellow_6(sK3,sK4)))
    | u1_struct_0(k9_yellow_6(sK3,sK4)) != X1
    | k1_setfam_1(k2_tarski(sK5,sK6)) != X0 ),
    inference(instantiation,[status(thm)],[c_744])).

cnf(c_1561,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK3,sK4)))
    | m1_subset_1(k1_setfam_1(k2_tarski(sK5,sK6)),u1_struct_0(k9_yellow_6(sK3,sK4)))
    | u1_struct_0(k9_yellow_6(sK3,sK4)) != u1_struct_0(k9_yellow_6(sK3,sK4))
    | k1_setfam_1(k2_tarski(sK5,sK6)) != X0 ),
    inference(instantiation,[status(thm)],[c_1470])).

cnf(c_1725,plain,
    ( m1_subset_1(k1_setfam_1(k2_tarski(sK5,sK6)),u1_struct_0(k9_yellow_6(sK3,sK4)))
    | ~ m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK3,sK4)))
    | u1_struct_0(k9_yellow_6(sK3,sK4)) != u1_struct_0(k9_yellow_6(sK3,sK4))
    | k1_setfam_1(k2_tarski(sK5,sK6)) != sK5 ),
    inference(instantiation,[status(thm)],[c_1561])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_354,plain,
    ( r2_hidden(sK1(X0,X1),X0)
    | k1_setfam_1(k2_tarski(X0,X1)) = X0 ),
    inference(resolution,[status(thm)],[c_3,c_10])).

cnf(c_1763,plain,
    ( r2_hidden(sK1(sK5,sK6),sK5)
    | k1_setfam_1(k2_tarski(sK5,sK6)) = sK5 ),
    inference(instantiation,[status(thm)],[c_354])).

cnf(c_1768,plain,
    ( k1_setfam_1(k2_tarski(sK5,sK6)) = sK5
    | r2_hidden(sK1(sK5,sK6),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1763])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2330,plain,
    ( ~ r2_hidden(sK1(sK5,sK6),sK5)
    | ~ v1_xboole_0(sK5) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2331,plain,
    ( r2_hidden(sK1(sK5,sK6),sK5) != iProver_top
    | v1_xboole_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2330])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1195,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2368,plain,
    ( r2_hidden(sK6,u1_struct_0(k9_yellow_6(sK3,sK4))) = iProver_top
    | v1_xboole_0(u1_struct_0(k9_yellow_6(sK3,sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1189,c_1195])).

cnf(c_22,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_457,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_31])).

cnf(c_458,plain,
    ( v3_pre_topc(X0,sK3)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(sK3,X1)))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_457])).

cnf(c_462,plain,
    ( v3_pre_topc(X0,sK3)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(sK3,X1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_458,c_30,c_29])).

cnf(c_1182,plain,
    ( v3_pre_topc(X0,sK3) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK3,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_462])).

cnf(c_2547,plain,
    ( v3_pre_topc(sK6,sK3) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v1_xboole_0(u1_struct_0(k9_yellow_6(sK3,sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2368,c_1182])).

cnf(c_2369,plain,
    ( r2_hidden(sK5,u1_struct_0(k9_yellow_6(sK3,sK4))) = iProver_top
    | v1_xboole_0(u1_struct_0(k9_yellow_6(sK3,sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1188,c_1195])).

cnf(c_2572,plain,
    ( v3_pre_topc(sK5,sK3) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v1_xboole_0(u1_struct_0(k9_yellow_6(sK3,sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2369,c_1182])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1196,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2983,plain,
    ( v1_xboole_0(u1_struct_0(k9_yellow_6(sK3,sK4))) != iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1188,c_1196])).

cnf(c_19,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ v3_pre_topc(X2,X1)
    | v3_pre_topc(k1_setfam_1(k2_tarski(X2,X0)),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_529,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ v3_pre_topc(X2,X1)
    | v3_pre_topc(k1_setfam_1(k2_tarski(X2,X0)),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_29])).

cnf(c_530,plain,
    ( ~ v3_pre_topc(X0,sK3)
    | ~ v3_pre_topc(X1,sK3)
    | v3_pre_topc(k1_setfam_1(k2_tarski(X1,X0)),sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_529])).

cnf(c_534,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v3_pre_topc(k1_setfam_1(k2_tarski(X1,X0)),sK3)
    | ~ v3_pre_topc(X1,sK3)
    | ~ v3_pre_topc(X0,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_530,c_30])).

cnf(c_535,plain,
    ( ~ v3_pre_topc(X0,sK3)
    | ~ v3_pre_topc(X1,sK3)
    | v3_pre_topc(k1_setfam_1(k2_tarski(X1,X0)),sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(renaming,[status(thm)],[c_534])).

cnf(c_3450,plain,
    ( ~ v3_pre_topc(X0,sK3)
    | v3_pre_topc(k1_setfam_1(k2_tarski(X0,sK6)),sK3)
    | ~ v3_pre_topc(sK6,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_535])).

cnf(c_6658,plain,
    ( v3_pre_topc(k1_setfam_1(k2_tarski(sK5,sK6)),sK3)
    | ~ v3_pre_topc(sK6,sK3)
    | ~ v3_pre_topc(sK5,sK3)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_3450])).

cnf(c_6659,plain,
    ( v3_pre_topc(k1_setfam_1(k2_tarski(sK5,sK6)),sK3) = iProver_top
    | v3_pre_topc(sK6,sK3) != iProver_top
    | v3_pre_topc(sK5,sK3) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6658])).

cnf(c_9231,plain,
    ( r2_hidden(sK4,k1_setfam_1(k2_tarski(sK5,sK6))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8568,c_35,c_27,c_25,c_1485,c_1486,c_1562,c_1725,c_1768,c_2331,c_2547,c_2572,c_2983,c_6659])).

cnf(c_9236,plain,
    ( r2_hidden(sK4,sK6) != iProver_top
    | r2_hidden(sK4,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1200,c_9231])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(X1,X0)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_433,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(X1,X0)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_31])).

cnf(c_434,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | r2_hidden(X0,X1)
    | ~ r2_hidden(X1,u1_struct_0(k9_yellow_6(sK3,X0)))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_433])).

cnf(c_438,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | r2_hidden(X0,X1)
    | ~ r2_hidden(X1,u1_struct_0(k9_yellow_6(sK3,X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_434,c_30,c_29])).

cnf(c_1183,plain,
    ( m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X1,u1_struct_0(k9_yellow_6(sK3,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_438])).

cnf(c_2571,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(sK4,sK5) = iProver_top
    | v1_xboole_0(u1_struct_0(k9_yellow_6(sK3,sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2369,c_1183])).

cnf(c_2546,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(sK4,sK6) = iProver_top
    | v1_xboole_0(u1_struct_0(k9_yellow_6(sK3,sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2368,c_1183])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9236,c_2983,c_2571,c_2546,c_2331,c_1768,c_1725,c_1562,c_1486,c_1485,c_25,c_27,c_35])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:22:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.13/1.05  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.05  
% 2.13/1.05  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.13/1.05  
% 2.13/1.05  ------  iProver source info
% 2.13/1.05  
% 2.13/1.05  git: date: 2020-06-30 10:37:57 +0100
% 2.13/1.05  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.13/1.05  git: non_committed_changes: false
% 2.13/1.05  git: last_make_outside_of_git: false
% 2.13/1.05  
% 2.13/1.05  ------ 
% 2.13/1.05  
% 2.13/1.05  ------ Input Options
% 2.13/1.05  
% 2.13/1.05  --out_options                           all
% 2.13/1.05  --tptp_safe_out                         true
% 2.13/1.05  --problem_path                          ""
% 2.13/1.05  --include_path                          ""
% 2.13/1.05  --clausifier                            res/vclausify_rel
% 2.13/1.05  --clausifier_options                    --mode clausify
% 2.13/1.05  --stdin                                 false
% 2.13/1.05  --stats_out                             all
% 2.13/1.05  
% 2.13/1.05  ------ General Options
% 2.13/1.05  
% 2.13/1.05  --fof                                   false
% 2.13/1.05  --time_out_real                         305.
% 2.13/1.05  --time_out_virtual                      -1.
% 2.13/1.05  --symbol_type_check                     false
% 2.13/1.05  --clausify_out                          false
% 2.13/1.05  --sig_cnt_out                           false
% 2.13/1.05  --trig_cnt_out                          false
% 2.13/1.05  --trig_cnt_out_tolerance                1.
% 2.13/1.05  --trig_cnt_out_sk_spl                   false
% 2.13/1.05  --abstr_cl_out                          false
% 2.13/1.05  
% 2.13/1.05  ------ Global Options
% 2.13/1.05  
% 2.13/1.05  --schedule                              default
% 2.13/1.05  --add_important_lit                     false
% 2.13/1.05  --prop_solver_per_cl                    1000
% 2.13/1.05  --min_unsat_core                        false
% 2.13/1.05  --soft_assumptions                      false
% 2.13/1.05  --soft_lemma_size                       3
% 2.13/1.05  --prop_impl_unit_size                   0
% 2.13/1.05  --prop_impl_unit                        []
% 2.13/1.05  --share_sel_clauses                     true
% 2.13/1.05  --reset_solvers                         false
% 2.13/1.05  --bc_imp_inh                            [conj_cone]
% 2.13/1.05  --conj_cone_tolerance                   3.
% 2.13/1.05  --extra_neg_conj                        none
% 2.13/1.05  --large_theory_mode                     true
% 2.13/1.05  --prolific_symb_bound                   200
% 2.13/1.05  --lt_threshold                          2000
% 2.13/1.05  --clause_weak_htbl                      true
% 2.13/1.05  --gc_record_bc_elim                     false
% 2.13/1.05  
% 2.13/1.05  ------ Preprocessing Options
% 2.13/1.05  
% 2.13/1.05  --preprocessing_flag                    true
% 2.13/1.05  --time_out_prep_mult                    0.1
% 2.13/1.05  --splitting_mode                        input
% 2.13/1.05  --splitting_grd                         true
% 2.13/1.05  --splitting_cvd                         false
% 2.13/1.05  --splitting_cvd_svl                     false
% 2.13/1.05  --splitting_nvd                         32
% 2.13/1.05  --sub_typing                            true
% 2.13/1.05  --prep_gs_sim                           true
% 2.13/1.05  --prep_unflatten                        true
% 2.13/1.05  --prep_res_sim                          true
% 2.13/1.05  --prep_upred                            true
% 2.13/1.05  --prep_sem_filter                       exhaustive
% 2.13/1.05  --prep_sem_filter_out                   false
% 2.13/1.05  --pred_elim                             true
% 2.13/1.05  --res_sim_input                         true
% 2.13/1.05  --eq_ax_congr_red                       true
% 2.13/1.05  --pure_diseq_elim                       true
% 2.13/1.05  --brand_transform                       false
% 2.13/1.05  --non_eq_to_eq                          false
% 2.13/1.05  --prep_def_merge                        true
% 2.13/1.05  --prep_def_merge_prop_impl              false
% 2.13/1.05  --prep_def_merge_mbd                    true
% 2.13/1.05  --prep_def_merge_tr_red                 false
% 2.13/1.05  --prep_def_merge_tr_cl                  false
% 2.13/1.05  --smt_preprocessing                     true
% 2.13/1.05  --smt_ac_axioms                         fast
% 2.13/1.05  --preprocessed_out                      false
% 2.13/1.05  --preprocessed_stats                    false
% 2.13/1.05  
% 2.13/1.05  ------ Abstraction refinement Options
% 2.13/1.05  
% 2.13/1.05  --abstr_ref                             []
% 2.13/1.05  --abstr_ref_prep                        false
% 2.13/1.05  --abstr_ref_until_sat                   false
% 2.13/1.05  --abstr_ref_sig_restrict                funpre
% 2.13/1.05  --abstr_ref_af_restrict_to_split_sk     false
% 2.13/1.05  --abstr_ref_under                       []
% 2.13/1.05  
% 2.13/1.05  ------ SAT Options
% 2.13/1.05  
% 2.13/1.05  --sat_mode                              false
% 2.13/1.05  --sat_fm_restart_options                ""
% 2.13/1.05  --sat_gr_def                            false
% 2.13/1.05  --sat_epr_types                         true
% 2.13/1.05  --sat_non_cyclic_types                  false
% 2.13/1.05  --sat_finite_models                     false
% 2.13/1.05  --sat_fm_lemmas                         false
% 2.13/1.05  --sat_fm_prep                           false
% 2.13/1.05  --sat_fm_uc_incr                        true
% 2.13/1.05  --sat_out_model                         small
% 2.13/1.05  --sat_out_clauses                       false
% 2.13/1.05  
% 2.13/1.05  ------ QBF Options
% 2.13/1.05  
% 2.13/1.05  --qbf_mode                              false
% 2.13/1.05  --qbf_elim_univ                         false
% 2.13/1.05  --qbf_dom_inst                          none
% 2.13/1.05  --qbf_dom_pre_inst                      false
% 2.13/1.05  --qbf_sk_in                             false
% 2.13/1.05  --qbf_pred_elim                         true
% 2.13/1.05  --qbf_split                             512
% 2.13/1.05  
% 2.13/1.05  ------ BMC1 Options
% 2.13/1.05  
% 2.13/1.05  --bmc1_incremental                      false
% 2.13/1.05  --bmc1_axioms                           reachable_all
% 2.13/1.05  --bmc1_min_bound                        0
% 2.13/1.05  --bmc1_max_bound                        -1
% 2.13/1.05  --bmc1_max_bound_default                -1
% 2.13/1.05  --bmc1_symbol_reachability              true
% 2.13/1.05  --bmc1_property_lemmas                  false
% 2.13/1.05  --bmc1_k_induction                      false
% 2.13/1.05  --bmc1_non_equiv_states                 false
% 2.13/1.05  --bmc1_deadlock                         false
% 2.13/1.05  --bmc1_ucm                              false
% 2.13/1.05  --bmc1_add_unsat_core                   none
% 2.13/1.05  --bmc1_unsat_core_children              false
% 2.13/1.05  --bmc1_unsat_core_extrapolate_axioms    false
% 2.13/1.05  --bmc1_out_stat                         full
% 2.13/1.05  --bmc1_ground_init                      false
% 2.13/1.05  --bmc1_pre_inst_next_state              false
% 2.13/1.05  --bmc1_pre_inst_state                   false
% 2.13/1.05  --bmc1_pre_inst_reach_state             false
% 2.13/1.05  --bmc1_out_unsat_core                   false
% 2.13/1.05  --bmc1_aig_witness_out                  false
% 2.13/1.05  --bmc1_verbose                          false
% 2.13/1.05  --bmc1_dump_clauses_tptp                false
% 2.13/1.05  --bmc1_dump_unsat_core_tptp             false
% 2.13/1.05  --bmc1_dump_file                        -
% 2.13/1.05  --bmc1_ucm_expand_uc_limit              128
% 2.13/1.05  --bmc1_ucm_n_expand_iterations          6
% 2.13/1.05  --bmc1_ucm_extend_mode                  1
% 2.13/1.05  --bmc1_ucm_init_mode                    2
% 2.13/1.05  --bmc1_ucm_cone_mode                    none
% 2.13/1.05  --bmc1_ucm_reduced_relation_type        0
% 2.13/1.05  --bmc1_ucm_relax_model                  4
% 2.13/1.05  --bmc1_ucm_full_tr_after_sat            true
% 2.13/1.05  --bmc1_ucm_expand_neg_assumptions       false
% 2.13/1.05  --bmc1_ucm_layered_model                none
% 2.13/1.05  --bmc1_ucm_max_lemma_size               10
% 2.13/1.05  
% 2.13/1.05  ------ AIG Options
% 2.13/1.05  
% 2.13/1.05  --aig_mode                              false
% 2.13/1.05  
% 2.13/1.05  ------ Instantiation Options
% 2.13/1.05  
% 2.13/1.05  --instantiation_flag                    true
% 2.13/1.05  --inst_sos_flag                         false
% 2.13/1.05  --inst_sos_phase                        true
% 2.13/1.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.13/1.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.13/1.05  --inst_lit_sel_side                     num_symb
% 2.13/1.05  --inst_solver_per_active                1400
% 2.13/1.05  --inst_solver_calls_frac                1.
% 2.13/1.05  --inst_passive_queue_type               priority_queues
% 2.13/1.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.13/1.05  --inst_passive_queues_freq              [25;2]
% 2.13/1.05  --inst_dismatching                      true
% 2.13/1.05  --inst_eager_unprocessed_to_passive     true
% 2.13/1.05  --inst_prop_sim_given                   true
% 2.13/1.05  --inst_prop_sim_new                     false
% 2.13/1.05  --inst_subs_new                         false
% 2.13/1.05  --inst_eq_res_simp                      false
% 2.13/1.05  --inst_subs_given                       false
% 2.13/1.05  --inst_orphan_elimination               true
% 2.13/1.05  --inst_learning_loop_flag               true
% 2.13/1.05  --inst_learning_start                   3000
% 2.13/1.05  --inst_learning_factor                  2
% 2.13/1.05  --inst_start_prop_sim_after_learn       3
% 2.13/1.05  --inst_sel_renew                        solver
% 2.13/1.05  --inst_lit_activity_flag                true
% 2.13/1.05  --inst_restr_to_given                   false
% 2.13/1.05  --inst_activity_threshold               500
% 2.13/1.05  --inst_out_proof                        true
% 2.13/1.05  
% 2.13/1.05  ------ Resolution Options
% 2.13/1.05  
% 2.13/1.05  --resolution_flag                       true
% 2.13/1.05  --res_lit_sel                           adaptive
% 2.13/1.05  --res_lit_sel_side                      none
% 2.13/1.05  --res_ordering                          kbo
% 2.13/1.05  --res_to_prop_solver                    active
% 2.13/1.05  --res_prop_simpl_new                    false
% 2.13/1.05  --res_prop_simpl_given                  true
% 2.13/1.05  --res_passive_queue_type                priority_queues
% 2.13/1.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.13/1.05  --res_passive_queues_freq               [15;5]
% 2.13/1.05  --res_forward_subs                      full
% 2.13/1.05  --res_backward_subs                     full
% 2.13/1.05  --res_forward_subs_resolution           true
% 2.13/1.05  --res_backward_subs_resolution          true
% 2.13/1.05  --res_orphan_elimination                true
% 2.13/1.05  --res_time_limit                        2.
% 2.13/1.05  --res_out_proof                         true
% 2.13/1.05  
% 2.13/1.05  ------ Superposition Options
% 2.13/1.05  
% 2.13/1.05  --superposition_flag                    true
% 2.13/1.05  --sup_passive_queue_type                priority_queues
% 2.13/1.05  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.13/1.05  --sup_passive_queues_freq               [8;1;4]
% 2.13/1.05  --demod_completeness_check              fast
% 2.13/1.05  --demod_use_ground                      true
% 2.13/1.05  --sup_to_prop_solver                    passive
% 2.13/1.05  --sup_prop_simpl_new                    true
% 2.13/1.05  --sup_prop_simpl_given                  true
% 2.13/1.05  --sup_fun_splitting                     false
% 2.13/1.05  --sup_smt_interval                      50000
% 2.13/1.05  
% 2.13/1.05  ------ Superposition Simplification Setup
% 2.13/1.05  
% 2.13/1.05  --sup_indices_passive                   []
% 2.13/1.05  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.13/1.05  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.13/1.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.13/1.05  --sup_full_triv                         [TrivRules;PropSubs]
% 2.13/1.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.13/1.05  --sup_full_bw                           [BwDemod]
% 2.13/1.05  --sup_immed_triv                        [TrivRules]
% 2.13/1.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.13/1.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.13/1.05  --sup_immed_bw_main                     []
% 2.13/1.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.13/1.05  --sup_input_triv                        [Unflattening;TrivRules]
% 2.13/1.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.13/1.05  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.13/1.05  
% 2.13/1.05  ------ Combination Options
% 2.13/1.05  
% 2.13/1.05  --comb_res_mult                         3
% 2.13/1.05  --comb_sup_mult                         2
% 2.13/1.05  --comb_inst_mult                        10
% 2.13/1.05  
% 2.13/1.05  ------ Debug Options
% 2.13/1.05  
% 2.13/1.05  --dbg_backtrace                         false
% 2.13/1.05  --dbg_dump_prop_clauses                 false
% 2.13/1.05  --dbg_dump_prop_clauses_file            -
% 2.13/1.05  --dbg_out_stat                          false
% 2.13/1.05  ------ Parsing...
% 2.13/1.05  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.13/1.05  
% 2.13/1.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.13/1.05  
% 2.13/1.05  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.13/1.05  
% 2.13/1.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.13/1.05  ------ Proving...
% 2.13/1.05  ------ Problem Properties 
% 2.13/1.05  
% 2.13/1.05  
% 2.13/1.05  clauses                                 26
% 2.13/1.05  conjectures                             4
% 2.13/1.05  EPR                                     5
% 2.13/1.05  Horn                                    21
% 2.13/1.05  unary                                   4
% 2.13/1.05  binary                                  9
% 2.13/1.05  lits                                    67
% 2.13/1.05  lits eq                                 6
% 2.13/1.05  fd_pure                                 0
% 2.13/1.05  fd_pseudo                               0
% 2.13/1.05  fd_cond                                 0
% 2.13/1.05  fd_pseudo_cond                          3
% 2.13/1.05  AC symbols                              0
% 2.13/1.05  
% 2.13/1.05  ------ Schedule dynamic 5 is on 
% 2.13/1.05  
% 2.13/1.05  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.13/1.05  
% 2.13/1.05  
% 2.13/1.05  ------ 
% 2.13/1.05  Current options:
% 2.13/1.05  ------ 
% 2.13/1.05  
% 2.13/1.05  ------ Input Options
% 2.13/1.05  
% 2.13/1.05  --out_options                           all
% 2.13/1.05  --tptp_safe_out                         true
% 2.13/1.05  --problem_path                          ""
% 2.13/1.05  --include_path                          ""
% 2.13/1.05  --clausifier                            res/vclausify_rel
% 2.13/1.05  --clausifier_options                    --mode clausify
% 2.13/1.05  --stdin                                 false
% 2.13/1.05  --stats_out                             all
% 2.13/1.05  
% 2.13/1.05  ------ General Options
% 2.13/1.05  
% 2.13/1.05  --fof                                   false
% 2.13/1.05  --time_out_real                         305.
% 2.13/1.05  --time_out_virtual                      -1.
% 2.13/1.05  --symbol_type_check                     false
% 2.13/1.05  --clausify_out                          false
% 2.13/1.05  --sig_cnt_out                           false
% 2.13/1.05  --trig_cnt_out                          false
% 2.13/1.05  --trig_cnt_out_tolerance                1.
% 2.13/1.05  --trig_cnt_out_sk_spl                   false
% 2.13/1.05  --abstr_cl_out                          false
% 2.13/1.05  
% 2.13/1.05  ------ Global Options
% 2.13/1.05  
% 2.13/1.05  --schedule                              default
% 2.13/1.05  --add_important_lit                     false
% 2.13/1.05  --prop_solver_per_cl                    1000
% 2.13/1.05  --min_unsat_core                        false
% 2.13/1.05  --soft_assumptions                      false
% 2.13/1.05  --soft_lemma_size                       3
% 2.13/1.05  --prop_impl_unit_size                   0
% 2.13/1.05  --prop_impl_unit                        []
% 2.13/1.05  --share_sel_clauses                     true
% 2.13/1.05  --reset_solvers                         false
% 2.13/1.05  --bc_imp_inh                            [conj_cone]
% 2.13/1.05  --conj_cone_tolerance                   3.
% 2.13/1.05  --extra_neg_conj                        none
% 2.13/1.05  --large_theory_mode                     true
% 2.13/1.05  --prolific_symb_bound                   200
% 2.13/1.05  --lt_threshold                          2000
% 2.13/1.05  --clause_weak_htbl                      true
% 2.13/1.05  --gc_record_bc_elim                     false
% 2.13/1.05  
% 2.13/1.05  ------ Preprocessing Options
% 2.13/1.05  
% 2.13/1.05  --preprocessing_flag                    true
% 2.13/1.05  --time_out_prep_mult                    0.1
% 2.13/1.05  --splitting_mode                        input
% 2.13/1.05  --splitting_grd                         true
% 2.13/1.05  --splitting_cvd                         false
% 2.13/1.05  --splitting_cvd_svl                     false
% 2.13/1.05  --splitting_nvd                         32
% 2.13/1.05  --sub_typing                            true
% 2.13/1.05  --prep_gs_sim                           true
% 2.13/1.05  --prep_unflatten                        true
% 2.13/1.05  --prep_res_sim                          true
% 2.13/1.05  --prep_upred                            true
% 2.13/1.05  --prep_sem_filter                       exhaustive
% 2.13/1.05  --prep_sem_filter_out                   false
% 2.13/1.05  --pred_elim                             true
% 2.13/1.05  --res_sim_input                         true
% 2.13/1.05  --eq_ax_congr_red                       true
% 2.13/1.05  --pure_diseq_elim                       true
% 2.13/1.05  --brand_transform                       false
% 2.13/1.05  --non_eq_to_eq                          false
% 2.13/1.05  --prep_def_merge                        true
% 2.13/1.05  --prep_def_merge_prop_impl              false
% 2.13/1.05  --prep_def_merge_mbd                    true
% 2.13/1.05  --prep_def_merge_tr_red                 false
% 2.13/1.05  --prep_def_merge_tr_cl                  false
% 2.13/1.05  --smt_preprocessing                     true
% 2.13/1.05  --smt_ac_axioms                         fast
% 2.13/1.05  --preprocessed_out                      false
% 2.13/1.05  --preprocessed_stats                    false
% 2.13/1.05  
% 2.13/1.05  ------ Abstraction refinement Options
% 2.13/1.05  
% 2.13/1.05  --abstr_ref                             []
% 2.13/1.05  --abstr_ref_prep                        false
% 2.13/1.05  --abstr_ref_until_sat                   false
% 2.13/1.05  --abstr_ref_sig_restrict                funpre
% 2.13/1.05  --abstr_ref_af_restrict_to_split_sk     false
% 2.13/1.05  --abstr_ref_under                       []
% 2.13/1.05  
% 2.13/1.05  ------ SAT Options
% 2.13/1.05  
% 2.13/1.05  --sat_mode                              false
% 2.13/1.05  --sat_fm_restart_options                ""
% 2.13/1.05  --sat_gr_def                            false
% 2.13/1.05  --sat_epr_types                         true
% 2.13/1.05  --sat_non_cyclic_types                  false
% 2.13/1.05  --sat_finite_models                     false
% 2.13/1.05  --sat_fm_lemmas                         false
% 2.13/1.05  --sat_fm_prep                           false
% 2.13/1.05  --sat_fm_uc_incr                        true
% 2.13/1.05  --sat_out_model                         small
% 2.13/1.05  --sat_out_clauses                       false
% 2.13/1.05  
% 2.13/1.05  ------ QBF Options
% 2.13/1.05  
% 2.13/1.05  --qbf_mode                              false
% 2.13/1.05  --qbf_elim_univ                         false
% 2.13/1.05  --qbf_dom_inst                          none
% 2.13/1.05  --qbf_dom_pre_inst                      false
% 2.13/1.05  --qbf_sk_in                             false
% 2.13/1.05  --qbf_pred_elim                         true
% 2.13/1.05  --qbf_split                             512
% 2.13/1.05  
% 2.13/1.05  ------ BMC1 Options
% 2.13/1.05  
% 2.13/1.05  --bmc1_incremental                      false
% 2.13/1.05  --bmc1_axioms                           reachable_all
% 2.13/1.05  --bmc1_min_bound                        0
% 2.13/1.05  --bmc1_max_bound                        -1
% 2.13/1.05  --bmc1_max_bound_default                -1
% 2.13/1.05  --bmc1_symbol_reachability              true
% 2.13/1.05  --bmc1_property_lemmas                  false
% 2.13/1.05  --bmc1_k_induction                      false
% 2.13/1.05  --bmc1_non_equiv_states                 false
% 2.13/1.05  --bmc1_deadlock                         false
% 2.13/1.05  --bmc1_ucm                              false
% 2.13/1.05  --bmc1_add_unsat_core                   none
% 2.13/1.05  --bmc1_unsat_core_children              false
% 2.13/1.05  --bmc1_unsat_core_extrapolate_axioms    false
% 2.13/1.05  --bmc1_out_stat                         full
% 2.13/1.05  --bmc1_ground_init                      false
% 2.13/1.05  --bmc1_pre_inst_next_state              false
% 2.13/1.05  --bmc1_pre_inst_state                   false
% 2.13/1.05  --bmc1_pre_inst_reach_state             false
% 2.13/1.05  --bmc1_out_unsat_core                   false
% 2.13/1.05  --bmc1_aig_witness_out                  false
% 2.13/1.05  --bmc1_verbose                          false
% 2.13/1.05  --bmc1_dump_clauses_tptp                false
% 2.13/1.05  --bmc1_dump_unsat_core_tptp             false
% 2.13/1.05  --bmc1_dump_file                        -
% 2.13/1.05  --bmc1_ucm_expand_uc_limit              128
% 2.13/1.05  --bmc1_ucm_n_expand_iterations          6
% 2.13/1.05  --bmc1_ucm_extend_mode                  1
% 2.13/1.05  --bmc1_ucm_init_mode                    2
% 2.13/1.05  --bmc1_ucm_cone_mode                    none
% 2.13/1.05  --bmc1_ucm_reduced_relation_type        0
% 2.13/1.05  --bmc1_ucm_relax_model                  4
% 2.13/1.05  --bmc1_ucm_full_tr_after_sat            true
% 2.13/1.05  --bmc1_ucm_expand_neg_assumptions       false
% 2.13/1.05  --bmc1_ucm_layered_model                none
% 2.13/1.05  --bmc1_ucm_max_lemma_size               10
% 2.13/1.05  
% 2.13/1.05  ------ AIG Options
% 2.13/1.05  
% 2.13/1.05  --aig_mode                              false
% 2.13/1.05  
% 2.13/1.05  ------ Instantiation Options
% 2.13/1.05  
% 2.13/1.05  --instantiation_flag                    true
% 2.13/1.05  --inst_sos_flag                         false
% 2.13/1.05  --inst_sos_phase                        true
% 2.13/1.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.13/1.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.13/1.05  --inst_lit_sel_side                     none
% 2.13/1.05  --inst_solver_per_active                1400
% 2.13/1.05  --inst_solver_calls_frac                1.
% 2.13/1.05  --inst_passive_queue_type               priority_queues
% 2.13/1.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.13/1.05  --inst_passive_queues_freq              [25;2]
% 2.13/1.05  --inst_dismatching                      true
% 2.13/1.05  --inst_eager_unprocessed_to_passive     true
% 2.13/1.05  --inst_prop_sim_given                   true
% 2.13/1.05  --inst_prop_sim_new                     false
% 2.13/1.05  --inst_subs_new                         false
% 2.13/1.05  --inst_eq_res_simp                      false
% 2.13/1.05  --inst_subs_given                       false
% 2.13/1.05  --inst_orphan_elimination               true
% 2.13/1.05  --inst_learning_loop_flag               true
% 2.13/1.05  --inst_learning_start                   3000
% 2.13/1.05  --inst_learning_factor                  2
% 2.13/1.05  --inst_start_prop_sim_after_learn       3
% 2.13/1.05  --inst_sel_renew                        solver
% 2.13/1.05  --inst_lit_activity_flag                true
% 2.13/1.05  --inst_restr_to_given                   false
% 2.13/1.05  --inst_activity_threshold               500
% 2.13/1.05  --inst_out_proof                        true
% 2.13/1.05  
% 2.13/1.05  ------ Resolution Options
% 2.13/1.05  
% 2.13/1.05  --resolution_flag                       false
% 2.13/1.05  --res_lit_sel                           adaptive
% 2.13/1.05  --res_lit_sel_side                      none
% 2.13/1.05  --res_ordering                          kbo
% 2.13/1.05  --res_to_prop_solver                    active
% 2.13/1.05  --res_prop_simpl_new                    false
% 2.13/1.05  --res_prop_simpl_given                  true
% 2.13/1.05  --res_passive_queue_type                priority_queues
% 2.13/1.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.13/1.05  --res_passive_queues_freq               [15;5]
% 2.13/1.05  --res_forward_subs                      full
% 2.13/1.05  --res_backward_subs                     full
% 2.13/1.05  --res_forward_subs_resolution           true
% 2.13/1.05  --res_backward_subs_resolution          true
% 2.13/1.05  --res_orphan_elimination                true
% 2.13/1.05  --res_time_limit                        2.
% 2.13/1.05  --res_out_proof                         true
% 2.13/1.05  
% 2.13/1.05  ------ Superposition Options
% 2.13/1.05  
% 2.13/1.05  --superposition_flag                    true
% 2.13/1.05  --sup_passive_queue_type                priority_queues
% 2.13/1.05  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.13/1.05  --sup_passive_queues_freq               [8;1;4]
% 2.13/1.05  --demod_completeness_check              fast
% 2.13/1.05  --demod_use_ground                      true
% 2.13/1.05  --sup_to_prop_solver                    passive
% 2.13/1.05  --sup_prop_simpl_new                    true
% 2.13/1.05  --sup_prop_simpl_given                  true
% 2.13/1.05  --sup_fun_splitting                     false
% 2.13/1.05  --sup_smt_interval                      50000
% 2.13/1.05  
% 2.13/1.05  ------ Superposition Simplification Setup
% 2.13/1.05  
% 2.13/1.05  --sup_indices_passive                   []
% 2.13/1.05  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.13/1.05  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.13/1.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.13/1.05  --sup_full_triv                         [TrivRules;PropSubs]
% 2.13/1.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.13/1.05  --sup_full_bw                           [BwDemod]
% 2.13/1.05  --sup_immed_triv                        [TrivRules]
% 2.13/1.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.13/1.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.13/1.05  --sup_immed_bw_main                     []
% 2.13/1.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.13/1.05  --sup_input_triv                        [Unflattening;TrivRules]
% 2.13/1.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.13/1.05  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.13/1.05  
% 2.13/1.05  ------ Combination Options
% 2.13/1.05  
% 2.13/1.05  --comb_res_mult                         3
% 2.13/1.05  --comb_sup_mult                         2
% 2.13/1.05  --comb_inst_mult                        10
% 2.13/1.05  
% 2.13/1.05  ------ Debug Options
% 2.13/1.05  
% 2.13/1.05  --dbg_backtrace                         false
% 2.13/1.05  --dbg_dump_prop_clauses                 false
% 2.13/1.05  --dbg_dump_prop_clauses_file            -
% 2.13/1.05  --dbg_out_stat                          false
% 2.13/1.05  
% 2.13/1.05  
% 2.13/1.05  
% 2.13/1.05  
% 2.13/1.05  ------ Proving...
% 2.13/1.05  
% 2.13/1.05  
% 2.13/1.05  % SZS status Theorem for theBenchmark.p
% 2.13/1.05  
% 2.13/1.05  % SZS output start CNFRefutation for theBenchmark.p
% 2.13/1.05  
% 2.13/1.05  fof(f3,axiom,(
% 2.13/1.05    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.13/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.13/1.05  
% 2.13/1.05  fof(f42,plain,(
% 2.13/1.05    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.13/1.05    inference(nnf_transformation,[],[f3])).
% 2.13/1.05  
% 2.13/1.05  fof(f43,plain,(
% 2.13/1.05    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.13/1.05    inference(flattening,[],[f42])).
% 2.13/1.05  
% 2.13/1.05  fof(f44,plain,(
% 2.13/1.05    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.13/1.05    inference(rectify,[],[f43])).
% 2.13/1.05  
% 2.13/1.05  fof(f45,plain,(
% 2.13/1.05    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 2.13/1.05    introduced(choice_axiom,[])).
% 2.13/1.05  
% 2.13/1.05  fof(f46,plain,(
% 2.13/1.05    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.13/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f44,f45])).
% 2.13/1.05  
% 2.13/1.05  fof(f61,plain,(
% 2.13/1.05    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k3_xboole_0(X0,X1) != X2) )),
% 2.13/1.05    inference(cnf_transformation,[],[f46])).
% 2.13/1.05  
% 2.13/1.05  fof(f8,axiom,(
% 2.13/1.05    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.13/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.13/1.05  
% 2.13/1.05  fof(f72,plain,(
% 2.13/1.05    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.13/1.05    inference(cnf_transformation,[],[f8])).
% 2.13/1.05  
% 2.13/1.05  fof(f91,plain,(
% 2.13/1.05    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k1_setfam_1(k2_tarski(X0,X1)) != X2) )),
% 2.13/1.05    inference(definition_unfolding,[],[f61,f72])).
% 2.13/1.05  
% 2.13/1.05  fof(f98,plain,(
% 2.13/1.05    ( ! [X4,X0,X1] : (r2_hidden(X4,k1_setfam_1(k2_tarski(X0,X1))) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 2.13/1.05    inference(equality_resolution,[],[f91])).
% 2.13/1.05  
% 2.13/1.05  fof(f15,conjecture,(
% 2.13/1.05    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) => m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))))))),
% 2.13/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.13/1.05  
% 2.13/1.05  fof(f16,negated_conjecture,(
% 2.13/1.05    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) => m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))))))),
% 2.13/1.05    inference(negated_conjecture,[],[f15])).
% 2.13/1.05  
% 2.13/1.05  fof(f34,plain,(
% 2.13/1.05    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.13/1.05    inference(ennf_transformation,[],[f16])).
% 2.13/1.05  
% 2.13/1.05  fof(f35,plain,(
% 2.13/1.05    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.13/1.05    inference(flattening,[],[f34])).
% 2.13/1.05  
% 2.13/1.05  fof(f53,plain,(
% 2.13/1.05    ( ! [X2,X0,X1] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) => (~m1_subset_1(k3_xboole_0(X2,sK6),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(sK6,u1_struct_0(k9_yellow_6(X0,X1))))) )),
% 2.13/1.05    introduced(choice_axiom,[])).
% 2.13/1.05  
% 2.13/1.05  fof(f52,plain,(
% 2.13/1.05    ( ! [X0,X1] : (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) => (? [X3] : (~m1_subset_1(k3_xboole_0(sK5,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(sK5,u1_struct_0(k9_yellow_6(X0,X1))))) )),
% 2.13/1.05    introduced(choice_axiom,[])).
% 2.13/1.05  
% 2.13/1.05  fof(f51,plain,(
% 2.13/1.05    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,sK4))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,sK4)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,sK4)))) & m1_subset_1(sK4,u1_struct_0(X0)))) )),
% 2.13/1.05    introduced(choice_axiom,[])).
% 2.13/1.05  
% 2.13/1.05  fof(f50,plain,(
% 2.13/1.05    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK3,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK3,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK3,X1)))) & m1_subset_1(X1,u1_struct_0(sK3))) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 2.13/1.05    introduced(choice_axiom,[])).
% 2.13/1.05  
% 2.13/1.05  fof(f54,plain,(
% 2.13/1.05    (((~m1_subset_1(k3_xboole_0(sK5,sK6),u1_struct_0(k9_yellow_6(sK3,sK4))) & m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4)))) & m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK3,sK4)))) & m1_subset_1(sK4,u1_struct_0(sK3))) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 2.13/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f35,f53,f52,f51,f50])).
% 2.13/1.05  
% 2.13/1.05  fof(f86,plain,(
% 2.13/1.05    m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4)))),
% 2.13/1.05    inference(cnf_transformation,[],[f54])).
% 2.13/1.05  
% 2.13/1.05  fof(f14,axiom,(
% 2.13/1.05    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => m1_connsp_2(X2,X0,X1))))),
% 2.13/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.13/1.05  
% 2.13/1.05  fof(f32,plain,(
% 2.13/1.05    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.13/1.05    inference(ennf_transformation,[],[f14])).
% 2.13/1.05  
% 2.13/1.05  fof(f33,plain,(
% 2.13/1.05    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.13/1.05    inference(flattening,[],[f32])).
% 2.13/1.05  
% 2.13/1.05  fof(f80,plain,(
% 2.13/1.05    ( ! [X2,X0,X1] : (m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.13/1.05    inference(cnf_transformation,[],[f33])).
% 2.13/1.05  
% 2.13/1.05  fof(f12,axiom,(
% 2.13/1.05    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.13/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.13/1.05  
% 2.13/1.05  fof(f28,plain,(
% 2.13/1.05    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.13/1.05    inference(ennf_transformation,[],[f12])).
% 2.13/1.05  
% 2.13/1.05  fof(f29,plain,(
% 2.13/1.05    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.13/1.05    inference(flattening,[],[f28])).
% 2.13/1.05  
% 2.13/1.05  fof(f76,plain,(
% 2.13/1.05    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.13/1.05    inference(cnf_transformation,[],[f29])).
% 2.13/1.05  
% 2.13/1.05  fof(f81,plain,(
% 2.13/1.05    ~v2_struct_0(sK3)),
% 2.13/1.05    inference(cnf_transformation,[],[f54])).
% 2.13/1.05  
% 2.13/1.05  fof(f82,plain,(
% 2.13/1.05    v2_pre_topc(sK3)),
% 2.13/1.05    inference(cnf_transformation,[],[f54])).
% 2.13/1.05  
% 2.13/1.05  fof(f83,plain,(
% 2.13/1.05    l1_pre_topc(sK3)),
% 2.13/1.05    inference(cnf_transformation,[],[f54])).
% 2.13/1.05  
% 2.13/1.05  fof(f84,plain,(
% 2.13/1.05    m1_subset_1(sK4,u1_struct_0(sK3))),
% 2.13/1.05    inference(cnf_transformation,[],[f54])).
% 2.13/1.05  
% 2.13/1.05  fof(f7,axiom,(
% 2.13/1.05    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 2.13/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.13/1.05  
% 2.13/1.05  fof(f22,plain,(
% 2.13/1.05    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 2.13/1.05    inference(ennf_transformation,[],[f7])).
% 2.13/1.05  
% 2.13/1.05  fof(f71,plain,(
% 2.13/1.05    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 2.13/1.05    inference(cnf_transformation,[],[f22])).
% 2.13/1.05  
% 2.13/1.05  fof(f95,plain,(
% 2.13/1.05    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 2.13/1.05    inference(definition_unfolding,[],[f71,f72])).
% 2.13/1.05  
% 2.13/1.05  fof(f6,axiom,(
% 2.13/1.05    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 2.13/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.13/1.05  
% 2.13/1.05  fof(f21,plain,(
% 2.13/1.05    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 2.13/1.05    inference(ennf_transformation,[],[f6])).
% 2.13/1.05  
% 2.13/1.05  fof(f70,plain,(
% 2.13/1.05    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 2.13/1.05    inference(cnf_transformation,[],[f21])).
% 2.13/1.05  
% 2.13/1.05  fof(f13,axiom,(
% 2.13/1.05    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))))))),
% 2.13/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.13/1.05  
% 2.13/1.05  fof(f30,plain,(
% 2.13/1.05    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.13/1.05    inference(ennf_transformation,[],[f13])).
% 2.13/1.05  
% 2.13/1.05  fof(f31,plain,(
% 2.13/1.05    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.13/1.05    inference(flattening,[],[f30])).
% 2.13/1.05  
% 2.13/1.05  fof(f48,plain,(
% 2.13/1.05    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | (~v3_pre_topc(X2,X0) | ~r2_hidden(X1,X2))) & ((v3_pre_topc(X2,X0) & r2_hidden(X1,X2)) | ~r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.13/1.05    inference(nnf_transformation,[],[f31])).
% 2.13/1.05  
% 2.13/1.05  fof(f49,plain,(
% 2.13/1.05    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~v3_pre_topc(X2,X0) | ~r2_hidden(X1,X2)) & ((v3_pre_topc(X2,X0) & r2_hidden(X1,X2)) | ~r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.13/1.05    inference(flattening,[],[f48])).
% 2.13/1.05  
% 2.13/1.05  fof(f79,plain,(
% 2.13/1.05    ( ! [X2,X0,X1] : (r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~v3_pre_topc(X2,X0) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.13/1.05    inference(cnf_transformation,[],[f49])).
% 2.13/1.05  
% 2.13/1.05  fof(f10,axiom,(
% 2.13/1.05    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 2.13/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.13/1.05  
% 2.13/1.05  fof(f24,plain,(
% 2.13/1.05    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 2.13/1.05    inference(ennf_transformation,[],[f10])).
% 2.13/1.05  
% 2.13/1.05  fof(f25,plain,(
% 2.13/1.05    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.13/1.05    inference(flattening,[],[f24])).
% 2.13/1.05  
% 2.13/1.05  fof(f74,plain,(
% 2.13/1.05    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.13/1.05    inference(cnf_transformation,[],[f25])).
% 2.13/1.05  
% 2.13/1.05  fof(f9,axiom,(
% 2.13/1.05    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 2.13/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.13/1.05  
% 2.13/1.05  fof(f23,plain,(
% 2.13/1.05    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 2.13/1.05    inference(ennf_transformation,[],[f9])).
% 2.13/1.05  
% 2.13/1.05  fof(f73,plain,(
% 2.13/1.05    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 2.13/1.05    inference(cnf_transformation,[],[f23])).
% 2.13/1.05  
% 2.13/1.05  fof(f87,plain,(
% 2.13/1.05    ~m1_subset_1(k3_xboole_0(sK5,sK6),u1_struct_0(k9_yellow_6(sK3,sK4)))),
% 2.13/1.05    inference(cnf_transformation,[],[f54])).
% 2.13/1.05  
% 2.13/1.05  fof(f97,plain,(
% 2.13/1.05    ~m1_subset_1(k1_setfam_1(k2_tarski(sK5,sK6)),u1_struct_0(k9_yellow_6(sK3,sK4)))),
% 2.13/1.05    inference(definition_unfolding,[],[f87,f72])).
% 2.13/1.05  
% 2.13/1.05  fof(f85,plain,(
% 2.13/1.05    m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK3,sK4)))),
% 2.13/1.05    inference(cnf_transformation,[],[f54])).
% 2.13/1.05  
% 2.13/1.05  fof(f2,axiom,(
% 2.13/1.05    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.13/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.13/1.05  
% 2.13/1.05  fof(f17,plain,(
% 2.13/1.05    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 2.13/1.05    inference(unused_predicate_definition_removal,[],[f2])).
% 2.13/1.05  
% 2.13/1.05  fof(f18,plain,(
% 2.13/1.05    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 2.13/1.05    inference(ennf_transformation,[],[f17])).
% 2.13/1.05  
% 2.13/1.05  fof(f40,plain,(
% 2.13/1.05    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 2.13/1.05    introduced(choice_axiom,[])).
% 2.13/1.05  
% 2.13/1.05  fof(f41,plain,(
% 2.13/1.05    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 2.13/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f18,f40])).
% 2.13/1.05  
% 2.13/1.05  fof(f57,plain,(
% 2.13/1.05    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 2.13/1.05    inference(cnf_transformation,[],[f41])).
% 2.13/1.05  
% 2.13/1.05  fof(f4,axiom,(
% 2.13/1.05    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.13/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.13/1.05  
% 2.13/1.05  fof(f19,plain,(
% 2.13/1.05    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.13/1.05    inference(ennf_transformation,[],[f4])).
% 2.13/1.05  
% 2.13/1.05  fof(f65,plain,(
% 2.13/1.05    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 2.13/1.05    inference(cnf_transformation,[],[f19])).
% 2.13/1.05  
% 2.13/1.05  fof(f94,plain,(
% 2.13/1.05    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 2.13/1.05    inference(definition_unfolding,[],[f65,f72])).
% 2.13/1.05  
% 2.13/1.05  fof(f1,axiom,(
% 2.13/1.05    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.13/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.13/1.05  
% 2.13/1.05  fof(f36,plain,(
% 2.13/1.05    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.13/1.05    inference(nnf_transformation,[],[f1])).
% 2.13/1.05  
% 2.13/1.05  fof(f37,plain,(
% 2.13/1.05    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.13/1.05    inference(rectify,[],[f36])).
% 2.13/1.05  
% 2.13/1.05  fof(f38,plain,(
% 2.13/1.05    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.13/1.05    introduced(choice_axiom,[])).
% 2.13/1.05  
% 2.13/1.05  fof(f39,plain,(
% 2.13/1.05    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.13/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f38])).
% 2.13/1.05  
% 2.13/1.05  fof(f55,plain,(
% 2.13/1.05    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 2.13/1.05    inference(cnf_transformation,[],[f39])).
% 2.13/1.05  
% 2.13/1.05  fof(f5,axiom,(
% 2.13/1.05    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 2.13/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.13/1.05  
% 2.13/1.05  fof(f20,plain,(
% 2.13/1.05    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 2.13/1.05    inference(ennf_transformation,[],[f5])).
% 2.13/1.05  
% 2.13/1.05  fof(f47,plain,(
% 2.13/1.05    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 2.13/1.05    inference(nnf_transformation,[],[f20])).
% 2.13/1.05  
% 2.13/1.05  fof(f66,plain,(
% 2.13/1.05    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.13/1.05    inference(cnf_transformation,[],[f47])).
% 2.13/1.05  
% 2.13/1.05  fof(f78,plain,(
% 2.13/1.05    ( ! [X2,X0,X1] : (v3_pre_topc(X2,X0) | ~r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.13/1.05    inference(cnf_transformation,[],[f49])).
% 2.13/1.05  
% 2.13/1.05  fof(f68,plain,(
% 2.13/1.05    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,X0) | ~v1_xboole_0(X0)) )),
% 2.13/1.05    inference(cnf_transformation,[],[f47])).
% 2.13/1.05  
% 2.13/1.05  fof(f11,axiom,(
% 2.13/1.05    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X2,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k3_xboole_0(X1,X2),X0))),
% 2.13/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.13/1.05  
% 2.13/1.05  fof(f26,plain,(
% 2.13/1.05    ! [X0,X1,X2] : (v3_pre_topc(k3_xboole_0(X1,X2),X0) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.13/1.05    inference(ennf_transformation,[],[f11])).
% 2.13/1.05  
% 2.13/1.05  fof(f27,plain,(
% 2.13/1.05    ! [X0,X1,X2] : (v3_pre_topc(k3_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.13/1.05    inference(flattening,[],[f26])).
% 2.13/1.05  
% 2.13/1.05  fof(f75,plain,(
% 2.13/1.05    ( ! [X2,X0,X1] : (v3_pre_topc(k3_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.13/1.05    inference(cnf_transformation,[],[f27])).
% 2.13/1.05  
% 2.13/1.05  fof(f96,plain,(
% 2.13/1.05    ( ! [X2,X0,X1] : (v3_pre_topc(k1_setfam_1(k2_tarski(X1,X2)),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.13/1.05    inference(definition_unfolding,[],[f75,f72])).
% 2.13/1.05  
% 2.13/1.05  fof(f77,plain,(
% 2.13/1.05    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.13/1.05    inference(cnf_transformation,[],[f49])).
% 2.13/1.05  
% 2.13/1.05  cnf(c_7,plain,
% 2.13/1.05      ( ~ r2_hidden(X0,X1)
% 2.13/1.05      | ~ r2_hidden(X0,X2)
% 2.13/1.05      | r2_hidden(X0,k1_setfam_1(k2_tarski(X2,X1))) ),
% 2.13/1.05      inference(cnf_transformation,[],[f98]) ).
% 2.13/1.05  
% 2.13/1.05  cnf(c_1200,plain,
% 2.13/1.05      ( r2_hidden(X0,X1) != iProver_top
% 2.13/1.05      | r2_hidden(X0,X2) != iProver_top
% 2.13/1.05      | r2_hidden(X0,k1_setfam_1(k2_tarski(X1,X2))) = iProver_top ),
% 2.13/1.05      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.13/1.05  
% 2.13/1.05  cnf(c_26,negated_conjecture,
% 2.13/1.05      ( m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4))) ),
% 2.13/1.05      inference(cnf_transformation,[],[f86]) ).
% 2.13/1.05  
% 2.13/1.05  cnf(c_1189,plain,
% 2.13/1.05      ( m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4))) = iProver_top ),
% 2.13/1.05      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.13/1.05  
% 2.13/1.05  cnf(c_24,plain,
% 2.13/1.05      ( m1_connsp_2(X0,X1,X2)
% 2.13/1.05      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.13/1.05      | ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(X1,X2)))
% 2.13/1.05      | v2_struct_0(X1)
% 2.13/1.05      | ~ v2_pre_topc(X1)
% 2.13/1.05      | ~ l1_pre_topc(X1) ),
% 2.13/1.05      inference(cnf_transformation,[],[f80]) ).
% 2.13/1.05  
% 2.13/1.05  cnf(c_20,plain,
% 2.13/1.05      ( ~ m1_connsp_2(X0,X1,X2)
% 2.13/1.05      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.13/1.05      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.13/1.05      | v2_struct_0(X1)
% 2.13/1.05      | ~ v2_pre_topc(X1)
% 2.13/1.05      | ~ l1_pre_topc(X1) ),
% 2.13/1.05      inference(cnf_transformation,[],[f76]) ).
% 2.13/1.05  
% 2.13/1.05  cnf(c_382,plain,
% 2.13/1.05      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.13/1.05      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
% 2.13/1.05      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.13/1.05      | v2_struct_0(X1)
% 2.13/1.05      | ~ v2_pre_topc(X1)
% 2.13/1.05      | ~ l1_pre_topc(X1) ),
% 2.13/1.05      inference(resolution,[status(thm)],[c_24,c_20]) ).
% 2.13/1.05  
% 2.13/1.05  cnf(c_31,negated_conjecture,
% 2.13/1.05      ( ~ v2_struct_0(sK3) ),
% 2.13/1.05      inference(cnf_transformation,[],[f81]) ).
% 2.13/1.05  
% 2.13/1.05  cnf(c_412,plain,
% 2.13/1.05      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.13/1.05      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
% 2.13/1.05      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.13/1.05      | ~ v2_pre_topc(X1)
% 2.13/1.05      | ~ l1_pre_topc(X1)
% 2.13/1.05      | sK3 != X1 ),
% 2.13/1.05      inference(resolution_lifted,[status(thm)],[c_382,c_31]) ).
% 2.13/1.05  
% 2.13/1.05  cnf(c_413,plain,
% 2.13/1.05      ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK3,X1)))
% 2.13/1.05      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.13/1.05      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.13/1.05      | ~ v2_pre_topc(sK3)
% 2.13/1.05      | ~ l1_pre_topc(sK3) ),
% 2.13/1.05      inference(unflattening,[status(thm)],[c_412]) ).
% 2.13/1.05  
% 2.13/1.05  cnf(c_30,negated_conjecture,
% 2.13/1.05      ( v2_pre_topc(sK3) ),
% 2.13/1.05      inference(cnf_transformation,[],[f82]) ).
% 2.13/1.05  
% 2.13/1.05  cnf(c_29,negated_conjecture,
% 2.13/1.05      ( l1_pre_topc(sK3) ),
% 2.13/1.05      inference(cnf_transformation,[],[f83]) ).
% 2.13/1.05  
% 2.13/1.05  cnf(c_417,plain,
% 2.13/1.05      ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK3,X1)))
% 2.13/1.05      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.13/1.05      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.13/1.05      inference(global_propositional_subsumption,
% 2.13/1.05                [status(thm)],
% 2.13/1.05                [c_413,c_30,c_29]) ).
% 2.13/1.05  
% 2.13/1.05  cnf(c_1184,plain,
% 2.13/1.05      ( m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK3,X1))) != iProver_top
% 2.13/1.05      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
% 2.13/1.05      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 2.13/1.05      inference(predicate_to_equality,[status(thm)],[c_417]) ).
% 2.13/1.05  
% 2.13/1.05  cnf(c_1485,plain,
% 2.13/1.05      ( m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 2.13/1.05      | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 2.13/1.05      inference(superposition,[status(thm)],[c_1189,c_1184]) ).
% 2.13/1.05  
% 2.13/1.05  cnf(c_28,negated_conjecture,
% 2.13/1.05      ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 2.13/1.05      inference(cnf_transformation,[],[f84]) ).
% 2.13/1.05  
% 2.13/1.05  cnf(c_35,plain,
% 2.13/1.05      ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
% 2.13/1.05      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.13/1.05  
% 2.13/1.05  cnf(c_1498,plain,
% 2.13/1.05      ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 2.13/1.05      inference(global_propositional_subsumption,
% 2.13/1.05                [status(thm)],
% 2.13/1.05                [c_1485,c_35]) ).
% 2.13/1.05  
% 2.13/1.05  cnf(c_16,plain,
% 2.13/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.13/1.05      | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
% 2.13/1.05      inference(cnf_transformation,[],[f95]) ).
% 2.13/1.05  
% 2.13/1.05  cnf(c_1193,plain,
% 2.13/1.05      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
% 2.13/1.05      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 2.13/1.05      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.13/1.05  
% 2.13/1.05  cnf(c_2299,plain,
% 2.13/1.05      ( k9_subset_1(u1_struct_0(sK3),X0,sK6) = k1_setfam_1(k2_tarski(X0,sK6)) ),
% 2.13/1.05      inference(superposition,[status(thm)],[c_1498,c_1193]) ).
% 2.13/1.05  
% 2.13/1.05  cnf(c_15,plain,
% 2.13/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.13/1.05      | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 2.13/1.05      inference(cnf_transformation,[],[f70]) ).
% 2.13/1.05  
% 2.13/1.05  cnf(c_1194,plain,
% 2.13/1.05      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.13/1.05      | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 2.13/1.05      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.13/1.05  
% 2.13/1.05  cnf(c_2680,plain,
% 2.13/1.05      ( m1_subset_1(k1_setfam_1(k2_tarski(X0,sK6)),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 2.13/1.05      | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.13/1.05      inference(superposition,[status(thm)],[c_2299,c_1194]) ).
% 2.13/1.05  
% 2.13/1.05  cnf(c_8556,plain,
% 2.13/1.05      ( m1_subset_1(k1_setfam_1(k2_tarski(X0,sK6)),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 2.13/1.05      inference(global_propositional_subsumption,
% 2.13/1.05                [status(thm)],
% 2.13/1.05                [c_2680,c_35,c_1485]) ).
% 2.13/1.05  
% 2.13/1.05  cnf(c_21,plain,
% 2.13/1.05      ( ~ v3_pre_topc(X0,X1)
% 2.13/1.05      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.13/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.13/1.05      | ~ r2_hidden(X2,X0)
% 2.13/1.05      | r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
% 2.13/1.05      | v2_struct_0(X1)
% 2.13/1.05      | ~ v2_pre_topc(X1)
% 2.13/1.05      | ~ l1_pre_topc(X1) ),
% 2.13/1.05      inference(cnf_transformation,[],[f79]) ).
% 2.13/1.05  
% 2.13/1.05  cnf(c_481,plain,
% 2.13/1.05      ( ~ v3_pre_topc(X0,X1)
% 2.13/1.05      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.13/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.13/1.05      | ~ r2_hidden(X2,X0)
% 2.13/1.05      | r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
% 2.13/1.05      | ~ v2_pre_topc(X1)
% 2.13/1.05      | ~ l1_pre_topc(X1)
% 2.13/1.05      | sK3 != X1 ),
% 2.13/1.05      inference(resolution_lifted,[status(thm)],[c_21,c_31]) ).
% 2.13/1.05  
% 2.13/1.05  cnf(c_482,plain,
% 2.13/1.05      ( ~ v3_pre_topc(X0,sK3)
% 2.13/1.05      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.13/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.13/1.05      | ~ r2_hidden(X1,X0)
% 2.13/1.05      | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK3,X1)))
% 2.13/1.05      | ~ v2_pre_topc(sK3)
% 2.13/1.05      | ~ l1_pre_topc(sK3) ),
% 2.13/1.05      inference(unflattening,[status(thm)],[c_481]) ).
% 2.13/1.05  
% 2.13/1.05  cnf(c_486,plain,
% 2.13/1.05      ( ~ v3_pre_topc(X0,sK3)
% 2.13/1.05      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.13/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.13/1.05      | ~ r2_hidden(X1,X0)
% 2.13/1.05      | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK3,X1))) ),
% 2.13/1.05      inference(global_propositional_subsumption,
% 2.13/1.05                [status(thm)],
% 2.13/1.05                [c_482,c_30,c_29]) ).
% 2.13/1.05  
% 2.13/1.05  cnf(c_18,plain,
% 2.13/1.05      ( m1_subset_1(X0,X1)
% 2.13/1.05      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 2.13/1.05      | ~ r2_hidden(X0,X2) ),
% 2.13/1.05      inference(cnf_transformation,[],[f74]) ).
% 2.13/1.05  
% 2.13/1.05  cnf(c_502,plain,
% 2.13/1.05      ( ~ v3_pre_topc(X0,sK3)
% 2.13/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.13/1.05      | ~ r2_hidden(X1,X0)
% 2.13/1.05      | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK3,X1))) ),
% 2.13/1.05      inference(forward_subsumption_resolution,
% 2.13/1.05                [status(thm)],
% 2.13/1.05                [c_486,c_18]) ).
% 2.13/1.05  
% 2.13/1.05  cnf(c_1181,plain,
% 2.13/1.05      ( v3_pre_topc(X0,sK3) != iProver_top
% 2.13/1.05      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.13/1.05      | r2_hidden(X1,X0) != iProver_top
% 2.13/1.05      | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK3,X1))) = iProver_top ),
% 2.13/1.05      inference(predicate_to_equality,[status(thm)],[c_502]) ).
% 2.13/1.05  
% 2.13/1.05  cnf(c_17,plain,
% 2.13/1.05      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 2.13/1.05      inference(cnf_transformation,[],[f73]) ).
% 2.13/1.05  
% 2.13/1.05  cnf(c_1192,plain,
% 2.13/1.05      ( m1_subset_1(X0,X1) = iProver_top
% 2.13/1.05      | r2_hidden(X0,X1) != iProver_top ),
% 2.13/1.05      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.13/1.05  
% 2.13/1.05  cnf(c_1920,plain,
% 2.13/1.05      ( v3_pre_topc(X0,sK3) != iProver_top
% 2.13/1.05      | m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK3,X1))) = iProver_top
% 2.13/1.05      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.13/1.05      | r2_hidden(X1,X0) != iProver_top ),
% 2.13/1.05      inference(superposition,[status(thm)],[c_1181,c_1192]) ).
% 2.13/1.05  
% 2.13/1.05  cnf(c_25,negated_conjecture,
% 2.13/1.05      ( ~ m1_subset_1(k1_setfam_1(k2_tarski(sK5,sK6)),u1_struct_0(k9_yellow_6(sK3,sK4))) ),
% 2.13/1.05      inference(cnf_transformation,[],[f97]) ).
% 2.13/1.05  
% 2.13/1.05  cnf(c_1190,plain,
% 2.13/1.05      ( m1_subset_1(k1_setfam_1(k2_tarski(sK5,sK6)),u1_struct_0(k9_yellow_6(sK3,sK4))) != iProver_top ),
% 2.13/1.05      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.13/1.05  
% 2.13/1.05  cnf(c_2222,plain,
% 2.13/1.05      ( v3_pre_topc(k1_setfam_1(k2_tarski(sK5,sK6)),sK3) != iProver_top
% 2.13/1.05      | m1_subset_1(k1_setfam_1(k2_tarski(sK5,sK6)),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.13/1.05      | r2_hidden(sK4,k1_setfam_1(k2_tarski(sK5,sK6))) != iProver_top ),
% 2.13/1.05      inference(superposition,[status(thm)],[c_1920,c_1190]) ).
% 2.13/1.05  
% 2.13/1.05  cnf(c_8568,plain,
% 2.13/1.05      ( v3_pre_topc(k1_setfam_1(k2_tarski(sK5,sK6)),sK3) != iProver_top
% 2.13/1.05      | r2_hidden(sK4,k1_setfam_1(k2_tarski(sK5,sK6))) != iProver_top ),
% 2.13/1.05      inference(superposition,[status(thm)],[c_8556,c_2222]) ).
% 2.13/1.05  
% 2.13/1.05  cnf(c_27,negated_conjecture,
% 2.13/1.05      ( m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK3,sK4))) ),
% 2.13/1.05      inference(cnf_transformation,[],[f85]) ).
% 2.13/1.05  
% 2.13/1.05  cnf(c_1188,plain,
% 2.13/1.05      ( m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK3,sK4))) = iProver_top ),
% 2.13/1.05      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.13/1.05  
% 2.13/1.05  cnf(c_1486,plain,
% 2.13/1.05      ( m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 2.13/1.05      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 2.13/1.05      inference(superposition,[status(thm)],[c_1188,c_1184]) ).
% 2.13/1.05  
% 2.13/1.05  cnf(c_739,plain,( X0 = X0 ),theory(equality) ).
% 2.13/1.05  
% 2.13/1.05  cnf(c_1562,plain,
% 2.13/1.05      ( u1_struct_0(k9_yellow_6(sK3,sK4)) = u1_struct_0(k9_yellow_6(sK3,sK4)) ),
% 2.13/1.05      inference(instantiation,[status(thm)],[c_739]) ).
% 2.13/1.05  
% 2.13/1.05  cnf(c_744,plain,
% 2.13/1.05      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.13/1.05      theory(equality) ).
% 2.13/1.05  
% 2.13/1.05  cnf(c_1470,plain,
% 2.13/1.05      ( ~ m1_subset_1(X0,X1)
% 2.13/1.05      | m1_subset_1(k1_setfam_1(k2_tarski(sK5,sK6)),u1_struct_0(k9_yellow_6(sK3,sK4)))
% 2.13/1.05      | u1_struct_0(k9_yellow_6(sK3,sK4)) != X1
% 2.13/1.05      | k1_setfam_1(k2_tarski(sK5,sK6)) != X0 ),
% 2.13/1.05      inference(instantiation,[status(thm)],[c_744]) ).
% 2.13/1.05  
% 2.13/1.05  cnf(c_1561,plain,
% 2.13/1.05      ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK3,sK4)))
% 2.13/1.05      | m1_subset_1(k1_setfam_1(k2_tarski(sK5,sK6)),u1_struct_0(k9_yellow_6(sK3,sK4)))
% 2.13/1.05      | u1_struct_0(k9_yellow_6(sK3,sK4)) != u1_struct_0(k9_yellow_6(sK3,sK4))
% 2.13/1.05      | k1_setfam_1(k2_tarski(sK5,sK6)) != X0 ),
% 2.13/1.05      inference(instantiation,[status(thm)],[c_1470]) ).
% 2.13/1.05  
% 2.13/1.05  cnf(c_1725,plain,
% 2.13/1.05      ( m1_subset_1(k1_setfam_1(k2_tarski(sK5,sK6)),u1_struct_0(k9_yellow_6(sK3,sK4)))
% 2.13/1.05      | ~ m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK3,sK4)))
% 2.13/1.05      | u1_struct_0(k9_yellow_6(sK3,sK4)) != u1_struct_0(k9_yellow_6(sK3,sK4))
% 2.13/1.05      | k1_setfam_1(k2_tarski(sK5,sK6)) != sK5 ),
% 2.13/1.05      inference(instantiation,[status(thm)],[c_1561]) ).
% 2.13/1.05  
% 2.13/1.05  cnf(c_3,plain,
% 2.13/1.05      ( r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 2.13/1.05      inference(cnf_transformation,[],[f57]) ).
% 2.13/1.05  
% 2.13/1.05  cnf(c_10,plain,
% 2.13/1.05      ( ~ r1_tarski(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) = X0 ),
% 2.13/1.05      inference(cnf_transformation,[],[f94]) ).
% 2.13/1.05  
% 2.13/1.05  cnf(c_354,plain,
% 2.13/1.05      ( r2_hidden(sK1(X0,X1),X0) | k1_setfam_1(k2_tarski(X0,X1)) = X0 ),
% 2.13/1.05      inference(resolution,[status(thm)],[c_3,c_10]) ).
% 2.13/1.05  
% 2.13/1.05  cnf(c_1763,plain,
% 2.13/1.05      ( r2_hidden(sK1(sK5,sK6),sK5)
% 2.13/1.05      | k1_setfam_1(k2_tarski(sK5,sK6)) = sK5 ),
% 2.13/1.05      inference(instantiation,[status(thm)],[c_354]) ).
% 2.13/1.05  
% 2.13/1.05  cnf(c_1768,plain,
% 2.13/1.05      ( k1_setfam_1(k2_tarski(sK5,sK6)) = sK5
% 2.13/1.05      | r2_hidden(sK1(sK5,sK6),sK5) = iProver_top ),
% 2.13/1.05      inference(predicate_to_equality,[status(thm)],[c_1763]) ).
% 2.13/1.05  
% 2.13/1.05  cnf(c_1,plain,
% 2.13/1.05      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 2.13/1.05      inference(cnf_transformation,[],[f55]) ).
% 2.13/1.05  
% 2.13/1.05  cnf(c_2330,plain,
% 2.13/1.05      ( ~ r2_hidden(sK1(sK5,sK6),sK5) | ~ v1_xboole_0(sK5) ),
% 2.13/1.05      inference(instantiation,[status(thm)],[c_1]) ).
% 2.13/1.05  
% 2.13/1.05  cnf(c_2331,plain,
% 2.13/1.05      ( r2_hidden(sK1(sK5,sK6),sK5) != iProver_top
% 2.13/1.05      | v1_xboole_0(sK5) != iProver_top ),
% 2.13/1.05      inference(predicate_to_equality,[status(thm)],[c_2330]) ).
% 2.13/1.05  
% 2.13/1.05  cnf(c_14,plain,
% 2.13/1.05      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.13/1.05      inference(cnf_transformation,[],[f66]) ).
% 2.13/1.05  
% 2.13/1.05  cnf(c_1195,plain,
% 2.13/1.05      ( m1_subset_1(X0,X1) != iProver_top
% 2.13/1.05      | r2_hidden(X0,X1) = iProver_top
% 2.13/1.05      | v1_xboole_0(X1) = iProver_top ),
% 2.13/1.05      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.13/1.05  
% 2.13/1.05  cnf(c_2368,plain,
% 2.13/1.05      ( r2_hidden(sK6,u1_struct_0(k9_yellow_6(sK3,sK4))) = iProver_top
% 2.13/1.05      | v1_xboole_0(u1_struct_0(k9_yellow_6(sK3,sK4))) = iProver_top ),
% 2.13/1.05      inference(superposition,[status(thm)],[c_1189,c_1195]) ).
% 2.13/1.05  
% 2.13/1.05  cnf(c_22,plain,
% 2.13/1.05      ( v3_pre_topc(X0,X1)
% 2.13/1.05      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.13/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.13/1.05      | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
% 2.13/1.05      | v2_struct_0(X1)
% 2.13/1.05      | ~ v2_pre_topc(X1)
% 2.13/1.05      | ~ l1_pre_topc(X1) ),
% 2.13/1.05      inference(cnf_transformation,[],[f78]) ).
% 2.13/1.05  
% 2.13/1.05  cnf(c_457,plain,
% 2.13/1.05      ( v3_pre_topc(X0,X1)
% 2.13/1.05      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.13/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.13/1.05      | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
% 2.13/1.05      | ~ v2_pre_topc(X1)
% 2.13/1.05      | ~ l1_pre_topc(X1)
% 2.13/1.05      | sK3 != X1 ),
% 2.13/1.05      inference(resolution_lifted,[status(thm)],[c_22,c_31]) ).
% 2.13/1.05  
% 2.13/1.05  cnf(c_458,plain,
% 2.13/1.05      ( v3_pre_topc(X0,sK3)
% 2.13/1.05      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.13/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.13/1.05      | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(sK3,X1)))
% 2.13/1.05      | ~ v2_pre_topc(sK3)
% 2.13/1.05      | ~ l1_pre_topc(sK3) ),
% 2.13/1.05      inference(unflattening,[status(thm)],[c_457]) ).
% 2.13/1.05  
% 2.13/1.05  cnf(c_462,plain,
% 2.13/1.05      ( v3_pre_topc(X0,sK3)
% 2.13/1.05      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.13/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.13/1.05      | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(sK3,X1))) ),
% 2.13/1.05      inference(global_propositional_subsumption,
% 2.13/1.05                [status(thm)],
% 2.13/1.05                [c_458,c_30,c_29]) ).
% 2.13/1.05  
% 2.13/1.05  cnf(c_1182,plain,
% 2.13/1.05      ( v3_pre_topc(X0,sK3) = iProver_top
% 2.13/1.05      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
% 2.13/1.05      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.13/1.05      | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK3,X1))) != iProver_top ),
% 2.13/1.05      inference(predicate_to_equality,[status(thm)],[c_462]) ).
% 2.13/1.05  
% 2.13/1.05  cnf(c_2547,plain,
% 2.13/1.05      ( v3_pre_topc(sK6,sK3) = iProver_top
% 2.13/1.05      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 2.13/1.05      | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.13/1.05      | v1_xboole_0(u1_struct_0(k9_yellow_6(sK3,sK4))) = iProver_top ),
% 2.13/1.05      inference(superposition,[status(thm)],[c_2368,c_1182]) ).
% 2.13/1.05  
% 2.13/1.05  cnf(c_2369,plain,
% 2.13/1.05      ( r2_hidden(sK5,u1_struct_0(k9_yellow_6(sK3,sK4))) = iProver_top
% 2.13/1.05      | v1_xboole_0(u1_struct_0(k9_yellow_6(sK3,sK4))) = iProver_top ),
% 2.13/1.05      inference(superposition,[status(thm)],[c_1188,c_1195]) ).
% 2.13/1.05  
% 2.13/1.05  cnf(c_2572,plain,
% 2.13/1.05      ( v3_pre_topc(sK5,sK3) = iProver_top
% 2.13/1.05      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 2.13/1.05      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.13/1.05      | v1_xboole_0(u1_struct_0(k9_yellow_6(sK3,sK4))) = iProver_top ),
% 2.13/1.05      inference(superposition,[status(thm)],[c_2369,c_1182]) ).
% 2.13/1.05  
% 2.13/1.05  cnf(c_12,plain,
% 2.13/1.05      ( ~ m1_subset_1(X0,X1) | ~ v1_xboole_0(X1) | v1_xboole_0(X0) ),
% 2.13/1.05      inference(cnf_transformation,[],[f68]) ).
% 2.13/1.05  
% 2.13/1.05  cnf(c_1196,plain,
% 2.13/1.05      ( m1_subset_1(X0,X1) != iProver_top
% 2.13/1.05      | v1_xboole_0(X1) != iProver_top
% 2.13/1.05      | v1_xboole_0(X0) = iProver_top ),
% 2.13/1.05      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.13/1.05  
% 2.13/1.05  cnf(c_2983,plain,
% 2.13/1.05      ( v1_xboole_0(u1_struct_0(k9_yellow_6(sK3,sK4))) != iProver_top
% 2.13/1.05      | v1_xboole_0(sK5) = iProver_top ),
% 2.13/1.05      inference(superposition,[status(thm)],[c_1188,c_1196]) ).
% 2.13/1.05  
% 2.13/1.05  cnf(c_19,plain,
% 2.13/1.05      ( ~ v3_pre_topc(X0,X1)
% 2.13/1.05      | ~ v3_pre_topc(X2,X1)
% 2.13/1.05      | v3_pre_topc(k1_setfam_1(k2_tarski(X2,X0)),X1)
% 2.13/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.13/1.05      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.13/1.05      | ~ v2_pre_topc(X1)
% 2.13/1.05      | ~ l1_pre_topc(X1) ),
% 2.13/1.05      inference(cnf_transformation,[],[f96]) ).
% 2.13/1.05  
% 2.13/1.05  cnf(c_529,plain,
% 2.13/1.05      ( ~ v3_pre_topc(X0,X1)
% 2.13/1.05      | ~ v3_pre_topc(X2,X1)
% 2.13/1.05      | v3_pre_topc(k1_setfam_1(k2_tarski(X2,X0)),X1)
% 2.13/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.13/1.05      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.13/1.05      | ~ v2_pre_topc(X1)
% 2.13/1.05      | sK3 != X1 ),
% 2.13/1.05      inference(resolution_lifted,[status(thm)],[c_19,c_29]) ).
% 2.13/1.05  
% 2.13/1.05  cnf(c_530,plain,
% 2.13/1.05      ( ~ v3_pre_topc(X0,sK3)
% 2.13/1.05      | ~ v3_pre_topc(X1,sK3)
% 2.13/1.05      | v3_pre_topc(k1_setfam_1(k2_tarski(X1,X0)),sK3)
% 2.13/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.13/1.05      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.13/1.05      | ~ v2_pre_topc(sK3) ),
% 2.13/1.05      inference(unflattening,[status(thm)],[c_529]) ).
% 2.13/1.05  
% 2.13/1.05  cnf(c_534,plain,
% 2.13/1.05      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.13/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.13/1.05      | v3_pre_topc(k1_setfam_1(k2_tarski(X1,X0)),sK3)
% 2.13/1.05      | ~ v3_pre_topc(X1,sK3)
% 2.13/1.05      | ~ v3_pre_topc(X0,sK3) ),
% 2.13/1.05      inference(global_propositional_subsumption,
% 2.13/1.05                [status(thm)],
% 2.13/1.05                [c_530,c_30]) ).
% 2.13/1.05  
% 2.13/1.05  cnf(c_535,plain,
% 2.13/1.05      ( ~ v3_pre_topc(X0,sK3)
% 2.13/1.05      | ~ v3_pre_topc(X1,sK3)
% 2.13/1.05      | v3_pre_topc(k1_setfam_1(k2_tarski(X1,X0)),sK3)
% 2.13/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.13/1.05      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.13/1.05      inference(renaming,[status(thm)],[c_534]) ).
% 2.13/1.05  
% 2.13/1.05  cnf(c_3450,plain,
% 2.13/1.05      ( ~ v3_pre_topc(X0,sK3)
% 2.13/1.05      | v3_pre_topc(k1_setfam_1(k2_tarski(X0,sK6)),sK3)
% 2.13/1.05      | ~ v3_pre_topc(sK6,sK3)
% 2.13/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.13/1.05      | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.13/1.05      inference(instantiation,[status(thm)],[c_535]) ).
% 2.13/1.05  
% 2.13/1.05  cnf(c_6658,plain,
% 2.13/1.05      ( v3_pre_topc(k1_setfam_1(k2_tarski(sK5,sK6)),sK3)
% 2.13/1.05      | ~ v3_pre_topc(sK6,sK3)
% 2.13/1.05      | ~ v3_pre_topc(sK5,sK3)
% 2.13/1.05      | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.13/1.05      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.13/1.05      inference(instantiation,[status(thm)],[c_3450]) ).
% 2.13/1.05  
% 2.13/1.05  cnf(c_6659,plain,
% 2.13/1.05      ( v3_pre_topc(k1_setfam_1(k2_tarski(sK5,sK6)),sK3) = iProver_top
% 2.13/1.05      | v3_pre_topc(sK6,sK3) != iProver_top
% 2.13/1.05      | v3_pre_topc(sK5,sK3) != iProver_top
% 2.13/1.05      | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.13/1.05      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.13/1.05      inference(predicate_to_equality,[status(thm)],[c_6658]) ).
% 2.13/1.05  
% 2.13/1.05  cnf(c_9231,plain,
% 2.13/1.05      ( r2_hidden(sK4,k1_setfam_1(k2_tarski(sK5,sK6))) != iProver_top ),
% 2.13/1.05      inference(global_propositional_subsumption,
% 2.13/1.05                [status(thm)],
% 2.13/1.05                [c_8568,c_35,c_27,c_25,c_1485,c_1486,c_1562,c_1725,
% 2.13/1.05                 c_1768,c_2331,c_2547,c_2572,c_2983,c_6659]) ).
% 2.13/1.05  
% 2.13/1.05  cnf(c_9236,plain,
% 2.13/1.05      ( r2_hidden(sK4,sK6) != iProver_top
% 2.13/1.05      | r2_hidden(sK4,sK5) != iProver_top ),
% 2.13/1.05      inference(superposition,[status(thm)],[c_1200,c_9231]) ).
% 2.13/1.05  
% 2.13/1.05  cnf(c_23,plain,
% 2.13/1.05      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.13/1.05      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.13/1.05      | r2_hidden(X0,X2)
% 2.13/1.05      | ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(X1,X0)))
% 2.13/1.05      | v2_struct_0(X1)
% 2.13/1.05      | ~ v2_pre_topc(X1)
% 2.13/1.05      | ~ l1_pre_topc(X1) ),
% 2.13/1.05      inference(cnf_transformation,[],[f77]) ).
% 2.13/1.05  
% 2.13/1.05  cnf(c_433,plain,
% 2.13/1.05      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.13/1.05      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.13/1.05      | r2_hidden(X0,X2)
% 2.13/1.05      | ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(X1,X0)))
% 2.13/1.05      | ~ v2_pre_topc(X1)
% 2.13/1.05      | ~ l1_pre_topc(X1)
% 2.13/1.05      | sK3 != X1 ),
% 2.13/1.05      inference(resolution_lifted,[status(thm)],[c_23,c_31]) ).
% 2.13/1.05  
% 2.13/1.05  cnf(c_434,plain,
% 2.13/1.05      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.13/1.05      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.13/1.05      | r2_hidden(X0,X1)
% 2.13/1.05      | ~ r2_hidden(X1,u1_struct_0(k9_yellow_6(sK3,X0)))
% 2.13/1.05      | ~ v2_pre_topc(sK3)
% 2.13/1.05      | ~ l1_pre_topc(sK3) ),
% 2.13/1.05      inference(unflattening,[status(thm)],[c_433]) ).
% 2.13/1.05  
% 2.13/1.05  cnf(c_438,plain,
% 2.13/1.05      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.13/1.05      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.13/1.05      | r2_hidden(X0,X1)
% 2.13/1.05      | ~ r2_hidden(X1,u1_struct_0(k9_yellow_6(sK3,X0))) ),
% 2.13/1.05      inference(global_propositional_subsumption,
% 2.13/1.05                [status(thm)],
% 2.13/1.05                [c_434,c_30,c_29]) ).
% 2.13/1.05  
% 2.13/1.05  cnf(c_1183,plain,
% 2.13/1.05      ( m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 2.13/1.05      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.13/1.05      | r2_hidden(X0,X1) = iProver_top
% 2.13/1.05      | r2_hidden(X1,u1_struct_0(k9_yellow_6(sK3,X0))) != iProver_top ),
% 2.13/1.05      inference(predicate_to_equality,[status(thm)],[c_438]) ).
% 2.13/1.05  
% 2.13/1.05  cnf(c_2571,plain,
% 2.13/1.05      ( m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 2.13/1.05      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.13/1.05      | r2_hidden(sK4,sK5) = iProver_top
% 2.13/1.05      | v1_xboole_0(u1_struct_0(k9_yellow_6(sK3,sK4))) = iProver_top ),
% 2.13/1.05      inference(superposition,[status(thm)],[c_2369,c_1183]) ).
% 2.13/1.05  
% 2.13/1.05  cnf(c_2546,plain,
% 2.13/1.05      ( m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 2.13/1.05      | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.13/1.05      | r2_hidden(sK4,sK6) = iProver_top
% 2.13/1.05      | v1_xboole_0(u1_struct_0(k9_yellow_6(sK3,sK4))) = iProver_top ),
% 2.13/1.05      inference(superposition,[status(thm)],[c_2368,c_1183]) ).
% 2.13/1.05  
% 2.13/1.05  cnf(contradiction,plain,
% 2.13/1.05      ( $false ),
% 2.13/1.05      inference(minisat,
% 2.13/1.05                [status(thm)],
% 2.13/1.05                [c_9236,c_2983,c_2571,c_2546,c_2331,c_1768,c_1725,c_1562,
% 2.13/1.05                 c_1486,c_1485,c_25,c_27,c_35]) ).
% 2.13/1.05  
% 2.13/1.05  
% 2.13/1.05  % SZS output end CNFRefutation for theBenchmark.p
% 2.13/1.05  
% 2.13/1.05  ------                               Statistics
% 2.13/1.05  
% 2.13/1.05  ------ General
% 2.13/1.05  
% 2.13/1.05  abstr_ref_over_cycles:                  0
% 2.13/1.05  abstr_ref_under_cycles:                 0
% 2.13/1.05  gc_basic_clause_elim:                   0
% 2.13/1.05  forced_gc_time:                         0
% 2.13/1.05  parsing_time:                           0.01
% 2.13/1.05  unif_index_cands_time:                  0.
% 2.13/1.05  unif_index_add_time:                    0.
% 2.13/1.05  orderings_time:                         0.
% 2.13/1.05  out_proof_time:                         0.011
% 2.13/1.05  total_time:                             0.265
% 2.13/1.05  num_of_symbols:                         53
% 2.13/1.05  num_of_terms:                           9795
% 2.13/1.05  
% 2.13/1.05  ------ Preprocessing
% 2.13/1.05  
% 2.13/1.05  num_of_splits:                          0
% 2.13/1.05  num_of_split_atoms:                     0
% 2.13/1.05  num_of_reused_defs:                     0
% 2.13/1.05  num_eq_ax_congr_red:                    36
% 2.13/1.05  num_of_sem_filtered_clauses:            1
% 2.13/1.05  num_of_subtypes:                        0
% 2.13/1.05  monotx_restored_types:                  0
% 2.13/1.05  sat_num_of_epr_types:                   0
% 2.13/1.05  sat_num_of_non_cyclic_types:            0
% 2.13/1.05  sat_guarded_non_collapsed_types:        0
% 2.13/1.05  num_pure_diseq_elim:                    0
% 2.13/1.05  simp_replaced_by:                       0
% 2.13/1.05  res_preprocessed:                       130
% 2.13/1.05  prep_upred:                             0
% 2.13/1.05  prep_unflattend:                        5
% 2.13/1.05  smt_new_axioms:                         0
% 2.13/1.05  pred_elim_cands:                        4
% 2.13/1.05  pred_elim:                              5
% 2.13/1.05  pred_elim_cl:                           5
% 2.13/1.05  pred_elim_cycles:                       7
% 2.13/1.05  merged_defs:                            0
% 2.13/1.05  merged_defs_ncl:                        0
% 2.13/1.05  bin_hyper_res:                          0
% 2.13/1.05  prep_cycles:                            4
% 2.13/1.05  pred_elim_time:                         0.006
% 2.13/1.05  splitting_time:                         0.
% 2.13/1.05  sem_filter_time:                        0.
% 2.13/1.05  monotx_time:                            0.
% 2.13/1.05  subtype_inf_time:                       0.
% 2.13/1.05  
% 2.13/1.05  ------ Problem properties
% 2.13/1.05  
% 2.13/1.05  clauses:                                26
% 2.13/1.05  conjectures:                            4
% 2.13/1.05  epr:                                    5
% 2.13/1.05  horn:                                   21
% 2.13/1.05  ground:                                 4
% 2.13/1.05  unary:                                  4
% 2.13/1.05  binary:                                 9
% 2.13/1.05  lits:                                   67
% 2.13/1.05  lits_eq:                                6
% 2.13/1.05  fd_pure:                                0
% 2.13/1.05  fd_pseudo:                              0
% 2.13/1.05  fd_cond:                                0
% 2.13/1.05  fd_pseudo_cond:                         3
% 2.13/1.05  ac_symbols:                             0
% 2.13/1.05  
% 2.13/1.05  ------ Propositional Solver
% 2.13/1.05  
% 2.13/1.05  prop_solver_calls:                      29
% 2.13/1.05  prop_fast_solver_calls:                 1025
% 2.13/1.05  smt_solver_calls:                       0
% 2.13/1.05  smt_fast_solver_calls:                  0
% 2.13/1.05  prop_num_of_clauses:                    4126
% 2.13/1.05  prop_preprocess_simplified:             9291
% 2.13/1.05  prop_fo_subsumed:                       28
% 2.13/1.05  prop_solver_time:                       0.
% 2.13/1.05  smt_solver_time:                        0.
% 2.13/1.05  smt_fast_solver_time:                   0.
% 2.13/1.05  prop_fast_solver_time:                  0.
% 2.13/1.05  prop_unsat_core_time:                   0.
% 2.13/1.05  
% 2.13/1.05  ------ QBF
% 2.13/1.05  
% 2.13/1.05  qbf_q_res:                              0
% 2.13/1.05  qbf_num_tautologies:                    0
% 2.13/1.05  qbf_prep_cycles:                        0
% 2.13/1.05  
% 2.13/1.05  ------ BMC1
% 2.13/1.05  
% 2.13/1.05  bmc1_current_bound:                     -1
% 2.13/1.05  bmc1_last_solved_bound:                 -1
% 2.13/1.05  bmc1_unsat_core_size:                   -1
% 2.13/1.05  bmc1_unsat_core_parents_size:           -1
% 2.13/1.05  bmc1_merge_next_fun:                    0
% 2.13/1.05  bmc1_unsat_core_clauses_time:           0.
% 2.13/1.05  
% 2.13/1.05  ------ Instantiation
% 2.13/1.05  
% 2.13/1.05  inst_num_of_clauses:                    1096
% 2.13/1.05  inst_num_in_passive:                    295
% 2.13/1.05  inst_num_in_active:                     345
% 2.13/1.05  inst_num_in_unprocessed:                456
% 2.13/1.05  inst_num_of_loops:                      440
% 2.13/1.05  inst_num_of_learning_restarts:          0
% 2.13/1.05  inst_num_moves_active_passive:          92
% 2.13/1.05  inst_lit_activity:                      0
% 2.13/1.05  inst_lit_activity_moves:                0
% 2.13/1.05  inst_num_tautologies:                   0
% 2.13/1.05  inst_num_prop_implied:                  0
% 2.13/1.05  inst_num_existing_simplified:           0
% 2.13/1.05  inst_num_eq_res_simplified:             0
% 2.13/1.05  inst_num_child_elim:                    0
% 2.13/1.05  inst_num_of_dismatching_blockings:      291
% 2.13/1.05  inst_num_of_non_proper_insts:           750
% 2.13/1.05  inst_num_of_duplicates:                 0
% 2.13/1.05  inst_inst_num_from_inst_to_res:         0
% 2.13/1.05  inst_dismatching_checking_time:         0.
% 2.13/1.05  
% 2.13/1.05  ------ Resolution
% 2.13/1.05  
% 2.13/1.05  res_num_of_clauses:                     0
% 2.13/1.05  res_num_in_passive:                     0
% 2.13/1.05  res_num_in_active:                      0
% 2.13/1.05  res_num_of_loops:                       134
% 2.13/1.05  res_forward_subset_subsumed:            65
% 2.13/1.05  res_backward_subset_subsumed:           0
% 2.13/1.05  res_forward_subsumed:                   0
% 2.13/1.05  res_backward_subsumed:                  0
% 2.13/1.05  res_forward_subsumption_resolution:     1
% 2.13/1.05  res_backward_subsumption_resolution:    0
% 2.13/1.05  res_clause_to_clause_subsumption:       668
% 2.13/1.05  res_orphan_elimination:                 0
% 2.13/1.05  res_tautology_del:                      31
% 2.13/1.05  res_num_eq_res_simplified:              0
% 2.13/1.05  res_num_sel_changes:                    0
% 2.13/1.05  res_moves_from_active_to_pass:          0
% 2.13/1.05  
% 2.13/1.05  ------ Superposition
% 2.13/1.05  
% 2.13/1.05  sup_time_total:                         0.
% 2.13/1.05  sup_time_generating:                    0.
% 2.13/1.05  sup_time_sim_full:                      0.
% 2.13/1.05  sup_time_sim_immed:                     0.
% 2.13/1.05  
% 2.13/1.05  sup_num_of_clauses:                     176
% 2.13/1.05  sup_num_in_active:                      87
% 2.13/1.05  sup_num_in_passive:                     89
% 2.13/1.05  sup_num_of_loops:                       87
% 2.13/1.05  sup_fw_superposition:                   70
% 2.13/1.05  sup_bw_superposition:                   140
% 2.13/1.05  sup_immediate_simplified:               42
% 2.13/1.05  sup_given_eliminated:                   0
% 2.13/1.05  comparisons_done:                       0
% 2.13/1.05  comparisons_avoided:                    0
% 2.13/1.05  
% 2.13/1.05  ------ Simplifications
% 2.13/1.05  
% 2.13/1.05  
% 2.13/1.05  sim_fw_subset_subsumed:                 31
% 2.13/1.05  sim_bw_subset_subsumed:                 6
% 2.13/1.05  sim_fw_subsumed:                        6
% 2.13/1.05  sim_bw_subsumed:                        0
% 2.13/1.05  sim_fw_subsumption_res:                 3
% 2.13/1.05  sim_bw_subsumption_res:                 0
% 2.13/1.05  sim_tautology_del:                      18
% 2.13/1.05  sim_eq_tautology_del:                   0
% 2.13/1.05  sim_eq_res_simp:                        2
% 2.13/1.05  sim_fw_demodulated:                     2
% 2.13/1.05  sim_bw_demodulated:                     0
% 2.13/1.05  sim_light_normalised:                   0
% 2.13/1.05  sim_joinable_taut:                      0
% 2.13/1.05  sim_joinable_simp:                      0
% 2.13/1.05  sim_ac_normalised:                      0
% 2.13/1.05  sim_smt_subsumption:                    0
% 2.13/1.05  
%------------------------------------------------------------------------------
