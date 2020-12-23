%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:28:47 EST 2020

% Result     : Theorem 15.82s
% Output     : CNFRefutation 15.82s
% Verified   : 
% Statistics : Number of formulae       :  170 (1288 expanded)
%              Number of clauses        :   99 ( 285 expanded)
%              Number of leaves         :   16 ( 452 expanded)
%              Depth                    :   22
%              Number of atoms          :  690 (7404 expanded)
%              Number of equality atoms :  163 ( 425 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
          | ~ r2_hidden(sK1(X0,X1,X2),X0)
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(sK1(X0,X1,X2),X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            | ~ r2_hidden(sK1(X0,X1,X2),X0)
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK1(X0,X1,X2),X1)
              & r2_hidden(sK1(X0,X1,X2),X0) )
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f30,f31])).

fof(f48,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f75,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k1_setfam_1(k2_tarski(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f48,f53])).

fof(f80,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k1_setfam_1(k2_tarski(X0,X1)))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f75])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_pre_topc(X2,X0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k3_xboole_0(X1,X2),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( v3_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( v3_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(k1_setfam_1(k2_tarski(X1,X2)),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(definition_unfolding,[],[f57,f53])).

fof(f10,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))
          & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
     => ( ~ m1_subset_1(k3_xboole_0(X2,sK6),u1_struct_0(k9_yellow_6(X0,X1)))
        & m1_subset_1(sK6,u1_struct_0(k9_yellow_6(X0,X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
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

fof(f39,plain,(
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

fof(f38,plain,
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

fof(f42,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK5,sK6),u1_struct_0(k9_yellow_6(sK3,sK4)))
    & m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4)))
    & m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK3,sK4)))
    & m1_subset_1(sK4,u1_struct_0(sK3))
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f23,f41,f40,f39,f38])).

fof(f67,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f66,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f24])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f46,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f77,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k1_setfam_1(k2_tarski(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f46,f53])).

fof(f82,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k1_setfam_1(k2_tarski(X0,X1))) ) ),
    inference(equality_resolution,[],[f77])).

fof(f43,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f9,axiom,(
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

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ v3_pre_topc(X2,X0)
      | ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f65,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f71,plain,(
    ~ m1_subset_1(k3_xboole_0(sK5,sK6),u1_struct_0(k9_yellow_6(sK3,sK4))) ),
    inference(cnf_transformation,[],[f42])).

fof(f79,plain,(
    ~ m1_subset_1(k1_setfam_1(k2_tarski(sK5,sK6)),u1_struct_0(k9_yellow_6(sK3,sK4))) ),
    inference(definition_unfolding,[],[f71,f53])).

fof(f70,plain,(
    m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4))) ),
    inference(cnf_transformation,[],[f42])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
             => ? [X3] :
                  ( v3_pre_topc(X3,X0)
                  & r2_hidden(X1,X3)
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( v3_pre_topc(X3,X0)
                  & r2_hidden(X1,X3)
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( v3_pre_topc(X3,X0)
                  & r2_hidden(X1,X3)
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( v3_pre_topc(X3,X0)
          & r2_hidden(X1,X3)
          & X2 = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( v3_pre_topc(sK2(X0,X1,X2),X0)
        & r2_hidden(X1,sK2(X0,X1,X2))
        & sK2(X0,X1,X2) = X2
        & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v3_pre_topc(sK2(X0,X1,X2),X0)
                & r2_hidden(X1,sK2(X0,X1,X2))
                & sK2(X0,X1,X2) = X2
                & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f19,f34])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( sK2(X0,X1,X2) = X2
      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f68,plain,(
    m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f42])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f47,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f76,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k1_setfam_1(k2_tarski(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f47,f53])).

fof(f81,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k1_setfam_1(k2_tarski(X0,X1))) ) ),
    inference(equality_resolution,[],[f76])).

fof(f69,plain,(
    m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK3,sK4))) ),
    inference(cnf_transformation,[],[f42])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(sK2(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,sK2(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k1_setfam_1(k2_tarski(X2,X1))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_2979,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X0,k1_setfam_1(k2_tarski(X1,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_13,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ v3_pre_topc(X2,X1)
    | v3_pre_topc(k1_setfam_1(k2_tarski(X2,X0)),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_25,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_633,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ v3_pre_topc(X2,X1)
    | v3_pre_topc(k1_setfam_1(k2_tarski(X2,X0)),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_25])).

cnf(c_634,plain,
    ( ~ v3_pre_topc(X0,sK3)
    | ~ v3_pre_topc(X1,sK3)
    | v3_pre_topc(k1_setfam_1(k2_tarski(X1,X0)),sK3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_633])).

cnf(c_26,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_638,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | v3_pre_topc(k1_setfam_1(k2_tarski(X1,X0)),sK3)
    | ~ v3_pre_topc(X1,sK3)
    | ~ v3_pre_topc(X0,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_634,c_26])).

cnf(c_639,plain,
    ( ~ v3_pre_topc(X0,sK3)
    | ~ v3_pre_topc(X1,sK3)
    | v3_pre_topc(k1_setfam_1(k2_tarski(X1,X0)),sK3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(renaming,[status(thm)],[c_638])).

cnf(c_2960,plain,
    ( v3_pre_topc(X0,sK3) != iProver_top
    | v3_pre_topc(X1,sK3) != iProver_top
    | v3_pre_topc(k1_setfam_1(k2_tarski(X1,X0)),sK3) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_639])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_2984,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_8,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_2977,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k1_setfam_1(k2_tarski(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3471,plain,
    ( r2_hidden(sK0(k1_setfam_1(k2_tarski(X0,X1)),X2),X0) = iProver_top
    | r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2984,c_2977])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_2983,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_4443,plain,
    ( r2_hidden(sK0(k1_setfam_1(k2_tarski(X0,X1)),X2),X3) = iProver_top
    | r1_tarski(X0,X3) != iProver_top
    | r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3471,c_2983])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_2985,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_7060,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_setfam_1(k2_tarski(X0,X2)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_4443,c_2985])).

cnf(c_10,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2976,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3267,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2984,c_2985])).

cnf(c_18,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_27,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_510,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_27])).

cnf(c_511,plain,
    ( ~ v3_pre_topc(X0,sK3)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X1,X0)
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK3,X1)))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_510])).

cnf(c_515,plain,
    ( ~ v3_pre_topc(X0,sK3)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X1,X0)
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK3,X1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_511,c_26,c_25])).

cnf(c_12,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_531,plain,
    ( ~ v3_pre_topc(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X1,X0)
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK3,X1))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_515,c_12])).

cnf(c_2964,plain,
    ( v3_pre_topc(X0,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(X1,X0) != iProver_top
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK3,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_531])).

cnf(c_2974,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3566,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r1_tarski(X2,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2976,c_2974])).

cnf(c_4598,plain,
    ( v3_pre_topc(X0,sK3) != iProver_top
    | m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r1_tarski(u1_struct_0(k9_yellow_6(sK3,X2)),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2964,c_3566])).

cnf(c_4848,plain,
    ( v3_pre_topc(X0,sK3) != iProver_top
    | m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK3,X1))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3267,c_4598])).

cnf(c_21,negated_conjecture,
    ( ~ m1_subset_1(k1_setfam_1(k2_tarski(sK5,sK6)),u1_struct_0(k9_yellow_6(sK3,sK4))) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_2973,plain,
    ( m1_subset_1(k1_setfam_1(k2_tarski(sK5,sK6)),u1_struct_0(k9_yellow_6(sK3,sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_64960,plain,
    ( v3_pre_topc(k1_setfam_1(k2_tarski(sK5,sK6)),sK3) != iProver_top
    | m1_subset_1(k1_setfam_1(k2_tarski(sK5,sK6)),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(sK4,k1_setfam_1(k2_tarski(sK5,sK6))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4848,c_2973])).

cnf(c_65072,plain,
    ( v3_pre_topc(k1_setfam_1(k2_tarski(sK5,sK6)),sK3) != iProver_top
    | r2_hidden(sK4,k1_setfam_1(k2_tarski(sK5,sK6))) != iProver_top
    | r1_tarski(k1_setfam_1(k2_tarski(sK5,sK6)),u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2976,c_64960])).

cnf(c_65082,plain,
    ( v3_pre_topc(k1_setfam_1(k2_tarski(sK5,sK6)),sK3) != iProver_top
    | r2_hidden(sK4,k1_setfam_1(k2_tarski(sK5,sK6))) != iProver_top
    | r1_tarski(sK5,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7060,c_65072])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2972,plain,
    ( m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK2(X1,X0,X2) = X2 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_560,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK2(X1,X0,X2) = X2
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_27])).

cnf(c_561,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK3,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | sK2(sK3,X1,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_560])).

cnf(c_565,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK3,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | sK2(sK3,X1,X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_561,c_26,c_25])).

cnf(c_2962,plain,
    ( sK2(sK3,X0,X1) = X1
    | m1_subset_1(X1,u1_struct_0(k9_yellow_6(sK3,X0))) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_565])).

cnf(c_3175,plain,
    ( sK2(sK3,sK4,sK6) = sK6
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2972,c_2962])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_31,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3194,plain,
    ( sK2(sK3,sK4,sK6) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3175,c_31])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
    | m1_subset_1(sK2(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_539,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
    | m1_subset_1(sK2(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_27])).

cnf(c_540,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK3,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | m1_subset_1(sK2(sK3,X1,X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_539])).

cnf(c_544,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK3,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | m1_subset_1(sK2(sK3,X1,X0),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_540,c_26,c_25])).

cnf(c_2963,plain,
    ( m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK3,X1))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK2(sK3,X1,X0),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_544])).

cnf(c_3303,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3194,c_2963])).

cnf(c_33,plain,
    ( m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3607,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3303,c_31,c_33])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2975,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3612,plain,
    ( r1_tarski(sK6,u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3607,c_2975])).

cnf(c_7,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_setfam_1(k2_tarski(X2,X1))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_2978,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k1_setfam_1(k2_tarski(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3489,plain,
    ( r2_hidden(sK0(k1_setfam_1(k2_tarski(X0,X1)),X2),X1) = iProver_top
    | r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2984,c_2978])).

cnf(c_4515,plain,
    ( r2_hidden(sK0(k1_setfam_1(k2_tarski(X0,X1)),X2),X3) = iProver_top
    | r1_tarski(X1,X3) != iProver_top
    | r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3489,c_2983])).

cnf(c_7584,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_setfam_1(k2_tarski(X2,X0)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_4515,c_2985])).

cnf(c_65083,plain,
    ( v3_pre_topc(k1_setfam_1(k2_tarski(sK5,sK6)),sK3) != iProver_top
    | r2_hidden(sK4,k1_setfam_1(k2_tarski(sK5,sK6))) != iProver_top
    | r1_tarski(sK6,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7584,c_65072])).

cnf(c_73060,plain,
    ( r2_hidden(sK4,k1_setfam_1(k2_tarski(sK5,sK6))) != iProver_top
    | v3_pre_topc(k1_setfam_1(k2_tarski(sK5,sK6)),sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_65082,c_3612,c_65083])).

cnf(c_73061,plain,
    ( v3_pre_topc(k1_setfam_1(k2_tarski(sK5,sK6)),sK3) != iProver_top
    | r2_hidden(sK4,k1_setfam_1(k2_tarski(sK5,sK6))) != iProver_top ),
    inference(renaming,[status(thm)],[c_73060])).

cnf(c_73066,plain,
    ( v3_pre_topc(sK6,sK3) != iProver_top
    | v3_pre_topc(sK5,sK3) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(sK4,k1_setfam_1(k2_tarski(sK5,sK6))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2960,c_73061])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK3,sK4))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_32,plain,
    ( m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2971,plain,
    ( m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_14,plain,
    ( v3_pre_topc(sK2(X0,X1,X2),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_441,plain,
    ( v3_pre_topc(sK2(X0,X1,X2),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_27])).

cnf(c_442,plain,
    ( v3_pre_topc(sK2(sK3,X0,X1),sK3)
    | ~ m1_subset_1(X1,u1_struct_0(k9_yellow_6(sK3,X0)))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_441])).

cnf(c_446,plain,
    ( v3_pre_topc(sK2(sK3,X0,X1),sK3)
    | ~ m1_subset_1(X1,u1_struct_0(k9_yellow_6(sK3,X0)))
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_442,c_26,c_25])).

cnf(c_2967,plain,
    ( v3_pre_topc(sK2(sK3,X0,X1),sK3) = iProver_top
    | m1_subset_1(X1,u1_struct_0(k9_yellow_6(sK3,X0))) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_446])).

cnf(c_3276,plain,
    ( v3_pre_topc(sK2(sK3,sK4,sK5),sK3) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2971,c_2967])).

cnf(c_3176,plain,
    ( sK2(sK3,sK4,sK5) = sK5
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2971,c_2962])).

cnf(c_3203,plain,
    ( sK2(sK3,sK4,sK5) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3176,c_31])).

cnf(c_3279,plain,
    ( v3_pre_topc(sK5,sK3) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3276,c_3203])).

cnf(c_3275,plain,
    ( v3_pre_topc(sK2(sK3,sK4,sK6),sK3) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2972,c_2967])).

cnf(c_3284,plain,
    ( v3_pre_topc(sK6,sK3) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3275,c_3194])).

cnf(c_3304,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK3,sK4))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3203,c_2963])).

cnf(c_73083,plain,
    ( r2_hidden(sK4,k1_setfam_1(k2_tarski(sK5,sK6))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_73066,c_31,c_32,c_33,c_3279,c_3284,c_3303,c_3304])).

cnf(c_73088,plain,
    ( r2_hidden(sK4,sK6) != iProver_top
    | r2_hidden(sK4,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2979,c_73083])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
    | r2_hidden(X0,sK2(X1,X0,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_581,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
    | r2_hidden(X0,sK2(X1,X0,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_27])).

cnf(c_582,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK3,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | r2_hidden(X1,sK2(sK3,X1,X0))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_581])).

cnf(c_586,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK3,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | r2_hidden(X1,sK2(sK3,X1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_582,c_26,c_25])).

cnf(c_2961,plain,
    ( m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK3,X1))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X1,sK2(sK3,X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_586])).

cnf(c_3215,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK4,sK2(sK3,sK4,sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2972,c_2961])).

cnf(c_3224,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK4,sK6) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3215,c_3194])).

cnf(c_3216,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK4,sK2(sK3,sK4,sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2971,c_2961])).

cnf(c_3219,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK4,sK5) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3216,c_3203])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_73088,c_3224,c_3219,c_31])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:20:15 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 15.82/2.46  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.82/2.46  
% 15.82/2.46  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.82/2.46  
% 15.82/2.46  ------  iProver source info
% 15.82/2.46  
% 15.82/2.46  git: date: 2020-06-30 10:37:57 +0100
% 15.82/2.46  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.82/2.46  git: non_committed_changes: false
% 15.82/2.46  git: last_make_outside_of_git: false
% 15.82/2.46  
% 15.82/2.46  ------ 
% 15.82/2.46  ------ Parsing...
% 15.82/2.46  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.82/2.46  
% 15.82/2.46  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 15.82/2.46  
% 15.82/2.46  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.82/2.46  
% 15.82/2.46  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.82/2.46  ------ Proving...
% 15.82/2.46  ------ Problem Properties 
% 15.82/2.46  
% 15.82/2.46  
% 15.82/2.46  clauses                                 24
% 15.82/2.46  conjectures                             4
% 15.82/2.46  EPR                                     1
% 15.82/2.46  Horn                                    21
% 15.82/2.46  unary                                   4
% 15.82/2.46  binary                                  6
% 15.82/2.46  lits                                    64
% 15.82/2.46  lits eq                                 4
% 15.82/2.46  fd_pure                                 0
% 15.82/2.46  fd_pseudo                               0
% 15.82/2.46  fd_cond                                 0
% 15.82/2.46  fd_pseudo_cond                          3
% 15.82/2.46  AC symbols                              0
% 15.82/2.46  
% 15.82/2.46  ------ Input Options Time Limit: Unbounded
% 15.82/2.46  
% 15.82/2.46  
% 15.82/2.46  
% 15.82/2.46  
% 15.82/2.46  ------ Preprocessing...
% 15.82/2.46  
% 15.82/2.46  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 15.82/2.46  Current options:
% 15.82/2.46  ------ 
% 15.82/2.46  
% 15.82/2.46  
% 15.82/2.46  
% 15.82/2.46  
% 15.82/2.46  ------ Proving...
% 15.82/2.46  
% 15.82/2.46  
% 15.82/2.46  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.82/2.46  
% 15.82/2.46  ------ Proving...
% 15.82/2.46  
% 15.82/2.46  
% 15.82/2.46  ------ Preprocessing...
% 15.82/2.46  
% 15.82/2.46  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.82/2.46  
% 15.82/2.46  ------ Proving...
% 15.82/2.46  
% 15.82/2.46  
% 15.82/2.46  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.82/2.46  
% 15.82/2.46  ------ Proving...
% 15.82/2.46  
% 15.82/2.46  
% 15.82/2.46  ------ Preprocessing...
% 15.82/2.46  
% 15.82/2.46  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.82/2.46  
% 15.82/2.46  ------ Proving...
% 15.82/2.46  
% 15.82/2.46  
% 15.82/2.46  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.82/2.46  
% 15.82/2.46  ------ Proving...
% 15.82/2.46  
% 15.82/2.46  
% 15.82/2.46  ------ Preprocessing...
% 15.82/2.46  
% 15.82/2.46  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.82/2.46  
% 15.82/2.46  ------ Proving...
% 15.82/2.46  
% 15.82/2.46  
% 15.82/2.46  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.82/2.46  
% 15.82/2.46  ------ Proving...
% 15.82/2.46  
% 15.82/2.46  
% 15.82/2.46  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.82/2.46  
% 15.82/2.46  ------ Proving...
% 15.82/2.46  
% 15.82/2.46  
% 15.82/2.46  % SZS status Theorem for theBenchmark.p
% 15.82/2.46  
% 15.82/2.46  % SZS output start CNFRefutation for theBenchmark.p
% 15.82/2.46  
% 15.82/2.46  fof(f2,axiom,(
% 15.82/2.46    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 15.82/2.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.82/2.46  
% 15.82/2.46  fof(f28,plain,(
% 15.82/2.46    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 15.82/2.46    inference(nnf_transformation,[],[f2])).
% 15.82/2.46  
% 15.82/2.46  fof(f29,plain,(
% 15.82/2.46    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 15.82/2.46    inference(flattening,[],[f28])).
% 15.82/2.46  
% 15.82/2.46  fof(f30,plain,(
% 15.82/2.46    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 15.82/2.46    inference(rectify,[],[f29])).
% 15.82/2.46  
% 15.82/2.46  fof(f31,plain,(
% 15.82/2.46    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 15.82/2.46    introduced(choice_axiom,[])).
% 15.82/2.46  
% 15.82/2.46  fof(f32,plain,(
% 15.82/2.46    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 15.82/2.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f30,f31])).
% 15.82/2.46  
% 15.82/2.46  fof(f48,plain,(
% 15.82/2.46    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k3_xboole_0(X0,X1) != X2) )),
% 15.82/2.46    inference(cnf_transformation,[],[f32])).
% 15.82/2.46  
% 15.82/2.46  fof(f4,axiom,(
% 15.82/2.46    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 15.82/2.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.82/2.46  
% 15.82/2.46  fof(f53,plain,(
% 15.82/2.46    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 15.82/2.46    inference(cnf_transformation,[],[f4])).
% 15.82/2.46  
% 15.82/2.46  fof(f75,plain,(
% 15.82/2.46    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k1_setfam_1(k2_tarski(X0,X1)) != X2) )),
% 15.82/2.46    inference(definition_unfolding,[],[f48,f53])).
% 15.82/2.46  
% 15.82/2.46  fof(f80,plain,(
% 15.82/2.46    ( ! [X4,X0,X1] : (r2_hidden(X4,k1_setfam_1(k2_tarski(X0,X1))) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 15.82/2.46    inference(equality_resolution,[],[f75])).
% 15.82/2.46  
% 15.82/2.46  fof(f7,axiom,(
% 15.82/2.46    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X2,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k3_xboole_0(X1,X2),X0))),
% 15.82/2.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.82/2.46  
% 15.82/2.46  fof(f16,plain,(
% 15.82/2.46    ! [X0,X1,X2] : (v3_pre_topc(k3_xboole_0(X1,X2),X0) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 15.82/2.46    inference(ennf_transformation,[],[f7])).
% 15.82/2.46  
% 15.82/2.46  fof(f17,plain,(
% 15.82/2.46    ! [X0,X1,X2] : (v3_pre_topc(k3_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 15.82/2.46    inference(flattening,[],[f16])).
% 15.82/2.46  
% 15.82/2.46  fof(f57,plain,(
% 15.82/2.46    ( ! [X2,X0,X1] : (v3_pre_topc(k3_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 15.82/2.46    inference(cnf_transformation,[],[f17])).
% 15.82/2.46  
% 15.82/2.46  fof(f78,plain,(
% 15.82/2.46    ( ! [X2,X0,X1] : (v3_pre_topc(k1_setfam_1(k2_tarski(X1,X2)),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 15.82/2.46    inference(definition_unfolding,[],[f57,f53])).
% 15.82/2.46  
% 15.82/2.46  fof(f10,conjecture,(
% 15.82/2.46    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) => m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))))))),
% 15.82/2.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.82/2.46  
% 15.82/2.46  fof(f11,negated_conjecture,(
% 15.82/2.46    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) => m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))))))),
% 15.82/2.46    inference(negated_conjecture,[],[f10])).
% 15.82/2.46  
% 15.82/2.46  fof(f22,plain,(
% 15.82/2.46    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 15.82/2.46    inference(ennf_transformation,[],[f11])).
% 15.82/2.46  
% 15.82/2.46  fof(f23,plain,(
% 15.82/2.46    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 15.82/2.46    inference(flattening,[],[f22])).
% 15.82/2.46  
% 15.82/2.46  fof(f41,plain,(
% 15.82/2.46    ( ! [X2,X0,X1] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) => (~m1_subset_1(k3_xboole_0(X2,sK6),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(sK6,u1_struct_0(k9_yellow_6(X0,X1))))) )),
% 15.82/2.46    introduced(choice_axiom,[])).
% 15.82/2.46  
% 15.82/2.46  fof(f40,plain,(
% 15.82/2.46    ( ! [X0,X1] : (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) => (? [X3] : (~m1_subset_1(k3_xboole_0(sK5,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(sK5,u1_struct_0(k9_yellow_6(X0,X1))))) )),
% 15.82/2.46    introduced(choice_axiom,[])).
% 15.82/2.46  
% 15.82/2.46  fof(f39,plain,(
% 15.82/2.46    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,sK4))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,sK4)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,sK4)))) & m1_subset_1(sK4,u1_struct_0(X0)))) )),
% 15.82/2.46    introduced(choice_axiom,[])).
% 15.82/2.46  
% 15.82/2.46  fof(f38,plain,(
% 15.82/2.46    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK3,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK3,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK3,X1)))) & m1_subset_1(X1,u1_struct_0(sK3))) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 15.82/2.46    introduced(choice_axiom,[])).
% 15.82/2.46  
% 15.82/2.46  fof(f42,plain,(
% 15.82/2.46    (((~m1_subset_1(k3_xboole_0(sK5,sK6),u1_struct_0(k9_yellow_6(sK3,sK4))) & m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4)))) & m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK3,sK4)))) & m1_subset_1(sK4,u1_struct_0(sK3))) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 15.82/2.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f23,f41,f40,f39,f38])).
% 15.82/2.46  
% 15.82/2.46  fof(f67,plain,(
% 15.82/2.46    l1_pre_topc(sK3)),
% 15.82/2.46    inference(cnf_transformation,[],[f42])).
% 15.82/2.46  
% 15.82/2.46  fof(f66,plain,(
% 15.82/2.46    v2_pre_topc(sK3)),
% 15.82/2.46    inference(cnf_transformation,[],[f42])).
% 15.82/2.46  
% 15.82/2.46  fof(f1,axiom,(
% 15.82/2.46    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 15.82/2.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.82/2.46  
% 15.82/2.46  fof(f12,plain,(
% 15.82/2.46    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 15.82/2.46    inference(ennf_transformation,[],[f1])).
% 15.82/2.46  
% 15.82/2.46  fof(f24,plain,(
% 15.82/2.46    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 15.82/2.46    inference(nnf_transformation,[],[f12])).
% 15.82/2.46  
% 15.82/2.46  fof(f25,plain,(
% 15.82/2.46    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 15.82/2.46    inference(rectify,[],[f24])).
% 15.82/2.46  
% 15.82/2.46  fof(f26,plain,(
% 15.82/2.46    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 15.82/2.46    introduced(choice_axiom,[])).
% 15.82/2.46  
% 15.82/2.46  fof(f27,plain,(
% 15.82/2.46    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 15.82/2.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).
% 15.82/2.46  
% 15.82/2.46  fof(f44,plain,(
% 15.82/2.46    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 15.82/2.46    inference(cnf_transformation,[],[f27])).
% 15.82/2.46  
% 15.82/2.46  fof(f46,plain,(
% 15.82/2.46    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 15.82/2.46    inference(cnf_transformation,[],[f32])).
% 15.82/2.46  
% 15.82/2.46  fof(f77,plain,(
% 15.82/2.46    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k1_setfam_1(k2_tarski(X0,X1)) != X2) )),
% 15.82/2.46    inference(definition_unfolding,[],[f46,f53])).
% 15.82/2.46  
% 15.82/2.46  fof(f82,plain,(
% 15.82/2.46    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 15.82/2.46    inference(equality_resolution,[],[f77])).
% 15.82/2.46  
% 15.82/2.46  fof(f43,plain,(
% 15.82/2.46    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 15.82/2.46    inference(cnf_transformation,[],[f27])).
% 15.82/2.46  
% 15.82/2.46  fof(f45,plain,(
% 15.82/2.46    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 15.82/2.46    inference(cnf_transformation,[],[f27])).
% 15.82/2.46  
% 15.82/2.46  fof(f5,axiom,(
% 15.82/2.46    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 15.82/2.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.82/2.46  
% 15.82/2.46  fof(f33,plain,(
% 15.82/2.46    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 15.82/2.46    inference(nnf_transformation,[],[f5])).
% 15.82/2.46  
% 15.82/2.46  fof(f55,plain,(
% 15.82/2.46    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 15.82/2.46    inference(cnf_transformation,[],[f33])).
% 15.82/2.46  
% 15.82/2.46  fof(f9,axiom,(
% 15.82/2.46    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))))))),
% 15.82/2.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.82/2.46  
% 15.82/2.46  fof(f20,plain,(
% 15.82/2.46    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 15.82/2.46    inference(ennf_transformation,[],[f9])).
% 15.82/2.46  
% 15.82/2.46  fof(f21,plain,(
% 15.82/2.46    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 15.82/2.46    inference(flattening,[],[f20])).
% 15.82/2.46  
% 15.82/2.46  fof(f36,plain,(
% 15.82/2.46    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | (~v3_pre_topc(X2,X0) | ~r2_hidden(X1,X2))) & ((v3_pre_topc(X2,X0) & r2_hidden(X1,X2)) | ~r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 15.82/2.46    inference(nnf_transformation,[],[f21])).
% 15.82/2.46  
% 15.82/2.46  fof(f37,plain,(
% 15.82/2.46    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~v3_pre_topc(X2,X0) | ~r2_hidden(X1,X2)) & ((v3_pre_topc(X2,X0) & r2_hidden(X1,X2)) | ~r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 15.82/2.46    inference(flattening,[],[f36])).
% 15.82/2.46  
% 15.82/2.46  fof(f64,plain,(
% 15.82/2.46    ( ! [X2,X0,X1] : (r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~v3_pre_topc(X2,X0) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 15.82/2.46    inference(cnf_transformation,[],[f37])).
% 15.82/2.46  
% 15.82/2.46  fof(f65,plain,(
% 15.82/2.46    ~v2_struct_0(sK3)),
% 15.82/2.46    inference(cnf_transformation,[],[f42])).
% 15.82/2.46  
% 15.82/2.46  fof(f6,axiom,(
% 15.82/2.46    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 15.82/2.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.82/2.46  
% 15.82/2.46  fof(f14,plain,(
% 15.82/2.46    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 15.82/2.46    inference(ennf_transformation,[],[f6])).
% 15.82/2.46  
% 15.82/2.46  fof(f15,plain,(
% 15.82/2.46    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 15.82/2.46    inference(flattening,[],[f14])).
% 15.82/2.46  
% 15.82/2.46  fof(f56,plain,(
% 15.82/2.46    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 15.82/2.46    inference(cnf_transformation,[],[f15])).
% 15.82/2.46  
% 15.82/2.46  fof(f71,plain,(
% 15.82/2.46    ~m1_subset_1(k3_xboole_0(sK5,sK6),u1_struct_0(k9_yellow_6(sK3,sK4)))),
% 15.82/2.46    inference(cnf_transformation,[],[f42])).
% 15.82/2.46  
% 15.82/2.46  fof(f79,plain,(
% 15.82/2.46    ~m1_subset_1(k1_setfam_1(k2_tarski(sK5,sK6)),u1_struct_0(k9_yellow_6(sK3,sK4)))),
% 15.82/2.46    inference(definition_unfolding,[],[f71,f53])).
% 15.82/2.46  
% 15.82/2.46  fof(f70,plain,(
% 15.82/2.46    m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4)))),
% 15.82/2.46    inference(cnf_transformation,[],[f42])).
% 15.82/2.46  
% 15.82/2.46  fof(f8,axiom,(
% 15.82/2.46    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ? [X3] : (v3_pre_topc(X3,X0) & r2_hidden(X1,X3) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))))),
% 15.82/2.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.82/2.46  
% 15.82/2.46  fof(f18,plain,(
% 15.82/2.46    ! [X0] : (! [X1] : (! [X2] : (? [X3] : (v3_pre_topc(X3,X0) & r2_hidden(X1,X3) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 15.82/2.46    inference(ennf_transformation,[],[f8])).
% 15.82/2.46  
% 15.82/2.46  fof(f19,plain,(
% 15.82/2.46    ! [X0] : (! [X1] : (! [X2] : (? [X3] : (v3_pre_topc(X3,X0) & r2_hidden(X1,X3) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 15.82/2.46    inference(flattening,[],[f18])).
% 15.82/2.46  
% 15.82/2.46  fof(f34,plain,(
% 15.82/2.46    ! [X2,X1,X0] : (? [X3] : (v3_pre_topc(X3,X0) & r2_hidden(X1,X3) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (v3_pre_topc(sK2(X0,X1,X2),X0) & r2_hidden(X1,sK2(X0,X1,X2)) & sK2(X0,X1,X2) = X2 & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 15.82/2.46    introduced(choice_axiom,[])).
% 15.82/2.46  
% 15.82/2.46  fof(f35,plain,(
% 15.82/2.46    ! [X0] : (! [X1] : (! [X2] : ((v3_pre_topc(sK2(X0,X1,X2),X0) & r2_hidden(X1,sK2(X0,X1,X2)) & sK2(X0,X1,X2) = X2 & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 15.82/2.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f19,f34])).
% 15.82/2.46  
% 15.82/2.46  fof(f59,plain,(
% 15.82/2.46    ( ! [X2,X0,X1] : (sK2(X0,X1,X2) = X2 | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 15.82/2.46    inference(cnf_transformation,[],[f35])).
% 15.82/2.46  
% 15.82/2.46  fof(f68,plain,(
% 15.82/2.46    m1_subset_1(sK4,u1_struct_0(sK3))),
% 15.82/2.46    inference(cnf_transformation,[],[f42])).
% 15.82/2.46  
% 15.82/2.46  fof(f58,plain,(
% 15.82/2.46    ( ! [X2,X0,X1] : (m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 15.82/2.46    inference(cnf_transformation,[],[f35])).
% 15.82/2.46  
% 15.82/2.46  fof(f54,plain,(
% 15.82/2.46    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 15.82/2.46    inference(cnf_transformation,[],[f33])).
% 15.82/2.46  
% 15.82/2.46  fof(f47,plain,(
% 15.82/2.46    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 15.82/2.46    inference(cnf_transformation,[],[f32])).
% 15.82/2.46  
% 15.82/2.46  fof(f76,plain,(
% 15.82/2.46    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k1_setfam_1(k2_tarski(X0,X1)) != X2) )),
% 15.82/2.46    inference(definition_unfolding,[],[f47,f53])).
% 15.82/2.46  
% 15.82/2.46  fof(f81,plain,(
% 15.82/2.46    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 15.82/2.46    inference(equality_resolution,[],[f76])).
% 15.82/2.46  
% 15.82/2.46  fof(f69,plain,(
% 15.82/2.46    m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK3,sK4)))),
% 15.82/2.46    inference(cnf_transformation,[],[f42])).
% 15.82/2.46  
% 15.82/2.46  fof(f61,plain,(
% 15.82/2.46    ( ! [X2,X0,X1] : (v3_pre_topc(sK2(X0,X1,X2),X0) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 15.82/2.46    inference(cnf_transformation,[],[f35])).
% 15.82/2.46  
% 15.82/2.46  fof(f60,plain,(
% 15.82/2.46    ( ! [X2,X0,X1] : (r2_hidden(X1,sK2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 15.82/2.46    inference(cnf_transformation,[],[f35])).
% 15.82/2.46  
% 15.82/2.46  cnf(c_6,plain,
% 15.82/2.46      ( ~ r2_hidden(X0,X1)
% 15.82/2.46      | ~ r2_hidden(X0,X2)
% 15.82/2.46      | r2_hidden(X0,k1_setfam_1(k2_tarski(X2,X1))) ),
% 15.82/2.46      inference(cnf_transformation,[],[f80]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_2979,plain,
% 15.82/2.46      ( r2_hidden(X0,X1) != iProver_top
% 15.82/2.46      | r2_hidden(X0,X2) != iProver_top
% 15.82/2.46      | r2_hidden(X0,k1_setfam_1(k2_tarski(X1,X2))) = iProver_top ),
% 15.82/2.46      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_13,plain,
% 15.82/2.46      ( ~ v3_pre_topc(X0,X1)
% 15.82/2.46      | ~ v3_pre_topc(X2,X1)
% 15.82/2.46      | v3_pre_topc(k1_setfam_1(k2_tarski(X2,X0)),X1)
% 15.82/2.46      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.82/2.46      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 15.82/2.46      | ~ v2_pre_topc(X1)
% 15.82/2.46      | ~ l1_pre_topc(X1) ),
% 15.82/2.46      inference(cnf_transformation,[],[f78]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_25,negated_conjecture,
% 15.82/2.46      ( l1_pre_topc(sK3) ),
% 15.82/2.46      inference(cnf_transformation,[],[f67]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_633,plain,
% 15.82/2.46      ( ~ v3_pre_topc(X0,X1)
% 15.82/2.46      | ~ v3_pre_topc(X2,X1)
% 15.82/2.46      | v3_pre_topc(k1_setfam_1(k2_tarski(X2,X0)),X1)
% 15.82/2.46      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.82/2.46      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 15.82/2.46      | ~ v2_pre_topc(X1)
% 15.82/2.46      | sK3 != X1 ),
% 15.82/2.46      inference(resolution_lifted,[status(thm)],[c_13,c_25]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_634,plain,
% 15.82/2.46      ( ~ v3_pre_topc(X0,sK3)
% 15.82/2.46      | ~ v3_pre_topc(X1,sK3)
% 15.82/2.46      | v3_pre_topc(k1_setfam_1(k2_tarski(X1,X0)),sK3)
% 15.82/2.46      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 15.82/2.46      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 15.82/2.46      | ~ v2_pre_topc(sK3) ),
% 15.82/2.46      inference(unflattening,[status(thm)],[c_633]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_26,negated_conjecture,
% 15.82/2.46      ( v2_pre_topc(sK3) ),
% 15.82/2.46      inference(cnf_transformation,[],[f66]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_638,plain,
% 15.82/2.46      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 15.82/2.46      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 15.82/2.46      | v3_pre_topc(k1_setfam_1(k2_tarski(X1,X0)),sK3)
% 15.82/2.46      | ~ v3_pre_topc(X1,sK3)
% 15.82/2.46      | ~ v3_pre_topc(X0,sK3) ),
% 15.82/2.46      inference(global_propositional_subsumption,
% 15.82/2.46                [status(thm)],
% 15.82/2.46                [c_634,c_26]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_639,plain,
% 15.82/2.46      ( ~ v3_pre_topc(X0,sK3)
% 15.82/2.46      | ~ v3_pre_topc(X1,sK3)
% 15.82/2.46      | v3_pre_topc(k1_setfam_1(k2_tarski(X1,X0)),sK3)
% 15.82/2.46      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 15.82/2.46      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 15.82/2.46      inference(renaming,[status(thm)],[c_638]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_2960,plain,
% 15.82/2.46      ( v3_pre_topc(X0,sK3) != iProver_top
% 15.82/2.46      | v3_pre_topc(X1,sK3) != iProver_top
% 15.82/2.46      | v3_pre_topc(k1_setfam_1(k2_tarski(X1,X0)),sK3) = iProver_top
% 15.82/2.46      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 15.82/2.46      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 15.82/2.46      inference(predicate_to_equality,[status(thm)],[c_639]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_1,plain,
% 15.82/2.46      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 15.82/2.46      inference(cnf_transformation,[],[f44]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_2984,plain,
% 15.82/2.46      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 15.82/2.46      | r1_tarski(X0,X1) = iProver_top ),
% 15.82/2.46      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_8,plain,
% 15.82/2.46      ( r2_hidden(X0,X1)
% 15.82/2.46      | ~ r2_hidden(X0,k1_setfam_1(k2_tarski(X1,X2))) ),
% 15.82/2.46      inference(cnf_transformation,[],[f82]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_2977,plain,
% 15.82/2.46      ( r2_hidden(X0,X1) = iProver_top
% 15.82/2.46      | r2_hidden(X0,k1_setfam_1(k2_tarski(X1,X2))) != iProver_top ),
% 15.82/2.46      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_3471,plain,
% 15.82/2.46      ( r2_hidden(sK0(k1_setfam_1(k2_tarski(X0,X1)),X2),X0) = iProver_top
% 15.82/2.46      | r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X2) = iProver_top ),
% 15.82/2.46      inference(superposition,[status(thm)],[c_2984,c_2977]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_2,plain,
% 15.82/2.46      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 15.82/2.46      inference(cnf_transformation,[],[f43]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_2983,plain,
% 15.82/2.46      ( r2_hidden(X0,X1) != iProver_top
% 15.82/2.46      | r2_hidden(X0,X2) = iProver_top
% 15.82/2.46      | r1_tarski(X1,X2) != iProver_top ),
% 15.82/2.46      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_4443,plain,
% 15.82/2.46      ( r2_hidden(sK0(k1_setfam_1(k2_tarski(X0,X1)),X2),X3) = iProver_top
% 15.82/2.46      | r1_tarski(X0,X3) != iProver_top
% 15.82/2.46      | r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X2) = iProver_top ),
% 15.82/2.46      inference(superposition,[status(thm)],[c_3471,c_2983]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_0,plain,
% 15.82/2.46      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 15.82/2.46      inference(cnf_transformation,[],[f45]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_2985,plain,
% 15.82/2.46      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 15.82/2.46      | r1_tarski(X0,X1) = iProver_top ),
% 15.82/2.46      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_7060,plain,
% 15.82/2.46      ( r1_tarski(X0,X1) != iProver_top
% 15.82/2.46      | r1_tarski(k1_setfam_1(k2_tarski(X0,X2)),X1) = iProver_top ),
% 15.82/2.46      inference(superposition,[status(thm)],[c_4443,c_2985]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_10,plain,
% 15.82/2.46      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 15.82/2.46      inference(cnf_transformation,[],[f55]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_2976,plain,
% 15.82/2.46      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 15.82/2.46      | r1_tarski(X0,X1) != iProver_top ),
% 15.82/2.46      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_3267,plain,
% 15.82/2.46      ( r1_tarski(X0,X0) = iProver_top ),
% 15.82/2.46      inference(superposition,[status(thm)],[c_2984,c_2985]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_18,plain,
% 15.82/2.46      ( ~ v3_pre_topc(X0,X1)
% 15.82/2.46      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 15.82/2.46      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.82/2.46      | ~ r2_hidden(X2,X0)
% 15.82/2.46      | r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
% 15.82/2.46      | v2_struct_0(X1)
% 15.82/2.46      | ~ v2_pre_topc(X1)
% 15.82/2.46      | ~ l1_pre_topc(X1) ),
% 15.82/2.46      inference(cnf_transformation,[],[f64]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_27,negated_conjecture,
% 15.82/2.46      ( ~ v2_struct_0(sK3) ),
% 15.82/2.46      inference(cnf_transformation,[],[f65]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_510,plain,
% 15.82/2.46      ( ~ v3_pre_topc(X0,X1)
% 15.82/2.46      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 15.82/2.46      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.82/2.46      | ~ r2_hidden(X2,X0)
% 15.82/2.46      | r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
% 15.82/2.46      | ~ v2_pre_topc(X1)
% 15.82/2.46      | ~ l1_pre_topc(X1)
% 15.82/2.46      | sK3 != X1 ),
% 15.82/2.46      inference(resolution_lifted,[status(thm)],[c_18,c_27]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_511,plain,
% 15.82/2.46      ( ~ v3_pre_topc(X0,sK3)
% 15.82/2.46      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 15.82/2.46      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 15.82/2.46      | ~ r2_hidden(X1,X0)
% 15.82/2.46      | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK3,X1)))
% 15.82/2.46      | ~ v2_pre_topc(sK3)
% 15.82/2.46      | ~ l1_pre_topc(sK3) ),
% 15.82/2.46      inference(unflattening,[status(thm)],[c_510]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_515,plain,
% 15.82/2.46      ( ~ v3_pre_topc(X0,sK3)
% 15.82/2.46      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 15.82/2.46      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 15.82/2.46      | ~ r2_hidden(X1,X0)
% 15.82/2.46      | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK3,X1))) ),
% 15.82/2.46      inference(global_propositional_subsumption,
% 15.82/2.46                [status(thm)],
% 15.82/2.46                [c_511,c_26,c_25]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_12,plain,
% 15.82/2.46      ( m1_subset_1(X0,X1)
% 15.82/2.46      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 15.82/2.46      | ~ r2_hidden(X0,X2) ),
% 15.82/2.46      inference(cnf_transformation,[],[f56]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_531,plain,
% 15.82/2.46      ( ~ v3_pre_topc(X0,sK3)
% 15.82/2.46      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 15.82/2.46      | ~ r2_hidden(X1,X0)
% 15.82/2.46      | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK3,X1))) ),
% 15.82/2.46      inference(forward_subsumption_resolution,
% 15.82/2.46                [status(thm)],
% 15.82/2.46                [c_515,c_12]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_2964,plain,
% 15.82/2.46      ( v3_pre_topc(X0,sK3) != iProver_top
% 15.82/2.46      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 15.82/2.46      | r2_hidden(X1,X0) != iProver_top
% 15.82/2.46      | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK3,X1))) = iProver_top ),
% 15.82/2.46      inference(predicate_to_equality,[status(thm)],[c_531]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_2974,plain,
% 15.82/2.46      ( m1_subset_1(X0,X1) = iProver_top
% 15.82/2.46      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 15.82/2.46      | r2_hidden(X0,X2) != iProver_top ),
% 15.82/2.46      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_3566,plain,
% 15.82/2.46      ( m1_subset_1(X0,X1) = iProver_top
% 15.82/2.46      | r2_hidden(X0,X2) != iProver_top
% 15.82/2.46      | r1_tarski(X2,X1) != iProver_top ),
% 15.82/2.46      inference(superposition,[status(thm)],[c_2976,c_2974]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_4598,plain,
% 15.82/2.46      ( v3_pre_topc(X0,sK3) != iProver_top
% 15.82/2.46      | m1_subset_1(X0,X1) = iProver_top
% 15.82/2.46      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 15.82/2.46      | r2_hidden(X2,X0) != iProver_top
% 15.82/2.46      | r1_tarski(u1_struct_0(k9_yellow_6(sK3,X2)),X1) != iProver_top ),
% 15.82/2.46      inference(superposition,[status(thm)],[c_2964,c_3566]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_4848,plain,
% 15.82/2.46      ( v3_pre_topc(X0,sK3) != iProver_top
% 15.82/2.46      | m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK3,X1))) = iProver_top
% 15.82/2.46      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 15.82/2.46      | r2_hidden(X1,X0) != iProver_top ),
% 15.82/2.46      inference(superposition,[status(thm)],[c_3267,c_4598]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_21,negated_conjecture,
% 15.82/2.46      ( ~ m1_subset_1(k1_setfam_1(k2_tarski(sK5,sK6)),u1_struct_0(k9_yellow_6(sK3,sK4))) ),
% 15.82/2.46      inference(cnf_transformation,[],[f79]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_2973,plain,
% 15.82/2.46      ( m1_subset_1(k1_setfam_1(k2_tarski(sK5,sK6)),u1_struct_0(k9_yellow_6(sK3,sK4))) != iProver_top ),
% 15.82/2.46      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_64960,plain,
% 15.82/2.46      ( v3_pre_topc(k1_setfam_1(k2_tarski(sK5,sK6)),sK3) != iProver_top
% 15.82/2.46      | m1_subset_1(k1_setfam_1(k2_tarski(sK5,sK6)),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 15.82/2.46      | r2_hidden(sK4,k1_setfam_1(k2_tarski(sK5,sK6))) != iProver_top ),
% 15.82/2.46      inference(superposition,[status(thm)],[c_4848,c_2973]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_65072,plain,
% 15.82/2.46      ( v3_pre_topc(k1_setfam_1(k2_tarski(sK5,sK6)),sK3) != iProver_top
% 15.82/2.46      | r2_hidden(sK4,k1_setfam_1(k2_tarski(sK5,sK6))) != iProver_top
% 15.82/2.46      | r1_tarski(k1_setfam_1(k2_tarski(sK5,sK6)),u1_struct_0(sK3)) != iProver_top ),
% 15.82/2.46      inference(superposition,[status(thm)],[c_2976,c_64960]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_65082,plain,
% 15.82/2.46      ( v3_pre_topc(k1_setfam_1(k2_tarski(sK5,sK6)),sK3) != iProver_top
% 15.82/2.46      | r2_hidden(sK4,k1_setfam_1(k2_tarski(sK5,sK6))) != iProver_top
% 15.82/2.46      | r1_tarski(sK5,u1_struct_0(sK3)) != iProver_top ),
% 15.82/2.46      inference(superposition,[status(thm)],[c_7060,c_65072]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_22,negated_conjecture,
% 15.82/2.46      ( m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4))) ),
% 15.82/2.46      inference(cnf_transformation,[],[f70]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_2972,plain,
% 15.82/2.46      ( m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4))) = iProver_top ),
% 15.82/2.46      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_16,plain,
% 15.82/2.46      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 15.82/2.46      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
% 15.82/2.46      | v2_struct_0(X1)
% 15.82/2.46      | ~ v2_pre_topc(X1)
% 15.82/2.46      | ~ l1_pre_topc(X1)
% 15.82/2.46      | sK2(X1,X0,X2) = X2 ),
% 15.82/2.46      inference(cnf_transformation,[],[f59]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_560,plain,
% 15.82/2.46      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 15.82/2.46      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
% 15.82/2.46      | ~ v2_pre_topc(X1)
% 15.82/2.46      | ~ l1_pre_topc(X1)
% 15.82/2.46      | sK2(X1,X0,X2) = X2
% 15.82/2.46      | sK3 != X1 ),
% 15.82/2.46      inference(resolution_lifted,[status(thm)],[c_16,c_27]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_561,plain,
% 15.82/2.46      ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK3,X1)))
% 15.82/2.46      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 15.82/2.46      | ~ v2_pre_topc(sK3)
% 15.82/2.46      | ~ l1_pre_topc(sK3)
% 15.82/2.46      | sK2(sK3,X1,X0) = X0 ),
% 15.82/2.46      inference(unflattening,[status(thm)],[c_560]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_565,plain,
% 15.82/2.46      ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK3,X1)))
% 15.82/2.46      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 15.82/2.46      | sK2(sK3,X1,X0) = X0 ),
% 15.82/2.46      inference(global_propositional_subsumption,
% 15.82/2.46                [status(thm)],
% 15.82/2.46                [c_561,c_26,c_25]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_2962,plain,
% 15.82/2.46      ( sK2(sK3,X0,X1) = X1
% 15.82/2.46      | m1_subset_1(X1,u1_struct_0(k9_yellow_6(sK3,X0))) != iProver_top
% 15.82/2.46      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
% 15.82/2.46      inference(predicate_to_equality,[status(thm)],[c_565]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_3175,plain,
% 15.82/2.46      ( sK2(sK3,sK4,sK6) = sK6
% 15.82/2.46      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
% 15.82/2.46      inference(superposition,[status(thm)],[c_2972,c_2962]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_24,negated_conjecture,
% 15.82/2.46      ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 15.82/2.46      inference(cnf_transformation,[],[f68]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_31,plain,
% 15.82/2.46      ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
% 15.82/2.46      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_3194,plain,
% 15.82/2.46      ( sK2(sK3,sK4,sK6) = sK6 ),
% 15.82/2.46      inference(global_propositional_subsumption,
% 15.82/2.46                [status(thm)],
% 15.82/2.46                [c_3175,c_31]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_17,plain,
% 15.82/2.46      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 15.82/2.46      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
% 15.82/2.46      | m1_subset_1(sK2(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
% 15.82/2.46      | v2_struct_0(X1)
% 15.82/2.46      | ~ v2_pre_topc(X1)
% 15.82/2.46      | ~ l1_pre_topc(X1) ),
% 15.82/2.46      inference(cnf_transformation,[],[f58]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_539,plain,
% 15.82/2.46      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 15.82/2.46      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
% 15.82/2.46      | m1_subset_1(sK2(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
% 15.82/2.46      | ~ v2_pre_topc(X1)
% 15.82/2.46      | ~ l1_pre_topc(X1)
% 15.82/2.46      | sK3 != X1 ),
% 15.82/2.46      inference(resolution_lifted,[status(thm)],[c_17,c_27]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_540,plain,
% 15.82/2.46      ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK3,X1)))
% 15.82/2.46      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 15.82/2.46      | m1_subset_1(sK2(sK3,X1,X0),k1_zfmisc_1(u1_struct_0(sK3)))
% 15.82/2.46      | ~ v2_pre_topc(sK3)
% 15.82/2.46      | ~ l1_pre_topc(sK3) ),
% 15.82/2.46      inference(unflattening,[status(thm)],[c_539]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_544,plain,
% 15.82/2.46      ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK3,X1)))
% 15.82/2.46      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 15.82/2.46      | m1_subset_1(sK2(sK3,X1,X0),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 15.82/2.46      inference(global_propositional_subsumption,
% 15.82/2.46                [status(thm)],
% 15.82/2.46                [c_540,c_26,c_25]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_2963,plain,
% 15.82/2.46      ( m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK3,X1))) != iProver_top
% 15.82/2.46      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
% 15.82/2.46      | m1_subset_1(sK2(sK3,X1,X0),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 15.82/2.46      inference(predicate_to_equality,[status(thm)],[c_544]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_3303,plain,
% 15.82/2.46      ( m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 15.82/2.46      | m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4))) != iProver_top
% 15.82/2.46      | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 15.82/2.46      inference(superposition,[status(thm)],[c_3194,c_2963]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_33,plain,
% 15.82/2.46      ( m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4))) = iProver_top ),
% 15.82/2.46      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_3607,plain,
% 15.82/2.46      ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 15.82/2.46      inference(global_propositional_subsumption,
% 15.82/2.46                [status(thm)],
% 15.82/2.46                [c_3303,c_31,c_33]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_11,plain,
% 15.82/2.46      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 15.82/2.46      inference(cnf_transformation,[],[f54]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_2975,plain,
% 15.82/2.46      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 15.82/2.46      | r1_tarski(X0,X1) = iProver_top ),
% 15.82/2.46      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_3612,plain,
% 15.82/2.46      ( r1_tarski(sK6,u1_struct_0(sK3)) = iProver_top ),
% 15.82/2.46      inference(superposition,[status(thm)],[c_3607,c_2975]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_7,plain,
% 15.82/2.46      ( r2_hidden(X0,X1)
% 15.82/2.46      | ~ r2_hidden(X0,k1_setfam_1(k2_tarski(X2,X1))) ),
% 15.82/2.46      inference(cnf_transformation,[],[f81]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_2978,plain,
% 15.82/2.46      ( r2_hidden(X0,X1) = iProver_top
% 15.82/2.46      | r2_hidden(X0,k1_setfam_1(k2_tarski(X2,X1))) != iProver_top ),
% 15.82/2.46      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_3489,plain,
% 15.82/2.46      ( r2_hidden(sK0(k1_setfam_1(k2_tarski(X0,X1)),X2),X1) = iProver_top
% 15.82/2.46      | r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X2) = iProver_top ),
% 15.82/2.46      inference(superposition,[status(thm)],[c_2984,c_2978]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_4515,plain,
% 15.82/2.46      ( r2_hidden(sK0(k1_setfam_1(k2_tarski(X0,X1)),X2),X3) = iProver_top
% 15.82/2.46      | r1_tarski(X1,X3) != iProver_top
% 15.82/2.46      | r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X2) = iProver_top ),
% 15.82/2.46      inference(superposition,[status(thm)],[c_3489,c_2983]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_7584,plain,
% 15.82/2.46      ( r1_tarski(X0,X1) != iProver_top
% 15.82/2.46      | r1_tarski(k1_setfam_1(k2_tarski(X2,X0)),X1) = iProver_top ),
% 15.82/2.46      inference(superposition,[status(thm)],[c_4515,c_2985]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_65083,plain,
% 15.82/2.46      ( v3_pre_topc(k1_setfam_1(k2_tarski(sK5,sK6)),sK3) != iProver_top
% 15.82/2.46      | r2_hidden(sK4,k1_setfam_1(k2_tarski(sK5,sK6))) != iProver_top
% 15.82/2.46      | r1_tarski(sK6,u1_struct_0(sK3)) != iProver_top ),
% 15.82/2.46      inference(superposition,[status(thm)],[c_7584,c_65072]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_73060,plain,
% 15.82/2.46      ( r2_hidden(sK4,k1_setfam_1(k2_tarski(sK5,sK6))) != iProver_top
% 15.82/2.46      | v3_pre_topc(k1_setfam_1(k2_tarski(sK5,sK6)),sK3) != iProver_top ),
% 15.82/2.46      inference(global_propositional_subsumption,
% 15.82/2.46                [status(thm)],
% 15.82/2.46                [c_65082,c_3612,c_65083]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_73061,plain,
% 15.82/2.46      ( v3_pre_topc(k1_setfam_1(k2_tarski(sK5,sK6)),sK3) != iProver_top
% 15.82/2.46      | r2_hidden(sK4,k1_setfam_1(k2_tarski(sK5,sK6))) != iProver_top ),
% 15.82/2.46      inference(renaming,[status(thm)],[c_73060]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_73066,plain,
% 15.82/2.46      ( v3_pre_topc(sK6,sK3) != iProver_top
% 15.82/2.46      | v3_pre_topc(sK5,sK3) != iProver_top
% 15.82/2.46      | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 15.82/2.46      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 15.82/2.46      | r2_hidden(sK4,k1_setfam_1(k2_tarski(sK5,sK6))) != iProver_top ),
% 15.82/2.46      inference(superposition,[status(thm)],[c_2960,c_73061]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_23,negated_conjecture,
% 15.82/2.46      ( m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK3,sK4))) ),
% 15.82/2.46      inference(cnf_transformation,[],[f69]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_32,plain,
% 15.82/2.46      ( m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK3,sK4))) = iProver_top ),
% 15.82/2.46      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_2971,plain,
% 15.82/2.46      ( m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK3,sK4))) = iProver_top ),
% 15.82/2.46      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_14,plain,
% 15.82/2.46      ( v3_pre_topc(sK2(X0,X1,X2),X0)
% 15.82/2.46      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.82/2.46      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
% 15.82/2.46      | v2_struct_0(X0)
% 15.82/2.46      | ~ v2_pre_topc(X0)
% 15.82/2.46      | ~ l1_pre_topc(X0) ),
% 15.82/2.46      inference(cnf_transformation,[],[f61]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_441,plain,
% 15.82/2.46      ( v3_pre_topc(sK2(X0,X1,X2),X0)
% 15.82/2.46      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.82/2.46      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
% 15.82/2.46      | ~ v2_pre_topc(X0)
% 15.82/2.46      | ~ l1_pre_topc(X0)
% 15.82/2.46      | sK3 != X0 ),
% 15.82/2.46      inference(resolution_lifted,[status(thm)],[c_14,c_27]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_442,plain,
% 15.82/2.46      ( v3_pre_topc(sK2(sK3,X0,X1),sK3)
% 15.82/2.46      | ~ m1_subset_1(X1,u1_struct_0(k9_yellow_6(sK3,X0)))
% 15.82/2.46      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 15.82/2.46      | ~ v2_pre_topc(sK3)
% 15.82/2.46      | ~ l1_pre_topc(sK3) ),
% 15.82/2.46      inference(unflattening,[status(thm)],[c_441]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_446,plain,
% 15.82/2.46      ( v3_pre_topc(sK2(sK3,X0,X1),sK3)
% 15.82/2.46      | ~ m1_subset_1(X1,u1_struct_0(k9_yellow_6(sK3,X0)))
% 15.82/2.46      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 15.82/2.46      inference(global_propositional_subsumption,
% 15.82/2.46                [status(thm)],
% 15.82/2.46                [c_442,c_26,c_25]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_2967,plain,
% 15.82/2.46      ( v3_pre_topc(sK2(sK3,X0,X1),sK3) = iProver_top
% 15.82/2.46      | m1_subset_1(X1,u1_struct_0(k9_yellow_6(sK3,X0))) != iProver_top
% 15.82/2.46      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
% 15.82/2.46      inference(predicate_to_equality,[status(thm)],[c_446]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_3276,plain,
% 15.82/2.46      ( v3_pre_topc(sK2(sK3,sK4,sK5),sK3) = iProver_top
% 15.82/2.46      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
% 15.82/2.46      inference(superposition,[status(thm)],[c_2971,c_2967]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_3176,plain,
% 15.82/2.46      ( sK2(sK3,sK4,sK5) = sK5
% 15.82/2.46      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
% 15.82/2.46      inference(superposition,[status(thm)],[c_2971,c_2962]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_3203,plain,
% 15.82/2.46      ( sK2(sK3,sK4,sK5) = sK5 ),
% 15.82/2.46      inference(global_propositional_subsumption,
% 15.82/2.46                [status(thm)],
% 15.82/2.46                [c_3176,c_31]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_3279,plain,
% 15.82/2.46      ( v3_pre_topc(sK5,sK3) = iProver_top
% 15.82/2.46      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
% 15.82/2.46      inference(light_normalisation,[status(thm)],[c_3276,c_3203]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_3275,plain,
% 15.82/2.46      ( v3_pre_topc(sK2(sK3,sK4,sK6),sK3) = iProver_top
% 15.82/2.46      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
% 15.82/2.46      inference(superposition,[status(thm)],[c_2972,c_2967]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_3284,plain,
% 15.82/2.46      ( v3_pre_topc(sK6,sK3) = iProver_top
% 15.82/2.46      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
% 15.82/2.46      inference(light_normalisation,[status(thm)],[c_3275,c_3194]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_3304,plain,
% 15.82/2.46      ( m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 15.82/2.46      | m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK3,sK4))) != iProver_top
% 15.82/2.46      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 15.82/2.46      inference(superposition,[status(thm)],[c_3203,c_2963]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_73083,plain,
% 15.82/2.46      ( r2_hidden(sK4,k1_setfam_1(k2_tarski(sK5,sK6))) != iProver_top ),
% 15.82/2.46      inference(global_propositional_subsumption,
% 15.82/2.46                [status(thm)],
% 15.82/2.46                [c_73066,c_31,c_32,c_33,c_3279,c_3284,c_3303,c_3304]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_73088,plain,
% 15.82/2.46      ( r2_hidden(sK4,sK6) != iProver_top
% 15.82/2.46      | r2_hidden(sK4,sK5) != iProver_top ),
% 15.82/2.46      inference(superposition,[status(thm)],[c_2979,c_73083]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_15,plain,
% 15.82/2.46      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 15.82/2.46      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
% 15.82/2.46      | r2_hidden(X0,sK2(X1,X0,X2))
% 15.82/2.46      | v2_struct_0(X1)
% 15.82/2.46      | ~ v2_pre_topc(X1)
% 15.82/2.46      | ~ l1_pre_topc(X1) ),
% 15.82/2.46      inference(cnf_transformation,[],[f60]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_581,plain,
% 15.82/2.46      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 15.82/2.46      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
% 15.82/2.46      | r2_hidden(X0,sK2(X1,X0,X2))
% 15.82/2.46      | ~ v2_pre_topc(X1)
% 15.82/2.46      | ~ l1_pre_topc(X1)
% 15.82/2.46      | sK3 != X1 ),
% 15.82/2.46      inference(resolution_lifted,[status(thm)],[c_15,c_27]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_582,plain,
% 15.82/2.46      ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK3,X1)))
% 15.82/2.46      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 15.82/2.46      | r2_hidden(X1,sK2(sK3,X1,X0))
% 15.82/2.46      | ~ v2_pre_topc(sK3)
% 15.82/2.46      | ~ l1_pre_topc(sK3) ),
% 15.82/2.46      inference(unflattening,[status(thm)],[c_581]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_586,plain,
% 15.82/2.46      ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK3,X1)))
% 15.82/2.46      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 15.82/2.46      | r2_hidden(X1,sK2(sK3,X1,X0)) ),
% 15.82/2.46      inference(global_propositional_subsumption,
% 15.82/2.46                [status(thm)],
% 15.82/2.46                [c_582,c_26,c_25]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_2961,plain,
% 15.82/2.46      ( m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK3,X1))) != iProver_top
% 15.82/2.46      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
% 15.82/2.46      | r2_hidden(X1,sK2(sK3,X1,X0)) = iProver_top ),
% 15.82/2.46      inference(predicate_to_equality,[status(thm)],[c_586]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_3215,plain,
% 15.82/2.46      ( m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 15.82/2.46      | r2_hidden(sK4,sK2(sK3,sK4,sK6)) = iProver_top ),
% 15.82/2.46      inference(superposition,[status(thm)],[c_2972,c_2961]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_3224,plain,
% 15.82/2.46      ( m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 15.82/2.46      | r2_hidden(sK4,sK6) = iProver_top ),
% 15.82/2.46      inference(light_normalisation,[status(thm)],[c_3215,c_3194]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_3216,plain,
% 15.82/2.46      ( m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 15.82/2.46      | r2_hidden(sK4,sK2(sK3,sK4,sK5)) = iProver_top ),
% 15.82/2.46      inference(superposition,[status(thm)],[c_2971,c_2961]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(c_3219,plain,
% 15.82/2.46      ( m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 15.82/2.46      | r2_hidden(sK4,sK5) = iProver_top ),
% 15.82/2.46      inference(light_normalisation,[status(thm)],[c_3216,c_3203]) ).
% 15.82/2.46  
% 15.82/2.46  cnf(contradiction,plain,
% 15.82/2.46      ( $false ),
% 15.82/2.46      inference(minisat,[status(thm)],[c_73088,c_3224,c_3219,c_31]) ).
% 15.82/2.46  
% 15.82/2.46  
% 15.82/2.46  % SZS output end CNFRefutation for theBenchmark.p
% 15.82/2.46  
% 15.82/2.46  ------                               Statistics
% 15.82/2.46  
% 15.82/2.46  ------ Selected
% 15.82/2.46  
% 15.82/2.46  total_time:                             1.966
% 15.82/2.46  
%------------------------------------------------------------------------------
