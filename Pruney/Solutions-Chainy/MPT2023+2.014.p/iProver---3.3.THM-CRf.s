%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:28:48 EST 2020

% Result     : Theorem 3.16s
% Output     : CNFRefutation 3.16s
% Verified   : 
% Statistics : Number of formulae       :  144 (1076 expanded)
%              Number of clauses        :   81 ( 226 expanded)
%              Number of leaves         :   16 ( 401 expanded)
%              Depth                    :   20
%              Number of atoms          :  608 (6406 expanded)
%              Number of equality atoms :  121 ( 312 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f26,plain,(
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
    inference(rectify,[],[f25])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).

fof(f41,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f69,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k1_setfam_1(k2_tarski(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f41,f46])).

fof(f75,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k1_setfam_1(k2_tarski(X0,X1)))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f69])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_pre_topc(X2,X0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k3_xboole_0(X1,X2),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(k1_setfam_1(k2_tarski(X1,X2)),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(definition_unfolding,[],[f51,f46])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))
          & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
     => ( ~ m1_subset_1(k3_xboole_0(X2,sK5),u1_struct_0(k9_yellow_6(X0,X1)))
        & m1_subset_1(sK5,u1_struct_0(k9_yellow_6(X0,X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))
              & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
          & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
     => ( ? [X3] :
            ( ~ m1_subset_1(k3_xboole_0(sK4,X3),u1_struct_0(k9_yellow_6(X0,X1)))
            & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
        & m1_subset_1(sK4,u1_struct_0(k9_yellow_6(X0,X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
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
                ( ~ m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,sK3)))
                & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,sK3))) )
            & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,sK3))) )
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
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
                  ( ~ m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK2,X1)))
                  & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK2,X1))) )
              & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK2,X1))) )
          & m1_subset_1(X1,u1_struct_0(sK2)) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK4,sK5),u1_struct_0(k9_yellow_6(sK2,sK3)))
    & m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3)))
    & m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3)))
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f23,f37,f36,f35,f34])).

fof(f61,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f60,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_setfam_1(k2_tarski(X0,X2)),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f45,f46])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f32,plain,(
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

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ v3_pre_topc(X2,X0)
      | ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f59,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f65,plain,(
    ~ m1_subset_1(k3_xboole_0(sK4,sK5),u1_struct_0(k9_yellow_6(sK2,sK3))) ),
    inference(cnf_transformation,[],[f38])).

fof(f74,plain,(
    ~ m1_subset_1(k1_setfam_1(k2_tarski(sK4,sK5)),u1_struct_0(k9_yellow_6(sK2,sK3))) ),
    inference(definition_unfolding,[],[f65,f46])).

fof(f63,plain,(
    m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))) ),
    inference(cnf_transformation,[],[f38])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( v3_pre_topc(X3,X0)
          & r2_hidden(X1,X3)
          & X2 = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( v3_pre_topc(sK1(X0,X1,X2),X0)
        & r2_hidden(X1,sK1(X0,X1,X2))
        & sK1(X0,X1,X2) = X2
        & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v3_pre_topc(sK1(X0,X1,X2),X0)
                & r2_hidden(X1,sK1(X0,X1,X2))
                & sK1(X0,X1,X2) = X2
                & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f30])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( sK1(X0,X1,X2) = X2
      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f62,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f38])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f64,plain,(
    m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3))) ),
    inference(cnf_transformation,[],[f38])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(sK1(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,sK1(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k1_setfam_1(k2_tarski(X2,X1))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1343,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X0,k1_setfam_1(k2_tarski(X1,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_11,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ v3_pre_topc(X2,X1)
    | v3_pre_topc(k1_setfam_1(k2_tarski(X2,X0)),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_23,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_540,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ v3_pre_topc(X2,X1)
    | v3_pre_topc(k1_setfam_1(k2_tarski(X2,X0)),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_23])).

cnf(c_541,plain,
    ( ~ v3_pre_topc(X0,sK2)
    | ~ v3_pre_topc(X1,sK2)
    | v3_pre_topc(k1_setfam_1(k2_tarski(X1,X0)),sK2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_540])).

cnf(c_24,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_545,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | v3_pre_topc(k1_setfam_1(k2_tarski(X1,X0)),sK2)
    | ~ v3_pre_topc(X1,sK2)
    | ~ v3_pre_topc(X0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_541,c_24])).

cnf(c_546,plain,
    ( ~ v3_pre_topc(X0,sK2)
    | ~ v3_pre_topc(X1,sK2)
    | v3_pre_topc(k1_setfam_1(k2_tarski(X1,X0)),sK2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(renaming,[status(thm)],[c_545])).

cnf(c_1324,plain,
    ( v3_pre_topc(X0,sK2) != iProver_top
    | v3_pre_topc(X1,sK2) != iProver_top
    | v3_pre_topc(k1_setfam_1(k2_tarski(X1,X0)),sK2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_546])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_setfam_1(k2_tarski(X0,X2)),X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1340,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_setfam_1(k2_tarski(X0,X2)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_8,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1338,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_16,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_25,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_417,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_25])).

cnf(c_418,plain,
    ( ~ v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X1,X0)
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK2,X1)))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_417])).

cnf(c_422,plain,
    ( ~ v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X1,X0)
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK2,X1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_418,c_24,c_23])).

cnf(c_10,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_438,plain,
    ( ~ v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X1,X0)
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK2,X1))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_422,c_10])).

cnf(c_1328,plain,
    ( v3_pre_topc(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(X1,X0) != iProver_top
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK2,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_438])).

cnf(c_7,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1339,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2493,plain,
    ( v3_pre_topc(X0,sK2) != iProver_top
    | m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,X1))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1328,c_1339])).

cnf(c_19,negated_conjecture,
    ( ~ m1_subset_1(k1_setfam_1(k2_tarski(sK4,sK5)),u1_struct_0(k9_yellow_6(sK2,sK3))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1335,plain,
    ( m1_subset_1(k1_setfam_1(k2_tarski(sK4,sK5)),u1_struct_0(k9_yellow_6(sK2,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4751,plain,
    ( v3_pre_topc(k1_setfam_1(k2_tarski(sK4,sK5)),sK2) != iProver_top
    | m1_subset_1(k1_setfam_1(k2_tarski(sK4,sK5)),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(sK3,k1_setfam_1(k2_tarski(sK4,sK5))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2493,c_1335])).

cnf(c_5165,plain,
    ( v3_pre_topc(k1_setfam_1(k2_tarski(sK4,sK5)),sK2) != iProver_top
    | r1_tarski(k1_setfam_1(k2_tarski(sK4,sK5)),u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK3,k1_setfam_1(k2_tarski(sK4,sK5))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1338,c_4751])).

cnf(c_5406,plain,
    ( v3_pre_topc(k1_setfam_1(k2_tarski(sK4,sK5)),sK2) != iProver_top
    | r1_tarski(sK4,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK3,k1_setfam_1(k2_tarski(sK4,sK5))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1340,c_5165])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1333,plain,
    ( m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK1(X1,X0,X2) = X2 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_467,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK1(X1,X0,X2) = X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_25])).

cnf(c_468,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | sK1(sK2,X1,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_467])).

cnf(c_472,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | sK1(sK2,X1,X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_468,c_24,c_23])).

cnf(c_1326,plain,
    ( sK1(sK2,X0,X1) = X1
    | m1_subset_1(X1,u1_struct_0(k9_yellow_6(sK2,X0))) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_472])).

cnf(c_1577,plain,
    ( sK1(sK2,sK3,sK4) = sK4
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1333,c_1326])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_29,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1643,plain,
    ( sK1(sK2,sK3,sK4) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1577,c_29])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
    | m1_subset_1(sK1(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_446,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
    | m1_subset_1(sK1(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_25])).

cnf(c_447,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(sK1(sK2,X1,X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_446])).

cnf(c_451,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(sK1(sK2,X1,X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_447,c_24,c_23])).

cnf(c_1327,plain,
    ( m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,X1))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK1(sK2,X1,X0),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_451])).

cnf(c_1986,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1643,c_1327])).

cnf(c_30,plain,
    ( m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2824,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1986,c_29,c_30])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1337,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2829,plain,
    ( r1_tarski(sK4,u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2824,c_1337])).

cnf(c_14413,plain,
    ( v3_pre_topc(k1_setfam_1(k2_tarski(sK4,sK5)),sK2) != iProver_top
    | r2_hidden(sK3,k1_setfam_1(k2_tarski(sK4,sK5))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5406,c_2829])).

cnf(c_14419,plain,
    ( v3_pre_topc(sK5,sK2) != iProver_top
    | v3_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(sK3,k1_setfam_1(k2_tarski(sK4,sK5))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1324,c_14413])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_31,plain,
    ( m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_12,plain,
    ( v3_pre_topc(sK1(X0,X1,X2),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_348,plain,
    ( v3_pre_topc(sK1(X0,X1,X2),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_25])).

cnf(c_349,plain,
    ( v3_pre_topc(sK1(sK2,X0,X1),sK2)
    | ~ m1_subset_1(X1,u1_struct_0(k9_yellow_6(sK2,X0)))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_348])).

cnf(c_353,plain,
    ( v3_pre_topc(sK1(sK2,X0,X1),sK2)
    | ~ m1_subset_1(X1,u1_struct_0(k9_yellow_6(sK2,X0)))
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_349,c_24,c_23])).

cnf(c_1331,plain,
    ( v3_pre_topc(sK1(sK2,X0,X1),sK2) = iProver_top
    | m1_subset_1(X1,u1_struct_0(k9_yellow_6(sK2,X0))) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_353])).

cnf(c_1902,plain,
    ( v3_pre_topc(sK1(sK2,sK3,sK4),sK2) = iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1333,c_1331])).

cnf(c_1905,plain,
    ( v3_pre_topc(sK4,sK2) = iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1902,c_1643])).

cnf(c_1334,plain,
    ( m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1901,plain,
    ( v3_pre_topc(sK1(sK2,sK3,sK5),sK2) = iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1334,c_1331])).

cnf(c_1576,plain,
    ( sK1(sK2,sK3,sK5) = sK5
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1334,c_1326])).

cnf(c_1589,plain,
    ( sK1(sK2,sK3,sK5) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1576,c_29])).

cnf(c_1910,plain,
    ( v3_pre_topc(sK5,sK2) = iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1901,c_1589])).

cnf(c_1985,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1589,c_1327])).

cnf(c_14602,plain,
    ( r2_hidden(sK3,k1_setfam_1(k2_tarski(sK4,sK5))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14419,c_29,c_30,c_31,c_1905,c_1910,c_1985,c_1986])).

cnf(c_14607,plain,
    ( r2_hidden(sK3,sK5) != iProver_top
    | r2_hidden(sK3,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1343,c_14602])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
    | r2_hidden(X0,sK1(X1,X0,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_488,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
    | r2_hidden(X0,sK1(X1,X0,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_25])).

cnf(c_489,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | r2_hidden(X1,sK1(sK2,X1,X0))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_488])).

cnf(c_493,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | r2_hidden(X1,sK1(sK2,X1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_489,c_24,c_23])).

cnf(c_1325,plain,
    ( m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,X1))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X1,sK1(sK2,X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_493])).

cnf(c_1650,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK3,sK1(sK2,sK3,sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1334,c_1325])).

cnf(c_1659,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK3,sK5) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1650,c_1589])).

cnf(c_1651,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK3,sK1(sK2,sK3,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1333,c_1325])).

cnf(c_1654,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK3,sK4) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1651,c_1643])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_14607,c_1659,c_1654,c_29])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.11/0.33  % Computer   : n005.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 18:18:32 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running in FOF mode
% 3.16/0.97  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.16/0.97  
% 3.16/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.16/0.97  
% 3.16/0.97  ------  iProver source info
% 3.16/0.97  
% 3.16/0.97  git: date: 2020-06-30 10:37:57 +0100
% 3.16/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.16/0.97  git: non_committed_changes: false
% 3.16/0.97  git: last_make_outside_of_git: false
% 3.16/0.97  
% 3.16/0.97  ------ 
% 3.16/0.97  
% 3.16/0.97  ------ Input Options
% 3.16/0.97  
% 3.16/0.97  --out_options                           all
% 3.16/0.97  --tptp_safe_out                         true
% 3.16/0.97  --problem_path                          ""
% 3.16/0.97  --include_path                          ""
% 3.16/0.97  --clausifier                            res/vclausify_rel
% 3.16/0.97  --clausifier_options                    --mode clausify
% 3.16/0.97  --stdin                                 false
% 3.16/0.97  --stats_out                             all
% 3.16/0.97  
% 3.16/0.97  ------ General Options
% 3.16/0.97  
% 3.16/0.97  --fof                                   false
% 3.16/0.97  --time_out_real                         305.
% 3.16/0.97  --time_out_virtual                      -1.
% 3.16/0.97  --symbol_type_check                     false
% 3.16/0.97  --clausify_out                          false
% 3.16/0.97  --sig_cnt_out                           false
% 3.16/0.97  --trig_cnt_out                          false
% 3.16/0.97  --trig_cnt_out_tolerance                1.
% 3.16/0.97  --trig_cnt_out_sk_spl                   false
% 3.16/0.97  --abstr_cl_out                          false
% 3.16/0.97  
% 3.16/0.97  ------ Global Options
% 3.16/0.97  
% 3.16/0.97  --schedule                              default
% 3.16/0.97  --add_important_lit                     false
% 3.16/0.97  --prop_solver_per_cl                    1000
% 3.16/0.97  --min_unsat_core                        false
% 3.16/0.97  --soft_assumptions                      false
% 3.16/0.97  --soft_lemma_size                       3
% 3.16/0.97  --prop_impl_unit_size                   0
% 3.16/0.97  --prop_impl_unit                        []
% 3.16/0.97  --share_sel_clauses                     true
% 3.16/0.97  --reset_solvers                         false
% 3.16/0.97  --bc_imp_inh                            [conj_cone]
% 3.16/0.97  --conj_cone_tolerance                   3.
% 3.16/0.97  --extra_neg_conj                        none
% 3.16/0.97  --large_theory_mode                     true
% 3.16/0.97  --prolific_symb_bound                   200
% 3.16/0.97  --lt_threshold                          2000
% 3.16/0.97  --clause_weak_htbl                      true
% 3.16/0.97  --gc_record_bc_elim                     false
% 3.16/0.97  
% 3.16/0.97  ------ Preprocessing Options
% 3.16/0.97  
% 3.16/0.97  --preprocessing_flag                    true
% 3.16/0.97  --time_out_prep_mult                    0.1
% 3.16/0.97  --splitting_mode                        input
% 3.16/0.97  --splitting_grd                         true
% 3.16/0.97  --splitting_cvd                         false
% 3.16/0.97  --splitting_cvd_svl                     false
% 3.16/0.97  --splitting_nvd                         32
% 3.16/0.97  --sub_typing                            true
% 3.16/0.97  --prep_gs_sim                           true
% 3.16/0.97  --prep_unflatten                        true
% 3.16/0.97  --prep_res_sim                          true
% 3.16/0.97  --prep_upred                            true
% 3.16/0.97  --prep_sem_filter                       exhaustive
% 3.16/0.97  --prep_sem_filter_out                   false
% 3.16/0.97  --pred_elim                             true
% 3.16/0.97  --res_sim_input                         true
% 3.16/0.97  --eq_ax_congr_red                       true
% 3.16/0.97  --pure_diseq_elim                       true
% 3.16/0.97  --brand_transform                       false
% 3.16/0.97  --non_eq_to_eq                          false
% 3.16/0.97  --prep_def_merge                        true
% 3.16/0.97  --prep_def_merge_prop_impl              false
% 3.16/0.97  --prep_def_merge_mbd                    true
% 3.16/0.97  --prep_def_merge_tr_red                 false
% 3.16/0.97  --prep_def_merge_tr_cl                  false
% 3.16/0.97  --smt_preprocessing                     true
% 3.16/0.97  --smt_ac_axioms                         fast
% 3.16/0.97  --preprocessed_out                      false
% 3.16/0.97  --preprocessed_stats                    false
% 3.16/0.97  
% 3.16/0.97  ------ Abstraction refinement Options
% 3.16/0.97  
% 3.16/0.97  --abstr_ref                             []
% 3.16/0.97  --abstr_ref_prep                        false
% 3.16/0.97  --abstr_ref_until_sat                   false
% 3.16/0.97  --abstr_ref_sig_restrict                funpre
% 3.16/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 3.16/0.97  --abstr_ref_under                       []
% 3.16/0.97  
% 3.16/0.97  ------ SAT Options
% 3.16/0.97  
% 3.16/0.97  --sat_mode                              false
% 3.16/0.97  --sat_fm_restart_options                ""
% 3.16/0.97  --sat_gr_def                            false
% 3.16/0.97  --sat_epr_types                         true
% 3.16/0.97  --sat_non_cyclic_types                  false
% 3.16/0.97  --sat_finite_models                     false
% 3.16/0.97  --sat_fm_lemmas                         false
% 3.16/0.97  --sat_fm_prep                           false
% 3.16/0.97  --sat_fm_uc_incr                        true
% 3.16/0.97  --sat_out_model                         small
% 3.16/0.97  --sat_out_clauses                       false
% 3.16/0.97  
% 3.16/0.97  ------ QBF Options
% 3.16/0.97  
% 3.16/0.97  --qbf_mode                              false
% 3.16/0.97  --qbf_elim_univ                         false
% 3.16/0.97  --qbf_dom_inst                          none
% 3.16/0.97  --qbf_dom_pre_inst                      false
% 3.16/0.97  --qbf_sk_in                             false
% 3.16/0.97  --qbf_pred_elim                         true
% 3.16/0.97  --qbf_split                             512
% 3.16/0.97  
% 3.16/0.97  ------ BMC1 Options
% 3.16/0.97  
% 3.16/0.97  --bmc1_incremental                      false
% 3.16/0.97  --bmc1_axioms                           reachable_all
% 3.16/0.97  --bmc1_min_bound                        0
% 3.16/0.97  --bmc1_max_bound                        -1
% 3.16/0.97  --bmc1_max_bound_default                -1
% 3.16/0.97  --bmc1_symbol_reachability              true
% 3.16/0.97  --bmc1_property_lemmas                  false
% 3.16/0.97  --bmc1_k_induction                      false
% 3.16/0.97  --bmc1_non_equiv_states                 false
% 3.16/0.97  --bmc1_deadlock                         false
% 3.16/0.97  --bmc1_ucm                              false
% 3.16/0.97  --bmc1_add_unsat_core                   none
% 3.16/0.97  --bmc1_unsat_core_children              false
% 3.16/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 3.16/0.97  --bmc1_out_stat                         full
% 3.16/0.97  --bmc1_ground_init                      false
% 3.16/0.97  --bmc1_pre_inst_next_state              false
% 3.16/0.97  --bmc1_pre_inst_state                   false
% 3.16/0.97  --bmc1_pre_inst_reach_state             false
% 3.16/0.97  --bmc1_out_unsat_core                   false
% 3.16/0.97  --bmc1_aig_witness_out                  false
% 3.16/0.97  --bmc1_verbose                          false
% 3.16/0.97  --bmc1_dump_clauses_tptp                false
% 3.16/0.97  --bmc1_dump_unsat_core_tptp             false
% 3.16/0.97  --bmc1_dump_file                        -
% 3.16/0.97  --bmc1_ucm_expand_uc_limit              128
% 3.16/0.97  --bmc1_ucm_n_expand_iterations          6
% 3.16/0.97  --bmc1_ucm_extend_mode                  1
% 3.16/0.97  --bmc1_ucm_init_mode                    2
% 3.16/0.97  --bmc1_ucm_cone_mode                    none
% 3.16/0.97  --bmc1_ucm_reduced_relation_type        0
% 3.16/0.97  --bmc1_ucm_relax_model                  4
% 3.16/0.97  --bmc1_ucm_full_tr_after_sat            true
% 3.16/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 3.16/0.97  --bmc1_ucm_layered_model                none
% 3.16/0.97  --bmc1_ucm_max_lemma_size               10
% 3.16/0.97  
% 3.16/0.97  ------ AIG Options
% 3.16/0.97  
% 3.16/0.97  --aig_mode                              false
% 3.16/0.97  
% 3.16/0.97  ------ Instantiation Options
% 3.16/0.97  
% 3.16/0.97  --instantiation_flag                    true
% 3.16/0.97  --inst_sos_flag                         false
% 3.16/0.97  --inst_sos_phase                        true
% 3.16/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.16/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.16/0.97  --inst_lit_sel_side                     num_symb
% 3.16/0.97  --inst_solver_per_active                1400
% 3.16/0.97  --inst_solver_calls_frac                1.
% 3.16/0.97  --inst_passive_queue_type               priority_queues
% 3.16/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.16/0.97  --inst_passive_queues_freq              [25;2]
% 3.16/0.97  --inst_dismatching                      true
% 3.16/0.97  --inst_eager_unprocessed_to_passive     true
% 3.16/0.97  --inst_prop_sim_given                   true
% 3.16/0.97  --inst_prop_sim_new                     false
% 3.16/0.97  --inst_subs_new                         false
% 3.16/0.97  --inst_eq_res_simp                      false
% 3.16/0.97  --inst_subs_given                       false
% 3.16/0.97  --inst_orphan_elimination               true
% 3.16/0.97  --inst_learning_loop_flag               true
% 3.16/0.97  --inst_learning_start                   3000
% 3.16/0.97  --inst_learning_factor                  2
% 3.16/0.97  --inst_start_prop_sim_after_learn       3
% 3.16/0.97  --inst_sel_renew                        solver
% 3.16/0.97  --inst_lit_activity_flag                true
% 3.16/0.97  --inst_restr_to_given                   false
% 3.16/0.97  --inst_activity_threshold               500
% 3.16/0.97  --inst_out_proof                        true
% 3.16/0.97  
% 3.16/0.97  ------ Resolution Options
% 3.16/0.97  
% 3.16/0.97  --resolution_flag                       true
% 3.16/0.97  --res_lit_sel                           adaptive
% 3.16/0.97  --res_lit_sel_side                      none
% 3.16/0.97  --res_ordering                          kbo
% 3.16/0.97  --res_to_prop_solver                    active
% 3.16/0.97  --res_prop_simpl_new                    false
% 3.16/0.97  --res_prop_simpl_given                  true
% 3.16/0.97  --res_passive_queue_type                priority_queues
% 3.16/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.16/0.97  --res_passive_queues_freq               [15;5]
% 3.16/0.97  --res_forward_subs                      full
% 3.16/0.97  --res_backward_subs                     full
% 3.16/0.97  --res_forward_subs_resolution           true
% 3.16/0.97  --res_backward_subs_resolution          true
% 3.16/0.97  --res_orphan_elimination                true
% 3.16/0.97  --res_time_limit                        2.
% 3.16/0.97  --res_out_proof                         true
% 3.16/0.97  
% 3.16/0.97  ------ Superposition Options
% 3.16/0.97  
% 3.16/0.97  --superposition_flag                    true
% 3.16/0.97  --sup_passive_queue_type                priority_queues
% 3.16/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.16/0.97  --sup_passive_queues_freq               [8;1;4]
% 3.16/0.97  --demod_completeness_check              fast
% 3.16/0.97  --demod_use_ground                      true
% 3.16/0.97  --sup_to_prop_solver                    passive
% 3.16/0.97  --sup_prop_simpl_new                    true
% 3.16/0.97  --sup_prop_simpl_given                  true
% 3.16/0.97  --sup_fun_splitting                     false
% 3.16/0.97  --sup_smt_interval                      50000
% 3.16/0.97  
% 3.16/0.97  ------ Superposition Simplification Setup
% 3.16/0.97  
% 3.16/0.97  --sup_indices_passive                   []
% 3.16/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.16/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.16/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.16/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 3.16/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.16/0.97  --sup_full_bw                           [BwDemod]
% 3.16/0.97  --sup_immed_triv                        [TrivRules]
% 3.16/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.16/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.16/0.97  --sup_immed_bw_main                     []
% 3.16/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.16/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 3.16/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.16/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.16/0.97  
% 3.16/0.97  ------ Combination Options
% 3.16/0.97  
% 3.16/0.97  --comb_res_mult                         3
% 3.16/0.97  --comb_sup_mult                         2
% 3.16/0.97  --comb_inst_mult                        10
% 3.16/0.97  
% 3.16/0.97  ------ Debug Options
% 3.16/0.97  
% 3.16/0.97  --dbg_backtrace                         false
% 3.16/0.97  --dbg_dump_prop_clauses                 false
% 3.16/0.97  --dbg_dump_prop_clauses_file            -
% 3.16/0.97  --dbg_out_stat                          false
% 3.16/0.97  ------ Parsing...
% 3.16/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.16/0.97  
% 3.16/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.16/0.97  
% 3.16/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.16/0.97  
% 3.16/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.16/0.97  ------ Proving...
% 3.16/0.97  ------ Problem Properties 
% 3.16/0.97  
% 3.16/0.97  
% 3.16/0.97  clauses                                 23
% 3.16/0.97  conjectures                             4
% 3.16/0.97  EPR                                     1
% 3.16/0.97  Horn                                    21
% 3.16/0.97  unary                                   4
% 3.16/0.97  binary                                  6
% 3.16/0.97  lits                                    61
% 3.16/0.97  lits eq                                 4
% 3.16/0.97  fd_pure                                 0
% 3.16/0.97  fd_pseudo                               0
% 3.16/0.97  fd_cond                                 0
% 3.16/0.97  fd_pseudo_cond                          3
% 3.16/0.97  AC symbols                              0
% 3.16/0.97  
% 3.16/0.97  ------ Schedule dynamic 5 is on 
% 3.16/0.97  
% 3.16/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.16/0.97  
% 3.16/0.97  
% 3.16/0.97  ------ 
% 3.16/0.97  Current options:
% 3.16/0.97  ------ 
% 3.16/0.97  
% 3.16/0.97  ------ Input Options
% 3.16/0.97  
% 3.16/0.97  --out_options                           all
% 3.16/0.97  --tptp_safe_out                         true
% 3.16/0.97  --problem_path                          ""
% 3.16/0.97  --include_path                          ""
% 3.16/0.97  --clausifier                            res/vclausify_rel
% 3.16/0.97  --clausifier_options                    --mode clausify
% 3.16/0.97  --stdin                                 false
% 3.16/0.97  --stats_out                             all
% 3.16/0.97  
% 3.16/0.97  ------ General Options
% 3.16/0.97  
% 3.16/0.97  --fof                                   false
% 3.16/0.97  --time_out_real                         305.
% 3.16/0.97  --time_out_virtual                      -1.
% 3.16/0.97  --symbol_type_check                     false
% 3.16/0.97  --clausify_out                          false
% 3.16/0.97  --sig_cnt_out                           false
% 3.16/0.97  --trig_cnt_out                          false
% 3.16/0.97  --trig_cnt_out_tolerance                1.
% 3.16/0.97  --trig_cnt_out_sk_spl                   false
% 3.16/0.97  --abstr_cl_out                          false
% 3.16/0.97  
% 3.16/0.97  ------ Global Options
% 3.16/0.97  
% 3.16/0.97  --schedule                              default
% 3.16/0.97  --add_important_lit                     false
% 3.16/0.97  --prop_solver_per_cl                    1000
% 3.16/0.97  --min_unsat_core                        false
% 3.16/0.97  --soft_assumptions                      false
% 3.16/0.97  --soft_lemma_size                       3
% 3.16/0.97  --prop_impl_unit_size                   0
% 3.16/0.97  --prop_impl_unit                        []
% 3.16/0.97  --share_sel_clauses                     true
% 3.16/0.97  --reset_solvers                         false
% 3.16/0.97  --bc_imp_inh                            [conj_cone]
% 3.16/0.97  --conj_cone_tolerance                   3.
% 3.16/0.97  --extra_neg_conj                        none
% 3.16/0.97  --large_theory_mode                     true
% 3.16/0.97  --prolific_symb_bound                   200
% 3.16/0.97  --lt_threshold                          2000
% 3.16/0.97  --clause_weak_htbl                      true
% 3.16/0.97  --gc_record_bc_elim                     false
% 3.16/0.97  
% 3.16/0.97  ------ Preprocessing Options
% 3.16/0.97  
% 3.16/0.97  --preprocessing_flag                    true
% 3.16/0.97  --time_out_prep_mult                    0.1
% 3.16/0.97  --splitting_mode                        input
% 3.16/0.97  --splitting_grd                         true
% 3.16/0.97  --splitting_cvd                         false
% 3.16/0.97  --splitting_cvd_svl                     false
% 3.16/0.97  --splitting_nvd                         32
% 3.16/0.97  --sub_typing                            true
% 3.16/0.97  --prep_gs_sim                           true
% 3.16/0.97  --prep_unflatten                        true
% 3.16/0.97  --prep_res_sim                          true
% 3.16/0.97  --prep_upred                            true
% 3.16/0.97  --prep_sem_filter                       exhaustive
% 3.16/0.97  --prep_sem_filter_out                   false
% 3.16/0.97  --pred_elim                             true
% 3.16/0.97  --res_sim_input                         true
% 3.16/0.97  --eq_ax_congr_red                       true
% 3.16/0.97  --pure_diseq_elim                       true
% 3.16/0.97  --brand_transform                       false
% 3.16/0.97  --non_eq_to_eq                          false
% 3.16/0.97  --prep_def_merge                        true
% 3.16/0.97  --prep_def_merge_prop_impl              false
% 3.16/0.97  --prep_def_merge_mbd                    true
% 3.16/0.97  --prep_def_merge_tr_red                 false
% 3.16/0.97  --prep_def_merge_tr_cl                  false
% 3.16/0.97  --smt_preprocessing                     true
% 3.16/0.97  --smt_ac_axioms                         fast
% 3.16/0.97  --preprocessed_out                      false
% 3.16/0.97  --preprocessed_stats                    false
% 3.16/0.97  
% 3.16/0.97  ------ Abstraction refinement Options
% 3.16/0.97  
% 3.16/0.97  --abstr_ref                             []
% 3.16/0.97  --abstr_ref_prep                        false
% 3.16/0.97  --abstr_ref_until_sat                   false
% 3.16/0.97  --abstr_ref_sig_restrict                funpre
% 3.16/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 3.16/0.97  --abstr_ref_under                       []
% 3.16/0.97  
% 3.16/0.97  ------ SAT Options
% 3.16/0.97  
% 3.16/0.97  --sat_mode                              false
% 3.16/0.97  --sat_fm_restart_options                ""
% 3.16/0.97  --sat_gr_def                            false
% 3.16/0.97  --sat_epr_types                         true
% 3.16/0.97  --sat_non_cyclic_types                  false
% 3.16/0.97  --sat_finite_models                     false
% 3.16/0.97  --sat_fm_lemmas                         false
% 3.16/0.97  --sat_fm_prep                           false
% 3.16/0.97  --sat_fm_uc_incr                        true
% 3.16/0.97  --sat_out_model                         small
% 3.16/0.97  --sat_out_clauses                       false
% 3.16/0.97  
% 3.16/0.97  ------ QBF Options
% 3.16/0.97  
% 3.16/0.97  --qbf_mode                              false
% 3.16/0.97  --qbf_elim_univ                         false
% 3.16/0.97  --qbf_dom_inst                          none
% 3.16/0.97  --qbf_dom_pre_inst                      false
% 3.16/0.97  --qbf_sk_in                             false
% 3.16/0.97  --qbf_pred_elim                         true
% 3.16/0.97  --qbf_split                             512
% 3.16/0.97  
% 3.16/0.97  ------ BMC1 Options
% 3.16/0.97  
% 3.16/0.97  --bmc1_incremental                      false
% 3.16/0.97  --bmc1_axioms                           reachable_all
% 3.16/0.97  --bmc1_min_bound                        0
% 3.16/0.97  --bmc1_max_bound                        -1
% 3.16/0.97  --bmc1_max_bound_default                -1
% 3.16/0.97  --bmc1_symbol_reachability              true
% 3.16/0.97  --bmc1_property_lemmas                  false
% 3.16/0.97  --bmc1_k_induction                      false
% 3.16/0.97  --bmc1_non_equiv_states                 false
% 3.16/0.97  --bmc1_deadlock                         false
% 3.16/0.97  --bmc1_ucm                              false
% 3.16/0.97  --bmc1_add_unsat_core                   none
% 3.16/0.97  --bmc1_unsat_core_children              false
% 3.16/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 3.16/0.97  --bmc1_out_stat                         full
% 3.16/0.97  --bmc1_ground_init                      false
% 3.16/0.97  --bmc1_pre_inst_next_state              false
% 3.16/0.97  --bmc1_pre_inst_state                   false
% 3.16/0.97  --bmc1_pre_inst_reach_state             false
% 3.16/0.97  --bmc1_out_unsat_core                   false
% 3.16/0.97  --bmc1_aig_witness_out                  false
% 3.16/0.97  --bmc1_verbose                          false
% 3.16/0.97  --bmc1_dump_clauses_tptp                false
% 3.16/0.97  --bmc1_dump_unsat_core_tptp             false
% 3.16/0.97  --bmc1_dump_file                        -
% 3.16/0.97  --bmc1_ucm_expand_uc_limit              128
% 3.16/0.97  --bmc1_ucm_n_expand_iterations          6
% 3.16/0.97  --bmc1_ucm_extend_mode                  1
% 3.16/0.97  --bmc1_ucm_init_mode                    2
% 3.16/0.97  --bmc1_ucm_cone_mode                    none
% 3.16/0.97  --bmc1_ucm_reduced_relation_type        0
% 3.16/0.97  --bmc1_ucm_relax_model                  4
% 3.16/0.97  --bmc1_ucm_full_tr_after_sat            true
% 3.16/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 3.16/0.97  --bmc1_ucm_layered_model                none
% 3.16/0.97  --bmc1_ucm_max_lemma_size               10
% 3.16/0.97  
% 3.16/0.97  ------ AIG Options
% 3.16/0.97  
% 3.16/0.97  --aig_mode                              false
% 3.16/0.97  
% 3.16/0.97  ------ Instantiation Options
% 3.16/0.97  
% 3.16/0.97  --instantiation_flag                    true
% 3.16/0.97  --inst_sos_flag                         false
% 3.16/0.97  --inst_sos_phase                        true
% 3.16/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.16/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.16/0.97  --inst_lit_sel_side                     none
% 3.16/0.97  --inst_solver_per_active                1400
% 3.16/0.97  --inst_solver_calls_frac                1.
% 3.16/0.97  --inst_passive_queue_type               priority_queues
% 3.16/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.16/0.97  --inst_passive_queues_freq              [25;2]
% 3.16/0.97  --inst_dismatching                      true
% 3.16/0.97  --inst_eager_unprocessed_to_passive     true
% 3.16/0.97  --inst_prop_sim_given                   true
% 3.16/0.97  --inst_prop_sim_new                     false
% 3.16/0.97  --inst_subs_new                         false
% 3.16/0.97  --inst_eq_res_simp                      false
% 3.16/0.97  --inst_subs_given                       false
% 3.16/0.97  --inst_orphan_elimination               true
% 3.16/0.97  --inst_learning_loop_flag               true
% 3.16/0.97  --inst_learning_start                   3000
% 3.16/0.97  --inst_learning_factor                  2
% 3.16/0.97  --inst_start_prop_sim_after_learn       3
% 3.16/0.97  --inst_sel_renew                        solver
% 3.16/0.97  --inst_lit_activity_flag                true
% 3.16/0.97  --inst_restr_to_given                   false
% 3.16/0.97  --inst_activity_threshold               500
% 3.16/0.97  --inst_out_proof                        true
% 3.16/0.97  
% 3.16/0.97  ------ Resolution Options
% 3.16/0.97  
% 3.16/0.97  --resolution_flag                       false
% 3.16/0.97  --res_lit_sel                           adaptive
% 3.16/0.97  --res_lit_sel_side                      none
% 3.16/0.97  --res_ordering                          kbo
% 3.16/0.97  --res_to_prop_solver                    active
% 3.16/0.97  --res_prop_simpl_new                    false
% 3.16/0.97  --res_prop_simpl_given                  true
% 3.16/0.97  --res_passive_queue_type                priority_queues
% 3.16/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.16/0.97  --res_passive_queues_freq               [15;5]
% 3.16/0.97  --res_forward_subs                      full
% 3.16/0.97  --res_backward_subs                     full
% 3.16/0.97  --res_forward_subs_resolution           true
% 3.16/0.97  --res_backward_subs_resolution          true
% 3.16/0.97  --res_orphan_elimination                true
% 3.16/0.97  --res_time_limit                        2.
% 3.16/0.97  --res_out_proof                         true
% 3.16/0.97  
% 3.16/0.97  ------ Superposition Options
% 3.16/0.97  
% 3.16/0.97  --superposition_flag                    true
% 3.16/0.97  --sup_passive_queue_type                priority_queues
% 3.16/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.16/0.97  --sup_passive_queues_freq               [8;1;4]
% 3.16/0.97  --demod_completeness_check              fast
% 3.16/0.97  --demod_use_ground                      true
% 3.16/0.97  --sup_to_prop_solver                    passive
% 3.16/0.97  --sup_prop_simpl_new                    true
% 3.16/0.97  --sup_prop_simpl_given                  true
% 3.16/0.97  --sup_fun_splitting                     false
% 3.16/0.97  --sup_smt_interval                      50000
% 3.16/0.97  
% 3.16/0.97  ------ Superposition Simplification Setup
% 3.16/0.97  
% 3.16/0.97  --sup_indices_passive                   []
% 3.16/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.16/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.16/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.16/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 3.16/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.16/0.97  --sup_full_bw                           [BwDemod]
% 3.16/0.97  --sup_immed_triv                        [TrivRules]
% 3.16/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.16/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.16/0.97  --sup_immed_bw_main                     []
% 3.16/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.16/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 3.16/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.16/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.16/0.97  
% 3.16/0.97  ------ Combination Options
% 3.16/0.97  
% 3.16/0.97  --comb_res_mult                         3
% 3.16/0.97  --comb_sup_mult                         2
% 3.16/0.97  --comb_inst_mult                        10
% 3.16/0.97  
% 3.16/0.97  ------ Debug Options
% 3.16/0.97  
% 3.16/0.97  --dbg_backtrace                         false
% 3.16/0.97  --dbg_dump_prop_clauses                 false
% 3.16/0.97  --dbg_dump_prop_clauses_file            -
% 3.16/0.97  --dbg_out_stat                          false
% 3.16/0.97  
% 3.16/0.97  
% 3.16/0.97  
% 3.16/0.97  
% 3.16/0.97  ------ Proving...
% 3.16/0.97  
% 3.16/0.97  
% 3.16/0.97  % SZS status Theorem for theBenchmark.p
% 3.16/0.97  
% 3.16/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 3.16/0.97  
% 3.16/0.97  fof(f1,axiom,(
% 3.16/0.97    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.16/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/0.97  
% 3.16/0.97  fof(f24,plain,(
% 3.16/0.97    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.16/0.97    inference(nnf_transformation,[],[f1])).
% 3.16/0.97  
% 3.16/0.97  fof(f25,plain,(
% 3.16/0.97    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.16/0.97    inference(flattening,[],[f24])).
% 3.16/0.97  
% 3.16/0.97  fof(f26,plain,(
% 3.16/0.97    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.16/0.97    inference(rectify,[],[f25])).
% 3.16/0.97  
% 3.16/0.97  fof(f27,plain,(
% 3.16/0.97    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 3.16/0.97    introduced(choice_axiom,[])).
% 3.16/0.97  
% 3.16/0.97  fof(f28,plain,(
% 3.16/0.97    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.16/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).
% 3.16/0.97  
% 3.16/0.97  fof(f41,plain,(
% 3.16/0.97    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k3_xboole_0(X0,X1) != X2) )),
% 3.16/0.97    inference(cnf_transformation,[],[f28])).
% 3.16/0.97  
% 3.16/0.97  fof(f3,axiom,(
% 3.16/0.97    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.16/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/0.97  
% 3.16/0.97  fof(f46,plain,(
% 3.16/0.97    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.16/0.97    inference(cnf_transformation,[],[f3])).
% 3.16/0.97  
% 3.16/0.97  fof(f69,plain,(
% 3.16/0.97    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k1_setfam_1(k2_tarski(X0,X1)) != X2) )),
% 3.16/0.97    inference(definition_unfolding,[],[f41,f46])).
% 3.16/0.97  
% 3.16/0.97  fof(f75,plain,(
% 3.16/0.97    ( ! [X4,X0,X1] : (r2_hidden(X4,k1_setfam_1(k2_tarski(X0,X1))) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 3.16/0.97    inference(equality_resolution,[],[f69])).
% 3.16/0.97  
% 3.16/0.97  fof(f7,axiom,(
% 3.16/0.97    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X2,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k3_xboole_0(X1,X2),X0))),
% 3.16/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/0.97  
% 3.16/0.97  fof(f16,plain,(
% 3.16/0.97    ! [X0,X1,X2] : (v3_pre_topc(k3_xboole_0(X1,X2),X0) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.16/0.97    inference(ennf_transformation,[],[f7])).
% 3.16/0.97  
% 3.16/0.97  fof(f17,plain,(
% 3.16/0.97    ! [X0,X1,X2] : (v3_pre_topc(k3_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.16/0.97    inference(flattening,[],[f16])).
% 3.16/0.97  
% 3.16/0.97  fof(f51,plain,(
% 3.16/0.97    ( ! [X2,X0,X1] : (v3_pre_topc(k3_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.16/0.97    inference(cnf_transformation,[],[f17])).
% 3.16/0.97  
% 3.16/0.97  fof(f73,plain,(
% 3.16/0.97    ( ! [X2,X0,X1] : (v3_pre_topc(k1_setfam_1(k2_tarski(X1,X2)),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.16/0.97    inference(definition_unfolding,[],[f51,f46])).
% 3.16/0.97  
% 3.16/0.97  fof(f10,conjecture,(
% 3.16/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) => m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))))))),
% 3.16/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/0.97  
% 3.16/0.97  fof(f11,negated_conjecture,(
% 3.16/0.97    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) => m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))))))),
% 3.16/0.97    inference(negated_conjecture,[],[f10])).
% 3.16/0.97  
% 3.16/0.97  fof(f22,plain,(
% 3.16/0.97    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.16/0.97    inference(ennf_transformation,[],[f11])).
% 3.16/0.97  
% 3.16/0.97  fof(f23,plain,(
% 3.16/0.97    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.16/0.97    inference(flattening,[],[f22])).
% 3.16/0.97  
% 3.16/0.97  fof(f37,plain,(
% 3.16/0.97    ( ! [X2,X0,X1] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) => (~m1_subset_1(k3_xboole_0(X2,sK5),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(sK5,u1_struct_0(k9_yellow_6(X0,X1))))) )),
% 3.16/0.97    introduced(choice_axiom,[])).
% 3.16/0.97  
% 3.16/0.97  fof(f36,plain,(
% 3.16/0.97    ( ! [X0,X1] : (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) => (? [X3] : (~m1_subset_1(k3_xboole_0(sK4,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(sK4,u1_struct_0(k9_yellow_6(X0,X1))))) )),
% 3.16/0.97    introduced(choice_axiom,[])).
% 3.16/0.97  
% 3.16/0.97  fof(f35,plain,(
% 3.16/0.97    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,sK3))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,sK3)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,sK3)))) & m1_subset_1(sK3,u1_struct_0(X0)))) )),
% 3.16/0.97    introduced(choice_axiom,[])).
% 3.16/0.97  
% 3.16/0.97  fof(f34,plain,(
% 3.16/0.97    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK2,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK2,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK2,X1)))) & m1_subset_1(X1,u1_struct_0(sK2))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 3.16/0.97    introduced(choice_axiom,[])).
% 3.16/0.97  
% 3.16/0.97  fof(f38,plain,(
% 3.16/0.97    (((~m1_subset_1(k3_xboole_0(sK4,sK5),u1_struct_0(k9_yellow_6(sK2,sK3))) & m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3)))) & m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3)))) & m1_subset_1(sK3,u1_struct_0(sK2))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 3.16/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f23,f37,f36,f35,f34])).
% 3.16/0.97  
% 3.16/0.97  fof(f61,plain,(
% 3.16/0.97    l1_pre_topc(sK2)),
% 3.16/0.97    inference(cnf_transformation,[],[f38])).
% 3.16/0.97  
% 3.16/0.97  fof(f60,plain,(
% 3.16/0.97    v2_pre_topc(sK2)),
% 3.16/0.97    inference(cnf_transformation,[],[f38])).
% 3.16/0.97  
% 3.16/0.97  fof(f2,axiom,(
% 3.16/0.97    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k3_xboole_0(X0,X2),X1))),
% 3.16/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/0.97  
% 3.16/0.97  fof(f12,plain,(
% 3.16/0.97    ! [X0,X1,X2] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 3.16/0.97    inference(ennf_transformation,[],[f2])).
% 3.16/0.97  
% 3.16/0.97  fof(f45,plain,(
% 3.16/0.97    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 3.16/0.97    inference(cnf_transformation,[],[f12])).
% 3.16/0.97  
% 3.16/0.97  fof(f72,plain,(
% 3.16/0.97    ( ! [X2,X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X0,X2)),X1) | ~r1_tarski(X0,X1)) )),
% 3.16/0.97    inference(definition_unfolding,[],[f45,f46])).
% 3.16/0.97  
% 3.16/0.97  fof(f5,axiom,(
% 3.16/0.97    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.16/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/0.97  
% 3.16/0.97  fof(f29,plain,(
% 3.16/0.97    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.16/0.97    inference(nnf_transformation,[],[f5])).
% 3.16/0.97  
% 3.16/0.97  fof(f49,plain,(
% 3.16/0.97    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.16/0.97    inference(cnf_transformation,[],[f29])).
% 3.16/0.97  
% 3.16/0.97  fof(f9,axiom,(
% 3.16/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))))))),
% 3.16/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/0.97  
% 3.16/0.97  fof(f20,plain,(
% 3.16/0.97    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.16/0.97    inference(ennf_transformation,[],[f9])).
% 3.16/0.97  
% 3.16/0.97  fof(f21,plain,(
% 3.16/0.97    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.16/0.97    inference(flattening,[],[f20])).
% 3.16/0.97  
% 3.16/0.97  fof(f32,plain,(
% 3.16/0.97    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | (~v3_pre_topc(X2,X0) | ~r2_hidden(X1,X2))) & ((v3_pre_topc(X2,X0) & r2_hidden(X1,X2)) | ~r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.16/0.97    inference(nnf_transformation,[],[f21])).
% 3.16/0.97  
% 3.16/0.97  fof(f33,plain,(
% 3.16/0.97    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~v3_pre_topc(X2,X0) | ~r2_hidden(X1,X2)) & ((v3_pre_topc(X2,X0) & r2_hidden(X1,X2)) | ~r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.16/0.97    inference(flattening,[],[f32])).
% 3.16/0.97  
% 3.16/0.97  fof(f58,plain,(
% 3.16/0.97    ( ! [X2,X0,X1] : (r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~v3_pre_topc(X2,X0) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.16/0.97    inference(cnf_transformation,[],[f33])).
% 3.16/0.97  
% 3.16/0.97  fof(f59,plain,(
% 3.16/0.97    ~v2_struct_0(sK2)),
% 3.16/0.97    inference(cnf_transformation,[],[f38])).
% 3.16/0.97  
% 3.16/0.97  fof(f6,axiom,(
% 3.16/0.97    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 3.16/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/0.97  
% 3.16/0.97  fof(f14,plain,(
% 3.16/0.97    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 3.16/0.97    inference(ennf_transformation,[],[f6])).
% 3.16/0.97  
% 3.16/0.97  fof(f15,plain,(
% 3.16/0.97    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.16/0.97    inference(flattening,[],[f14])).
% 3.16/0.97  
% 3.16/0.97  fof(f50,plain,(
% 3.16/0.97    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.16/0.97    inference(cnf_transformation,[],[f15])).
% 3.16/0.97  
% 3.16/0.97  fof(f4,axiom,(
% 3.16/0.97    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 3.16/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/0.97  
% 3.16/0.97  fof(f13,plain,(
% 3.16/0.97    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 3.16/0.97    inference(ennf_transformation,[],[f4])).
% 3.16/0.97  
% 3.16/0.97  fof(f47,plain,(
% 3.16/0.97    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 3.16/0.97    inference(cnf_transformation,[],[f13])).
% 3.16/0.97  
% 3.16/0.97  fof(f65,plain,(
% 3.16/0.97    ~m1_subset_1(k3_xboole_0(sK4,sK5),u1_struct_0(k9_yellow_6(sK2,sK3)))),
% 3.16/0.97    inference(cnf_transformation,[],[f38])).
% 3.16/0.97  
% 3.16/0.97  fof(f74,plain,(
% 3.16/0.97    ~m1_subset_1(k1_setfam_1(k2_tarski(sK4,sK5)),u1_struct_0(k9_yellow_6(sK2,sK3)))),
% 3.16/0.97    inference(definition_unfolding,[],[f65,f46])).
% 3.16/0.97  
% 3.16/0.97  fof(f63,plain,(
% 3.16/0.97    m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3)))),
% 3.16/0.97    inference(cnf_transformation,[],[f38])).
% 3.16/0.97  
% 3.16/0.97  fof(f8,axiom,(
% 3.16/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ? [X3] : (v3_pre_topc(X3,X0) & r2_hidden(X1,X3) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))))),
% 3.16/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/0.97  
% 3.16/0.97  fof(f18,plain,(
% 3.16/0.97    ! [X0] : (! [X1] : (! [X2] : (? [X3] : (v3_pre_topc(X3,X0) & r2_hidden(X1,X3) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.16/0.97    inference(ennf_transformation,[],[f8])).
% 3.16/0.97  
% 3.16/0.97  fof(f19,plain,(
% 3.16/0.97    ! [X0] : (! [X1] : (! [X2] : (? [X3] : (v3_pre_topc(X3,X0) & r2_hidden(X1,X3) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.16/0.97    inference(flattening,[],[f18])).
% 3.16/0.97  
% 3.16/0.97  fof(f30,plain,(
% 3.16/0.97    ! [X2,X1,X0] : (? [X3] : (v3_pre_topc(X3,X0) & r2_hidden(X1,X3) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (v3_pre_topc(sK1(X0,X1,X2),X0) & r2_hidden(X1,sK1(X0,X1,X2)) & sK1(X0,X1,X2) = X2 & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.16/0.97    introduced(choice_axiom,[])).
% 3.16/0.97  
% 3.16/0.97  fof(f31,plain,(
% 3.16/0.97    ! [X0] : (! [X1] : (! [X2] : ((v3_pre_topc(sK1(X0,X1,X2),X0) & r2_hidden(X1,sK1(X0,X1,X2)) & sK1(X0,X1,X2) = X2 & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.16/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f30])).
% 3.16/0.97  
% 3.16/0.97  fof(f53,plain,(
% 3.16/0.97    ( ! [X2,X0,X1] : (sK1(X0,X1,X2) = X2 | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.16/0.97    inference(cnf_transformation,[],[f31])).
% 3.16/0.97  
% 3.16/0.97  fof(f62,plain,(
% 3.16/0.97    m1_subset_1(sK3,u1_struct_0(sK2))),
% 3.16/0.97    inference(cnf_transformation,[],[f38])).
% 3.16/0.97  
% 3.16/0.97  fof(f52,plain,(
% 3.16/0.97    ( ! [X2,X0,X1] : (m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.16/0.97    inference(cnf_transformation,[],[f31])).
% 3.16/0.97  
% 3.16/0.97  fof(f48,plain,(
% 3.16/0.97    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.16/0.97    inference(cnf_transformation,[],[f29])).
% 3.16/0.97  
% 3.16/0.97  fof(f64,plain,(
% 3.16/0.97    m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3)))),
% 3.16/0.97    inference(cnf_transformation,[],[f38])).
% 3.16/0.97  
% 3.16/0.97  fof(f55,plain,(
% 3.16/0.97    ( ! [X2,X0,X1] : (v3_pre_topc(sK1(X0,X1,X2),X0) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.16/0.97    inference(cnf_transformation,[],[f31])).
% 3.16/0.97  
% 3.16/0.97  fof(f54,plain,(
% 3.16/0.97    ( ! [X2,X0,X1] : (r2_hidden(X1,sK1(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.16/0.97    inference(cnf_transformation,[],[f31])).
% 3.16/0.97  
% 3.16/0.97  cnf(c_3,plain,
% 3.16/0.97      ( ~ r2_hidden(X0,X1)
% 3.16/0.97      | ~ r2_hidden(X0,X2)
% 3.16/0.97      | r2_hidden(X0,k1_setfam_1(k2_tarski(X2,X1))) ),
% 3.16/0.97      inference(cnf_transformation,[],[f75]) ).
% 3.16/0.97  
% 3.16/0.97  cnf(c_1343,plain,
% 3.16/0.97      ( r2_hidden(X0,X1) != iProver_top
% 3.16/0.97      | r2_hidden(X0,X2) != iProver_top
% 3.16/0.97      | r2_hidden(X0,k1_setfam_1(k2_tarski(X1,X2))) = iProver_top ),
% 3.16/0.97      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.16/0.97  
% 3.16/0.97  cnf(c_11,plain,
% 3.16/0.97      ( ~ v3_pre_topc(X0,X1)
% 3.16/0.97      | ~ v3_pre_topc(X2,X1)
% 3.16/0.97      | v3_pre_topc(k1_setfam_1(k2_tarski(X2,X0)),X1)
% 3.16/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.16/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.16/0.97      | ~ v2_pre_topc(X1)
% 3.16/0.97      | ~ l1_pre_topc(X1) ),
% 3.16/0.97      inference(cnf_transformation,[],[f73]) ).
% 3.16/0.97  
% 3.16/0.97  cnf(c_23,negated_conjecture,
% 3.16/0.97      ( l1_pre_topc(sK2) ),
% 3.16/0.97      inference(cnf_transformation,[],[f61]) ).
% 3.16/0.97  
% 3.16/0.97  cnf(c_540,plain,
% 3.16/0.97      ( ~ v3_pre_topc(X0,X1)
% 3.16/0.97      | ~ v3_pre_topc(X2,X1)
% 3.16/0.97      | v3_pre_topc(k1_setfam_1(k2_tarski(X2,X0)),X1)
% 3.16/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.16/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.16/0.97      | ~ v2_pre_topc(X1)
% 3.16/0.97      | sK2 != X1 ),
% 3.16/0.97      inference(resolution_lifted,[status(thm)],[c_11,c_23]) ).
% 3.16/0.97  
% 3.16/0.97  cnf(c_541,plain,
% 3.16/0.97      ( ~ v3_pre_topc(X0,sK2)
% 3.16/0.97      | ~ v3_pre_topc(X1,sK2)
% 3.16/0.97      | v3_pre_topc(k1_setfam_1(k2_tarski(X1,X0)),sK2)
% 3.16/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.16/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.16/0.97      | ~ v2_pre_topc(sK2) ),
% 3.16/0.97      inference(unflattening,[status(thm)],[c_540]) ).
% 3.16/0.97  
% 3.16/0.97  cnf(c_24,negated_conjecture,
% 3.16/0.97      ( v2_pre_topc(sK2) ),
% 3.16/0.97      inference(cnf_transformation,[],[f60]) ).
% 3.16/0.97  
% 3.16/0.97  cnf(c_545,plain,
% 3.16/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.16/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.16/0.97      | v3_pre_topc(k1_setfam_1(k2_tarski(X1,X0)),sK2)
% 3.16/0.97      | ~ v3_pre_topc(X1,sK2)
% 3.16/0.97      | ~ v3_pre_topc(X0,sK2) ),
% 3.16/0.97      inference(global_propositional_subsumption,
% 3.16/0.97                [status(thm)],
% 3.16/0.97                [c_541,c_24]) ).
% 3.16/0.97  
% 3.16/0.97  cnf(c_546,plain,
% 3.16/0.97      ( ~ v3_pre_topc(X0,sK2)
% 3.16/0.97      | ~ v3_pre_topc(X1,sK2)
% 3.16/0.97      | v3_pre_topc(k1_setfam_1(k2_tarski(X1,X0)),sK2)
% 3.16/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.16/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.16/0.97      inference(renaming,[status(thm)],[c_545]) ).
% 3.16/0.97  
% 3.16/0.97  cnf(c_1324,plain,
% 3.16/0.97      ( v3_pre_topc(X0,sK2) != iProver_top
% 3.16/0.97      | v3_pre_topc(X1,sK2) != iProver_top
% 3.16/0.97      | v3_pre_topc(k1_setfam_1(k2_tarski(X1,X0)),sK2) = iProver_top
% 3.16/0.97      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.16/0.97      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 3.16/0.97      inference(predicate_to_equality,[status(thm)],[c_546]) ).
% 3.16/0.97  
% 3.16/0.97  cnf(c_6,plain,
% 3.16/0.97      ( ~ r1_tarski(X0,X1)
% 3.16/0.97      | r1_tarski(k1_setfam_1(k2_tarski(X0,X2)),X1) ),
% 3.16/0.97      inference(cnf_transformation,[],[f72]) ).
% 3.16/0.97  
% 3.16/0.97  cnf(c_1340,plain,
% 3.16/0.97      ( r1_tarski(X0,X1) != iProver_top
% 3.16/0.97      | r1_tarski(k1_setfam_1(k2_tarski(X0,X2)),X1) = iProver_top ),
% 3.16/0.97      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.16/0.97  
% 3.16/0.97  cnf(c_8,plain,
% 3.16/0.97      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.16/0.97      inference(cnf_transformation,[],[f49]) ).
% 3.16/0.97  
% 3.16/0.97  cnf(c_1338,plain,
% 3.16/0.97      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.16/0.97      | r1_tarski(X0,X1) != iProver_top ),
% 3.16/0.97      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.16/0.97  
% 3.16/0.97  cnf(c_16,plain,
% 3.16/0.97      ( ~ v3_pre_topc(X0,X1)
% 3.16/0.97      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.16/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.16/0.97      | ~ r2_hidden(X2,X0)
% 3.16/0.97      | r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
% 3.16/0.97      | v2_struct_0(X1)
% 3.16/0.97      | ~ v2_pre_topc(X1)
% 3.16/0.97      | ~ l1_pre_topc(X1) ),
% 3.16/0.97      inference(cnf_transformation,[],[f58]) ).
% 3.16/0.97  
% 3.16/0.97  cnf(c_25,negated_conjecture,
% 3.16/0.97      ( ~ v2_struct_0(sK2) ),
% 3.16/0.97      inference(cnf_transformation,[],[f59]) ).
% 3.16/0.97  
% 3.16/0.97  cnf(c_417,plain,
% 3.16/0.97      ( ~ v3_pre_topc(X0,X1)
% 3.16/0.97      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.16/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.16/0.97      | ~ r2_hidden(X2,X0)
% 3.16/0.97      | r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
% 3.16/0.97      | ~ v2_pre_topc(X1)
% 3.16/0.97      | ~ l1_pre_topc(X1)
% 3.16/0.97      | sK2 != X1 ),
% 3.16/0.97      inference(resolution_lifted,[status(thm)],[c_16,c_25]) ).
% 3.16/0.97  
% 3.16/0.97  cnf(c_418,plain,
% 3.16/0.97      ( ~ v3_pre_topc(X0,sK2)
% 3.16/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 3.16/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.16/0.97      | ~ r2_hidden(X1,X0)
% 3.16/0.97      | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK2,X1)))
% 3.16/0.97      | ~ v2_pre_topc(sK2)
% 3.16/0.97      | ~ l1_pre_topc(sK2) ),
% 3.16/0.97      inference(unflattening,[status(thm)],[c_417]) ).
% 3.16/0.97  
% 3.16/0.97  cnf(c_422,plain,
% 3.16/0.97      ( ~ v3_pre_topc(X0,sK2)
% 3.16/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 3.16/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.16/0.97      | ~ r2_hidden(X1,X0)
% 3.16/0.97      | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK2,X1))) ),
% 3.16/0.97      inference(global_propositional_subsumption,
% 3.16/0.97                [status(thm)],
% 3.16/0.97                [c_418,c_24,c_23]) ).
% 3.16/0.97  
% 3.16/0.97  cnf(c_10,plain,
% 3.16/0.97      ( m1_subset_1(X0,X1)
% 3.16/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.16/0.97      | ~ r2_hidden(X0,X2) ),
% 3.16/0.97      inference(cnf_transformation,[],[f50]) ).
% 3.16/0.97  
% 3.16/0.97  cnf(c_438,plain,
% 3.16/0.97      ( ~ v3_pre_topc(X0,sK2)
% 3.16/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.16/0.97      | ~ r2_hidden(X1,X0)
% 3.16/0.97      | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK2,X1))) ),
% 3.16/0.97      inference(forward_subsumption_resolution,
% 3.16/0.97                [status(thm)],
% 3.16/0.97                [c_422,c_10]) ).
% 3.16/0.97  
% 3.16/0.97  cnf(c_1328,plain,
% 3.16/0.97      ( v3_pre_topc(X0,sK2) != iProver_top
% 3.16/0.97      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.16/0.97      | r2_hidden(X1,X0) != iProver_top
% 3.16/0.97      | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK2,X1))) = iProver_top ),
% 3.16/0.97      inference(predicate_to_equality,[status(thm)],[c_438]) ).
% 3.16/0.97  
% 3.16/0.97  cnf(c_7,plain,
% 3.16/0.97      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 3.16/0.97      inference(cnf_transformation,[],[f47]) ).
% 3.16/0.97  
% 3.16/0.97  cnf(c_1339,plain,
% 3.16/0.97      ( m1_subset_1(X0,X1) = iProver_top
% 3.16/0.97      | r2_hidden(X0,X1) != iProver_top ),
% 3.16/0.97      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.16/0.97  
% 3.16/0.97  cnf(c_2493,plain,
% 3.16/0.97      ( v3_pre_topc(X0,sK2) != iProver_top
% 3.16/0.97      | m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,X1))) = iProver_top
% 3.16/0.97      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.16/0.97      | r2_hidden(X1,X0) != iProver_top ),
% 3.16/0.97      inference(superposition,[status(thm)],[c_1328,c_1339]) ).
% 3.16/0.97  
% 3.16/0.97  cnf(c_19,negated_conjecture,
% 3.16/0.97      ( ~ m1_subset_1(k1_setfam_1(k2_tarski(sK4,sK5)),u1_struct_0(k9_yellow_6(sK2,sK3))) ),
% 3.16/0.97      inference(cnf_transformation,[],[f74]) ).
% 3.16/0.97  
% 3.16/0.97  cnf(c_1335,plain,
% 3.16/0.97      ( m1_subset_1(k1_setfam_1(k2_tarski(sK4,sK5)),u1_struct_0(k9_yellow_6(sK2,sK3))) != iProver_top ),
% 3.16/0.97      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.16/0.97  
% 3.16/0.97  cnf(c_4751,plain,
% 3.16/0.97      ( v3_pre_topc(k1_setfam_1(k2_tarski(sK4,sK5)),sK2) != iProver_top
% 3.16/0.97      | m1_subset_1(k1_setfam_1(k2_tarski(sK4,sK5)),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.16/0.97      | r2_hidden(sK3,k1_setfam_1(k2_tarski(sK4,sK5))) != iProver_top ),
% 3.16/0.97      inference(superposition,[status(thm)],[c_2493,c_1335]) ).
% 3.16/0.97  
% 3.16/0.97  cnf(c_5165,plain,
% 3.16/0.97      ( v3_pre_topc(k1_setfam_1(k2_tarski(sK4,sK5)),sK2) != iProver_top
% 3.16/0.97      | r1_tarski(k1_setfam_1(k2_tarski(sK4,sK5)),u1_struct_0(sK2)) != iProver_top
% 3.16/0.97      | r2_hidden(sK3,k1_setfam_1(k2_tarski(sK4,sK5))) != iProver_top ),
% 3.16/0.97      inference(superposition,[status(thm)],[c_1338,c_4751]) ).
% 3.16/0.97  
% 3.16/0.97  cnf(c_5406,plain,
% 3.16/0.97      ( v3_pre_topc(k1_setfam_1(k2_tarski(sK4,sK5)),sK2) != iProver_top
% 3.16/0.97      | r1_tarski(sK4,u1_struct_0(sK2)) != iProver_top
% 3.16/0.97      | r2_hidden(sK3,k1_setfam_1(k2_tarski(sK4,sK5))) != iProver_top ),
% 3.16/0.97      inference(superposition,[status(thm)],[c_1340,c_5165]) ).
% 3.16/0.97  
% 3.16/0.97  cnf(c_21,negated_conjecture,
% 3.16/0.97      ( m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))) ),
% 3.16/0.97      inference(cnf_transformation,[],[f63]) ).
% 3.16/0.97  
% 3.16/0.97  cnf(c_1333,plain,
% 3.16/0.97      ( m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))) = iProver_top ),
% 3.16/0.97      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.16/0.97  
% 3.16/0.97  cnf(c_14,plain,
% 3.16/0.97      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.16/0.97      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
% 3.16/0.97      | v2_struct_0(X1)
% 3.16/0.97      | ~ v2_pre_topc(X1)
% 3.16/0.97      | ~ l1_pre_topc(X1)
% 3.16/0.97      | sK1(X1,X0,X2) = X2 ),
% 3.16/0.97      inference(cnf_transformation,[],[f53]) ).
% 3.16/0.97  
% 3.16/0.97  cnf(c_467,plain,
% 3.16/0.97      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.16/0.97      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
% 3.16/0.97      | ~ v2_pre_topc(X1)
% 3.16/0.97      | ~ l1_pre_topc(X1)
% 3.16/0.97      | sK1(X1,X0,X2) = X2
% 3.16/0.97      | sK2 != X1 ),
% 3.16/0.97      inference(resolution_lifted,[status(thm)],[c_14,c_25]) ).
% 3.16/0.97  
% 3.16/0.97  cnf(c_468,plain,
% 3.16/0.97      ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,X1)))
% 3.16/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 3.16/0.97      | ~ v2_pre_topc(sK2)
% 3.16/0.97      | ~ l1_pre_topc(sK2)
% 3.16/0.97      | sK1(sK2,X1,X0) = X0 ),
% 3.16/0.97      inference(unflattening,[status(thm)],[c_467]) ).
% 3.16/0.97  
% 3.16/0.97  cnf(c_472,plain,
% 3.16/0.97      ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,X1)))
% 3.16/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 3.16/0.97      | sK1(sK2,X1,X0) = X0 ),
% 3.16/0.97      inference(global_propositional_subsumption,
% 3.16/0.97                [status(thm)],
% 3.16/0.97                [c_468,c_24,c_23]) ).
% 3.16/0.97  
% 3.16/0.97  cnf(c_1326,plain,
% 3.16/0.97      ( sK1(sK2,X0,X1) = X1
% 3.16/0.97      | m1_subset_1(X1,u1_struct_0(k9_yellow_6(sK2,X0))) != iProver_top
% 3.16/0.97      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
% 3.16/0.97      inference(predicate_to_equality,[status(thm)],[c_472]) ).
% 3.16/0.97  
% 3.16/0.97  cnf(c_1577,plain,
% 3.16/0.97      ( sK1(sK2,sK3,sK4) = sK4
% 3.16/0.97      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
% 3.16/0.97      inference(superposition,[status(thm)],[c_1333,c_1326]) ).
% 3.16/0.97  
% 3.16/0.97  cnf(c_22,negated_conjecture,
% 3.16/0.97      ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 3.16/0.97      inference(cnf_transformation,[],[f62]) ).
% 3.16/0.97  
% 3.16/0.97  cnf(c_29,plain,
% 3.16/0.97      ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
% 3.16/0.97      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.16/0.97  
% 3.16/0.97  cnf(c_1643,plain,
% 3.16/0.97      ( sK1(sK2,sK3,sK4) = sK4 ),
% 3.16/0.97      inference(global_propositional_subsumption,
% 3.16/0.97                [status(thm)],
% 3.16/0.97                [c_1577,c_29]) ).
% 3.16/0.97  
% 3.16/0.97  cnf(c_15,plain,
% 3.16/0.97      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.16/0.97      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
% 3.16/0.97      | m1_subset_1(sK1(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
% 3.16/0.97      | v2_struct_0(X1)
% 3.16/0.97      | ~ v2_pre_topc(X1)
% 3.16/0.97      | ~ l1_pre_topc(X1) ),
% 3.16/0.97      inference(cnf_transformation,[],[f52]) ).
% 3.16/0.97  
% 3.16/0.97  cnf(c_446,plain,
% 3.16/0.97      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.16/0.97      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
% 3.16/0.97      | m1_subset_1(sK1(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
% 3.16/0.97      | ~ v2_pre_topc(X1)
% 3.16/0.97      | ~ l1_pre_topc(X1)
% 3.16/0.97      | sK2 != X1 ),
% 3.16/0.97      inference(resolution_lifted,[status(thm)],[c_15,c_25]) ).
% 3.16/0.97  
% 3.16/0.97  cnf(c_447,plain,
% 3.16/0.97      ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,X1)))
% 3.16/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 3.16/0.97      | m1_subset_1(sK1(sK2,X1,X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.16/0.97      | ~ v2_pre_topc(sK2)
% 3.16/0.97      | ~ l1_pre_topc(sK2) ),
% 3.16/0.97      inference(unflattening,[status(thm)],[c_446]) ).
% 3.16/0.97  
% 3.16/0.97  cnf(c_451,plain,
% 3.16/0.97      ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,X1)))
% 3.16/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 3.16/0.97      | m1_subset_1(sK1(sK2,X1,X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.16/0.97      inference(global_propositional_subsumption,
% 3.16/0.97                [status(thm)],
% 3.16/0.97                [c_447,c_24,c_23]) ).
% 3.16/0.97  
% 3.16/0.97  cnf(c_1327,plain,
% 3.16/0.97      ( m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,X1))) != iProver_top
% 3.16/0.97      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
% 3.16/0.97      | m1_subset_1(sK1(sK2,X1,X0),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.16/0.97      inference(predicate_to_equality,[status(thm)],[c_451]) ).
% 3.16/0.97  
% 3.16/0.97  cnf(c_1986,plain,
% 3.16/0.97      ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 3.16/0.97      | m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))) != iProver_top
% 3.16/0.97      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.16/0.97      inference(superposition,[status(thm)],[c_1643,c_1327]) ).
% 3.16/0.97  
% 3.16/0.97  cnf(c_30,plain,
% 3.16/0.97      ( m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))) = iProver_top ),
% 3.16/0.97      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.16/0.97  
% 3.16/0.97  cnf(c_2824,plain,
% 3.16/0.97      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.16/0.97      inference(global_propositional_subsumption,
% 3.16/0.97                [status(thm)],
% 3.16/0.97                [c_1986,c_29,c_30]) ).
% 3.16/0.97  
% 3.16/0.97  cnf(c_9,plain,
% 3.16/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.16/0.97      inference(cnf_transformation,[],[f48]) ).
% 3.16/0.97  
% 3.16/0.97  cnf(c_1337,plain,
% 3.16/0.97      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.16/0.97      | r1_tarski(X0,X1) = iProver_top ),
% 3.16/0.97      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.16/0.97  
% 3.16/0.97  cnf(c_2829,plain,
% 3.16/0.97      ( r1_tarski(sK4,u1_struct_0(sK2)) = iProver_top ),
% 3.16/0.97      inference(superposition,[status(thm)],[c_2824,c_1337]) ).
% 3.16/0.97  
% 3.16/0.97  cnf(c_14413,plain,
% 3.16/0.97      ( v3_pre_topc(k1_setfam_1(k2_tarski(sK4,sK5)),sK2) != iProver_top
% 3.16/0.97      | r2_hidden(sK3,k1_setfam_1(k2_tarski(sK4,sK5))) != iProver_top ),
% 3.16/0.97      inference(global_propositional_subsumption,
% 3.16/0.97                [status(thm)],
% 3.16/0.97                [c_5406,c_2829]) ).
% 3.16/0.97  
% 3.16/0.97  cnf(c_14419,plain,
% 3.16/0.97      ( v3_pre_topc(sK5,sK2) != iProver_top
% 3.16/0.97      | v3_pre_topc(sK4,sK2) != iProver_top
% 3.16/0.97      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.16/0.97      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.16/0.97      | r2_hidden(sK3,k1_setfam_1(k2_tarski(sK4,sK5))) != iProver_top ),
% 3.16/0.97      inference(superposition,[status(thm)],[c_1324,c_14413]) ).
% 3.16/0.97  
% 3.16/0.97  cnf(c_20,negated_conjecture,
% 3.16/0.97      ( m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3))) ),
% 3.16/0.97      inference(cnf_transformation,[],[f64]) ).
% 3.16/0.97  
% 3.16/0.97  cnf(c_31,plain,
% 3.16/0.97      ( m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3))) = iProver_top ),
% 3.16/0.97      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.16/0.97  
% 3.16/0.97  cnf(c_12,plain,
% 3.16/0.97      ( v3_pre_topc(sK1(X0,X1,X2),X0)
% 3.16/0.97      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.16/0.97      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
% 3.16/0.97      | v2_struct_0(X0)
% 3.16/0.97      | ~ v2_pre_topc(X0)
% 3.16/0.97      | ~ l1_pre_topc(X0) ),
% 3.16/0.97      inference(cnf_transformation,[],[f55]) ).
% 3.16/0.97  
% 3.16/0.97  cnf(c_348,plain,
% 3.16/0.97      ( v3_pre_topc(sK1(X0,X1,X2),X0)
% 3.16/0.97      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.16/0.97      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
% 3.16/0.97      | ~ v2_pre_topc(X0)
% 3.16/0.97      | ~ l1_pre_topc(X0)
% 3.16/0.97      | sK2 != X0 ),
% 3.16/0.97      inference(resolution_lifted,[status(thm)],[c_12,c_25]) ).
% 3.16/0.97  
% 3.16/0.97  cnf(c_349,plain,
% 3.16/0.97      ( v3_pre_topc(sK1(sK2,X0,X1),sK2)
% 3.16/0.97      | ~ m1_subset_1(X1,u1_struct_0(k9_yellow_6(sK2,X0)))
% 3.16/0.97      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 3.16/0.97      | ~ v2_pre_topc(sK2)
% 3.16/0.97      | ~ l1_pre_topc(sK2) ),
% 3.16/0.97      inference(unflattening,[status(thm)],[c_348]) ).
% 3.16/0.97  
% 3.16/0.97  cnf(c_353,plain,
% 3.16/0.97      ( v3_pre_topc(sK1(sK2,X0,X1),sK2)
% 3.16/0.97      | ~ m1_subset_1(X1,u1_struct_0(k9_yellow_6(sK2,X0)))
% 3.16/0.97      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
% 3.16/0.97      inference(global_propositional_subsumption,
% 3.16/0.97                [status(thm)],
% 3.16/0.97                [c_349,c_24,c_23]) ).
% 3.16/0.97  
% 3.16/0.97  cnf(c_1331,plain,
% 3.16/0.97      ( v3_pre_topc(sK1(sK2,X0,X1),sK2) = iProver_top
% 3.16/0.97      | m1_subset_1(X1,u1_struct_0(k9_yellow_6(sK2,X0))) != iProver_top
% 3.16/0.97      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
% 3.16/0.97      inference(predicate_to_equality,[status(thm)],[c_353]) ).
% 3.16/0.97  
% 3.16/0.97  cnf(c_1902,plain,
% 3.16/0.97      ( v3_pre_topc(sK1(sK2,sK3,sK4),sK2) = iProver_top
% 3.16/0.97      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
% 3.16/0.97      inference(superposition,[status(thm)],[c_1333,c_1331]) ).
% 3.16/0.97  
% 3.16/0.97  cnf(c_1905,plain,
% 3.16/0.97      ( v3_pre_topc(sK4,sK2) = iProver_top
% 3.16/0.97      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
% 3.16/0.97      inference(light_normalisation,[status(thm)],[c_1902,c_1643]) ).
% 3.16/0.97  
% 3.16/0.97  cnf(c_1334,plain,
% 3.16/0.97      ( m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3))) = iProver_top ),
% 3.16/0.97      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.16/0.97  
% 3.16/0.97  cnf(c_1901,plain,
% 3.16/0.97      ( v3_pre_topc(sK1(sK2,sK3,sK5),sK2) = iProver_top
% 3.16/0.97      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
% 3.16/0.97      inference(superposition,[status(thm)],[c_1334,c_1331]) ).
% 3.16/0.97  
% 3.16/0.97  cnf(c_1576,plain,
% 3.16/0.97      ( sK1(sK2,sK3,sK5) = sK5
% 3.16/0.97      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
% 3.16/0.97      inference(superposition,[status(thm)],[c_1334,c_1326]) ).
% 3.16/0.97  
% 3.16/0.97  cnf(c_1589,plain,
% 3.16/0.97      ( sK1(sK2,sK3,sK5) = sK5 ),
% 3.16/0.97      inference(global_propositional_subsumption,
% 3.16/0.97                [status(thm)],
% 3.16/0.97                [c_1576,c_29]) ).
% 3.16/0.97  
% 3.16/0.97  cnf(c_1910,plain,
% 3.16/0.97      ( v3_pre_topc(sK5,sK2) = iProver_top
% 3.16/0.97      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
% 3.16/0.97      inference(light_normalisation,[status(thm)],[c_1901,c_1589]) ).
% 3.16/0.97  
% 3.16/0.97  cnf(c_1985,plain,
% 3.16/0.97      ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 3.16/0.97      | m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3))) != iProver_top
% 3.16/0.97      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.16/0.97      inference(superposition,[status(thm)],[c_1589,c_1327]) ).
% 3.16/0.97  
% 3.16/0.97  cnf(c_14602,plain,
% 3.16/0.97      ( r2_hidden(sK3,k1_setfam_1(k2_tarski(sK4,sK5))) != iProver_top ),
% 3.16/0.97      inference(global_propositional_subsumption,
% 3.16/0.97                [status(thm)],
% 3.16/0.97                [c_14419,c_29,c_30,c_31,c_1905,c_1910,c_1985,c_1986]) ).
% 3.16/0.97  
% 3.16/0.97  cnf(c_14607,plain,
% 3.16/0.97      ( r2_hidden(sK3,sK5) != iProver_top
% 3.16/0.97      | r2_hidden(sK3,sK4) != iProver_top ),
% 3.16/0.97      inference(superposition,[status(thm)],[c_1343,c_14602]) ).
% 3.16/0.97  
% 3.16/0.97  cnf(c_13,plain,
% 3.16/0.97      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.16/0.97      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
% 3.16/0.97      | r2_hidden(X0,sK1(X1,X0,X2))
% 3.16/0.97      | v2_struct_0(X1)
% 3.16/0.97      | ~ v2_pre_topc(X1)
% 3.16/0.97      | ~ l1_pre_topc(X1) ),
% 3.16/0.97      inference(cnf_transformation,[],[f54]) ).
% 3.16/0.97  
% 3.16/0.97  cnf(c_488,plain,
% 3.16/0.97      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.16/0.97      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
% 3.16/0.97      | r2_hidden(X0,sK1(X1,X0,X2))
% 3.16/0.97      | ~ v2_pre_topc(X1)
% 3.16/0.97      | ~ l1_pre_topc(X1)
% 3.16/0.97      | sK2 != X1 ),
% 3.16/0.97      inference(resolution_lifted,[status(thm)],[c_13,c_25]) ).
% 3.16/0.97  
% 3.16/0.97  cnf(c_489,plain,
% 3.16/0.97      ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,X1)))
% 3.16/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 3.16/0.97      | r2_hidden(X1,sK1(sK2,X1,X0))
% 3.16/0.97      | ~ v2_pre_topc(sK2)
% 3.16/0.97      | ~ l1_pre_topc(sK2) ),
% 3.16/0.97      inference(unflattening,[status(thm)],[c_488]) ).
% 3.16/0.97  
% 3.16/0.97  cnf(c_493,plain,
% 3.16/0.97      ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,X1)))
% 3.16/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 3.16/0.97      | r2_hidden(X1,sK1(sK2,X1,X0)) ),
% 3.16/0.97      inference(global_propositional_subsumption,
% 3.16/0.97                [status(thm)],
% 3.16/0.97                [c_489,c_24,c_23]) ).
% 3.16/0.97  
% 3.16/0.97  cnf(c_1325,plain,
% 3.16/0.97      ( m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,X1))) != iProver_top
% 3.16/0.97      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
% 3.16/0.97      | r2_hidden(X1,sK1(sK2,X1,X0)) = iProver_top ),
% 3.16/0.97      inference(predicate_to_equality,[status(thm)],[c_493]) ).
% 3.16/0.97  
% 3.16/0.97  cnf(c_1650,plain,
% 3.16/0.97      ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 3.16/0.97      | r2_hidden(sK3,sK1(sK2,sK3,sK5)) = iProver_top ),
% 3.16/0.97      inference(superposition,[status(thm)],[c_1334,c_1325]) ).
% 3.16/0.97  
% 3.16/0.97  cnf(c_1659,plain,
% 3.16/0.97      ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 3.16/0.97      | r2_hidden(sK3,sK5) = iProver_top ),
% 3.16/0.97      inference(light_normalisation,[status(thm)],[c_1650,c_1589]) ).
% 3.16/0.97  
% 3.16/0.97  cnf(c_1651,plain,
% 3.16/0.97      ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 3.16/0.97      | r2_hidden(sK3,sK1(sK2,sK3,sK4)) = iProver_top ),
% 3.16/0.97      inference(superposition,[status(thm)],[c_1333,c_1325]) ).
% 3.16/0.97  
% 3.16/0.97  cnf(c_1654,plain,
% 3.16/0.97      ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 3.16/0.97      | r2_hidden(sK3,sK4) = iProver_top ),
% 3.16/0.97      inference(light_normalisation,[status(thm)],[c_1651,c_1643]) ).
% 3.16/0.97  
% 3.16/0.97  cnf(contradiction,plain,
% 3.16/0.97      ( $false ),
% 3.16/0.97      inference(minisat,[status(thm)],[c_14607,c_1659,c_1654,c_29]) ).
% 3.16/0.97  
% 3.16/0.97  
% 3.16/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 3.16/0.97  
% 3.16/0.97  ------                               Statistics
% 3.16/0.97  
% 3.16/0.97  ------ General
% 3.16/0.97  
% 3.16/0.97  abstr_ref_over_cycles:                  0
% 3.16/0.97  abstr_ref_under_cycles:                 0
% 3.16/0.97  gc_basic_clause_elim:                   0
% 3.16/0.97  forced_gc_time:                         0
% 3.16/0.97  parsing_time:                           0.01
% 3.16/0.97  unif_index_cands_time:                  0.
% 3.16/0.97  unif_index_add_time:                    0.
% 3.16/0.97  orderings_time:                         0.
% 3.16/0.97  out_proof_time:                         0.014
% 3.16/0.97  total_time:                             0.41
% 3.16/0.97  num_of_symbols:                         49
% 3.16/0.97  num_of_terms:                           13461
% 3.16/0.97  
% 3.16/0.97  ------ Preprocessing
% 3.16/0.97  
% 3.16/0.97  num_of_splits:                          0
% 3.16/0.97  num_of_split_atoms:                     0
% 3.16/0.97  num_of_reused_defs:                     0
% 3.16/0.97  num_eq_ax_congr_red:                    20
% 3.16/0.97  num_of_sem_filtered_clauses:            1
% 3.16/0.97  num_of_subtypes:                        0
% 3.16/0.97  monotx_restored_types:                  0
% 3.16/0.97  sat_num_of_epr_types:                   0
% 3.16/0.97  sat_num_of_non_cyclic_types:            0
% 3.16/0.97  sat_guarded_non_collapsed_types:        0
% 3.16/0.97  num_pure_diseq_elim:                    0
% 3.16/0.97  simp_replaced_by:                       0
% 3.16/0.97  res_preprocessed:                       120
% 3.16/0.97  prep_upred:                             0
% 3.16/0.97  prep_unflattend:                        8
% 3.16/0.97  smt_new_axioms:                         0
% 3.16/0.97  pred_elim_cands:                        4
% 3.16/0.97  pred_elim:                              3
% 3.16/0.97  pred_elim_cl:                           3
% 3.16/0.97  pred_elim_cycles:                       5
% 3.16/0.97  merged_defs:                            8
% 3.16/0.97  merged_defs_ncl:                        0
% 3.16/0.97  bin_hyper_res:                          8
% 3.16/0.97  prep_cycles:                            4
% 3.16/0.97  pred_elim_time:                         0.005
% 3.16/0.97  splitting_time:                         0.
% 3.16/0.97  sem_filter_time:                        0.
% 3.16/0.97  monotx_time:                            0.001
% 3.16/0.97  subtype_inf_time:                       0.
% 3.16/0.97  
% 3.16/0.97  ------ Problem properties
% 3.16/0.97  
% 3.16/0.97  clauses:                                23
% 3.16/0.97  conjectures:                            4
% 3.16/0.97  epr:                                    1
% 3.16/0.97  horn:                                   21
% 3.16/0.97  ground:                                 4
% 3.16/0.97  unary:                                  4
% 3.16/0.97  binary:                                 6
% 3.16/0.97  lits:                                   61
% 3.16/0.97  lits_eq:                                4
% 3.16/0.97  fd_pure:                                0
% 3.16/0.97  fd_pseudo:                              0
% 3.16/0.97  fd_cond:                                0
% 3.16/0.97  fd_pseudo_cond:                         3
% 3.16/0.97  ac_symbols:                             0
% 3.16/0.97  
% 3.16/0.97  ------ Propositional Solver
% 3.16/0.97  
% 3.16/0.97  prop_solver_calls:                      28
% 3.16/0.97  prop_fast_solver_calls:                 1134
% 3.16/0.97  smt_solver_calls:                       0
% 3.16/0.97  smt_fast_solver_calls:                  0
% 3.16/0.97  prop_num_of_clauses:                    4936
% 3.16/0.97  prop_preprocess_simplified:             8910
% 3.16/0.97  prop_fo_subsumed:                       34
% 3.16/0.97  prop_solver_time:                       0.
% 3.16/0.97  smt_solver_time:                        0.
% 3.16/0.97  smt_fast_solver_time:                   0.
% 3.16/0.97  prop_fast_solver_time:                  0.
% 3.16/0.97  prop_unsat_core_time:                   0.
% 3.16/0.97  
% 3.16/0.97  ------ QBF
% 3.16/0.97  
% 3.16/0.97  qbf_q_res:                              0
% 3.16/0.97  qbf_num_tautologies:                    0
% 3.16/0.97  qbf_prep_cycles:                        0
% 3.16/0.97  
% 3.16/0.97  ------ BMC1
% 3.16/0.97  
% 3.16/0.97  bmc1_current_bound:                     -1
% 3.16/0.97  bmc1_last_solved_bound:                 -1
% 3.16/0.97  bmc1_unsat_core_size:                   -1
% 3.16/0.97  bmc1_unsat_core_parents_size:           -1
% 3.16/0.97  bmc1_merge_next_fun:                    0
% 3.16/0.97  bmc1_unsat_core_clauses_time:           0.
% 3.16/0.97  
% 3.16/0.97  ------ Instantiation
% 3.16/0.97  
% 3.16/0.97  inst_num_of_clauses:                    1194
% 3.16/0.97  inst_num_in_passive:                    201
% 3.16/0.97  inst_num_in_active:                     468
% 3.16/0.97  inst_num_in_unprocessed:                525
% 3.16/0.97  inst_num_of_loops:                      510
% 3.16/0.97  inst_num_of_learning_restarts:          0
% 3.16/0.97  inst_num_moves_active_passive:          39
% 3.16/0.97  inst_lit_activity:                      0
% 3.16/0.97  inst_lit_activity_moves:                1
% 3.16/0.97  inst_num_tautologies:                   0
% 3.16/0.97  inst_num_prop_implied:                  0
% 3.16/0.97  inst_num_existing_simplified:           0
% 3.16/0.97  inst_num_eq_res_simplified:             0
% 3.16/0.97  inst_num_child_elim:                    0
% 3.16/0.97  inst_num_of_dismatching_blockings:      617
% 3.16/0.97  inst_num_of_non_proper_insts:           1211
% 3.16/0.97  inst_num_of_duplicates:                 0
% 3.16/0.97  inst_inst_num_from_inst_to_res:         0
% 3.16/0.97  inst_dismatching_checking_time:         0.
% 3.16/0.97  
% 3.16/0.97  ------ Resolution
% 3.16/0.97  
% 3.16/0.97  res_num_of_clauses:                     0
% 3.16/0.97  res_num_in_passive:                     0
% 3.16/0.97  res_num_in_active:                      0
% 3.16/0.97  res_num_of_loops:                       124
% 3.16/0.97  res_forward_subset_subsumed:            61
% 3.16/0.97  res_backward_subset_subsumed:           0
% 3.16/0.97  res_forward_subsumed:                   0
% 3.16/0.97  res_backward_subsumed:                  0
% 3.16/0.97  res_forward_subsumption_resolution:     1
% 3.16/0.97  res_backward_subsumption_resolution:    0
% 3.16/0.97  res_clause_to_clause_subsumption:       2492
% 3.16/0.97  res_orphan_elimination:                 0
% 3.16/0.97  res_tautology_del:                      61
% 3.16/0.97  res_num_eq_res_simplified:              0
% 3.16/0.97  res_num_sel_changes:                    0
% 3.16/0.97  res_moves_from_active_to_pass:          0
% 3.16/0.97  
% 3.16/0.97  ------ Superposition
% 3.16/0.97  
% 3.16/0.97  sup_time_total:                         0.
% 3.16/0.97  sup_time_generating:                    0.
% 3.16/0.97  sup_time_sim_full:                      0.
% 3.16/0.97  sup_time_sim_immed:                     0.
% 3.16/0.97  
% 3.16/0.97  sup_num_of_clauses:                     460
% 3.16/0.97  sup_num_in_active:                      102
% 3.16/0.97  sup_num_in_passive:                     358
% 3.16/0.97  sup_num_of_loops:                       101
% 3.16/0.97  sup_fw_superposition:                   129
% 3.16/0.97  sup_bw_superposition:                   483
% 3.16/0.97  sup_immediate_simplified:               142
% 3.16/0.97  sup_given_eliminated:                   0
% 3.16/0.97  comparisons_done:                       0
% 3.16/0.97  comparisons_avoided:                    20
% 3.16/0.97  
% 3.16/0.97  ------ Simplifications
% 3.16/0.97  
% 3.16/0.97  
% 3.16/0.97  sim_fw_subset_subsumed:                 4
% 3.16/0.97  sim_bw_subset_subsumed:                 5
% 3.16/0.97  sim_fw_subsumed:                        109
% 3.16/0.97  sim_bw_subsumed:                        4
% 3.16/0.97  sim_fw_subsumption_res:                 21
% 3.16/0.97  sim_bw_subsumption_res:                 0
% 3.16/0.97  sim_tautology_del:                      13
% 3.16/0.97  sim_eq_tautology_del:                   0
% 3.16/0.97  sim_eq_res_simp:                        7
% 3.16/0.97  sim_fw_demodulated:                     0
% 3.16/0.97  sim_bw_demodulated:                     0
% 3.16/0.97  sim_light_normalised:                   8
% 3.16/0.97  sim_joinable_taut:                      0
% 3.16/0.97  sim_joinable_simp:                      0
% 3.16/0.97  sim_ac_normalised:                      0
% 3.16/0.97  sim_smt_subsumption:                    0
% 3.16/0.97  
%------------------------------------------------------------------------------
