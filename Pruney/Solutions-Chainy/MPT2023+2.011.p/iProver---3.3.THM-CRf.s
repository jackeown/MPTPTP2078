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
% DateTime   : Thu Dec  3 12:28:47 EST 2020

% Result     : Theorem 3.06s
% Output     : CNFRefutation 3.06s
% Verified   : 
% Statistics : Number of formulae       :  141 (1210 expanded)
%              Number of clauses        :   79 ( 251 expanded)
%              Number of leaves         :   16 ( 454 expanded)
%              Depth                    :   22
%              Number of atoms          :  597 (7235 expanded)
%              Number of equality atoms :  121 ( 347 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(nnf_transformation,[],[f1])).

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
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f25])).

fof(f27,plain,(
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
    inference(rectify,[],[f26])).

fof(f28,plain,(
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

fof(f29,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).

fof(f41,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f68,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k1_setfam_1(k2_tarski(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f41,f47])).

fof(f74,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k1_setfam_1(k2_tarski(X0,X1)))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f68])).

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

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( v3_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( v3_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(k1_setfam_1(k2_tarski(X1,X2)),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(definition_unfolding,[],[f50,f47])).

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
    inference(ennf_transformation,[],[f11])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f24,f37,f36,f35,f34])).

fof(f60,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f59,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f62,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f8])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f30])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( sK1(X0,X1,X2) = X2
      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f58,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f61,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f38])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k8_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k8_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k8_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k8_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f46,f47])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k8_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k8_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k8_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

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
    inference(ennf_transformation,[],[f9])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

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
    inference(nnf_transformation,[],[f22])).

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

fof(f57,plain,(
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

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f64,plain,(
    ~ m1_subset_1(k3_xboole_0(sK4,sK5),u1_struct_0(k9_yellow_6(sK2,sK3))) ),
    inference(cnf_transformation,[],[f38])).

fof(f73,plain,(
    ~ m1_subset_1(k1_setfam_1(k2_tarski(sK4,sK5)),u1_struct_0(k9_yellow_6(sK2,sK3))) ),
    inference(definition_unfolding,[],[f64,f47])).

fof(f63,plain,(
    m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3))) ),
    inference(cnf_transformation,[],[f38])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(sK1(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f53,plain,(
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
    inference(cnf_transformation,[],[f74])).

cnf(c_1048,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X0,k1_setfam_1(k2_tarski(X1,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_10,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ v3_pre_topc(X2,X1)
    | v3_pre_topc(k1_setfam_1(k2_tarski(X2,X0)),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_22,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_468,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ v3_pre_topc(X2,X1)
    | v3_pre_topc(k1_setfam_1(k2_tarski(X2,X0)),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_22])).

cnf(c_469,plain,
    ( ~ v3_pre_topc(X0,sK2)
    | ~ v3_pre_topc(X1,sK2)
    | v3_pre_topc(k1_setfam_1(k2_tarski(X1,X0)),sK2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_468])).

cnf(c_23,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_473,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | v3_pre_topc(k1_setfam_1(k2_tarski(X1,X0)),sK2)
    | ~ v3_pre_topc(X1,sK2)
    | ~ v3_pre_topc(X0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_469,c_23])).

cnf(c_474,plain,
    ( ~ v3_pre_topc(X0,sK2)
    | ~ v3_pre_topc(X1,sK2)
    | v3_pre_topc(k1_setfam_1(k2_tarski(X1,X0)),sK2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(renaming,[status(thm)],[c_473])).

cnf(c_1030,plain,
    ( v3_pre_topc(X0,sK2) != iProver_top
    | v3_pre_topc(X1,sK2) != iProver_top
    | v3_pre_topc(k1_setfam_1(k2_tarski(X1,X0)),sK2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_474])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1039,plain,
    ( m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK1(X1,X0,X2) = X2 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_24,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_395,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK1(X1,X0,X2) = X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_24])).

cnf(c_396,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | sK1(sK2,X1,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_395])).

cnf(c_400,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | sK1(sK2,X1,X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_396,c_23,c_22])).

cnf(c_1032,plain,
    ( sK1(sK2,X0,X1) = X1
    | m1_subset_1(X1,u1_struct_0(k9_yellow_6(sK2,X0))) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_400])).

cnf(c_1275,plain,
    ( sK1(sK2,sK3,sK4) = sK4
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1039,c_1032])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_28,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1375,plain,
    ( sK1(sK2,sK3,sK4) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1275,c_28])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
    | m1_subset_1(sK1(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_374,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
    | m1_subset_1(sK1(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_24])).

cnf(c_375,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(sK1(sK2,X1,X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_374])).

cnf(c_379,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(sK1(sK2,X1,X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_375,c_23,c_22])).

cnf(c_1033,plain,
    ( m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,X1))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK1(sK2,X1,X0),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_379])).

cnf(c_1777,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1375,c_1033])).

cnf(c_29,plain,
    ( m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2640,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1777,c_28,c_29])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k8_subset_1(X1,X0,X2) = k1_setfam_1(k2_tarski(X0,X2)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1044,plain,
    ( k8_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2645,plain,
    ( k8_subset_1(u1_struct_0(sK2),sK4,X0) = k1_setfam_1(k2_tarski(sK4,X0)) ),
    inference(superposition,[status(thm)],[c_2640,c_1044])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k8_subset_1(X1,X0,X2),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1045,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k8_subset_1(X1,X0,X2),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4230,plain,
    ( m1_subset_1(k1_setfam_1(k2_tarski(sK4,X0)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2645,c_1045])).

cnf(c_6140,plain,
    ( m1_subset_1(k1_setfam_1(k2_tarski(sK4,X0)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4230,c_28,c_29,c_1777])).

cnf(c_15,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_345,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_24])).

cnf(c_346,plain,
    ( ~ v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X1,X0)
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK2,X1)))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_345])).

cnf(c_350,plain,
    ( ~ v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X1,X0)
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK2,X1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_346,c_23,c_22])).

cnf(c_9,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_366,plain,
    ( ~ v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X1,X0)
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK2,X1))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_350,c_9])).

cnf(c_1034,plain,
    ( v3_pre_topc(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(X1,X0) != iProver_top
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK2,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_366])).

cnf(c_8,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1043,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2224,plain,
    ( v3_pre_topc(X0,sK2) != iProver_top
    | m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,X1))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1034,c_1043])).

cnf(c_18,negated_conjecture,
    ( ~ m1_subset_1(k1_setfam_1(k2_tarski(sK4,sK5)),u1_struct_0(k9_yellow_6(sK2,sK3))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1041,plain,
    ( m1_subset_1(k1_setfam_1(k2_tarski(sK4,sK5)),u1_struct_0(k9_yellow_6(sK2,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_4344,plain,
    ( v3_pre_topc(k1_setfam_1(k2_tarski(sK4,sK5)),sK2) != iProver_top
    | m1_subset_1(k1_setfam_1(k2_tarski(sK4,sK5)),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(sK3,k1_setfam_1(k2_tarski(sK4,sK5))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2224,c_1041])).

cnf(c_6151,plain,
    ( v3_pre_topc(k1_setfam_1(k2_tarski(sK4,sK5)),sK2) != iProver_top
    | r2_hidden(sK3,k1_setfam_1(k2_tarski(sK4,sK5))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6140,c_4344])).

cnf(c_6915,plain,
    ( v3_pre_topc(sK5,sK2) != iProver_top
    | v3_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(sK3,k1_setfam_1(k2_tarski(sK4,sK5))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1030,c_6151])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_30,plain,
    ( m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_11,plain,
    ( v3_pre_topc(sK1(X0,X1,X2),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_276,plain,
    ( v3_pre_topc(sK1(X0,X1,X2),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_24])).

cnf(c_277,plain,
    ( v3_pre_topc(sK1(sK2,X0,X1),sK2)
    | ~ m1_subset_1(X1,u1_struct_0(k9_yellow_6(sK2,X0)))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_276])).

cnf(c_281,plain,
    ( v3_pre_topc(sK1(sK2,X0,X1),sK2)
    | ~ m1_subset_1(X1,u1_struct_0(k9_yellow_6(sK2,X0)))
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_277,c_23,c_22])).

cnf(c_1037,plain,
    ( v3_pre_topc(sK1(sK2,X0,X1),sK2) = iProver_top
    | m1_subset_1(X1,u1_struct_0(k9_yellow_6(sK2,X0))) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_281])).

cnf(c_1628,plain,
    ( v3_pre_topc(sK1(sK2,sK3,sK4),sK2) = iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1039,c_1037])).

cnf(c_1631,plain,
    ( v3_pre_topc(sK4,sK2) = iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1628,c_1375])).

cnf(c_1040,plain,
    ( m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1627,plain,
    ( v3_pre_topc(sK1(sK2,sK3,sK5),sK2) = iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1040,c_1037])).

cnf(c_1274,plain,
    ( sK1(sK2,sK3,sK5) = sK5
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1040,c_1032])).

cnf(c_1287,plain,
    ( sK1(sK2,sK3,sK5) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1274,c_28])).

cnf(c_1636,plain,
    ( v3_pre_topc(sK5,sK2) = iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1627,c_1287])).

cnf(c_1776,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1287,c_1033])).

cnf(c_6918,plain,
    ( r2_hidden(sK3,k1_setfam_1(k2_tarski(sK4,sK5))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6915,c_28,c_29,c_30,c_1631,c_1636,c_1776,c_1777])).

cnf(c_6923,plain,
    ( r2_hidden(sK3,sK5) != iProver_top
    | r2_hidden(sK3,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1048,c_6918])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
    | r2_hidden(X0,sK1(X1,X0,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_416,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
    | r2_hidden(X0,sK1(X1,X0,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_24])).

cnf(c_417,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | r2_hidden(X1,sK1(sK2,X1,X0))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_416])).

cnf(c_421,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | r2_hidden(X1,sK1(sK2,X1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_417,c_23,c_22])).

cnf(c_1031,plain,
    ( m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,X1))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X1,sK1(sK2,X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_421])).

cnf(c_1382,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK3,sK1(sK2,sK3,sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1040,c_1031])).

cnf(c_1391,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK3,sK5) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1382,c_1287])).

cnf(c_1383,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK3,sK1(sK2,sK3,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1039,c_1031])).

cnf(c_1386,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK3,sK4) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1383,c_1375])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6923,c_1391,c_1386,c_28])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n019.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:24:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.06/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.06/0.99  
% 3.06/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.06/0.99  
% 3.06/0.99  ------  iProver source info
% 3.06/0.99  
% 3.06/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.06/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.06/0.99  git: non_committed_changes: false
% 3.06/0.99  git: last_make_outside_of_git: false
% 3.06/0.99  
% 3.06/0.99  ------ 
% 3.06/0.99  
% 3.06/0.99  ------ Input Options
% 3.06/0.99  
% 3.06/0.99  --out_options                           all
% 3.06/0.99  --tptp_safe_out                         true
% 3.06/0.99  --problem_path                          ""
% 3.06/0.99  --include_path                          ""
% 3.06/0.99  --clausifier                            res/vclausify_rel
% 3.06/0.99  --clausifier_options                    --mode clausify
% 3.06/0.99  --stdin                                 false
% 3.06/0.99  --stats_out                             all
% 3.06/0.99  
% 3.06/0.99  ------ General Options
% 3.06/0.99  
% 3.06/0.99  --fof                                   false
% 3.06/0.99  --time_out_real                         305.
% 3.06/0.99  --time_out_virtual                      -1.
% 3.06/0.99  --symbol_type_check                     false
% 3.06/0.99  --clausify_out                          false
% 3.06/0.99  --sig_cnt_out                           false
% 3.06/0.99  --trig_cnt_out                          false
% 3.06/0.99  --trig_cnt_out_tolerance                1.
% 3.06/0.99  --trig_cnt_out_sk_spl                   false
% 3.06/0.99  --abstr_cl_out                          false
% 3.06/0.99  
% 3.06/0.99  ------ Global Options
% 3.06/0.99  
% 3.06/0.99  --schedule                              default
% 3.06/0.99  --add_important_lit                     false
% 3.06/0.99  --prop_solver_per_cl                    1000
% 3.06/0.99  --min_unsat_core                        false
% 3.06/0.99  --soft_assumptions                      false
% 3.06/0.99  --soft_lemma_size                       3
% 3.06/0.99  --prop_impl_unit_size                   0
% 3.06/0.99  --prop_impl_unit                        []
% 3.06/0.99  --share_sel_clauses                     true
% 3.06/0.99  --reset_solvers                         false
% 3.06/0.99  --bc_imp_inh                            [conj_cone]
% 3.06/0.99  --conj_cone_tolerance                   3.
% 3.06/0.99  --extra_neg_conj                        none
% 3.06/0.99  --large_theory_mode                     true
% 3.06/0.99  --prolific_symb_bound                   200
% 3.06/0.99  --lt_threshold                          2000
% 3.06/0.99  --clause_weak_htbl                      true
% 3.06/0.99  --gc_record_bc_elim                     false
% 3.06/0.99  
% 3.06/0.99  ------ Preprocessing Options
% 3.06/0.99  
% 3.06/0.99  --preprocessing_flag                    true
% 3.06/0.99  --time_out_prep_mult                    0.1
% 3.06/0.99  --splitting_mode                        input
% 3.06/0.99  --splitting_grd                         true
% 3.06/0.99  --splitting_cvd                         false
% 3.06/0.99  --splitting_cvd_svl                     false
% 3.06/0.99  --splitting_nvd                         32
% 3.06/0.99  --sub_typing                            true
% 3.06/0.99  --prep_gs_sim                           true
% 3.06/0.99  --prep_unflatten                        true
% 3.06/0.99  --prep_res_sim                          true
% 3.06/0.99  --prep_upred                            true
% 3.06/0.99  --prep_sem_filter                       exhaustive
% 3.06/0.99  --prep_sem_filter_out                   false
% 3.06/0.99  --pred_elim                             true
% 3.06/0.99  --res_sim_input                         true
% 3.06/0.99  --eq_ax_congr_red                       true
% 3.06/0.99  --pure_diseq_elim                       true
% 3.06/0.99  --brand_transform                       false
% 3.06/0.99  --non_eq_to_eq                          false
% 3.06/0.99  --prep_def_merge                        true
% 3.06/0.99  --prep_def_merge_prop_impl              false
% 3.06/0.99  --prep_def_merge_mbd                    true
% 3.06/0.99  --prep_def_merge_tr_red                 false
% 3.06/0.99  --prep_def_merge_tr_cl                  false
% 3.06/0.99  --smt_preprocessing                     true
% 3.06/0.99  --smt_ac_axioms                         fast
% 3.06/0.99  --preprocessed_out                      false
% 3.06/0.99  --preprocessed_stats                    false
% 3.06/0.99  
% 3.06/0.99  ------ Abstraction refinement Options
% 3.06/0.99  
% 3.06/0.99  --abstr_ref                             []
% 3.06/0.99  --abstr_ref_prep                        false
% 3.06/0.99  --abstr_ref_until_sat                   false
% 3.06/0.99  --abstr_ref_sig_restrict                funpre
% 3.06/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.06/0.99  --abstr_ref_under                       []
% 3.06/0.99  
% 3.06/0.99  ------ SAT Options
% 3.06/0.99  
% 3.06/0.99  --sat_mode                              false
% 3.06/0.99  --sat_fm_restart_options                ""
% 3.06/0.99  --sat_gr_def                            false
% 3.06/0.99  --sat_epr_types                         true
% 3.06/0.99  --sat_non_cyclic_types                  false
% 3.06/0.99  --sat_finite_models                     false
% 3.06/0.99  --sat_fm_lemmas                         false
% 3.06/0.99  --sat_fm_prep                           false
% 3.06/0.99  --sat_fm_uc_incr                        true
% 3.06/0.99  --sat_out_model                         small
% 3.06/0.99  --sat_out_clauses                       false
% 3.06/0.99  
% 3.06/0.99  ------ QBF Options
% 3.06/0.99  
% 3.06/0.99  --qbf_mode                              false
% 3.06/0.99  --qbf_elim_univ                         false
% 3.06/0.99  --qbf_dom_inst                          none
% 3.06/0.99  --qbf_dom_pre_inst                      false
% 3.06/0.99  --qbf_sk_in                             false
% 3.06/0.99  --qbf_pred_elim                         true
% 3.06/0.99  --qbf_split                             512
% 3.06/0.99  
% 3.06/0.99  ------ BMC1 Options
% 3.06/0.99  
% 3.06/0.99  --bmc1_incremental                      false
% 3.06/0.99  --bmc1_axioms                           reachable_all
% 3.06/0.99  --bmc1_min_bound                        0
% 3.06/0.99  --bmc1_max_bound                        -1
% 3.06/0.99  --bmc1_max_bound_default                -1
% 3.06/0.99  --bmc1_symbol_reachability              true
% 3.06/0.99  --bmc1_property_lemmas                  false
% 3.06/0.99  --bmc1_k_induction                      false
% 3.06/0.99  --bmc1_non_equiv_states                 false
% 3.06/0.99  --bmc1_deadlock                         false
% 3.06/0.99  --bmc1_ucm                              false
% 3.06/0.99  --bmc1_add_unsat_core                   none
% 3.06/0.99  --bmc1_unsat_core_children              false
% 3.06/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.06/0.99  --bmc1_out_stat                         full
% 3.06/0.99  --bmc1_ground_init                      false
% 3.06/0.99  --bmc1_pre_inst_next_state              false
% 3.06/0.99  --bmc1_pre_inst_state                   false
% 3.06/0.99  --bmc1_pre_inst_reach_state             false
% 3.06/0.99  --bmc1_out_unsat_core                   false
% 3.06/0.99  --bmc1_aig_witness_out                  false
% 3.06/0.99  --bmc1_verbose                          false
% 3.06/0.99  --bmc1_dump_clauses_tptp                false
% 3.06/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.06/0.99  --bmc1_dump_file                        -
% 3.06/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.06/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.06/0.99  --bmc1_ucm_extend_mode                  1
% 3.06/0.99  --bmc1_ucm_init_mode                    2
% 3.06/0.99  --bmc1_ucm_cone_mode                    none
% 3.06/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.06/0.99  --bmc1_ucm_relax_model                  4
% 3.06/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.06/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.06/0.99  --bmc1_ucm_layered_model                none
% 3.06/0.99  --bmc1_ucm_max_lemma_size               10
% 3.06/0.99  
% 3.06/0.99  ------ AIG Options
% 3.06/0.99  
% 3.06/0.99  --aig_mode                              false
% 3.06/0.99  
% 3.06/0.99  ------ Instantiation Options
% 3.06/0.99  
% 3.06/0.99  --instantiation_flag                    true
% 3.06/0.99  --inst_sos_flag                         false
% 3.06/0.99  --inst_sos_phase                        true
% 3.06/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.06/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.06/0.99  --inst_lit_sel_side                     num_symb
% 3.06/0.99  --inst_solver_per_active                1400
% 3.06/0.99  --inst_solver_calls_frac                1.
% 3.06/0.99  --inst_passive_queue_type               priority_queues
% 3.06/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.06/0.99  --inst_passive_queues_freq              [25;2]
% 3.06/0.99  --inst_dismatching                      true
% 3.06/0.99  --inst_eager_unprocessed_to_passive     true
% 3.06/0.99  --inst_prop_sim_given                   true
% 3.06/0.99  --inst_prop_sim_new                     false
% 3.06/0.99  --inst_subs_new                         false
% 3.06/0.99  --inst_eq_res_simp                      false
% 3.06/0.99  --inst_subs_given                       false
% 3.06/0.99  --inst_orphan_elimination               true
% 3.06/0.99  --inst_learning_loop_flag               true
% 3.06/0.99  --inst_learning_start                   3000
% 3.06/0.99  --inst_learning_factor                  2
% 3.06/0.99  --inst_start_prop_sim_after_learn       3
% 3.06/0.99  --inst_sel_renew                        solver
% 3.06/0.99  --inst_lit_activity_flag                true
% 3.06/0.99  --inst_restr_to_given                   false
% 3.06/0.99  --inst_activity_threshold               500
% 3.06/0.99  --inst_out_proof                        true
% 3.06/0.99  
% 3.06/0.99  ------ Resolution Options
% 3.06/0.99  
% 3.06/0.99  --resolution_flag                       true
% 3.06/0.99  --res_lit_sel                           adaptive
% 3.06/0.99  --res_lit_sel_side                      none
% 3.06/0.99  --res_ordering                          kbo
% 3.06/0.99  --res_to_prop_solver                    active
% 3.06/0.99  --res_prop_simpl_new                    false
% 3.06/0.99  --res_prop_simpl_given                  true
% 3.06/0.99  --res_passive_queue_type                priority_queues
% 3.06/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.06/0.99  --res_passive_queues_freq               [15;5]
% 3.06/0.99  --res_forward_subs                      full
% 3.06/0.99  --res_backward_subs                     full
% 3.06/0.99  --res_forward_subs_resolution           true
% 3.06/0.99  --res_backward_subs_resolution          true
% 3.06/0.99  --res_orphan_elimination                true
% 3.06/0.99  --res_time_limit                        2.
% 3.06/0.99  --res_out_proof                         true
% 3.06/0.99  
% 3.06/0.99  ------ Superposition Options
% 3.06/0.99  
% 3.06/0.99  --superposition_flag                    true
% 3.06/0.99  --sup_passive_queue_type                priority_queues
% 3.06/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.06/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.06/0.99  --demod_completeness_check              fast
% 3.06/0.99  --demod_use_ground                      true
% 3.06/0.99  --sup_to_prop_solver                    passive
% 3.06/0.99  --sup_prop_simpl_new                    true
% 3.06/0.99  --sup_prop_simpl_given                  true
% 3.06/0.99  --sup_fun_splitting                     false
% 3.06/0.99  --sup_smt_interval                      50000
% 3.06/0.99  
% 3.06/0.99  ------ Superposition Simplification Setup
% 3.06/0.99  
% 3.06/0.99  --sup_indices_passive                   []
% 3.06/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.06/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.06/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.06/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.06/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.06/0.99  --sup_full_bw                           [BwDemod]
% 3.06/0.99  --sup_immed_triv                        [TrivRules]
% 3.06/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.06/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.06/0.99  --sup_immed_bw_main                     []
% 3.06/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.06/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.06/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.06/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.06/0.99  
% 3.06/0.99  ------ Combination Options
% 3.06/0.99  
% 3.06/0.99  --comb_res_mult                         3
% 3.06/0.99  --comb_sup_mult                         2
% 3.06/0.99  --comb_inst_mult                        10
% 3.06/0.99  
% 3.06/0.99  ------ Debug Options
% 3.06/0.99  
% 3.06/0.99  --dbg_backtrace                         false
% 3.06/0.99  --dbg_dump_prop_clauses                 false
% 3.06/0.99  --dbg_dump_prop_clauses_file            -
% 3.06/0.99  --dbg_out_stat                          false
% 3.06/0.99  ------ Parsing...
% 3.06/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.06/0.99  
% 3.06/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.06/0.99  
% 3.06/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.06/0.99  
% 3.06/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.06/0.99  ------ Proving...
% 3.06/0.99  ------ Problem Properties 
% 3.06/0.99  
% 3.06/0.99  
% 3.06/0.99  clauses                                 22
% 3.06/0.99  conjectures                             4
% 3.06/0.99  EPR                                     1
% 3.06/0.99  Horn                                    20
% 3.06/0.99  unary                                   4
% 3.06/0.99  binary                                  5
% 3.06/0.99  lits                                    59
% 3.06/0.99  lits eq                                 5
% 3.06/0.99  fd_pure                                 0
% 3.06/0.99  fd_pseudo                               0
% 3.06/0.99  fd_cond                                 0
% 3.06/0.99  fd_pseudo_cond                          3
% 3.06/0.99  AC symbols                              0
% 3.06/0.99  
% 3.06/0.99  ------ Schedule dynamic 5 is on 
% 3.06/0.99  
% 3.06/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.06/0.99  
% 3.06/0.99  
% 3.06/0.99  ------ 
% 3.06/0.99  Current options:
% 3.06/0.99  ------ 
% 3.06/0.99  
% 3.06/0.99  ------ Input Options
% 3.06/0.99  
% 3.06/0.99  --out_options                           all
% 3.06/0.99  --tptp_safe_out                         true
% 3.06/0.99  --problem_path                          ""
% 3.06/0.99  --include_path                          ""
% 3.06/0.99  --clausifier                            res/vclausify_rel
% 3.06/0.99  --clausifier_options                    --mode clausify
% 3.06/0.99  --stdin                                 false
% 3.06/0.99  --stats_out                             all
% 3.06/0.99  
% 3.06/0.99  ------ General Options
% 3.06/0.99  
% 3.06/0.99  --fof                                   false
% 3.06/0.99  --time_out_real                         305.
% 3.06/0.99  --time_out_virtual                      -1.
% 3.06/0.99  --symbol_type_check                     false
% 3.06/0.99  --clausify_out                          false
% 3.06/0.99  --sig_cnt_out                           false
% 3.06/0.99  --trig_cnt_out                          false
% 3.06/0.99  --trig_cnt_out_tolerance                1.
% 3.06/0.99  --trig_cnt_out_sk_spl                   false
% 3.06/0.99  --abstr_cl_out                          false
% 3.06/0.99  
% 3.06/0.99  ------ Global Options
% 3.06/0.99  
% 3.06/0.99  --schedule                              default
% 3.06/0.99  --add_important_lit                     false
% 3.06/0.99  --prop_solver_per_cl                    1000
% 3.06/0.99  --min_unsat_core                        false
% 3.06/0.99  --soft_assumptions                      false
% 3.06/0.99  --soft_lemma_size                       3
% 3.06/0.99  --prop_impl_unit_size                   0
% 3.06/0.99  --prop_impl_unit                        []
% 3.06/0.99  --share_sel_clauses                     true
% 3.06/0.99  --reset_solvers                         false
% 3.06/0.99  --bc_imp_inh                            [conj_cone]
% 3.06/0.99  --conj_cone_tolerance                   3.
% 3.06/0.99  --extra_neg_conj                        none
% 3.06/0.99  --large_theory_mode                     true
% 3.06/0.99  --prolific_symb_bound                   200
% 3.06/0.99  --lt_threshold                          2000
% 3.06/0.99  --clause_weak_htbl                      true
% 3.06/0.99  --gc_record_bc_elim                     false
% 3.06/0.99  
% 3.06/0.99  ------ Preprocessing Options
% 3.06/0.99  
% 3.06/0.99  --preprocessing_flag                    true
% 3.06/0.99  --time_out_prep_mult                    0.1
% 3.06/0.99  --splitting_mode                        input
% 3.06/0.99  --splitting_grd                         true
% 3.06/0.99  --splitting_cvd                         false
% 3.06/0.99  --splitting_cvd_svl                     false
% 3.06/0.99  --splitting_nvd                         32
% 3.06/0.99  --sub_typing                            true
% 3.06/0.99  --prep_gs_sim                           true
% 3.06/0.99  --prep_unflatten                        true
% 3.06/0.99  --prep_res_sim                          true
% 3.06/0.99  --prep_upred                            true
% 3.06/0.99  --prep_sem_filter                       exhaustive
% 3.06/0.99  --prep_sem_filter_out                   false
% 3.06/0.99  --pred_elim                             true
% 3.06/0.99  --res_sim_input                         true
% 3.06/0.99  --eq_ax_congr_red                       true
% 3.06/0.99  --pure_diseq_elim                       true
% 3.06/0.99  --brand_transform                       false
% 3.06/0.99  --non_eq_to_eq                          false
% 3.06/0.99  --prep_def_merge                        true
% 3.06/0.99  --prep_def_merge_prop_impl              false
% 3.06/0.99  --prep_def_merge_mbd                    true
% 3.06/0.99  --prep_def_merge_tr_red                 false
% 3.06/0.99  --prep_def_merge_tr_cl                  false
% 3.06/0.99  --smt_preprocessing                     true
% 3.06/0.99  --smt_ac_axioms                         fast
% 3.06/0.99  --preprocessed_out                      false
% 3.06/0.99  --preprocessed_stats                    false
% 3.06/0.99  
% 3.06/0.99  ------ Abstraction refinement Options
% 3.06/0.99  
% 3.06/0.99  --abstr_ref                             []
% 3.06/0.99  --abstr_ref_prep                        false
% 3.06/0.99  --abstr_ref_until_sat                   false
% 3.06/0.99  --abstr_ref_sig_restrict                funpre
% 3.06/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.06/0.99  --abstr_ref_under                       []
% 3.06/0.99  
% 3.06/0.99  ------ SAT Options
% 3.06/0.99  
% 3.06/0.99  --sat_mode                              false
% 3.06/0.99  --sat_fm_restart_options                ""
% 3.06/0.99  --sat_gr_def                            false
% 3.06/0.99  --sat_epr_types                         true
% 3.06/0.99  --sat_non_cyclic_types                  false
% 3.06/0.99  --sat_finite_models                     false
% 3.06/0.99  --sat_fm_lemmas                         false
% 3.06/0.99  --sat_fm_prep                           false
% 3.06/0.99  --sat_fm_uc_incr                        true
% 3.06/0.99  --sat_out_model                         small
% 3.06/0.99  --sat_out_clauses                       false
% 3.06/0.99  
% 3.06/0.99  ------ QBF Options
% 3.06/0.99  
% 3.06/0.99  --qbf_mode                              false
% 3.06/0.99  --qbf_elim_univ                         false
% 3.06/0.99  --qbf_dom_inst                          none
% 3.06/0.99  --qbf_dom_pre_inst                      false
% 3.06/0.99  --qbf_sk_in                             false
% 3.06/0.99  --qbf_pred_elim                         true
% 3.06/0.99  --qbf_split                             512
% 3.06/0.99  
% 3.06/0.99  ------ BMC1 Options
% 3.06/0.99  
% 3.06/0.99  --bmc1_incremental                      false
% 3.06/0.99  --bmc1_axioms                           reachable_all
% 3.06/0.99  --bmc1_min_bound                        0
% 3.06/0.99  --bmc1_max_bound                        -1
% 3.06/0.99  --bmc1_max_bound_default                -1
% 3.06/0.99  --bmc1_symbol_reachability              true
% 3.06/0.99  --bmc1_property_lemmas                  false
% 3.06/0.99  --bmc1_k_induction                      false
% 3.06/0.99  --bmc1_non_equiv_states                 false
% 3.06/0.99  --bmc1_deadlock                         false
% 3.06/0.99  --bmc1_ucm                              false
% 3.06/0.99  --bmc1_add_unsat_core                   none
% 3.06/0.99  --bmc1_unsat_core_children              false
% 3.06/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.06/0.99  --bmc1_out_stat                         full
% 3.06/0.99  --bmc1_ground_init                      false
% 3.06/0.99  --bmc1_pre_inst_next_state              false
% 3.06/0.99  --bmc1_pre_inst_state                   false
% 3.06/0.99  --bmc1_pre_inst_reach_state             false
% 3.06/0.99  --bmc1_out_unsat_core                   false
% 3.06/0.99  --bmc1_aig_witness_out                  false
% 3.06/0.99  --bmc1_verbose                          false
% 3.06/0.99  --bmc1_dump_clauses_tptp                false
% 3.06/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.06/0.99  --bmc1_dump_file                        -
% 3.06/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.06/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.06/0.99  --bmc1_ucm_extend_mode                  1
% 3.06/0.99  --bmc1_ucm_init_mode                    2
% 3.06/0.99  --bmc1_ucm_cone_mode                    none
% 3.06/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.06/0.99  --bmc1_ucm_relax_model                  4
% 3.06/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.06/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.06/0.99  --bmc1_ucm_layered_model                none
% 3.06/0.99  --bmc1_ucm_max_lemma_size               10
% 3.06/0.99  
% 3.06/0.99  ------ AIG Options
% 3.06/0.99  
% 3.06/0.99  --aig_mode                              false
% 3.06/0.99  
% 3.06/0.99  ------ Instantiation Options
% 3.06/0.99  
% 3.06/0.99  --instantiation_flag                    true
% 3.06/0.99  --inst_sos_flag                         false
% 3.06/0.99  --inst_sos_phase                        true
% 3.06/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.06/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.06/0.99  --inst_lit_sel_side                     none
% 3.06/0.99  --inst_solver_per_active                1400
% 3.06/0.99  --inst_solver_calls_frac                1.
% 3.06/0.99  --inst_passive_queue_type               priority_queues
% 3.06/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.06/0.99  --inst_passive_queues_freq              [25;2]
% 3.06/0.99  --inst_dismatching                      true
% 3.06/0.99  --inst_eager_unprocessed_to_passive     true
% 3.06/0.99  --inst_prop_sim_given                   true
% 3.06/0.99  --inst_prop_sim_new                     false
% 3.06/0.99  --inst_subs_new                         false
% 3.06/0.99  --inst_eq_res_simp                      false
% 3.06/0.99  --inst_subs_given                       false
% 3.06/0.99  --inst_orphan_elimination               true
% 3.06/0.99  --inst_learning_loop_flag               true
% 3.06/0.99  --inst_learning_start                   3000
% 3.06/0.99  --inst_learning_factor                  2
% 3.06/0.99  --inst_start_prop_sim_after_learn       3
% 3.06/0.99  --inst_sel_renew                        solver
% 3.06/0.99  --inst_lit_activity_flag                true
% 3.06/0.99  --inst_restr_to_given                   false
% 3.06/0.99  --inst_activity_threshold               500
% 3.06/0.99  --inst_out_proof                        true
% 3.06/0.99  
% 3.06/0.99  ------ Resolution Options
% 3.06/0.99  
% 3.06/0.99  --resolution_flag                       false
% 3.06/0.99  --res_lit_sel                           adaptive
% 3.06/0.99  --res_lit_sel_side                      none
% 3.06/0.99  --res_ordering                          kbo
% 3.06/0.99  --res_to_prop_solver                    active
% 3.06/0.99  --res_prop_simpl_new                    false
% 3.06/0.99  --res_prop_simpl_given                  true
% 3.06/0.99  --res_passive_queue_type                priority_queues
% 3.06/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.06/0.99  --res_passive_queues_freq               [15;5]
% 3.06/0.99  --res_forward_subs                      full
% 3.06/0.99  --res_backward_subs                     full
% 3.06/0.99  --res_forward_subs_resolution           true
% 3.06/0.99  --res_backward_subs_resolution          true
% 3.06/0.99  --res_orphan_elimination                true
% 3.06/0.99  --res_time_limit                        2.
% 3.06/0.99  --res_out_proof                         true
% 3.06/0.99  
% 3.06/0.99  ------ Superposition Options
% 3.06/0.99  
% 3.06/0.99  --superposition_flag                    true
% 3.06/0.99  --sup_passive_queue_type                priority_queues
% 3.06/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.06/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.06/0.99  --demod_completeness_check              fast
% 3.06/0.99  --demod_use_ground                      true
% 3.06/0.99  --sup_to_prop_solver                    passive
% 3.06/0.99  --sup_prop_simpl_new                    true
% 3.06/0.99  --sup_prop_simpl_given                  true
% 3.06/0.99  --sup_fun_splitting                     false
% 3.06/0.99  --sup_smt_interval                      50000
% 3.06/0.99  
% 3.06/0.99  ------ Superposition Simplification Setup
% 3.06/0.99  
% 3.06/0.99  --sup_indices_passive                   []
% 3.06/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.06/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.06/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.06/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.06/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.06/0.99  --sup_full_bw                           [BwDemod]
% 3.06/0.99  --sup_immed_triv                        [TrivRules]
% 3.06/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.06/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.06/0.99  --sup_immed_bw_main                     []
% 3.06/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.06/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.06/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.06/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.06/0.99  
% 3.06/0.99  ------ Combination Options
% 3.06/0.99  
% 3.06/0.99  --comb_res_mult                         3
% 3.06/0.99  --comb_sup_mult                         2
% 3.06/0.99  --comb_inst_mult                        10
% 3.06/0.99  
% 3.06/0.99  ------ Debug Options
% 3.06/0.99  
% 3.06/0.99  --dbg_backtrace                         false
% 3.06/0.99  --dbg_dump_prop_clauses                 false
% 3.06/0.99  --dbg_dump_prop_clauses_file            -
% 3.06/0.99  --dbg_out_stat                          false
% 3.06/0.99  
% 3.06/0.99  
% 3.06/0.99  
% 3.06/0.99  
% 3.06/0.99  ------ Proving...
% 3.06/0.99  
% 3.06/0.99  
% 3.06/0.99  % SZS status Theorem for theBenchmark.p
% 3.06/0.99  
% 3.06/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.06/0.99  
% 3.06/0.99  fof(f1,axiom,(
% 3.06/0.99    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.06/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/0.99  
% 3.06/0.99  fof(f25,plain,(
% 3.06/0.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.06/0.99    inference(nnf_transformation,[],[f1])).
% 3.06/0.99  
% 3.06/0.99  fof(f26,plain,(
% 3.06/0.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.06/0.99    inference(flattening,[],[f25])).
% 3.06/0.99  
% 3.06/0.99  fof(f27,plain,(
% 3.06/0.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.06/0.99    inference(rectify,[],[f26])).
% 3.06/0.99  
% 3.06/0.99  fof(f28,plain,(
% 3.06/0.99    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 3.06/0.99    introduced(choice_axiom,[])).
% 3.06/0.99  
% 3.06/0.99  fof(f29,plain,(
% 3.06/0.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.06/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).
% 3.06/0.99  
% 3.06/0.99  fof(f41,plain,(
% 3.06/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k3_xboole_0(X0,X1) != X2) )),
% 3.06/0.99    inference(cnf_transformation,[],[f29])).
% 3.06/0.99  
% 3.06/0.99  fof(f4,axiom,(
% 3.06/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.06/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/0.99  
% 3.06/0.99  fof(f47,plain,(
% 3.06/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.06/0.99    inference(cnf_transformation,[],[f4])).
% 3.06/0.99  
% 3.06/0.99  fof(f68,plain,(
% 3.06/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k1_setfam_1(k2_tarski(X0,X1)) != X2) )),
% 3.06/0.99    inference(definition_unfolding,[],[f41,f47])).
% 3.06/0.99  
% 3.06/0.99  fof(f74,plain,(
% 3.06/0.99    ( ! [X4,X0,X1] : (r2_hidden(X4,k1_setfam_1(k2_tarski(X0,X1))) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 3.06/0.99    inference(equality_resolution,[],[f68])).
% 3.06/0.99  
% 3.06/0.99  fof(f7,axiom,(
% 3.06/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X2,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k3_xboole_0(X1,X2),X0))),
% 3.06/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/0.99  
% 3.06/0.99  fof(f17,plain,(
% 3.06/0.99    ! [X0,X1,X2] : (v3_pre_topc(k3_xboole_0(X1,X2),X0) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.06/0.99    inference(ennf_transformation,[],[f7])).
% 3.06/0.99  
% 3.06/0.99  fof(f18,plain,(
% 3.06/0.99    ! [X0,X1,X2] : (v3_pre_topc(k3_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.06/0.99    inference(flattening,[],[f17])).
% 3.06/0.99  
% 3.06/0.99  fof(f50,plain,(
% 3.06/0.99    ( ! [X2,X0,X1] : (v3_pre_topc(k3_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.06/0.99    inference(cnf_transformation,[],[f18])).
% 3.06/0.99  
% 3.06/0.99  fof(f72,plain,(
% 3.06/0.99    ( ! [X2,X0,X1] : (v3_pre_topc(k1_setfam_1(k2_tarski(X1,X2)),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.06/0.99    inference(definition_unfolding,[],[f50,f47])).
% 3.06/0.99  
% 3.06/0.99  fof(f10,conjecture,(
% 3.06/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) => m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))))))),
% 3.06/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/0.99  
% 3.06/0.99  fof(f11,negated_conjecture,(
% 3.06/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) => m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))))))),
% 3.06/0.99    inference(negated_conjecture,[],[f10])).
% 3.06/0.99  
% 3.06/0.99  fof(f23,plain,(
% 3.06/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.06/0.99    inference(ennf_transformation,[],[f11])).
% 3.06/0.99  
% 3.06/0.99  fof(f24,plain,(
% 3.06/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.06/0.99    inference(flattening,[],[f23])).
% 3.06/0.99  
% 3.06/0.99  fof(f37,plain,(
% 3.06/0.99    ( ! [X2,X0,X1] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) => (~m1_subset_1(k3_xboole_0(X2,sK5),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(sK5,u1_struct_0(k9_yellow_6(X0,X1))))) )),
% 3.06/0.99    introduced(choice_axiom,[])).
% 3.06/0.99  
% 3.06/0.99  fof(f36,plain,(
% 3.06/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) => (? [X3] : (~m1_subset_1(k3_xboole_0(sK4,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(sK4,u1_struct_0(k9_yellow_6(X0,X1))))) )),
% 3.06/0.99    introduced(choice_axiom,[])).
% 3.06/0.99  
% 3.06/0.99  fof(f35,plain,(
% 3.06/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,sK3))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,sK3)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,sK3)))) & m1_subset_1(sK3,u1_struct_0(X0)))) )),
% 3.06/0.99    introduced(choice_axiom,[])).
% 3.06/0.99  
% 3.06/0.99  fof(f34,plain,(
% 3.06/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK2,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK2,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK2,X1)))) & m1_subset_1(X1,u1_struct_0(sK2))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 3.06/0.99    introduced(choice_axiom,[])).
% 3.06/0.99  
% 3.06/0.99  fof(f38,plain,(
% 3.06/0.99    (((~m1_subset_1(k3_xboole_0(sK4,sK5),u1_struct_0(k9_yellow_6(sK2,sK3))) & m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3)))) & m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3)))) & m1_subset_1(sK3,u1_struct_0(sK2))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 3.06/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f24,f37,f36,f35,f34])).
% 3.06/0.99  
% 3.06/0.99  fof(f60,plain,(
% 3.06/0.99    l1_pre_topc(sK2)),
% 3.06/0.99    inference(cnf_transformation,[],[f38])).
% 3.06/0.99  
% 3.06/0.99  fof(f59,plain,(
% 3.06/0.99    v2_pre_topc(sK2)),
% 3.06/0.99    inference(cnf_transformation,[],[f38])).
% 3.06/0.99  
% 3.06/0.99  fof(f62,plain,(
% 3.06/0.99    m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3)))),
% 3.06/0.99    inference(cnf_transformation,[],[f38])).
% 3.06/0.99  
% 3.06/0.99  fof(f8,axiom,(
% 3.06/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ? [X3] : (v3_pre_topc(X3,X0) & r2_hidden(X1,X3) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))))),
% 3.06/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/0.99  
% 3.06/0.99  fof(f19,plain,(
% 3.06/0.99    ! [X0] : (! [X1] : (! [X2] : (? [X3] : (v3_pre_topc(X3,X0) & r2_hidden(X1,X3) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.06/0.99    inference(ennf_transformation,[],[f8])).
% 3.06/0.99  
% 3.06/0.99  fof(f20,plain,(
% 3.06/0.99    ! [X0] : (! [X1] : (! [X2] : (? [X3] : (v3_pre_topc(X3,X0) & r2_hidden(X1,X3) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.06/0.99    inference(flattening,[],[f19])).
% 3.06/0.99  
% 3.06/0.99  fof(f30,plain,(
% 3.06/0.99    ! [X2,X1,X0] : (? [X3] : (v3_pre_topc(X3,X0) & r2_hidden(X1,X3) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (v3_pre_topc(sK1(X0,X1,X2),X0) & r2_hidden(X1,sK1(X0,X1,X2)) & sK1(X0,X1,X2) = X2 & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.06/0.99    introduced(choice_axiom,[])).
% 3.06/0.99  
% 3.06/0.99  fof(f31,plain,(
% 3.06/0.99    ! [X0] : (! [X1] : (! [X2] : ((v3_pre_topc(sK1(X0,X1,X2),X0) & r2_hidden(X1,sK1(X0,X1,X2)) & sK1(X0,X1,X2) = X2 & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.06/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f30])).
% 3.06/0.99  
% 3.06/0.99  fof(f52,plain,(
% 3.06/0.99    ( ! [X2,X0,X1] : (sK1(X0,X1,X2) = X2 | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.06/0.99    inference(cnf_transformation,[],[f31])).
% 3.06/0.99  
% 3.06/0.99  fof(f58,plain,(
% 3.06/0.99    ~v2_struct_0(sK2)),
% 3.06/0.99    inference(cnf_transformation,[],[f38])).
% 3.06/0.99  
% 3.06/0.99  fof(f61,plain,(
% 3.06/0.99    m1_subset_1(sK3,u1_struct_0(sK2))),
% 3.06/0.99    inference(cnf_transformation,[],[f38])).
% 3.06/0.99  
% 3.06/0.99  fof(f51,plain,(
% 3.06/0.99    ( ! [X2,X0,X1] : (m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.06/0.99    inference(cnf_transformation,[],[f31])).
% 3.06/0.99  
% 3.06/0.99  fof(f3,axiom,(
% 3.06/0.99    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k8_subset_1(X0,X1,X2))),
% 3.06/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/0.99  
% 3.06/0.99  fof(f13,plain,(
% 3.06/0.99    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k8_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.06/0.99    inference(ennf_transformation,[],[f3])).
% 3.06/0.99  
% 3.06/0.99  fof(f46,plain,(
% 3.06/0.99    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k8_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.06/0.99    inference(cnf_transformation,[],[f13])).
% 3.06/0.99  
% 3.06/0.99  fof(f71,plain,(
% 3.06/0.99    ( ! [X2,X0,X1] : (k8_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.06/0.99    inference(definition_unfolding,[],[f46,f47])).
% 3.06/0.99  
% 3.06/0.99  fof(f2,axiom,(
% 3.06/0.99    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k8_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 3.06/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/0.99  
% 3.06/0.99  fof(f12,plain,(
% 3.06/0.99    ! [X0,X1,X2] : (m1_subset_1(k8_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.06/0.99    inference(ennf_transformation,[],[f2])).
% 3.06/0.99  
% 3.06/0.99  fof(f45,plain,(
% 3.06/0.99    ( ! [X2,X0,X1] : (m1_subset_1(k8_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.06/0.99    inference(cnf_transformation,[],[f12])).
% 3.06/0.99  
% 3.06/0.99  fof(f9,axiom,(
% 3.06/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))))))),
% 3.06/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/0.99  
% 3.06/0.99  fof(f21,plain,(
% 3.06/0.99    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.06/0.99    inference(ennf_transformation,[],[f9])).
% 3.06/0.99  
% 3.06/0.99  fof(f22,plain,(
% 3.06/0.99    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.06/0.99    inference(flattening,[],[f21])).
% 3.06/0.99  
% 3.06/0.99  fof(f32,plain,(
% 3.06/0.99    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | (~v3_pre_topc(X2,X0) | ~r2_hidden(X1,X2))) & ((v3_pre_topc(X2,X0) & r2_hidden(X1,X2)) | ~r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.06/0.99    inference(nnf_transformation,[],[f22])).
% 3.06/0.99  
% 3.06/0.99  fof(f33,plain,(
% 3.06/0.99    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~v3_pre_topc(X2,X0) | ~r2_hidden(X1,X2)) & ((v3_pre_topc(X2,X0) & r2_hidden(X1,X2)) | ~r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.06/0.99    inference(flattening,[],[f32])).
% 3.06/0.99  
% 3.06/0.99  fof(f57,plain,(
% 3.06/0.99    ( ! [X2,X0,X1] : (r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~v3_pre_topc(X2,X0) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.06/0.99    inference(cnf_transformation,[],[f33])).
% 3.06/0.99  
% 3.06/0.99  fof(f6,axiom,(
% 3.06/0.99    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 3.06/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/0.99  
% 3.06/0.99  fof(f15,plain,(
% 3.06/0.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 3.06/0.99    inference(ennf_transformation,[],[f6])).
% 3.06/0.99  
% 3.06/0.99  fof(f16,plain,(
% 3.06/0.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.06/0.99    inference(flattening,[],[f15])).
% 3.06/0.99  
% 3.06/0.99  fof(f49,plain,(
% 3.06/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.06/0.99    inference(cnf_transformation,[],[f16])).
% 3.06/0.99  
% 3.06/0.99  fof(f5,axiom,(
% 3.06/0.99    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 3.06/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/0.99  
% 3.06/0.99  fof(f14,plain,(
% 3.06/0.99    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 3.06/0.99    inference(ennf_transformation,[],[f5])).
% 3.06/0.99  
% 3.06/0.99  fof(f48,plain,(
% 3.06/0.99    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 3.06/0.99    inference(cnf_transformation,[],[f14])).
% 3.06/0.99  
% 3.06/0.99  fof(f64,plain,(
% 3.06/0.99    ~m1_subset_1(k3_xboole_0(sK4,sK5),u1_struct_0(k9_yellow_6(sK2,sK3)))),
% 3.06/0.99    inference(cnf_transformation,[],[f38])).
% 3.06/0.99  
% 3.06/0.99  fof(f73,plain,(
% 3.06/0.99    ~m1_subset_1(k1_setfam_1(k2_tarski(sK4,sK5)),u1_struct_0(k9_yellow_6(sK2,sK3)))),
% 3.06/0.99    inference(definition_unfolding,[],[f64,f47])).
% 3.06/0.99  
% 3.06/0.99  fof(f63,plain,(
% 3.06/0.99    m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3)))),
% 3.06/0.99    inference(cnf_transformation,[],[f38])).
% 3.06/0.99  
% 3.06/0.99  fof(f54,plain,(
% 3.06/0.99    ( ! [X2,X0,X1] : (v3_pre_topc(sK1(X0,X1,X2),X0) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.06/0.99    inference(cnf_transformation,[],[f31])).
% 3.06/0.99  
% 3.06/0.99  fof(f53,plain,(
% 3.06/0.99    ( ! [X2,X0,X1] : (r2_hidden(X1,sK1(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.06/0.99    inference(cnf_transformation,[],[f31])).
% 3.06/0.99  
% 3.06/0.99  cnf(c_3,plain,
% 3.06/0.99      ( ~ r2_hidden(X0,X1)
% 3.06/0.99      | ~ r2_hidden(X0,X2)
% 3.06/0.99      | r2_hidden(X0,k1_setfam_1(k2_tarski(X2,X1))) ),
% 3.06/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_1048,plain,
% 3.06/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.06/0.99      | r2_hidden(X0,X2) != iProver_top
% 3.06/0.99      | r2_hidden(X0,k1_setfam_1(k2_tarski(X1,X2))) = iProver_top ),
% 3.06/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_10,plain,
% 3.06/0.99      ( ~ v3_pre_topc(X0,X1)
% 3.06/0.99      | ~ v3_pre_topc(X2,X1)
% 3.06/0.99      | v3_pre_topc(k1_setfam_1(k2_tarski(X2,X0)),X1)
% 3.06/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.06/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.06/0.99      | ~ v2_pre_topc(X1)
% 3.06/0.99      | ~ l1_pre_topc(X1) ),
% 3.06/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_22,negated_conjecture,
% 3.06/0.99      ( l1_pre_topc(sK2) ),
% 3.06/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_468,plain,
% 3.06/0.99      ( ~ v3_pre_topc(X0,X1)
% 3.06/0.99      | ~ v3_pre_topc(X2,X1)
% 3.06/0.99      | v3_pre_topc(k1_setfam_1(k2_tarski(X2,X0)),X1)
% 3.06/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.06/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.06/0.99      | ~ v2_pre_topc(X1)
% 3.06/0.99      | sK2 != X1 ),
% 3.06/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_22]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_469,plain,
% 3.06/0.99      ( ~ v3_pre_topc(X0,sK2)
% 3.06/0.99      | ~ v3_pre_topc(X1,sK2)
% 3.06/0.99      | v3_pre_topc(k1_setfam_1(k2_tarski(X1,X0)),sK2)
% 3.06/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.06/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.06/0.99      | ~ v2_pre_topc(sK2) ),
% 3.06/0.99      inference(unflattening,[status(thm)],[c_468]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_23,negated_conjecture,
% 3.06/0.99      ( v2_pre_topc(sK2) ),
% 3.06/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_473,plain,
% 3.06/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.06/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.06/0.99      | v3_pre_topc(k1_setfam_1(k2_tarski(X1,X0)),sK2)
% 3.06/0.99      | ~ v3_pre_topc(X1,sK2)
% 3.06/0.99      | ~ v3_pre_topc(X0,sK2) ),
% 3.06/0.99      inference(global_propositional_subsumption,
% 3.06/0.99                [status(thm)],
% 3.06/0.99                [c_469,c_23]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_474,plain,
% 3.06/0.99      ( ~ v3_pre_topc(X0,sK2)
% 3.06/0.99      | ~ v3_pre_topc(X1,sK2)
% 3.06/0.99      | v3_pre_topc(k1_setfam_1(k2_tarski(X1,X0)),sK2)
% 3.06/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.06/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.06/0.99      inference(renaming,[status(thm)],[c_473]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_1030,plain,
% 3.06/0.99      ( v3_pre_topc(X0,sK2) != iProver_top
% 3.06/0.99      | v3_pre_topc(X1,sK2) != iProver_top
% 3.06/0.99      | v3_pre_topc(k1_setfam_1(k2_tarski(X1,X0)),sK2) = iProver_top
% 3.06/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.06/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 3.06/0.99      inference(predicate_to_equality,[status(thm)],[c_474]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_20,negated_conjecture,
% 3.06/0.99      ( m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))) ),
% 3.06/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_1039,plain,
% 3.06/0.99      ( m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))) = iProver_top ),
% 3.06/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_13,plain,
% 3.06/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.06/0.99      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
% 3.06/0.99      | v2_struct_0(X1)
% 3.06/0.99      | ~ v2_pre_topc(X1)
% 3.06/0.99      | ~ l1_pre_topc(X1)
% 3.06/0.99      | sK1(X1,X0,X2) = X2 ),
% 3.06/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_24,negated_conjecture,
% 3.06/0.99      ( ~ v2_struct_0(sK2) ),
% 3.06/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_395,plain,
% 3.06/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.06/0.99      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
% 3.06/0.99      | ~ v2_pre_topc(X1)
% 3.06/0.99      | ~ l1_pre_topc(X1)
% 3.06/0.99      | sK1(X1,X0,X2) = X2
% 3.06/0.99      | sK2 != X1 ),
% 3.06/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_24]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_396,plain,
% 3.06/0.99      ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,X1)))
% 3.06/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 3.06/0.99      | ~ v2_pre_topc(sK2)
% 3.06/0.99      | ~ l1_pre_topc(sK2)
% 3.06/0.99      | sK1(sK2,X1,X0) = X0 ),
% 3.06/0.99      inference(unflattening,[status(thm)],[c_395]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_400,plain,
% 3.06/0.99      ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,X1)))
% 3.06/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 3.06/0.99      | sK1(sK2,X1,X0) = X0 ),
% 3.06/0.99      inference(global_propositional_subsumption,
% 3.06/0.99                [status(thm)],
% 3.06/0.99                [c_396,c_23,c_22]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_1032,plain,
% 3.06/0.99      ( sK1(sK2,X0,X1) = X1
% 3.06/0.99      | m1_subset_1(X1,u1_struct_0(k9_yellow_6(sK2,X0))) != iProver_top
% 3.06/0.99      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
% 3.06/0.99      inference(predicate_to_equality,[status(thm)],[c_400]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_1275,plain,
% 3.06/0.99      ( sK1(sK2,sK3,sK4) = sK4
% 3.06/0.99      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
% 3.06/0.99      inference(superposition,[status(thm)],[c_1039,c_1032]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_21,negated_conjecture,
% 3.06/0.99      ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 3.06/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_28,plain,
% 3.06/0.99      ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
% 3.06/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_1375,plain,
% 3.06/0.99      ( sK1(sK2,sK3,sK4) = sK4 ),
% 3.06/0.99      inference(global_propositional_subsumption,
% 3.06/0.99                [status(thm)],
% 3.06/0.99                [c_1275,c_28]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_14,plain,
% 3.06/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.06/0.99      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
% 3.06/0.99      | m1_subset_1(sK1(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
% 3.06/0.99      | v2_struct_0(X1)
% 3.06/0.99      | ~ v2_pre_topc(X1)
% 3.06/0.99      | ~ l1_pre_topc(X1) ),
% 3.06/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_374,plain,
% 3.06/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.06/0.99      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
% 3.06/0.99      | m1_subset_1(sK1(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
% 3.06/0.99      | ~ v2_pre_topc(X1)
% 3.06/0.99      | ~ l1_pre_topc(X1)
% 3.06/0.99      | sK2 != X1 ),
% 3.06/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_24]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_375,plain,
% 3.06/0.99      ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,X1)))
% 3.06/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 3.06/0.99      | m1_subset_1(sK1(sK2,X1,X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.06/0.99      | ~ v2_pre_topc(sK2)
% 3.06/0.99      | ~ l1_pre_topc(sK2) ),
% 3.06/0.99      inference(unflattening,[status(thm)],[c_374]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_379,plain,
% 3.06/0.99      ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,X1)))
% 3.06/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 3.06/0.99      | m1_subset_1(sK1(sK2,X1,X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.06/0.99      inference(global_propositional_subsumption,
% 3.06/0.99                [status(thm)],
% 3.06/0.99                [c_375,c_23,c_22]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_1033,plain,
% 3.06/0.99      ( m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,X1))) != iProver_top
% 3.06/0.99      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
% 3.06/0.99      | m1_subset_1(sK1(sK2,X1,X0),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.06/0.99      inference(predicate_to_equality,[status(thm)],[c_379]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_1777,plain,
% 3.06/0.99      ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 3.06/0.99      | m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))) != iProver_top
% 3.06/0.99      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.06/0.99      inference(superposition,[status(thm)],[c_1375,c_1033]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_29,plain,
% 3.06/0.99      ( m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))) = iProver_top ),
% 3.06/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_2640,plain,
% 3.06/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.06/0.99      inference(global_propositional_subsumption,
% 3.06/0.99                [status(thm)],
% 3.06/0.99                [c_1777,c_28,c_29]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_7,plain,
% 3.06/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.06/0.99      | k8_subset_1(X1,X0,X2) = k1_setfam_1(k2_tarski(X0,X2)) ),
% 3.06/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_1044,plain,
% 3.06/0.99      ( k8_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
% 3.06/0.99      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.06/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_2645,plain,
% 3.06/0.99      ( k8_subset_1(u1_struct_0(sK2),sK4,X0) = k1_setfam_1(k2_tarski(sK4,X0)) ),
% 3.06/0.99      inference(superposition,[status(thm)],[c_2640,c_1044]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_6,plain,
% 3.06/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.06/0.99      | m1_subset_1(k8_subset_1(X1,X0,X2),k1_zfmisc_1(X1)) ),
% 3.06/0.99      inference(cnf_transformation,[],[f45]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_1045,plain,
% 3.06/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.06/0.99      | m1_subset_1(k8_subset_1(X1,X0,X2),k1_zfmisc_1(X1)) = iProver_top ),
% 3.06/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_4230,plain,
% 3.06/0.99      ( m1_subset_1(k1_setfam_1(k2_tarski(sK4,X0)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 3.06/0.99      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 3.06/0.99      inference(superposition,[status(thm)],[c_2645,c_1045]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_6140,plain,
% 3.06/0.99      ( m1_subset_1(k1_setfam_1(k2_tarski(sK4,X0)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.06/0.99      inference(global_propositional_subsumption,
% 3.06/0.99                [status(thm)],
% 3.06/0.99                [c_4230,c_28,c_29,c_1777]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_15,plain,
% 3.06/0.99      ( ~ v3_pre_topc(X0,X1)
% 3.06/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.06/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.06/0.99      | ~ r2_hidden(X2,X0)
% 3.06/0.99      | r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
% 3.06/0.99      | v2_struct_0(X1)
% 3.06/0.99      | ~ v2_pre_topc(X1)
% 3.06/0.99      | ~ l1_pre_topc(X1) ),
% 3.06/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_345,plain,
% 3.06/0.99      ( ~ v3_pre_topc(X0,X1)
% 3.06/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.06/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.06/0.99      | ~ r2_hidden(X2,X0)
% 3.06/0.99      | r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
% 3.06/0.99      | ~ v2_pre_topc(X1)
% 3.06/0.99      | ~ l1_pre_topc(X1)
% 3.06/0.99      | sK2 != X1 ),
% 3.06/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_24]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_346,plain,
% 3.06/0.99      ( ~ v3_pre_topc(X0,sK2)
% 3.06/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 3.06/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.06/0.99      | ~ r2_hidden(X1,X0)
% 3.06/0.99      | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK2,X1)))
% 3.06/0.99      | ~ v2_pre_topc(sK2)
% 3.06/0.99      | ~ l1_pre_topc(sK2) ),
% 3.06/0.99      inference(unflattening,[status(thm)],[c_345]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_350,plain,
% 3.06/0.99      ( ~ v3_pre_topc(X0,sK2)
% 3.06/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 3.06/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.06/0.99      | ~ r2_hidden(X1,X0)
% 3.06/0.99      | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK2,X1))) ),
% 3.06/0.99      inference(global_propositional_subsumption,
% 3.06/0.99                [status(thm)],
% 3.06/0.99                [c_346,c_23,c_22]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_9,plain,
% 3.06/0.99      ( m1_subset_1(X0,X1)
% 3.06/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.06/0.99      | ~ r2_hidden(X0,X2) ),
% 3.06/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_366,plain,
% 3.06/0.99      ( ~ v3_pre_topc(X0,sK2)
% 3.06/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.06/0.99      | ~ r2_hidden(X1,X0)
% 3.06/0.99      | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK2,X1))) ),
% 3.06/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_350,c_9]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_1034,plain,
% 3.06/0.99      ( v3_pre_topc(X0,sK2) != iProver_top
% 3.06/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.06/0.99      | r2_hidden(X1,X0) != iProver_top
% 3.06/0.99      | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK2,X1))) = iProver_top ),
% 3.06/0.99      inference(predicate_to_equality,[status(thm)],[c_366]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_8,plain,
% 3.06/0.99      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 3.06/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_1043,plain,
% 3.06/0.99      ( m1_subset_1(X0,X1) = iProver_top
% 3.06/0.99      | r2_hidden(X0,X1) != iProver_top ),
% 3.06/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_2224,plain,
% 3.06/0.99      ( v3_pre_topc(X0,sK2) != iProver_top
% 3.06/0.99      | m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,X1))) = iProver_top
% 3.06/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.06/0.99      | r2_hidden(X1,X0) != iProver_top ),
% 3.06/0.99      inference(superposition,[status(thm)],[c_1034,c_1043]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_18,negated_conjecture,
% 3.06/0.99      ( ~ m1_subset_1(k1_setfam_1(k2_tarski(sK4,sK5)),u1_struct_0(k9_yellow_6(sK2,sK3))) ),
% 3.06/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_1041,plain,
% 3.06/0.99      ( m1_subset_1(k1_setfam_1(k2_tarski(sK4,sK5)),u1_struct_0(k9_yellow_6(sK2,sK3))) != iProver_top ),
% 3.06/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_4344,plain,
% 3.06/0.99      ( v3_pre_topc(k1_setfam_1(k2_tarski(sK4,sK5)),sK2) != iProver_top
% 3.06/0.99      | m1_subset_1(k1_setfam_1(k2_tarski(sK4,sK5)),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.06/0.99      | r2_hidden(sK3,k1_setfam_1(k2_tarski(sK4,sK5))) != iProver_top ),
% 3.06/0.99      inference(superposition,[status(thm)],[c_2224,c_1041]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_6151,plain,
% 3.06/0.99      ( v3_pre_topc(k1_setfam_1(k2_tarski(sK4,sK5)),sK2) != iProver_top
% 3.06/0.99      | r2_hidden(sK3,k1_setfam_1(k2_tarski(sK4,sK5))) != iProver_top ),
% 3.06/0.99      inference(superposition,[status(thm)],[c_6140,c_4344]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_6915,plain,
% 3.06/0.99      ( v3_pre_topc(sK5,sK2) != iProver_top
% 3.06/0.99      | v3_pre_topc(sK4,sK2) != iProver_top
% 3.06/0.99      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.06/0.99      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.06/0.99      | r2_hidden(sK3,k1_setfam_1(k2_tarski(sK4,sK5))) != iProver_top ),
% 3.06/0.99      inference(superposition,[status(thm)],[c_1030,c_6151]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_19,negated_conjecture,
% 3.06/0.99      ( m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3))) ),
% 3.06/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_30,plain,
% 3.06/0.99      ( m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3))) = iProver_top ),
% 3.06/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_11,plain,
% 3.06/0.99      ( v3_pre_topc(sK1(X0,X1,X2),X0)
% 3.06/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.06/0.99      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
% 3.06/0.99      | v2_struct_0(X0)
% 3.06/0.99      | ~ v2_pre_topc(X0)
% 3.06/0.99      | ~ l1_pre_topc(X0) ),
% 3.06/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_276,plain,
% 3.06/0.99      ( v3_pre_topc(sK1(X0,X1,X2),X0)
% 3.06/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.06/0.99      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
% 3.06/0.99      | ~ v2_pre_topc(X0)
% 3.06/0.99      | ~ l1_pre_topc(X0)
% 3.06/0.99      | sK2 != X0 ),
% 3.06/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_24]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_277,plain,
% 3.06/0.99      ( v3_pre_topc(sK1(sK2,X0,X1),sK2)
% 3.06/0.99      | ~ m1_subset_1(X1,u1_struct_0(k9_yellow_6(sK2,X0)))
% 3.06/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 3.06/0.99      | ~ v2_pre_topc(sK2)
% 3.06/0.99      | ~ l1_pre_topc(sK2) ),
% 3.06/0.99      inference(unflattening,[status(thm)],[c_276]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_281,plain,
% 3.06/0.99      ( v3_pre_topc(sK1(sK2,X0,X1),sK2)
% 3.06/0.99      | ~ m1_subset_1(X1,u1_struct_0(k9_yellow_6(sK2,X0)))
% 3.06/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
% 3.06/0.99      inference(global_propositional_subsumption,
% 3.06/0.99                [status(thm)],
% 3.06/0.99                [c_277,c_23,c_22]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_1037,plain,
% 3.06/0.99      ( v3_pre_topc(sK1(sK2,X0,X1),sK2) = iProver_top
% 3.06/0.99      | m1_subset_1(X1,u1_struct_0(k9_yellow_6(sK2,X0))) != iProver_top
% 3.06/0.99      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
% 3.06/0.99      inference(predicate_to_equality,[status(thm)],[c_281]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_1628,plain,
% 3.06/0.99      ( v3_pre_topc(sK1(sK2,sK3,sK4),sK2) = iProver_top
% 3.06/0.99      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
% 3.06/0.99      inference(superposition,[status(thm)],[c_1039,c_1037]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_1631,plain,
% 3.06/0.99      ( v3_pre_topc(sK4,sK2) = iProver_top
% 3.06/0.99      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
% 3.06/0.99      inference(light_normalisation,[status(thm)],[c_1628,c_1375]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_1040,plain,
% 3.06/0.99      ( m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3))) = iProver_top ),
% 3.06/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_1627,plain,
% 3.06/0.99      ( v3_pre_topc(sK1(sK2,sK3,sK5),sK2) = iProver_top
% 3.06/0.99      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
% 3.06/0.99      inference(superposition,[status(thm)],[c_1040,c_1037]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_1274,plain,
% 3.06/0.99      ( sK1(sK2,sK3,sK5) = sK5
% 3.06/0.99      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
% 3.06/0.99      inference(superposition,[status(thm)],[c_1040,c_1032]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_1287,plain,
% 3.06/0.99      ( sK1(sK2,sK3,sK5) = sK5 ),
% 3.06/0.99      inference(global_propositional_subsumption,
% 3.06/0.99                [status(thm)],
% 3.06/0.99                [c_1274,c_28]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_1636,plain,
% 3.06/0.99      ( v3_pre_topc(sK5,sK2) = iProver_top
% 3.06/0.99      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
% 3.06/0.99      inference(light_normalisation,[status(thm)],[c_1627,c_1287]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_1776,plain,
% 3.06/0.99      ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 3.06/0.99      | m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3))) != iProver_top
% 3.06/0.99      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.06/0.99      inference(superposition,[status(thm)],[c_1287,c_1033]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_6918,plain,
% 3.06/0.99      ( r2_hidden(sK3,k1_setfam_1(k2_tarski(sK4,sK5))) != iProver_top ),
% 3.06/0.99      inference(global_propositional_subsumption,
% 3.06/0.99                [status(thm)],
% 3.06/0.99                [c_6915,c_28,c_29,c_30,c_1631,c_1636,c_1776,c_1777]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_6923,plain,
% 3.06/0.99      ( r2_hidden(sK3,sK5) != iProver_top
% 3.06/0.99      | r2_hidden(sK3,sK4) != iProver_top ),
% 3.06/0.99      inference(superposition,[status(thm)],[c_1048,c_6918]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_12,plain,
% 3.06/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.06/0.99      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
% 3.06/0.99      | r2_hidden(X0,sK1(X1,X0,X2))
% 3.06/0.99      | v2_struct_0(X1)
% 3.06/0.99      | ~ v2_pre_topc(X1)
% 3.06/0.99      | ~ l1_pre_topc(X1) ),
% 3.06/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_416,plain,
% 3.06/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.06/0.99      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
% 3.06/0.99      | r2_hidden(X0,sK1(X1,X0,X2))
% 3.06/0.99      | ~ v2_pre_topc(X1)
% 3.06/0.99      | ~ l1_pre_topc(X1)
% 3.06/0.99      | sK2 != X1 ),
% 3.06/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_24]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_417,plain,
% 3.06/0.99      ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,X1)))
% 3.06/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 3.06/0.99      | r2_hidden(X1,sK1(sK2,X1,X0))
% 3.06/0.99      | ~ v2_pre_topc(sK2)
% 3.06/0.99      | ~ l1_pre_topc(sK2) ),
% 3.06/0.99      inference(unflattening,[status(thm)],[c_416]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_421,plain,
% 3.06/0.99      ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,X1)))
% 3.06/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 3.06/0.99      | r2_hidden(X1,sK1(sK2,X1,X0)) ),
% 3.06/0.99      inference(global_propositional_subsumption,
% 3.06/0.99                [status(thm)],
% 3.06/0.99                [c_417,c_23,c_22]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_1031,plain,
% 3.06/0.99      ( m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,X1))) != iProver_top
% 3.06/0.99      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
% 3.06/0.99      | r2_hidden(X1,sK1(sK2,X1,X0)) = iProver_top ),
% 3.06/0.99      inference(predicate_to_equality,[status(thm)],[c_421]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_1382,plain,
% 3.06/0.99      ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 3.06/0.99      | r2_hidden(sK3,sK1(sK2,sK3,sK5)) = iProver_top ),
% 3.06/0.99      inference(superposition,[status(thm)],[c_1040,c_1031]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_1391,plain,
% 3.06/0.99      ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 3.06/0.99      | r2_hidden(sK3,sK5) = iProver_top ),
% 3.06/0.99      inference(light_normalisation,[status(thm)],[c_1382,c_1287]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_1383,plain,
% 3.06/0.99      ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 3.06/0.99      | r2_hidden(sK3,sK1(sK2,sK3,sK4)) = iProver_top ),
% 3.06/0.99      inference(superposition,[status(thm)],[c_1039,c_1031]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_1386,plain,
% 3.06/0.99      ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 3.06/0.99      | r2_hidden(sK3,sK4) = iProver_top ),
% 3.06/0.99      inference(light_normalisation,[status(thm)],[c_1383,c_1375]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(contradiction,plain,
% 3.06/0.99      ( $false ),
% 3.06/0.99      inference(minisat,[status(thm)],[c_6923,c_1391,c_1386,c_28]) ).
% 3.06/0.99  
% 3.06/0.99  
% 3.06/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.06/0.99  
% 3.06/0.99  ------                               Statistics
% 3.06/0.99  
% 3.06/0.99  ------ General
% 3.06/0.99  
% 3.06/0.99  abstr_ref_over_cycles:                  0
% 3.06/0.99  abstr_ref_under_cycles:                 0
% 3.06/0.99  gc_basic_clause_elim:                   0
% 3.06/0.99  forced_gc_time:                         0
% 3.06/0.99  parsing_time:                           0.009
% 3.06/0.99  unif_index_cands_time:                  0.
% 3.06/0.99  unif_index_add_time:                    0.
% 3.06/0.99  orderings_time:                         0.
% 3.06/0.99  out_proof_time:                         0.011
% 3.06/0.99  total_time:                             0.226
% 3.06/0.99  num_of_symbols:                         49
% 3.06/0.99  num_of_terms:                           7271
% 3.06/0.99  
% 3.06/0.99  ------ Preprocessing
% 3.06/0.99  
% 3.06/0.99  num_of_splits:                          0
% 3.06/0.99  num_of_split_atoms:                     0
% 3.06/0.99  num_of_reused_defs:                     0
% 3.06/0.99  num_eq_ax_congr_red:                    26
% 3.06/0.99  num_of_sem_filtered_clauses:            1
% 3.06/0.99  num_of_subtypes:                        0
% 3.06/0.99  monotx_restored_types:                  0
% 3.06/0.99  sat_num_of_epr_types:                   0
% 3.06/0.99  sat_num_of_non_cyclic_types:            0
% 3.06/0.99  sat_guarded_non_collapsed_types:        0
% 3.06/0.99  num_pure_diseq_elim:                    0
% 3.06/0.99  simp_replaced_by:                       0
% 3.06/0.99  res_preprocessed:                       114
% 3.06/0.99  prep_upred:                             0
% 3.06/0.99  prep_unflattend:                        8
% 3.06/0.99  smt_new_axioms:                         0
% 3.06/0.99  pred_elim_cands:                        3
% 3.06/0.99  pred_elim:                              3
% 3.06/0.99  pred_elim_cl:                           3
% 3.06/0.99  pred_elim_cycles:                       5
% 3.06/0.99  merged_defs:                            0
% 3.06/0.99  merged_defs_ncl:                        0
% 3.06/0.99  bin_hyper_res:                          0
% 3.06/0.99  prep_cycles:                            4
% 3.06/0.99  pred_elim_time:                         0.004
% 3.06/0.99  splitting_time:                         0.
% 3.06/0.99  sem_filter_time:                        0.
% 3.06/0.99  monotx_time:                            0.
% 3.06/0.99  subtype_inf_time:                       0.
% 3.06/0.99  
% 3.06/0.99  ------ Problem properties
% 3.06/0.99  
% 3.06/0.99  clauses:                                22
% 3.06/0.99  conjectures:                            4
% 3.06/0.99  epr:                                    1
% 3.06/0.99  horn:                                   20
% 3.06/0.99  ground:                                 4
% 3.06/0.99  unary:                                  4
% 3.06/0.99  binary:                                 5
% 3.06/0.99  lits:                                   59
% 3.06/0.99  lits_eq:                                5
% 3.06/0.99  fd_pure:                                0
% 3.06/0.99  fd_pseudo:                              0
% 3.06/0.99  fd_cond:                                0
% 3.06/0.99  fd_pseudo_cond:                         3
% 3.06/0.99  ac_symbols:                             0
% 3.06/0.99  
% 3.06/0.99  ------ Propositional Solver
% 3.06/0.99  
% 3.06/0.99  prop_solver_calls:                      27
% 3.06/0.99  prop_fast_solver_calls:                 958
% 3.06/0.99  smt_solver_calls:                       0
% 3.06/0.99  smt_fast_solver_calls:                  0
% 3.06/0.99  prop_num_of_clauses:                    2949
% 3.06/0.99  prop_preprocess_simplified:             7170
% 3.06/0.99  prop_fo_subsumed:                       36
% 3.06/0.99  prop_solver_time:                       0.
% 3.06/0.99  smt_solver_time:                        0.
% 3.06/0.99  smt_fast_solver_time:                   0.
% 3.06/0.99  prop_fast_solver_time:                  0.
% 3.06/0.99  prop_unsat_core_time:                   0.
% 3.06/0.99  
% 3.06/0.99  ------ QBF
% 3.06/0.99  
% 3.06/0.99  qbf_q_res:                              0
% 3.06/0.99  qbf_num_tautologies:                    0
% 3.06/0.99  qbf_prep_cycles:                        0
% 3.06/0.99  
% 3.06/0.99  ------ BMC1
% 3.06/0.99  
% 3.06/0.99  bmc1_current_bound:                     -1
% 3.06/0.99  bmc1_last_solved_bound:                 -1
% 3.06/0.99  bmc1_unsat_core_size:                   -1
% 3.06/0.99  bmc1_unsat_core_parents_size:           -1
% 3.06/0.99  bmc1_merge_next_fun:                    0
% 3.06/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.06/0.99  
% 3.06/0.99  ------ Instantiation
% 3.06/0.99  
% 3.06/0.99  inst_num_of_clauses:                    879
% 3.06/0.99  inst_num_in_passive:                    323
% 3.06/0.99  inst_num_in_active:                     293
% 3.06/0.99  inst_num_in_unprocessed:                263
% 3.06/0.99  inst_num_of_loops:                      320
% 3.06/0.99  inst_num_of_learning_restarts:          0
% 3.06/0.99  inst_num_moves_active_passive:          24
% 3.06/0.99  inst_lit_activity:                      0
% 3.06/0.99  inst_lit_activity_moves:                0
% 3.06/0.99  inst_num_tautologies:                   0
% 3.06/0.99  inst_num_prop_implied:                  0
% 3.06/0.99  inst_num_existing_simplified:           0
% 3.06/0.99  inst_num_eq_res_simplified:             0
% 3.06/0.99  inst_num_child_elim:                    0
% 3.06/0.99  inst_num_of_dismatching_blockings:      229
% 3.06/0.99  inst_num_of_non_proper_insts:           691
% 3.06/0.99  inst_num_of_duplicates:                 0
% 3.06/0.99  inst_inst_num_from_inst_to_res:         0
% 3.06/0.99  inst_dismatching_checking_time:         0.
% 3.06/0.99  
% 3.06/0.99  ------ Resolution
% 3.06/0.99  
% 3.06/0.99  res_num_of_clauses:                     0
% 3.06/0.99  res_num_in_passive:                     0
% 3.06/0.99  res_num_in_active:                      0
% 3.06/0.99  res_num_of_loops:                       118
% 3.06/0.99  res_forward_subset_subsumed:            22
% 3.06/0.99  res_backward_subset_subsumed:           0
% 3.06/0.99  res_forward_subsumed:                   0
% 3.06/0.99  res_backward_subsumed:                  0
% 3.06/0.99  res_forward_subsumption_resolution:     1
% 3.06/0.99  res_backward_subsumption_resolution:    0
% 3.06/0.99  res_clause_to_clause_subsumption:       420
% 3.06/0.99  res_orphan_elimination:                 0
% 3.06/0.99  res_tautology_del:                      32
% 3.06/0.99  res_num_eq_res_simplified:              0
% 3.06/0.99  res_num_sel_changes:                    0
% 3.06/0.99  res_moves_from_active_to_pass:          0
% 3.06/0.99  
% 3.06/0.99  ------ Superposition
% 3.06/0.99  
% 3.06/0.99  sup_time_total:                         0.
% 3.06/0.99  sup_time_generating:                    0.
% 3.06/0.99  sup_time_sim_full:                      0.
% 3.06/0.99  sup_time_sim_immed:                     0.
% 3.06/0.99  
% 3.06/0.99  sup_num_of_clauses:                     116
% 3.06/0.99  sup_num_in_active:                      64
% 3.06/0.99  sup_num_in_passive:                     52
% 3.06/0.99  sup_num_of_loops:                       63
% 3.06/0.99  sup_fw_superposition:                   66
% 3.06/0.99  sup_bw_superposition:                   51
% 3.06/0.99  sup_immediate_simplified:               19
% 3.06/0.99  sup_given_eliminated:                   0
% 3.06/0.99  comparisons_done:                       0
% 3.06/0.99  comparisons_avoided:                    0
% 3.06/0.99  
% 3.06/0.99  ------ Simplifications
% 3.06/0.99  
% 3.06/0.99  
% 3.06/0.99  sim_fw_subset_subsumed:                 2
% 3.06/0.99  sim_bw_subset_subsumed:                 0
% 3.06/0.99  sim_fw_subsumed:                        4
% 3.06/0.99  sim_bw_subsumed:                        0
% 3.06/0.99  sim_fw_subsumption_res:                 4
% 3.06/0.99  sim_bw_subsumption_res:                 0
% 3.06/0.99  sim_tautology_del:                      12
% 3.06/0.99  sim_eq_tautology_del:                   1
% 3.06/0.99  sim_eq_res_simp:                        2
% 3.06/0.99  sim_fw_demodulated:                     0
% 3.06/0.99  sim_bw_demodulated:                     0
% 3.06/0.99  sim_light_normalised:                   13
% 3.06/0.99  sim_joinable_taut:                      0
% 3.06/0.99  sim_joinable_simp:                      0
% 3.06/0.99  sim_ac_normalised:                      0
% 3.06/0.99  sim_smt_subsumption:                    0
% 3.06/0.99  
%------------------------------------------------------------------------------
