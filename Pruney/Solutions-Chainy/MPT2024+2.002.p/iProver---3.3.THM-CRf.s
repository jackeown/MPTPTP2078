%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:28:48 EST 2020

% Result     : Theorem 11.82s
% Output     : CNFRefutation 11.82s
% Verified   : 
% Statistics : Number of formulae       :  216 (1438 expanded)
%              Number of clauses        :  119 ( 320 expanded)
%              Number of leaves         :   27 ( 495 expanded)
%              Depth                    :   20
%              Number of atoms          :  745 (8054 expanded)
%              Number of equality atoms :  121 ( 186 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f50])).

fof(f64,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f19,axiom,(
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

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X2,X0,X1)
              | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X2,X0,X1)
              | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( m1_connsp_2(X1,X0,X2)
               => r2_hidden(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,X1)
              | ~ m1_connsp_2(X1,X0,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,X1)
              | ~ m1_connsp_2(X1,X0,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ m1_connsp_2(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f20,conjecture,(
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

fof(f21,negated_conjecture,(
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
    inference(negated_conjecture,[],[f20])).

fof(f44,plain,(
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
    inference(ennf_transformation,[],[f21])).

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))
          & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
     => ( ~ m1_subset_1(k2_xboole_0(X2,sK4),u1_struct_0(k9_yellow_6(X0,X1)))
        & m1_subset_1(sK4,u1_struct_0(k9_yellow_6(X0,X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))
              & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
          & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
     => ( ? [X3] :
            ( ~ m1_subset_1(k2_xboole_0(sK3,X3),u1_struct_0(k9_yellow_6(X0,X1)))
            & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
        & m1_subset_1(sK3,u1_struct_0(k9_yellow_6(X0,X1))) ) ) ),
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
                ( ~ m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,sK2)))
                & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,sK2))) )
            & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,sK2))) )
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
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
                  ( ~ m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK1,X1)))
                  & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK1,X1))) )
              & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK1,X1))) )
          & m1_subset_1(X1,u1_struct_0(sK1)) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK3,sK4),u1_struct_0(k9_yellow_6(sK1,sK2)))
    & m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK1,sK2)))
    & m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK1,sK2)))
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f45,f58,f57,f56,f55])).

fof(f87,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f59])).

fof(f88,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f59])).

fof(f89,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f59])).

fof(f91,plain,(
    m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK1,sK2))) ),
    inference(cnf_transformation,[],[f59])).

fof(f90,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f59])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f96,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f67,f71])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f98,plain,(
    ! [X0,X1] :
      ( k3_tarski(k2_tarski(k2_tarski(X0,X0),X1)) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f70,f71,f68])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k3_tarski(k2_tarski(X0,X1)),X2) ) ),
    inference(definition_unfolding,[],[f65,f71])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f95,plain,(
    ! [X0,X1] :
      ( k3_tarski(k2_tarski(X0,X1)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f66,f71])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)
     => r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f97,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k3_tarski(k2_tarski(k2_tarski(X0,X0),X1)),X1) ) ),
    inference(definition_unfolding,[],[f69,f71,f68])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f103,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f62])).

fof(f93,plain,(
    ~ m1_subset_1(k2_xboole_0(sK3,sK4),u1_struct_0(k9_yellow_6(sK1,sK2))) ),
    inference(cnf_transformation,[],[f59])).

fof(f101,plain,(
    ~ m1_subset_1(k3_tarski(k2_tarski(sK3,sK4)),u1_struct_0(k9_yellow_6(sK1,sK2))) ),
    inference(definition_unfolding,[],[f93,f71])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f78,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f18,axiom,(
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

fof(f40,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

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
    inference(nnf_transformation,[],[f41])).

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

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f32])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f92,plain,(
    m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK1,sK2))) ),
    inference(cnf_transformation,[],[f59])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f47,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f46])).

fof(f48,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f47,f48])).

fof(f60,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f10])).

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
    inference(nnf_transformation,[],[f26])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

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

fof(f74,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_pre_topc(X2,X0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_xboole_0(X1,X2),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v3_pre_topc(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v3_pre_topc(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(k3_tarski(k2_tarski(X1,X2)),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(definition_unfolding,[],[f80,f71])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f29])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k2_tarski(X1,X2)) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f77,f71])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f27])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_769,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_4872,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | ~ r2_hidden(X2,X1)
    | r2_hidden(X3,X0)
    | X3 != X2 ),
    inference(resolution,[status(thm)],[c_769,c_2])).

cnf(c_767,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_12994,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | ~ r2_hidden(X2,X1)
    | r2_hidden(X2,X0) ),
    inference(resolution,[status(thm)],[c_4872,c_767])).

cnf(c_24,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(X1,X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_20,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X2,X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_19,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_184,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_connsp_2(X0,X1,X2)
    | r2_hidden(X2,X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_20,c_19])).

cnf(c_185,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_184])).

cnf(c_356,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
    | r2_hidden(X0,X2)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(resolution,[status(thm)],[c_24,c_185])).

cnf(c_31,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_437,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
    | r2_hidden(X0,X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_356,c_31])).

cnf(c_438,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK1,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | r2_hidden(X1,X0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_437])).

cnf(c_30,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_29,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_442,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK1,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | r2_hidden(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_438,c_30,c_29])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK1,sK2))) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1499,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | r2_hidden(sK2,sK3) ),
    inference(resolution,[status(thm)],[c_442,c_27])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1532,plain,
    ( r2_hidden(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1499,c_28])).

cnf(c_40839,plain,
    ( ~ r1_tarski(X0,sK3)
    | ~ r1_tarski(sK3,X0)
    | r2_hidden(sK2,X0) ),
    inference(resolution,[status(thm)],[c_12994,c_1532])).

cnf(c_7,plain,
    ( r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_41389,plain,
    ( ~ r1_tarski(k3_tarski(k2_tarski(sK3,X0)),sK3)
    | r2_hidden(sK2,k3_tarski(k2_tarski(sK3,X0))) ),
    inference(resolution,[status(thm)],[c_40839,c_7])).

cnf(c_1256,plain,
    ( m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_1253,plain,
    ( m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK1,X1))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | r2_hidden(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_442])).

cnf(c_1571,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | r2_hidden(sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1256,c_1253])).

cnf(c_35,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_1500,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | r2_hidden(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1499])).

cnf(c_1648,plain,
    ( r2_hidden(sK2,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1571,c_35,c_1500])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | k3_tarski(k2_tarski(k2_tarski(X0,X0),X1)) = X1 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1266,plain,
    ( k3_tarski(k2_tarski(k2_tarski(X0,X0),X1)) = X1
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2758,plain,
    ( k3_tarski(k2_tarski(k2_tarski(sK2,sK2),sK3)) = sK3 ),
    inference(superposition,[status(thm)],[c_1648,c_1266])).

cnf(c_1268,plain,
    ( r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_5,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1270,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2795,plain,
    ( r1_tarski(X0,k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1268,c_1270])).

cnf(c_5614,plain,
    ( r1_tarski(k2_tarski(sK2,sK2),k3_tarski(k2_tarski(sK3,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2758,c_2795])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_tarski(k2_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1269,plain,
    ( k3_tarski(k2_tarski(X0,X1)) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_7286,plain,
    ( k3_tarski(k2_tarski(k2_tarski(sK2,sK2),k3_tarski(k2_tarski(sK3,X0)))) = k3_tarski(k2_tarski(sK3,X0)) ),
    inference(superposition,[status(thm)],[c_5614,c_1269])).

cnf(c_2651,plain,
    ( k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(superposition,[status(thm)],[c_1268,c_1269])).

cnf(c_8,plain,
    ( ~ r1_tarski(k3_tarski(k2_tarski(k2_tarski(X0,X0),X1)),X1)
    | r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1267,plain,
    ( r1_tarski(k3_tarski(k2_tarski(k2_tarski(X0,X0),X1)),X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_5658,plain,
    ( r1_tarski(k3_tarski(k2_tarski(k2_tarski(X0,X0),X1)),k3_tarski(k2_tarski(k2_tarski(X0,X0),X1))) != iProver_top
    | r2_hidden(X0,k3_tarski(k2_tarski(k2_tarski(X0,X0),X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2651,c_1267])).

cnf(c_4,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_6779,plain,
    ( r1_tarski(k3_tarski(X0),k3_tarski(X0)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_10464,plain,
    ( r1_tarski(k3_tarski(k2_tarski(k2_tarski(X0,X0),X1)),k3_tarski(k2_tarski(k2_tarski(X0,X0),X1))) ),
    inference(instantiation,[status(thm)],[c_6779])).

cnf(c_10466,plain,
    ( r1_tarski(k3_tarski(k2_tarski(k2_tarski(X0,X0),X1)),k3_tarski(k2_tarski(k2_tarski(X0,X0),X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10464])).

cnf(c_41596,plain,
    ( r2_hidden(X0,k3_tarski(k2_tarski(k2_tarski(X0,X0),X1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5658,c_10466])).

cnf(c_41618,plain,
    ( r2_hidden(sK2,k3_tarski(k2_tarski(sK3,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_7286,c_41596])).

cnf(c_41666,plain,
    ( r2_hidden(sK2,k3_tarski(k2_tarski(sK3,X0))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_41618])).

cnf(c_42843,plain,
    ( r2_hidden(sK2,k3_tarski(k2_tarski(sK3,X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_41389,c_41666])).

cnf(c_25,negated_conjecture,
    ( ~ m1_subset_1(k3_tarski(k2_tarski(sK3,sK4)),u1_struct_0(k9_yellow_6(sK1,sK2))) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_16,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_2188,plain,
    ( ~ r2_hidden(k3_tarski(k2_tarski(sK3,sK4)),u1_struct_0(k9_yellow_6(sK1,sK2))) ),
    inference(resolution,[status(thm)],[c_25,c_16])).

cnf(c_21,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_506,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_31])).

cnf(c_507,plain,
    ( ~ v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X1,X0)
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK1,X1)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_506])).

cnf(c_511,plain,
    ( ~ v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X1,X0)
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK1,X1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_507,c_30,c_29])).

cnf(c_17,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_527,plain,
    ( ~ v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X1,X0)
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK1,X1))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_511,c_17])).

cnf(c_3351,plain,
    ( ~ v3_pre_topc(k3_tarski(k2_tarski(sK3,sK4)),sK1)
    | ~ m1_subset_1(k3_tarski(k2_tarski(sK3,sK4)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK2,k3_tarski(k2_tarski(sK3,sK4))) ),
    inference(resolution,[status(thm)],[c_2188,c_527])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK1,sK2))) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1497,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | r2_hidden(sK2,sK4) ),
    inference(resolution,[status(thm)],[c_442,c_26])).

cnf(c_379,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(resolution,[status(thm)],[c_24,c_19])).

cnf(c_416,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_379,c_31])).

cnf(c_417,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK1,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_416])).

cnf(c_421,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK1,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_417,c_30,c_29])).

cnf(c_1596,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(resolution,[status(thm)],[c_421,c_26])).

cnf(c_1598,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(resolution,[status(thm)],[c_421,c_27])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1803,plain,
    ( ~ r2_hidden(sK2,sK4)
    | ~ v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2675,plain,
    ( r2_hidden(sK4,u1_struct_0(k9_yellow_6(sK1,sK2)))
    | v1_xboole_0(u1_struct_0(k9_yellow_6(sK1,sK2))) ),
    inference(resolution,[status(thm)],[c_13,c_26])).

cnf(c_2099,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X1,u1_struct_0(k9_yellow_6(sK1,X0))) ),
    inference(resolution,[status(thm)],[c_16,c_421])).

cnf(c_22,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_482,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_31])).

cnf(c_483,plain,
    ( v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(sK1,X1)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_482])).

cnf(c_487,plain,
    ( v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(sK1,X1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_483,c_30,c_29])).

cnf(c_2270,plain,
    ( v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(sK1,X1))) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2099,c_487])).

cnf(c_2819,plain,
    ( v3_pre_topc(sK4,sK1)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(k9_yellow_6(sK1,sK2))) ),
    inference(resolution,[status(thm)],[c_2675,c_2270])).

cnf(c_2677,plain,
    ( r2_hidden(sK3,u1_struct_0(k9_yellow_6(sK1,sK2)))
    | v1_xboole_0(u1_struct_0(k9_yellow_6(sK1,sK2))) ),
    inference(resolution,[status(thm)],[c_13,c_27])).

cnf(c_2955,plain,
    ( v3_pre_topc(sK3,sK1)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(k9_yellow_6(sK1,sK2))) ),
    inference(resolution,[status(thm)],[c_2677,c_2270])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_2205,plain,
    ( ~ m1_subset_1(sK4,X0)
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_3020,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK1,sK2)))
    | ~ v1_xboole_0(u1_struct_0(k9_yellow_6(sK1,sK2)))
    | v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_2205])).

cnf(c_18,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ v3_pre_topc(X2,X1)
    | v3_pre_topc(k3_tarski(k2_tarski(X2,X0)),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_558,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ v3_pre_topc(X2,X1)
    | v3_pre_topc(k3_tarski(k2_tarski(X2,X0)),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_29])).

cnf(c_559,plain,
    ( ~ v3_pre_topc(X0,sK1)
    | ~ v3_pre_topc(X1,sK1)
    | v3_pre_topc(k3_tarski(k2_tarski(X1,X0)),sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_558])).

cnf(c_563,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v3_pre_topc(k3_tarski(k2_tarski(X1,X0)),sK1)
    | ~ v3_pre_topc(X1,sK1)
    | ~ v3_pre_topc(X0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_559,c_30])).

cnf(c_564,plain,
    ( ~ v3_pre_topc(X0,sK1)
    | ~ v3_pre_topc(X1,sK1)
    | v3_pre_topc(k3_tarski(k2_tarski(X1,X0)),sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(renaming,[status(thm)],[c_563])).

cnf(c_1249,plain,
    ( v3_pre_topc(X0,sK1) != iProver_top
    | v3_pre_topc(X1,sK1) != iProver_top
    | v3_pre_topc(k3_tarski(k2_tarski(X1,X0)),sK1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_564])).

cnf(c_1250,plain,
    ( v3_pre_topc(X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(X1,X0) != iProver_top
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK1,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_527])).

cnf(c_1260,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2250,plain,
    ( v3_pre_topc(X0,sK1) != iProver_top
    | m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK1,X1))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1250,c_1260])).

cnf(c_1258,plain,
    ( m1_subset_1(k3_tarski(k2_tarski(sK3,sK4)),u1_struct_0(k9_yellow_6(sK1,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_5377,plain,
    ( v3_pre_topc(k3_tarski(k2_tarski(sK3,sK4)),sK1) != iProver_top
    | m1_subset_1(k3_tarski(k2_tarski(sK3,sK4)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(sK2,k3_tarski(k2_tarski(sK3,sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2250,c_1258])).

cnf(c_1597,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1596])).

cnf(c_1599,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1598])).

cnf(c_3352,plain,
    ( v3_pre_topc(k3_tarski(k2_tarski(sK3,sK4)),sK1) != iProver_top
    | m1_subset_1(k3_tarski(k2_tarski(sK3,sK4)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(sK2,k3_tarski(k2_tarski(sK3,sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3351])).

cnf(c_1257,plain,
    ( m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_1254,plain,
    ( m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK1,X1))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_421])).

cnf(c_1657,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1257,c_1254])).

cnf(c_1997,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1657,c_35,c_1597])).

cnf(c_1658,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1256,c_1254])).

cnf(c_2060,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1658,c_35,c_1599])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X2,X0) = k3_tarski(k2_tarski(X2,X0)) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1261,plain,
    ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3465,plain,
    ( k4_subset_1(u1_struct_0(sK1),sK3,X0) = k3_tarski(k2_tarski(sK3,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2060,c_1261])).

cnf(c_5248,plain,
    ( k4_subset_1(u1_struct_0(sK1),sK3,sK4) = k3_tarski(k2_tarski(sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_1997,c_3465])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | m1_subset_1(k4_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1262,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k4_subset_1(X1,X0,X2),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_5271,plain,
    ( m1_subset_1(k3_tarski(k2_tarski(sK3,sK4)),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5248,c_1262])).

cnf(c_5785,plain,
    ( v3_pre_topc(k3_tarski(k2_tarski(sK3,sK4)),sK1) != iProver_top
    | r2_hidden(sK2,k3_tarski(k2_tarski(sK3,sK4))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5377,c_35,c_1597,c_1599,c_3352,c_5271])).

cnf(c_5791,plain,
    ( v3_pre_topc(sK4,sK1) != iProver_top
    | v3_pre_topc(sK3,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(sK2,k3_tarski(k2_tarski(sK3,sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1249,c_5785])).

cnf(c_5792,plain,
    ( ~ v3_pre_topc(sK4,sK1)
    | ~ v3_pre_topc(sK3,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK2,k3_tarski(k2_tarski(sK3,sK4))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5791])).

cnf(c_6734,plain,
    ( ~ r2_hidden(sK2,k3_tarski(k2_tarski(sK3,sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3351,c_28,c_26,c_1497,c_1596,c_1598,c_1803,c_2819,c_2955,c_3020,c_5792])).

cnf(c_42854,plain,
    ( $false ),
    inference(backward_subsumption_resolution,[status(thm)],[c_42843,c_6734])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:44:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 11.82/1.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.82/1.99  
% 11.82/1.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.82/1.99  
% 11.82/1.99  ------  iProver source info
% 11.82/1.99  
% 11.82/1.99  git: date: 2020-06-30 10:37:57 +0100
% 11.82/1.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.82/1.99  git: non_committed_changes: false
% 11.82/1.99  git: last_make_outside_of_git: false
% 11.82/1.99  
% 11.82/1.99  ------ 
% 11.82/1.99  ------ Parsing...
% 11.82/1.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.82/1.99  
% 11.82/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 11.82/1.99  
% 11.82/1.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.82/1.99  
% 11.82/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.82/1.99  ------ Proving...
% 11.82/1.99  ------ Problem Properties 
% 11.82/1.99  
% 11.82/1.99  
% 11.82/1.99  clauses                                 26
% 11.82/1.99  conjectures                             4
% 11.82/1.99  EPR                                     7
% 11.82/1.99  Horn                                    24
% 11.82/1.99  unary                                   6
% 11.82/1.99  binary                                  7
% 11.82/1.99  lits                                    64
% 11.82/1.99  lits eq                                 4
% 11.82/1.99  fd_pure                                 0
% 11.82/1.99  fd_pseudo                               0
% 11.82/1.99  fd_cond                                 0
% 11.82/1.99  fd_pseudo_cond                          1
% 11.82/1.99  AC symbols                              0
% 11.82/1.99  
% 11.82/1.99  ------ Input Options Time Limit: Unbounded
% 11.82/1.99  
% 11.82/1.99  
% 11.82/1.99  ------ 
% 11.82/1.99  Current options:
% 11.82/1.99  ------ 
% 11.82/1.99  
% 11.82/1.99  
% 11.82/1.99  
% 11.82/1.99  
% 11.82/1.99  ------ Proving...
% 11.82/1.99  
% 11.82/1.99  
% 11.82/1.99  % SZS status Theorem for theBenchmark.p
% 11.82/1.99  
% 11.82/1.99   Resolution empty clause
% 11.82/1.99  
% 11.82/1.99  % SZS output start CNFRefutation for theBenchmark.p
% 11.82/1.99  
% 11.82/1.99  fof(f2,axiom,(
% 11.82/1.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 11.82/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.82/1.99  
% 11.82/1.99  fof(f50,plain,(
% 11.82/1.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.82/1.99    inference(nnf_transformation,[],[f2])).
% 11.82/1.99  
% 11.82/1.99  fof(f51,plain,(
% 11.82/1.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.82/1.99    inference(flattening,[],[f50])).
% 11.82/1.99  
% 11.82/1.99  fof(f64,plain,(
% 11.82/1.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 11.82/1.99    inference(cnf_transformation,[],[f51])).
% 11.82/1.99  
% 11.82/1.99  fof(f19,axiom,(
% 11.82/1.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => m1_connsp_2(X2,X0,X1))))),
% 11.82/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.82/1.99  
% 11.82/1.99  fof(f42,plain,(
% 11.82/1.99    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 11.82/1.99    inference(ennf_transformation,[],[f19])).
% 11.82/1.99  
% 11.82/1.99  fof(f43,plain,(
% 11.82/1.99    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.82/1.99    inference(flattening,[],[f42])).
% 11.82/1.99  
% 11.82/1.99  fof(f86,plain,(
% 11.82/1.99    ( ! [X2,X0,X1] : (m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.82/1.99    inference(cnf_transformation,[],[f43])).
% 11.82/1.99  
% 11.82/1.99  fof(f17,axiom,(
% 11.82/1.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (m1_connsp_2(X1,X0,X2) => r2_hidden(X2,X1)))))),
% 11.82/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.82/1.99  
% 11.82/1.99  fof(f38,plain,(
% 11.82/1.99    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 11.82/1.99    inference(ennf_transformation,[],[f17])).
% 11.82/1.99  
% 11.82/1.99  fof(f39,plain,(
% 11.82/1.99    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.82/1.99    inference(flattening,[],[f38])).
% 11.82/1.99  
% 11.82/1.99  fof(f82,plain,(
% 11.82/1.99    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.82/1.99    inference(cnf_transformation,[],[f39])).
% 11.82/1.99  
% 11.82/1.99  fof(f16,axiom,(
% 11.82/1.99    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 11.82/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.82/1.99  
% 11.82/1.99  fof(f36,plain,(
% 11.82/1.99    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 11.82/1.99    inference(ennf_transformation,[],[f16])).
% 11.82/1.99  
% 11.82/1.99  fof(f37,plain,(
% 11.82/1.99    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.82/1.99    inference(flattening,[],[f36])).
% 11.82/1.99  
% 11.82/1.99  fof(f81,plain,(
% 11.82/1.99    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.82/1.99    inference(cnf_transformation,[],[f37])).
% 11.82/1.99  
% 11.82/1.99  fof(f20,conjecture,(
% 11.82/1.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) => m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))))))),
% 11.82/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.82/1.99  
% 11.82/1.99  fof(f21,negated_conjecture,(
% 11.82/1.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) => m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))))))),
% 11.82/1.99    inference(negated_conjecture,[],[f20])).
% 11.82/1.99  
% 11.82/1.99  fof(f44,plain,(
% 11.82/1.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 11.82/1.99    inference(ennf_transformation,[],[f21])).
% 11.82/1.99  
% 11.82/1.99  fof(f45,plain,(
% 11.82/1.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 11.82/1.99    inference(flattening,[],[f44])).
% 11.82/1.99  
% 11.82/1.99  fof(f58,plain,(
% 11.82/1.99    ( ! [X2,X0,X1] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) => (~m1_subset_1(k2_xboole_0(X2,sK4),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(sK4,u1_struct_0(k9_yellow_6(X0,X1))))) )),
% 11.82/1.99    introduced(choice_axiom,[])).
% 11.82/1.99  
% 11.82/1.99  fof(f57,plain,(
% 11.82/1.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) => (? [X3] : (~m1_subset_1(k2_xboole_0(sK3,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(sK3,u1_struct_0(k9_yellow_6(X0,X1))))) )),
% 11.82/1.99    introduced(choice_axiom,[])).
% 11.82/1.99  
% 11.82/1.99  fof(f56,plain,(
% 11.82/1.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,sK2))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,sK2)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,sK2)))) & m1_subset_1(sK2,u1_struct_0(X0)))) )),
% 11.82/1.99    introduced(choice_axiom,[])).
% 11.82/1.99  
% 11.82/1.99  fof(f55,plain,(
% 11.82/1.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK1,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK1,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK1,X1)))) & m1_subset_1(X1,u1_struct_0(sK1))) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 11.82/1.99    introduced(choice_axiom,[])).
% 11.82/1.99  
% 11.82/1.99  fof(f59,plain,(
% 11.82/1.99    (((~m1_subset_1(k2_xboole_0(sK3,sK4),u1_struct_0(k9_yellow_6(sK1,sK2))) & m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK1,sK2)))) & m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK1,sK2)))) & m1_subset_1(sK2,u1_struct_0(sK1))) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 11.82/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f45,f58,f57,f56,f55])).
% 11.82/1.99  
% 11.82/1.99  fof(f87,plain,(
% 11.82/1.99    ~v2_struct_0(sK1)),
% 11.82/1.99    inference(cnf_transformation,[],[f59])).
% 11.82/1.99  
% 11.82/1.99  fof(f88,plain,(
% 11.82/1.99    v2_pre_topc(sK1)),
% 11.82/1.99    inference(cnf_transformation,[],[f59])).
% 11.82/1.99  
% 11.82/1.99  fof(f89,plain,(
% 11.82/1.99    l1_pre_topc(sK1)),
% 11.82/1.99    inference(cnf_transformation,[],[f59])).
% 11.82/1.99  
% 11.82/1.99  fof(f91,plain,(
% 11.82/1.99    m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK1,sK2)))),
% 11.82/1.99    inference(cnf_transformation,[],[f59])).
% 11.82/1.99  
% 11.82/1.99  fof(f90,plain,(
% 11.82/1.99    m1_subset_1(sK2,u1_struct_0(sK1))),
% 11.82/1.99    inference(cnf_transformation,[],[f59])).
% 11.82/1.99  
% 11.82/1.99  fof(f5,axiom,(
% 11.82/1.99    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 11.82/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.82/1.99  
% 11.82/1.99  fof(f67,plain,(
% 11.82/1.99    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 11.82/1.99    inference(cnf_transformation,[],[f5])).
% 11.82/1.99  
% 11.82/1.99  fof(f9,axiom,(
% 11.82/1.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 11.82/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.82/1.99  
% 11.82/1.99  fof(f71,plain,(
% 11.82/1.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 11.82/1.99    inference(cnf_transformation,[],[f9])).
% 11.82/1.99  
% 11.82/1.99  fof(f96,plain,(
% 11.82/1.99    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) )),
% 11.82/1.99    inference(definition_unfolding,[],[f67,f71])).
% 11.82/1.99  
% 11.82/1.99  fof(f8,axiom,(
% 11.82/1.99    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 11.82/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.82/1.99  
% 11.82/1.99  fof(f25,plain,(
% 11.82/1.99    ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1))),
% 11.82/1.99    inference(ennf_transformation,[],[f8])).
% 11.82/1.99  
% 11.82/1.99  fof(f70,plain,(
% 11.82/1.99    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1)) )),
% 11.82/1.99    inference(cnf_transformation,[],[f25])).
% 11.82/1.99  
% 11.82/1.99  fof(f6,axiom,(
% 11.82/1.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 11.82/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.82/1.99  
% 11.82/1.99  fof(f68,plain,(
% 11.82/1.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 11.82/1.99    inference(cnf_transformation,[],[f6])).
% 11.82/1.99  
% 11.82/1.99  fof(f98,plain,(
% 11.82/1.99    ( ! [X0,X1] : (k3_tarski(k2_tarski(k2_tarski(X0,X0),X1)) = X1 | ~r2_hidden(X0,X1)) )),
% 11.82/1.99    inference(definition_unfolding,[],[f70,f71,f68])).
% 11.82/1.99  
% 11.82/1.99  fof(f3,axiom,(
% 11.82/1.99    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 11.82/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.82/1.99  
% 11.82/1.99  fof(f22,plain,(
% 11.82/1.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 11.82/1.99    inference(ennf_transformation,[],[f3])).
% 11.82/1.99  
% 11.82/1.99  fof(f65,plain,(
% 11.82/1.99    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 11.82/1.99    inference(cnf_transformation,[],[f22])).
% 11.82/1.99  
% 11.82/1.99  fof(f94,plain,(
% 11.82/1.99    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k3_tarski(k2_tarski(X0,X1)),X2)) )),
% 11.82/1.99    inference(definition_unfolding,[],[f65,f71])).
% 11.82/1.99  
% 11.82/1.99  fof(f4,axiom,(
% 11.82/1.99    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 11.82/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.82/1.99  
% 11.82/1.99  fof(f23,plain,(
% 11.82/1.99    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 11.82/1.99    inference(ennf_transformation,[],[f4])).
% 11.82/1.99  
% 11.82/1.99  fof(f66,plain,(
% 11.82/1.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 11.82/1.99    inference(cnf_transformation,[],[f23])).
% 11.82/1.99  
% 11.82/1.99  fof(f95,plain,(
% 11.82/1.99    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = X1 | ~r1_tarski(X0,X1)) )),
% 11.82/1.99    inference(definition_unfolding,[],[f66,f71])).
% 11.82/1.99  
% 11.82/1.99  fof(f7,axiom,(
% 11.82/1.99    ! [X0,X1] : (r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) => r2_hidden(X0,X1))),
% 11.82/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.82/1.99  
% 11.82/1.99  fof(f24,plain,(
% 11.82/1.99    ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1))),
% 11.82/1.99    inference(ennf_transformation,[],[f7])).
% 11.82/1.99  
% 11.82/1.99  fof(f69,plain,(
% 11.82/1.99    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)) )),
% 11.82/1.99    inference(cnf_transformation,[],[f24])).
% 11.82/1.99  
% 11.82/1.99  fof(f97,plain,(
% 11.82/1.99    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k3_tarski(k2_tarski(k2_tarski(X0,X0),X1)),X1)) )),
% 11.82/1.99    inference(definition_unfolding,[],[f69,f71,f68])).
% 11.82/1.99  
% 11.82/1.99  fof(f62,plain,(
% 11.82/1.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 11.82/1.99    inference(cnf_transformation,[],[f51])).
% 11.82/1.99  
% 11.82/1.99  fof(f103,plain,(
% 11.82/1.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 11.82/1.99    inference(equality_resolution,[],[f62])).
% 11.82/1.99  
% 11.82/1.99  fof(f93,plain,(
% 11.82/1.99    ~m1_subset_1(k2_xboole_0(sK3,sK4),u1_struct_0(k9_yellow_6(sK1,sK2)))),
% 11.82/1.99    inference(cnf_transformation,[],[f59])).
% 11.82/1.99  
% 11.82/1.99  fof(f101,plain,(
% 11.82/1.99    ~m1_subset_1(k3_tarski(k2_tarski(sK3,sK4)),u1_struct_0(k9_yellow_6(sK1,sK2)))),
% 11.82/1.99    inference(definition_unfolding,[],[f93,f71])).
% 11.82/1.99  
% 11.82/1.99  fof(f13,axiom,(
% 11.82/1.99    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 11.82/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.82/1.99  
% 11.82/1.99  fof(f31,plain,(
% 11.82/1.99    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 11.82/1.99    inference(ennf_transformation,[],[f13])).
% 11.82/1.99  
% 11.82/1.99  fof(f78,plain,(
% 11.82/1.99    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 11.82/1.99    inference(cnf_transformation,[],[f31])).
% 11.82/1.99  
% 11.82/1.99  fof(f18,axiom,(
% 11.82/1.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))))))),
% 11.82/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.82/1.99  
% 11.82/1.99  fof(f40,plain,(
% 11.82/1.99    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 11.82/1.99    inference(ennf_transformation,[],[f18])).
% 11.82/1.99  
% 11.82/1.99  fof(f41,plain,(
% 11.82/1.99    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.82/1.99    inference(flattening,[],[f40])).
% 11.82/1.99  
% 11.82/1.99  fof(f53,plain,(
% 11.82/1.99    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | (~v3_pre_topc(X2,X0) | ~r2_hidden(X1,X2))) & ((v3_pre_topc(X2,X0) & r2_hidden(X1,X2)) | ~r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.82/1.99    inference(nnf_transformation,[],[f41])).
% 11.82/1.99  
% 11.82/1.99  fof(f54,plain,(
% 11.82/1.99    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~v3_pre_topc(X2,X0) | ~r2_hidden(X1,X2)) & ((v3_pre_topc(X2,X0) & r2_hidden(X1,X2)) | ~r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.82/1.99    inference(flattening,[],[f53])).
% 11.82/1.99  
% 11.82/1.99  fof(f85,plain,(
% 11.82/1.99    ( ! [X2,X0,X1] : (r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~v3_pre_topc(X2,X0) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.82/1.99    inference(cnf_transformation,[],[f54])).
% 11.82/1.99  
% 11.82/1.99  fof(f14,axiom,(
% 11.82/1.99    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 11.82/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.82/1.99  
% 11.82/1.99  fof(f32,plain,(
% 11.82/1.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 11.82/1.99    inference(ennf_transformation,[],[f14])).
% 11.82/1.99  
% 11.82/1.99  fof(f33,plain,(
% 11.82/1.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 11.82/1.99    inference(flattening,[],[f32])).
% 11.82/1.99  
% 11.82/1.99  fof(f79,plain,(
% 11.82/1.99    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 11.82/1.99    inference(cnf_transformation,[],[f33])).
% 11.82/1.99  
% 11.82/1.99  fof(f92,plain,(
% 11.82/1.99    m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK1,sK2)))),
% 11.82/1.99    inference(cnf_transformation,[],[f59])).
% 11.82/1.99  
% 11.82/1.99  fof(f1,axiom,(
% 11.82/1.99    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 11.82/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.82/1.99  
% 11.82/1.99  fof(f46,plain,(
% 11.82/1.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 11.82/1.99    inference(nnf_transformation,[],[f1])).
% 11.82/1.99  
% 11.82/1.99  fof(f47,plain,(
% 11.82/1.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 11.82/1.99    inference(rectify,[],[f46])).
% 11.82/1.99  
% 11.82/1.99  fof(f48,plain,(
% 11.82/1.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 11.82/1.99    introduced(choice_axiom,[])).
% 11.82/1.99  
% 11.82/1.99  fof(f49,plain,(
% 11.82/1.99    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 11.82/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f47,f48])).
% 11.82/1.99  
% 11.82/1.99  fof(f60,plain,(
% 11.82/1.99    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 11.82/1.99    inference(cnf_transformation,[],[f49])).
% 11.82/1.99  
% 11.82/1.99  fof(f10,axiom,(
% 11.82/1.99    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 11.82/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.82/1.99  
% 11.82/1.99  fof(f26,plain,(
% 11.82/1.99    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 11.82/1.99    inference(ennf_transformation,[],[f10])).
% 11.82/1.99  
% 11.82/1.99  fof(f52,plain,(
% 11.82/1.99    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 11.82/1.99    inference(nnf_transformation,[],[f26])).
% 11.82/1.99  
% 11.82/1.99  fof(f72,plain,(
% 11.82/1.99    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 11.82/1.99    inference(cnf_transformation,[],[f52])).
% 11.82/1.99  
% 11.82/1.99  fof(f84,plain,(
% 11.82/1.99    ( ! [X2,X0,X1] : (v3_pre_topc(X2,X0) | ~r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.82/1.99    inference(cnf_transformation,[],[f54])).
% 11.82/1.99  
% 11.82/1.99  fof(f74,plain,(
% 11.82/1.99    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,X0) | ~v1_xboole_0(X0)) )),
% 11.82/1.99    inference(cnf_transformation,[],[f52])).
% 11.82/1.99  
% 11.82/1.99  fof(f15,axiom,(
% 11.82/1.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X2,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_xboole_0(X1,X2),X0))),
% 11.82/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.82/1.99  
% 11.82/1.99  fof(f34,plain,(
% 11.82/1.99    ! [X0,X1,X2] : (v3_pre_topc(k2_xboole_0(X1,X2),X0) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 11.82/1.99    inference(ennf_transformation,[],[f15])).
% 11.82/1.99  
% 11.82/1.99  fof(f35,plain,(
% 11.82/1.99    ! [X0,X1,X2] : (v3_pre_topc(k2_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 11.82/1.99    inference(flattening,[],[f34])).
% 11.82/1.99  
% 11.82/1.99  fof(f80,plain,(
% 11.82/1.99    ( ! [X2,X0,X1] : (v3_pre_topc(k2_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 11.82/1.99    inference(cnf_transformation,[],[f35])).
% 11.82/1.99  
% 11.82/1.99  fof(f100,plain,(
% 11.82/1.99    ( ! [X2,X0,X1] : (v3_pre_topc(k3_tarski(k2_tarski(X1,X2)),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 11.82/1.99    inference(definition_unfolding,[],[f80,f71])).
% 11.82/1.99  
% 11.82/1.99  fof(f12,axiom,(
% 11.82/1.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 11.82/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.82/1.99  
% 11.82/1.99  fof(f29,plain,(
% 11.82/1.99    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 11.82/1.99    inference(ennf_transformation,[],[f12])).
% 11.82/1.99  
% 11.82/1.99  fof(f30,plain,(
% 11.82/1.99    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.82/1.99    inference(flattening,[],[f29])).
% 11.82/1.99  
% 11.82/1.99  fof(f77,plain,(
% 11.82/1.99    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.82/1.99    inference(cnf_transformation,[],[f30])).
% 11.82/1.99  
% 11.82/1.99  fof(f99,plain,(
% 11.82/1.99    ( ! [X2,X0,X1] : (k3_tarski(k2_tarski(X1,X2)) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.82/1.99    inference(definition_unfolding,[],[f77,f71])).
% 11.82/1.99  
% 11.82/1.99  fof(f11,axiom,(
% 11.82/1.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 11.82/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.82/1.99  
% 11.82/1.99  fof(f27,plain,(
% 11.82/1.99    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 11.82/1.99    inference(ennf_transformation,[],[f11])).
% 11.82/1.99  
% 11.82/1.99  fof(f28,plain,(
% 11.82/1.99    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.82/1.99    inference(flattening,[],[f27])).
% 11.82/1.99  
% 11.82/1.99  fof(f76,plain,(
% 11.82/1.99    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.82/1.99    inference(cnf_transformation,[],[f28])).
% 11.82/1.99  
% 11.82/1.99  cnf(c_769,plain,
% 11.82/1.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 11.82/1.99      theory(equality) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_2,plain,
% 11.82/1.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 11.82/1.99      inference(cnf_transformation,[],[f64]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_4872,plain,
% 11.82/1.99      ( ~ r1_tarski(X0,X1)
% 11.82/1.99      | ~ r1_tarski(X1,X0)
% 11.82/1.99      | ~ r2_hidden(X2,X1)
% 11.82/1.99      | r2_hidden(X3,X0)
% 11.82/1.99      | X3 != X2 ),
% 11.82/1.99      inference(resolution,[status(thm)],[c_769,c_2]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_767,plain,( X0 = X0 ),theory(equality) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_12994,plain,
% 11.82/1.99      ( ~ r1_tarski(X0,X1)
% 11.82/1.99      | ~ r1_tarski(X1,X0)
% 11.82/1.99      | ~ r2_hidden(X2,X1)
% 11.82/1.99      | r2_hidden(X2,X0) ),
% 11.82/1.99      inference(resolution,[status(thm)],[c_4872,c_767]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_24,plain,
% 11.82/1.99      ( m1_connsp_2(X0,X1,X2)
% 11.82/1.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 11.82/1.99      | ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(X1,X2)))
% 11.82/1.99      | v2_struct_0(X1)
% 11.82/1.99      | ~ v2_pre_topc(X1)
% 11.82/1.99      | ~ l1_pre_topc(X1) ),
% 11.82/1.99      inference(cnf_transformation,[],[f86]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_20,plain,
% 11.82/1.99      ( ~ m1_connsp_2(X0,X1,X2)
% 11.82/1.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 11.82/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.82/1.99      | r2_hidden(X2,X0)
% 11.82/1.99      | v2_struct_0(X1)
% 11.82/1.99      | ~ v2_pre_topc(X1)
% 11.82/1.99      | ~ l1_pre_topc(X1) ),
% 11.82/1.99      inference(cnf_transformation,[],[f82]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_19,plain,
% 11.82/1.99      ( ~ m1_connsp_2(X0,X1,X2)
% 11.82/1.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 11.82/1.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.82/1.99      | v2_struct_0(X1)
% 11.82/1.99      | ~ v2_pre_topc(X1)
% 11.82/1.99      | ~ l1_pre_topc(X1) ),
% 11.82/1.99      inference(cnf_transformation,[],[f81]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_184,plain,
% 11.82/1.99      ( ~ m1_subset_1(X2,u1_struct_0(X1))
% 11.82/1.99      | ~ m1_connsp_2(X0,X1,X2)
% 11.82/1.99      | r2_hidden(X2,X0)
% 11.82/1.99      | v2_struct_0(X1)
% 11.82/1.99      | ~ v2_pre_topc(X1)
% 11.82/1.99      | ~ l1_pre_topc(X1) ),
% 11.82/1.99      inference(global_propositional_subsumption,[status(thm)],[c_20,c_19]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_185,plain,
% 11.82/1.99      ( ~ m1_connsp_2(X0,X1,X2)
% 11.82/1.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 11.82/1.99      | r2_hidden(X2,X0)
% 11.82/1.99      | v2_struct_0(X1)
% 11.82/1.99      | ~ v2_pre_topc(X1)
% 11.82/1.99      | ~ l1_pre_topc(X1) ),
% 11.82/1.99      inference(renaming,[status(thm)],[c_184]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_356,plain,
% 11.82/1.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 11.82/1.99      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
% 11.82/1.99      | r2_hidden(X0,X2)
% 11.82/1.99      | v2_struct_0(X1)
% 11.82/1.99      | ~ v2_pre_topc(X1)
% 11.82/1.99      | ~ l1_pre_topc(X1) ),
% 11.82/1.99      inference(resolution,[status(thm)],[c_24,c_185]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_31,negated_conjecture,
% 11.82/1.99      ( ~ v2_struct_0(sK1) ),
% 11.82/1.99      inference(cnf_transformation,[],[f87]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_437,plain,
% 11.82/1.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 11.82/1.99      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
% 11.82/1.99      | r2_hidden(X0,X2)
% 11.82/1.99      | ~ v2_pre_topc(X1)
% 11.82/1.99      | ~ l1_pre_topc(X1)
% 11.82/1.99      | sK1 != X1 ),
% 11.82/1.99      inference(resolution_lifted,[status(thm)],[c_356,c_31]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_438,plain,
% 11.82/1.99      ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK1,X1)))
% 11.82/1.99      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 11.82/1.99      | r2_hidden(X1,X0)
% 11.82/1.99      | ~ v2_pre_topc(sK1)
% 11.82/1.99      | ~ l1_pre_topc(sK1) ),
% 11.82/1.99      inference(unflattening,[status(thm)],[c_437]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_30,negated_conjecture,
% 11.82/1.99      ( v2_pre_topc(sK1) ),
% 11.82/1.99      inference(cnf_transformation,[],[f88]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_29,negated_conjecture,
% 11.82/1.99      ( l1_pre_topc(sK1) ),
% 11.82/1.99      inference(cnf_transformation,[],[f89]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_442,plain,
% 11.82/1.99      ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK1,X1)))
% 11.82/1.99      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 11.82/1.99      | r2_hidden(X1,X0) ),
% 11.82/1.99      inference(global_propositional_subsumption,
% 11.82/1.99                [status(thm)],
% 11.82/1.99                [c_438,c_30,c_29]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_27,negated_conjecture,
% 11.82/1.99      ( m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK1,sK2))) ),
% 11.82/1.99      inference(cnf_transformation,[],[f91]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_1499,plain,
% 11.82/1.99      ( ~ m1_subset_1(sK2,u1_struct_0(sK1)) | r2_hidden(sK2,sK3) ),
% 11.82/1.99      inference(resolution,[status(thm)],[c_442,c_27]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_28,negated_conjecture,
% 11.82/1.99      ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 11.82/1.99      inference(cnf_transformation,[],[f90]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_1532,plain,
% 11.82/1.99      ( r2_hidden(sK2,sK3) ),
% 11.82/1.99      inference(global_propositional_subsumption,[status(thm)],[c_1499,c_28]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_40839,plain,
% 11.82/1.99      ( ~ r1_tarski(X0,sK3) | ~ r1_tarski(sK3,X0) | r2_hidden(sK2,X0) ),
% 11.82/1.99      inference(resolution,[status(thm)],[c_12994,c_1532]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_7,plain,
% 11.82/1.99      ( r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
% 11.82/1.99      inference(cnf_transformation,[],[f96]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_41389,plain,
% 11.82/1.99      ( ~ r1_tarski(k3_tarski(k2_tarski(sK3,X0)),sK3)
% 11.82/1.99      | r2_hidden(sK2,k3_tarski(k2_tarski(sK3,X0))) ),
% 11.82/1.99      inference(resolution,[status(thm)],[c_40839,c_7]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_1256,plain,
% 11.82/1.99      ( m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK1,sK2))) = iProver_top ),
% 11.82/1.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_1253,plain,
% 11.82/1.99      ( m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK1,X1))) != iProver_top
% 11.82/1.99      | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
% 11.82/1.99      | r2_hidden(X1,X0) = iProver_top ),
% 11.82/1.99      inference(predicate_to_equality,[status(thm)],[c_442]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_1571,plain,
% 11.82/1.99      ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 11.82/1.99      | r2_hidden(sK2,sK3) = iProver_top ),
% 11.82/1.99      inference(superposition,[status(thm)],[c_1256,c_1253]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_35,plain,
% 11.82/1.99      ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
% 11.82/1.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_1500,plain,
% 11.82/1.99      ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 11.82/1.99      | r2_hidden(sK2,sK3) = iProver_top ),
% 11.82/1.99      inference(predicate_to_equality,[status(thm)],[c_1499]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_1648,plain,
% 11.82/1.99      ( r2_hidden(sK2,sK3) = iProver_top ),
% 11.82/1.99      inference(global_propositional_subsumption,
% 11.82/1.99                [status(thm)],
% 11.82/1.99                [c_1571,c_35,c_1500]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_9,plain,
% 11.82/1.99      ( ~ r2_hidden(X0,X1) | k3_tarski(k2_tarski(k2_tarski(X0,X0),X1)) = X1 ),
% 11.82/1.99      inference(cnf_transformation,[],[f98]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_1266,plain,
% 11.82/1.99      ( k3_tarski(k2_tarski(k2_tarski(X0,X0),X1)) = X1
% 11.82/1.99      | r2_hidden(X0,X1) != iProver_top ),
% 11.82/1.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_2758,plain,
% 11.82/1.99      ( k3_tarski(k2_tarski(k2_tarski(sK2,sK2),sK3)) = sK3 ),
% 11.82/1.99      inference(superposition,[status(thm)],[c_1648,c_1266]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_1268,plain,
% 11.82/1.99      ( r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) = iProver_top ),
% 11.82/1.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_5,plain,
% 11.82/1.99      ( r1_tarski(X0,X1) | ~ r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1) ),
% 11.82/1.99      inference(cnf_transformation,[],[f94]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_1270,plain,
% 11.82/1.99      ( r1_tarski(X0,X1) = iProver_top
% 11.82/1.99      | r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1) != iProver_top ),
% 11.82/1.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_2795,plain,
% 11.82/1.99      ( r1_tarski(X0,k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X2))) = iProver_top ),
% 11.82/1.99      inference(superposition,[status(thm)],[c_1268,c_1270]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_5614,plain,
% 11.82/1.99      ( r1_tarski(k2_tarski(sK2,sK2),k3_tarski(k2_tarski(sK3,X0))) = iProver_top ),
% 11.82/1.99      inference(superposition,[status(thm)],[c_2758,c_2795]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_6,plain,
% 11.82/1.99      ( ~ r1_tarski(X0,X1) | k3_tarski(k2_tarski(X0,X1)) = X1 ),
% 11.82/1.99      inference(cnf_transformation,[],[f95]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_1269,plain,
% 11.82/1.99      ( k3_tarski(k2_tarski(X0,X1)) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 11.82/1.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_7286,plain,
% 11.82/1.99      ( k3_tarski(k2_tarski(k2_tarski(sK2,sK2),k3_tarski(k2_tarski(sK3,X0)))) = k3_tarski(k2_tarski(sK3,X0)) ),
% 11.82/1.99      inference(superposition,[status(thm)],[c_5614,c_1269]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_2651,plain,
% 11.82/1.99      ( k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(X0,X1)) ),
% 11.82/1.99      inference(superposition,[status(thm)],[c_1268,c_1269]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_8,plain,
% 11.82/1.99      ( ~ r1_tarski(k3_tarski(k2_tarski(k2_tarski(X0,X0),X1)),X1)
% 11.82/1.99      | r2_hidden(X0,X1) ),
% 11.82/1.99      inference(cnf_transformation,[],[f97]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_1267,plain,
% 11.82/1.99      ( r1_tarski(k3_tarski(k2_tarski(k2_tarski(X0,X0),X1)),X1) != iProver_top
% 11.82/1.99      | r2_hidden(X0,X1) = iProver_top ),
% 11.82/1.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_5658,plain,
% 11.82/1.99      ( r1_tarski(k3_tarski(k2_tarski(k2_tarski(X0,X0),X1)),k3_tarski(k2_tarski(k2_tarski(X0,X0),X1))) != iProver_top
% 11.82/1.99      | r2_hidden(X0,k3_tarski(k2_tarski(k2_tarski(X0,X0),X1))) = iProver_top ),
% 11.82/1.99      inference(superposition,[status(thm)],[c_2651,c_1267]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_4,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f103]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_6779,plain,
% 11.82/1.99      ( r1_tarski(k3_tarski(X0),k3_tarski(X0)) ),
% 11.82/1.99      inference(instantiation,[status(thm)],[c_4]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_10464,plain,
% 11.82/1.99      ( r1_tarski(k3_tarski(k2_tarski(k2_tarski(X0,X0),X1)),k3_tarski(k2_tarski(k2_tarski(X0,X0),X1))) ),
% 11.82/1.99      inference(instantiation,[status(thm)],[c_6779]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_10466,plain,
% 11.82/1.99      ( r1_tarski(k3_tarski(k2_tarski(k2_tarski(X0,X0),X1)),k3_tarski(k2_tarski(k2_tarski(X0,X0),X1))) = iProver_top ),
% 11.82/1.99      inference(predicate_to_equality,[status(thm)],[c_10464]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_41596,plain,
% 11.82/1.99      ( r2_hidden(X0,k3_tarski(k2_tarski(k2_tarski(X0,X0),X1))) = iProver_top ),
% 11.82/1.99      inference(global_propositional_subsumption,
% 11.82/1.99                [status(thm)],
% 11.82/1.99                [c_5658,c_10466]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_41618,plain,
% 11.82/1.99      ( r2_hidden(sK2,k3_tarski(k2_tarski(sK3,X0))) = iProver_top ),
% 11.82/1.99      inference(superposition,[status(thm)],[c_7286,c_41596]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_41666,plain,
% 11.82/1.99      ( r2_hidden(sK2,k3_tarski(k2_tarski(sK3,X0))) ),
% 11.82/1.99      inference(predicate_to_equality_rev,[status(thm)],[c_41618]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_42843,plain,
% 11.82/1.99      ( r2_hidden(sK2,k3_tarski(k2_tarski(sK3,X0))) ),
% 11.82/1.99      inference(global_propositional_subsumption,
% 11.82/1.99                [status(thm)],
% 11.82/1.99                [c_41389,c_41666]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_25,negated_conjecture,
% 11.82/1.99      ( ~ m1_subset_1(k3_tarski(k2_tarski(sK3,sK4)),u1_struct_0(k9_yellow_6(sK1,sK2))) ),
% 11.82/1.99      inference(cnf_transformation,[],[f101]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_16,plain,
% 11.82/1.99      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 11.82/1.99      inference(cnf_transformation,[],[f78]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_2188,plain,
% 11.82/1.99      ( ~ r2_hidden(k3_tarski(k2_tarski(sK3,sK4)),u1_struct_0(k9_yellow_6(sK1,sK2))) ),
% 11.82/1.99      inference(resolution,[status(thm)],[c_25,c_16]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_21,plain,
% 11.82/1.99      ( ~ v3_pre_topc(X0,X1)
% 11.82/1.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 11.82/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.82/1.99      | ~ r2_hidden(X2,X0)
% 11.82/1.99      | r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
% 11.82/1.99      | v2_struct_0(X1)
% 11.82/1.99      | ~ v2_pre_topc(X1)
% 11.82/1.99      | ~ l1_pre_topc(X1) ),
% 11.82/1.99      inference(cnf_transformation,[],[f85]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_506,plain,
% 11.82/1.99      ( ~ v3_pre_topc(X0,X1)
% 11.82/1.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 11.82/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.82/1.99      | ~ r2_hidden(X2,X0)
% 11.82/1.99      | r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
% 11.82/1.99      | ~ v2_pre_topc(X1)
% 11.82/1.99      | ~ l1_pre_topc(X1)
% 11.82/1.99      | sK1 != X1 ),
% 11.82/1.99      inference(resolution_lifted,[status(thm)],[c_21,c_31]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_507,plain,
% 11.82/1.99      ( ~ v3_pre_topc(X0,sK1)
% 11.82/1.99      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 11.82/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 11.82/1.99      | ~ r2_hidden(X1,X0)
% 11.82/1.99      | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK1,X1)))
% 11.82/1.99      | ~ v2_pre_topc(sK1)
% 11.82/1.99      | ~ l1_pre_topc(sK1) ),
% 11.82/1.99      inference(unflattening,[status(thm)],[c_506]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_511,plain,
% 11.82/1.99      ( ~ v3_pre_topc(X0,sK1)
% 11.82/1.99      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 11.82/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 11.82/1.99      | ~ r2_hidden(X1,X0)
% 11.82/1.99      | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK1,X1))) ),
% 11.82/1.99      inference(global_propositional_subsumption,
% 11.82/1.99                [status(thm)],
% 11.82/1.99                [c_507,c_30,c_29]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_17,plain,
% 11.82/1.99      ( m1_subset_1(X0,X1)
% 11.82/1.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 11.82/1.99      | ~ r2_hidden(X0,X2) ),
% 11.82/1.99      inference(cnf_transformation,[],[f79]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_527,plain,
% 11.82/1.99      ( ~ v3_pre_topc(X0,sK1)
% 11.82/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 11.82/1.99      | ~ r2_hidden(X1,X0)
% 11.82/1.99      | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK1,X1))) ),
% 11.82/1.99      inference(forward_subsumption_resolution,[status(thm)],[c_511,c_17]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_3351,plain,
% 11.82/1.99      ( ~ v3_pre_topc(k3_tarski(k2_tarski(sK3,sK4)),sK1)
% 11.82/1.99      | ~ m1_subset_1(k3_tarski(k2_tarski(sK3,sK4)),k1_zfmisc_1(u1_struct_0(sK1)))
% 11.82/1.99      | ~ r2_hidden(sK2,k3_tarski(k2_tarski(sK3,sK4))) ),
% 11.82/1.99      inference(resolution,[status(thm)],[c_2188,c_527]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_26,negated_conjecture,
% 11.82/1.99      ( m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK1,sK2))) ),
% 11.82/1.99      inference(cnf_transformation,[],[f92]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_1497,plain,
% 11.82/1.99      ( ~ m1_subset_1(sK2,u1_struct_0(sK1)) | r2_hidden(sK2,sK4) ),
% 11.82/1.99      inference(resolution,[status(thm)],[c_442,c_26]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_379,plain,
% 11.82/1.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 11.82/1.99      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
% 11.82/1.99      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 11.82/1.99      | v2_struct_0(X1)
% 11.82/1.99      | ~ v2_pre_topc(X1)
% 11.82/1.99      | ~ l1_pre_topc(X1) ),
% 11.82/1.99      inference(resolution,[status(thm)],[c_24,c_19]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_416,plain,
% 11.82/1.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 11.82/1.99      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
% 11.82/1.99      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 11.82/1.99      | ~ v2_pre_topc(X1)
% 11.82/1.99      | ~ l1_pre_topc(X1)
% 11.82/1.99      | sK1 != X1 ),
% 11.82/1.99      inference(resolution_lifted,[status(thm)],[c_379,c_31]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_417,plain,
% 11.82/1.99      ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK1,X1)))
% 11.82/1.99      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 11.82/1.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 11.82/1.99      | ~ v2_pre_topc(sK1)
% 11.82/1.99      | ~ l1_pre_topc(sK1) ),
% 11.82/1.99      inference(unflattening,[status(thm)],[c_416]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_421,plain,
% 11.82/1.99      ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK1,X1)))
% 11.82/1.99      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 11.82/1.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 11.82/1.99      inference(global_propositional_subsumption,
% 11.82/1.99                [status(thm)],
% 11.82/1.99                [c_417,c_30,c_29]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_1596,plain,
% 11.82/1.99      ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 11.82/1.99      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 11.82/1.99      inference(resolution,[status(thm)],[c_421,c_26]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_1598,plain,
% 11.82/1.99      ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 11.82/1.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 11.82/1.99      inference(resolution,[status(thm)],[c_421,c_27]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_1,plain,
% 11.82/1.99      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 11.82/1.99      inference(cnf_transformation,[],[f60]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_1803,plain,
% 11.82/1.99      ( ~ r2_hidden(sK2,sK4) | ~ v1_xboole_0(sK4) ),
% 11.82/1.99      inference(instantiation,[status(thm)],[c_1]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_13,plain,
% 11.82/1.99      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 11.82/1.99      inference(cnf_transformation,[],[f72]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_2675,plain,
% 11.82/1.99      ( r2_hidden(sK4,u1_struct_0(k9_yellow_6(sK1,sK2)))
% 11.82/1.99      | v1_xboole_0(u1_struct_0(k9_yellow_6(sK1,sK2))) ),
% 11.82/1.99      inference(resolution,[status(thm)],[c_13,c_26]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_2099,plain,
% 11.82/1.99      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 11.82/1.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 11.82/1.99      | ~ r2_hidden(X1,u1_struct_0(k9_yellow_6(sK1,X0))) ),
% 11.82/1.99      inference(resolution,[status(thm)],[c_16,c_421]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_22,plain,
% 11.82/1.99      ( v3_pre_topc(X0,X1)
% 11.82/1.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 11.82/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.82/1.99      | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
% 11.82/1.99      | v2_struct_0(X1)
% 11.82/1.99      | ~ v2_pre_topc(X1)
% 11.82/1.99      | ~ l1_pre_topc(X1) ),
% 11.82/1.99      inference(cnf_transformation,[],[f84]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_482,plain,
% 11.82/1.99      ( v3_pre_topc(X0,X1)
% 11.82/1.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 11.82/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.82/1.99      | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
% 11.82/1.99      | ~ v2_pre_topc(X1)
% 11.82/1.99      | ~ l1_pre_topc(X1)
% 11.82/1.99      | sK1 != X1 ),
% 11.82/1.99      inference(resolution_lifted,[status(thm)],[c_22,c_31]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_483,plain,
% 11.82/1.99      ( v3_pre_topc(X0,sK1)
% 11.82/1.99      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 11.82/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 11.82/1.99      | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(sK1,X1)))
% 11.82/1.99      | ~ v2_pre_topc(sK1)
% 11.82/1.99      | ~ l1_pre_topc(sK1) ),
% 11.82/1.99      inference(unflattening,[status(thm)],[c_482]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_487,plain,
% 11.82/1.99      ( v3_pre_topc(X0,sK1)
% 11.82/1.99      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 11.82/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 11.82/1.99      | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(sK1,X1))) ),
% 11.82/1.99      inference(global_propositional_subsumption,
% 11.82/1.99                [status(thm)],
% 11.82/1.99                [c_483,c_30,c_29]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_2270,plain,
% 11.82/1.99      ( v3_pre_topc(X0,sK1)
% 11.82/1.99      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 11.82/1.99      | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(sK1,X1))) ),
% 11.82/1.99      inference(backward_subsumption_resolution,[status(thm)],[c_2099,c_487]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_2819,plain,
% 11.82/1.99      ( v3_pre_topc(sK4,sK1)
% 11.82/1.99      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 11.82/1.99      | v1_xboole_0(u1_struct_0(k9_yellow_6(sK1,sK2))) ),
% 11.82/1.99      inference(resolution,[status(thm)],[c_2675,c_2270]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_2677,plain,
% 11.82/1.99      ( r2_hidden(sK3,u1_struct_0(k9_yellow_6(sK1,sK2)))
% 11.82/1.99      | v1_xboole_0(u1_struct_0(k9_yellow_6(sK1,sK2))) ),
% 11.82/1.99      inference(resolution,[status(thm)],[c_13,c_27]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_2955,plain,
% 11.82/1.99      ( v3_pre_topc(sK3,sK1)
% 11.82/1.99      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 11.82/1.99      | v1_xboole_0(u1_struct_0(k9_yellow_6(sK1,sK2))) ),
% 11.82/1.99      inference(resolution,[status(thm)],[c_2677,c_2270]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_11,plain,
% 11.82/1.99      ( ~ m1_subset_1(X0,X1) | ~ v1_xboole_0(X1) | v1_xboole_0(X0) ),
% 11.82/1.99      inference(cnf_transformation,[],[f74]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_2205,plain,
% 11.82/1.99      ( ~ m1_subset_1(sK4,X0) | ~ v1_xboole_0(X0) | v1_xboole_0(sK4) ),
% 11.82/1.99      inference(instantiation,[status(thm)],[c_11]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_3020,plain,
% 11.82/1.99      ( ~ m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK1,sK2)))
% 11.82/1.99      | ~ v1_xboole_0(u1_struct_0(k9_yellow_6(sK1,sK2)))
% 11.82/1.99      | v1_xboole_0(sK4) ),
% 11.82/1.99      inference(instantiation,[status(thm)],[c_2205]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_18,plain,
% 11.82/1.99      ( ~ v3_pre_topc(X0,X1)
% 11.82/1.99      | ~ v3_pre_topc(X2,X1)
% 11.82/1.99      | v3_pre_topc(k3_tarski(k2_tarski(X2,X0)),X1)
% 11.82/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.82/1.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 11.82/1.99      | ~ v2_pre_topc(X1)
% 11.82/1.99      | ~ l1_pre_topc(X1) ),
% 11.82/1.99      inference(cnf_transformation,[],[f100]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_558,plain,
% 11.82/1.99      ( ~ v3_pre_topc(X0,X1)
% 11.82/1.99      | ~ v3_pre_topc(X2,X1)
% 11.82/1.99      | v3_pre_topc(k3_tarski(k2_tarski(X2,X0)),X1)
% 11.82/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.82/1.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 11.82/1.99      | ~ v2_pre_topc(X1)
% 11.82/1.99      | sK1 != X1 ),
% 11.82/1.99      inference(resolution_lifted,[status(thm)],[c_18,c_29]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_559,plain,
% 11.82/1.99      ( ~ v3_pre_topc(X0,sK1)
% 11.82/1.99      | ~ v3_pre_topc(X1,sK1)
% 11.82/1.99      | v3_pre_topc(k3_tarski(k2_tarski(X1,X0)),sK1)
% 11.82/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 11.82/1.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 11.82/1.99      | ~ v2_pre_topc(sK1) ),
% 11.82/1.99      inference(unflattening,[status(thm)],[c_558]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_563,plain,
% 11.82/1.99      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 11.82/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 11.82/1.99      | v3_pre_topc(k3_tarski(k2_tarski(X1,X0)),sK1)
% 11.82/1.99      | ~ v3_pre_topc(X1,sK1)
% 11.82/1.99      | ~ v3_pre_topc(X0,sK1) ),
% 11.82/1.99      inference(global_propositional_subsumption,[status(thm)],[c_559,c_30]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_564,plain,
% 11.82/1.99      ( ~ v3_pre_topc(X0,sK1)
% 11.82/1.99      | ~ v3_pre_topc(X1,sK1)
% 11.82/1.99      | v3_pre_topc(k3_tarski(k2_tarski(X1,X0)),sK1)
% 11.82/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 11.82/1.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 11.82/1.99      inference(renaming,[status(thm)],[c_563]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_1249,plain,
% 11.82/1.99      ( v3_pre_topc(X0,sK1) != iProver_top
% 11.82/1.99      | v3_pre_topc(X1,sK1) != iProver_top
% 11.82/1.99      | v3_pre_topc(k3_tarski(k2_tarski(X1,X0)),sK1) = iProver_top
% 11.82/1.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 11.82/1.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 11.82/1.99      inference(predicate_to_equality,[status(thm)],[c_564]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_1250,plain,
% 11.82/1.99      ( v3_pre_topc(X0,sK1) != iProver_top
% 11.82/1.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 11.82/1.99      | r2_hidden(X1,X0) != iProver_top
% 11.82/1.99      | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK1,X1))) = iProver_top ),
% 11.82/1.99      inference(predicate_to_equality,[status(thm)],[c_527]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_1260,plain,
% 11.82/1.99      ( m1_subset_1(X0,X1) = iProver_top | r2_hidden(X0,X1) != iProver_top ),
% 11.82/1.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_2250,plain,
% 11.82/1.99      ( v3_pre_topc(X0,sK1) != iProver_top
% 11.82/1.99      | m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK1,X1))) = iProver_top
% 11.82/1.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 11.82/1.99      | r2_hidden(X1,X0) != iProver_top ),
% 11.82/1.99      inference(superposition,[status(thm)],[c_1250,c_1260]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_1258,plain,
% 11.82/1.99      ( m1_subset_1(k3_tarski(k2_tarski(sK3,sK4)),u1_struct_0(k9_yellow_6(sK1,sK2))) != iProver_top ),
% 11.82/1.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_5377,plain,
% 11.82/1.99      ( v3_pre_topc(k3_tarski(k2_tarski(sK3,sK4)),sK1) != iProver_top
% 11.82/1.99      | m1_subset_1(k3_tarski(k2_tarski(sK3,sK4)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 11.82/1.99      | r2_hidden(sK2,k3_tarski(k2_tarski(sK3,sK4))) != iProver_top ),
% 11.82/1.99      inference(superposition,[status(thm)],[c_2250,c_1258]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_1597,plain,
% 11.82/1.99      ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 11.82/1.99      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 11.82/1.99      inference(predicate_to_equality,[status(thm)],[c_1596]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_1599,plain,
% 11.82/1.99      ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 11.82/1.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 11.82/1.99      inference(predicate_to_equality,[status(thm)],[c_1598]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_3352,plain,
% 11.82/1.99      ( v3_pre_topc(k3_tarski(k2_tarski(sK3,sK4)),sK1) != iProver_top
% 11.82/1.99      | m1_subset_1(k3_tarski(k2_tarski(sK3,sK4)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 11.82/1.99      | r2_hidden(sK2,k3_tarski(k2_tarski(sK3,sK4))) != iProver_top ),
% 11.82/1.99      inference(predicate_to_equality,[status(thm)],[c_3351]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_1257,plain,
% 11.82/1.99      ( m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK1,sK2))) = iProver_top ),
% 11.82/1.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_1254,plain,
% 11.82/1.99      ( m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK1,X1))) != iProver_top
% 11.82/1.99      | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
% 11.82/1.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 11.82/1.99      inference(predicate_to_equality,[status(thm)],[c_421]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_1657,plain,
% 11.82/1.99      ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 11.82/1.99      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 11.82/1.99      inference(superposition,[status(thm)],[c_1257,c_1254]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_1997,plain,
% 11.82/1.99      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 11.82/1.99      inference(global_propositional_subsumption,
% 11.82/1.99                [status(thm)],
% 11.82/1.99                [c_1657,c_35,c_1597]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_1658,plain,
% 11.82/1.99      ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 11.82/1.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 11.82/1.99      inference(superposition,[status(thm)],[c_1256,c_1254]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_2060,plain,
% 11.82/1.99      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 11.82/1.99      inference(global_propositional_subsumption,
% 11.82/1.99                [status(thm)],
% 11.82/1.99                [c_1658,c_35,c_1599]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_15,plain,
% 11.82/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.82/1.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 11.82/1.99      | k4_subset_1(X1,X2,X0) = k3_tarski(k2_tarski(X2,X0)) ),
% 11.82/1.99      inference(cnf_transformation,[],[f99]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_1261,plain,
% 11.82/1.99      ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
% 11.82/1.99      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 11.82/1.99      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 11.82/1.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_3465,plain,
% 11.82/1.99      ( k4_subset_1(u1_struct_0(sK1),sK3,X0) = k3_tarski(k2_tarski(sK3,X0))
% 11.82/1.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 11.82/1.99      inference(superposition,[status(thm)],[c_2060,c_1261]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_5248,plain,
% 11.82/1.99      ( k4_subset_1(u1_struct_0(sK1),sK3,sK4) = k3_tarski(k2_tarski(sK3,sK4)) ),
% 11.82/1.99      inference(superposition,[status(thm)],[c_1997,c_3465]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_14,plain,
% 11.82/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.82/1.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 11.82/1.99      | m1_subset_1(k4_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 11.82/1.99      inference(cnf_transformation,[],[f76]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_1262,plain,
% 11.82/1.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 11.82/1.99      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 11.82/1.99      | m1_subset_1(k4_subset_1(X1,X0,X2),k1_zfmisc_1(X1)) = iProver_top ),
% 11.82/1.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_5271,plain,
% 11.82/1.99      ( m1_subset_1(k3_tarski(k2_tarski(sK3,sK4)),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 11.82/1.99      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 11.82/1.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 11.82/1.99      inference(superposition,[status(thm)],[c_5248,c_1262]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_5785,plain,
% 11.82/1.99      ( v3_pre_topc(k3_tarski(k2_tarski(sK3,sK4)),sK1) != iProver_top
% 11.82/1.99      | r2_hidden(sK2,k3_tarski(k2_tarski(sK3,sK4))) != iProver_top ),
% 11.82/1.99      inference(global_propositional_subsumption,
% 11.82/1.99                [status(thm)],
% 11.82/1.99                [c_5377,c_35,c_1597,c_1599,c_3352,c_5271]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_5791,plain,
% 11.82/1.99      ( v3_pre_topc(sK4,sK1) != iProver_top
% 11.82/1.99      | v3_pre_topc(sK3,sK1) != iProver_top
% 11.82/1.99      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 11.82/1.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 11.82/1.99      | r2_hidden(sK2,k3_tarski(k2_tarski(sK3,sK4))) != iProver_top ),
% 11.82/1.99      inference(superposition,[status(thm)],[c_1249,c_5785]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_5792,plain,
% 11.82/1.99      ( ~ v3_pre_topc(sK4,sK1)
% 11.82/1.99      | ~ v3_pre_topc(sK3,sK1)
% 11.82/1.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
% 11.82/1.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 11.82/1.99      | ~ r2_hidden(sK2,k3_tarski(k2_tarski(sK3,sK4))) ),
% 11.82/1.99      inference(predicate_to_equality_rev,[status(thm)],[c_5791]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_6734,plain,
% 11.82/1.99      ( ~ r2_hidden(sK2,k3_tarski(k2_tarski(sK3,sK4))) ),
% 11.82/1.99      inference(global_propositional_subsumption,
% 11.82/1.99                [status(thm)],
% 11.82/1.99                [c_3351,c_28,c_26,c_1497,c_1596,c_1598,c_1803,c_2819,c_2955,
% 11.82/1.99                 c_3020,c_5792]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_42854,plain,
% 11.82/1.99      ( $false ),
% 11.82/1.99      inference(backward_subsumption_resolution,[status(thm)],[c_42843,c_6734]) ).
% 11.82/1.99  
% 11.82/1.99  
% 11.82/1.99  % SZS output end CNFRefutation for theBenchmark.p
% 11.82/1.99  
% 11.82/1.99  ------                               Statistics
% 11.82/1.99  
% 11.82/1.99  ------ Selected
% 11.82/1.99  
% 11.82/1.99  total_time:                             1.232
% 11.82/1.99  
%------------------------------------------------------------------------------
