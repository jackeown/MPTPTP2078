%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:28:50 EST 2020

% Result     : Theorem 3.45s
% Output     : CNFRefutation 3.45s
% Verified   : 
% Statistics : Number of formulae       :  206 ( 956 expanded)
%              Number of clauses        :  123 ( 252 expanded)
%              Number of leaves         :   21 ( 310 expanded)
%              Depth                    :   19
%              Number of atoms          :  771 (5317 expanded)
%              Number of equality atoms :  127 ( 162 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f56,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f45])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k2_tarski(X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f57,f58])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f55,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

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
    inference(nnf_transformation,[],[f36])).

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

fof(f76,plain,(
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

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))
          & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
     => ( ~ m1_subset_1(k2_xboole_0(X2,sK4),u1_struct_0(k9_yellow_6(X0,X1)))
        & m1_subset_1(sK4,u1_struct_0(k9_yellow_6(X0,X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
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

fof(f51,plain,(
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

fof(f50,plain,
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

fof(f54,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK3,sK4),u1_struct_0(k9_yellow_6(sK1,sK2)))
    & m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK1,sK2)))
    & m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK1,sK2)))
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f40,f53,f52,f51,f50])).

fof(f78,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f79,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f80,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f84,plain,(
    ~ m1_subset_1(k2_xboole_0(sK3,sK4),u1_struct_0(k9_yellow_6(sK1,sK2))) ),
    inference(cnf_transformation,[],[f54])).

fof(f88,plain,(
    ~ m1_subset_1(k3_tarski(k2_tarski(sK3,sK4)),u1_struct_0(k9_yellow_6(sK1,sK2))) ),
    inference(definition_unfolding,[],[f84,f58])).

fof(f81,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f54])).

fof(f82,plain,(
    m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK1,sK2))) ),
    inference(cnf_transformation,[],[f54])).

fof(f83,plain,(
    m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK1,sK2))) ),
    inference(cnf_transformation,[],[f54])).

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

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

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

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(X2,X0)
      | ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f13,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ m1_connsp_2(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f22])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k2_tarski(X1,X2)) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f67,f58])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f20])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_pre_topc(X2,X0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_xboole_0(X1,X2),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v3_pre_topc(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v3_pre_topc(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(k3_tarski(k2_tarski(X1,X2)),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(definition_unfolding,[],[f71,f58])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_733,plain,
    ( r2_hidden(sK0(X0_48),X0_48)
    | v1_xboole_0(X0_48) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1179,plain,
    ( r2_hidden(sK0(X0_48),X0_48) = iProver_top
    | v1_xboole_0(X0_48) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_733])).

cnf(c_3,plain,
    ( r1_tarski(k2_tarski(X0,X1),X2)
    | ~ r2_hidden(X0,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_730,plain,
    ( r1_tarski(k2_tarski(X0_48,X1_48),X2_48)
    | ~ r2_hidden(X0_48,X2_48)
    | ~ r2_hidden(X1_48,X2_48) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1182,plain,
    ( r1_tarski(k2_tarski(X0_48,X1_48),X2_48) = iProver_top
    | r2_hidden(X0_48,X2_48) != iProver_top
    | r2_hidden(X1_48,X2_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_730])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k3_tarski(k2_tarski(X2,X1))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_731,plain,
    ( ~ r1_tarski(X0_50,X0_48)
    | r1_tarski(X0_50,k3_tarski(k2_tarski(X1_48,X0_48))) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1181,plain,
    ( r1_tarski(X0_50,X0_48) != iProver_top
    | r1_tarski(X0_50,k3_tarski(k2_tarski(X1_48,X0_48))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_731])).

cnf(c_4,plain,
    ( ~ r1_tarski(k2_tarski(X0,X1),X2)
    | r2_hidden(X1,X2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_729,plain,
    ( ~ r1_tarski(k2_tarski(X0_48,X1_48),X2_48)
    | r2_hidden(X1_48,X2_48) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1183,plain,
    ( r1_tarski(k2_tarski(X0_48,X1_48),X2_48) != iProver_top
    | r2_hidden(X1_48,X2_48) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_729])).

cnf(c_1896,plain,
    ( r1_tarski(k2_tarski(X0_48,X1_48),X2_48) != iProver_top
    | r2_hidden(X1_48,k3_tarski(k2_tarski(X3_48,X2_48))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1181,c_1183])).

cnf(c_4172,plain,
    ( r2_hidden(X0_48,X1_48) != iProver_top
    | r2_hidden(X2_48,X1_48) != iProver_top
    | r2_hidden(X2_48,k3_tarski(k2_tarski(X3_48,X1_48))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1182,c_1896])).

cnf(c_14096,plain,
    ( r2_hidden(X0_48,X1_48) != iProver_top
    | r2_hidden(X0_48,k3_tarski(k2_tarski(X2_48,X1_48))) = iProver_top
    | v1_xboole_0(X1_48) = iProver_top ),
    inference(superposition,[status(thm)],[c_1179,c_4172])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_732,plain,
    ( ~ r2_hidden(X0_48,X1_48)
    | ~ v1_xboole_0(X1_48) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_764,plain,
    ( r2_hidden(X0_48,X1_48) != iProver_top
    | v1_xboole_0(X1_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_732])).

cnf(c_14410,plain,
    ( r2_hidden(X0_48,k3_tarski(k2_tarski(X2_48,X1_48))) = iProver_top
    | r2_hidden(X0_48,X1_48) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14096,c_764])).

cnf(c_14411,plain,
    ( r2_hidden(X0_48,X1_48) != iProver_top
    | r2_hidden(X0_48,k3_tarski(k2_tarski(X2_48,X1_48))) = iProver_top ),
    inference(renaming,[status(thm)],[c_14410])).

cnf(c_18,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_470,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_28])).

cnf(c_471,plain,
    ( ~ v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X1,X0)
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK1,X1)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_470])).

cnf(c_27,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_26,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_475,plain,
    ( ~ v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X1,X0)
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK1,X1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_471,c_27,c_26])).

cnf(c_14,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_491,plain,
    ( ~ v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X1,X0)
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK1,X1))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_475,c_14])).

cnf(c_712,plain,
    ( ~ v3_pre_topc(X0_48,sK1)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X1_48,X0_48)
    | r2_hidden(X0_48,u1_struct_0(k9_yellow_6(sK1,X1_48))) ),
    inference(subtyping,[status(esa)],[c_491])).

cnf(c_1200,plain,
    ( v3_pre_topc(X0_48,sK1) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(X1_48,X0_48) != iProver_top
    | r2_hidden(X0_48,u1_struct_0(k9_yellow_6(sK1,X1_48))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_712])).

cnf(c_12,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_722,plain,
    ( m1_subset_1(X0_48,X1_48)
    | ~ r2_hidden(X0_48,X1_48) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1190,plain,
    ( m1_subset_1(X0_48,X1_48) = iProver_top
    | r2_hidden(X0_48,X1_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_722])).

cnf(c_4053,plain,
    ( v3_pre_topc(X0_48,sK1) != iProver_top
    | m1_subset_1(X0_48,u1_struct_0(k9_yellow_6(sK1,X1_48))) = iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(X1_48,X0_48) != iProver_top ),
    inference(superposition,[status(thm)],[c_1200,c_1190])).

cnf(c_22,negated_conjecture,
    ( ~ m1_subset_1(k3_tarski(k2_tarski(sK3,sK4)),u1_struct_0(k9_yellow_6(sK1,sK2))) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_720,negated_conjecture,
    ( ~ m1_subset_1(k3_tarski(k2_tarski(sK3,sK4)),u1_struct_0(k9_yellow_6(sK1,sK2))) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1192,plain,
    ( m1_subset_1(k3_tarski(k2_tarski(sK3,sK4)),u1_struct_0(k9_yellow_6(sK1,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_720])).

cnf(c_7552,plain,
    ( v3_pre_topc(k3_tarski(k2_tarski(sK3,sK4)),sK1) != iProver_top
    | m1_subset_1(k3_tarski(k2_tarski(sK3,sK4)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(sK2,k3_tarski(k2_tarski(sK3,sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4053,c_1192])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_32,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK1,sK2))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_33,plain,
    ( m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK1,sK2))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_34,plain,
    ( m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_21,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(X1,X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_16,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_343,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(resolution,[status(thm)],[c_21,c_16])).

cnf(c_380,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_343,c_28])).

cnf(c_381,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK1,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_380])).

cnf(c_385,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK1,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_381,c_27,c_26])).

cnf(c_716,plain,
    ( ~ m1_subset_1(X0_48,u1_struct_0(k9_yellow_6(sK1,X1_48)))
    | ~ m1_subset_1(X1_48,u1_struct_0(sK1))
    | m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subtyping,[status(esa)],[c_385])).

cnf(c_1372,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK1,sK2)))
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_716])).

cnf(c_1373,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK1,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1372])).

cnf(c_1375,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK1,sK2)))
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_716])).

cnf(c_1376,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK1,sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1375])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_725,plain,
    ( ~ m1_subset_1(X0_48,X1_48)
    | r2_hidden(X0_48,X1_48)
    | v1_xboole_0(X1_48) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1388,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK1,sK2)))
    | r2_hidden(sK4,u1_struct_0(k9_yellow_6(sK1,sK2)))
    | v1_xboole_0(u1_struct_0(k9_yellow_6(sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_725])).

cnf(c_1389,plain,
    ( m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK1,sK2))) != iProver_top
    | r2_hidden(sK4,u1_struct_0(k9_yellow_6(sK1,sK2))) = iProver_top
    | v1_xboole_0(u1_struct_0(k9_yellow_6(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1388])).

cnf(c_1391,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK1,sK2)))
    | r2_hidden(sK3,u1_struct_0(k9_yellow_6(sK1,sK2)))
    | v1_xboole_0(u1_struct_0(k9_yellow_6(sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_725])).

cnf(c_1392,plain,
    ( m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK1,sK2))) != iProver_top
    | r2_hidden(sK3,u1_struct_0(k9_yellow_6(sK1,sK2))) = iProver_top
    | v1_xboole_0(u1_struct_0(k9_yellow_6(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1391])).

cnf(c_19,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_446,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_28])).

cnf(c_447,plain,
    ( v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(sK1,X1)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_446])).

cnf(c_451,plain,
    ( v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(sK1,X1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_447,c_27,c_26])).

cnf(c_713,plain,
    ( v3_pre_topc(X0_48,sK1)
    | ~ m1_subset_1(X1_48,u1_struct_0(sK1))
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X0_48,u1_struct_0(k9_yellow_6(sK1,X1_48))) ),
    inference(subtyping,[status(esa)],[c_451])).

cnf(c_1458,plain,
    ( v3_pre_topc(sK4,sK1)
    | ~ m1_subset_1(X0_48,u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK4,u1_struct_0(k9_yellow_6(sK1,X0_48))) ),
    inference(instantiation,[status(thm)],[c_713])).

cnf(c_1459,plain,
    ( v3_pre_topc(sK4,sK1) = iProver_top
    | m1_subset_1(X0_48,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(sK4,u1_struct_0(k9_yellow_6(sK1,X0_48))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1458])).

cnf(c_1461,plain,
    ( v3_pre_topc(sK4,sK1) = iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(sK4,u1_struct_0(k9_yellow_6(sK1,sK2))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1459])).

cnf(c_1484,plain,
    ( v3_pre_topc(sK3,sK1)
    | ~ m1_subset_1(X0_48,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK3,u1_struct_0(k9_yellow_6(sK1,X0_48))) ),
    inference(instantiation,[status(thm)],[c_713])).

cnf(c_1485,plain,
    ( v3_pre_topc(sK3,sK1) = iProver_top
    | m1_subset_1(X0_48,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(sK3,u1_struct_0(k9_yellow_6(sK1,X0_48))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1484])).

cnf(c_1487,plain,
    ( v3_pre_topc(sK3,sK1) = iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(sK3,u1_struct_0(k9_yellow_6(sK1,sK2))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1485])).

cnf(c_719,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK1,sK2))) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_1193,plain,
    ( m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_719])).

cnf(c_17,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X2,X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_164,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_connsp_2(X0,X1,X2)
    | r2_hidden(X2,X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17,c_16])).

cnf(c_165,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_164])).

cnf(c_320,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
    | r2_hidden(X0,X2)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(resolution,[status(thm)],[c_21,c_165])).

cnf(c_401,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
    | r2_hidden(X0,X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_320,c_28])).

cnf(c_402,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK1,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | r2_hidden(X1,X0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_401])).

cnf(c_406,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK1,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | r2_hidden(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_402,c_27,c_26])).

cnf(c_715,plain,
    ( ~ m1_subset_1(X0_48,u1_struct_0(k9_yellow_6(sK1,X1_48)))
    | ~ m1_subset_1(X1_48,u1_struct_0(sK1))
    | r2_hidden(X1_48,X0_48) ),
    inference(subtyping,[status(esa)],[c_406])).

cnf(c_1197,plain,
    ( m1_subset_1(X0_48,u1_struct_0(k9_yellow_6(sK1,X1_48))) != iProver_top
    | m1_subset_1(X1_48,u1_struct_0(sK1)) != iProver_top
    | r2_hidden(X1_48,X0_48) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_715])).

cnf(c_1420,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | r2_hidden(sK2,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1193,c_1197])).

cnf(c_1378,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK1,sK2)))
    | r2_hidden(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_715])).

cnf(c_1379,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK1,sK2))) != iProver_top
    | r2_hidden(sK2,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1378])).

cnf(c_1433,plain,
    ( r2_hidden(sK2,sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1420,c_32,c_34,c_1379])).

cnf(c_1180,plain,
    ( r2_hidden(X0_48,X1_48) != iProver_top
    | v1_xboole_0(X1_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_732])).

cnf(c_1796,plain,
    ( v1_xboole_0(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1433,c_1180])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_726,plain,
    ( ~ m1_subset_1(X0_48,X1_48)
    | ~ v1_xboole_0(X1_48)
    | v1_xboole_0(X0_48) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1572,plain,
    ( ~ m1_subset_1(X0_48,u1_struct_0(k9_yellow_6(sK1,sK2)))
    | v1_xboole_0(X0_48)
    | ~ v1_xboole_0(u1_struct_0(k9_yellow_6(sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_726])).

cnf(c_1847,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK1,sK2)))
    | ~ v1_xboole_0(u1_struct_0(k9_yellow_6(sK1,sK2)))
    | v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_1572])).

cnf(c_1848,plain,
    ( m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK1,sK2))) != iProver_top
    | v1_xboole_0(u1_struct_0(k9_yellow_6(sK1,sK2))) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1847])).

cnf(c_1196,plain,
    ( m1_subset_1(X0_48,u1_struct_0(k9_yellow_6(sK1,X1_48))) != iProver_top
    | m1_subset_1(X1_48,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_716])).

cnf(c_1540,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1193,c_1196])).

cnf(c_1901,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1540,c_32,c_34,c_1373])).

cnf(c_718,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK1,sK2))) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_1194,plain,
    ( m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_718])).

cnf(c_1541,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1194,c_1196])).

cnf(c_2134,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1541,c_32,c_33,c_1376])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X2,X0) = k3_tarski(k2_tarski(X2,X0)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_723,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(X1_48))
    | ~ m1_subset_1(X2_48,k1_zfmisc_1(X1_48))
    | k4_subset_1(X1_48,X2_48,X0_48) = k3_tarski(k2_tarski(X2_48,X0_48)) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1189,plain,
    ( k4_subset_1(X0_48,X1_48,X2_48) = k3_tarski(k2_tarski(X1_48,X2_48))
    | m1_subset_1(X1_48,k1_zfmisc_1(X0_48)) != iProver_top
    | m1_subset_1(X2_48,k1_zfmisc_1(X0_48)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_723])).

cnf(c_3252,plain,
    ( k4_subset_1(u1_struct_0(sK1),sK3,X0_48) = k3_tarski(k2_tarski(sK3,X0_48))
    | m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2134,c_1189])).

cnf(c_3866,plain,
    ( k4_subset_1(u1_struct_0(sK1),sK3,sK4) = k3_tarski(k2_tarski(sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_1901,c_3252])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | m1_subset_1(k4_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_724,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(X1_48))
    | ~ m1_subset_1(X2_48,k1_zfmisc_1(X1_48))
    | m1_subset_1(k4_subset_1(X1_48,X2_48,X0_48),k1_zfmisc_1(X1_48)) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1188,plain,
    ( m1_subset_1(X0_48,k1_zfmisc_1(X1_48)) != iProver_top
    | m1_subset_1(X2_48,k1_zfmisc_1(X1_48)) != iProver_top
    | m1_subset_1(k4_subset_1(X1_48,X0_48,X2_48),k1_zfmisc_1(X1_48)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_724])).

cnf(c_3888,plain,
    ( m1_subset_1(k3_tarski(k2_tarski(sK3,sK4)),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3866,c_1188])).

cnf(c_15,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ v3_pre_topc(X2,X1)
    | v3_pre_topc(k3_tarski(k2_tarski(X2,X0)),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_522,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ v3_pre_topc(X2,X1)
    | v3_pre_topc(k3_tarski(k2_tarski(X2,X0)),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_26])).

cnf(c_523,plain,
    ( ~ v3_pre_topc(X0,sK1)
    | ~ v3_pre_topc(X1,sK1)
    | v3_pre_topc(k3_tarski(k2_tarski(X1,X0)),sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_522])).

cnf(c_527,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v3_pre_topc(k3_tarski(k2_tarski(X1,X0)),sK1)
    | ~ v3_pre_topc(X1,sK1)
    | ~ v3_pre_topc(X0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_523,c_27])).

cnf(c_528,plain,
    ( ~ v3_pre_topc(X0,sK1)
    | ~ v3_pre_topc(X1,sK1)
    | v3_pre_topc(k3_tarski(k2_tarski(X1,X0)),sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(renaming,[status(thm)],[c_527])).

cnf(c_711,plain,
    ( ~ v3_pre_topc(X0_48,sK1)
    | ~ v3_pre_topc(X1_48,sK1)
    | v3_pre_topc(k3_tarski(k2_tarski(X1_48,X0_48)),sK1)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1_48,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subtyping,[status(esa)],[c_528])).

cnf(c_2252,plain,
    ( ~ v3_pre_topc(X0_48,sK1)
    | v3_pre_topc(k3_tarski(k2_tarski(X0_48,sK4)),sK1)
    | ~ v3_pre_topc(sK4,sK1)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_711])).

cnf(c_4027,plain,
    ( v3_pre_topc(k3_tarski(k2_tarski(sK3,sK4)),sK1)
    | ~ v3_pre_topc(sK4,sK1)
    | ~ v3_pre_topc(sK3,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_2252])).

cnf(c_4028,plain,
    ( v3_pre_topc(k3_tarski(k2_tarski(sK3,sK4)),sK1) = iProver_top
    | v3_pre_topc(sK4,sK1) != iProver_top
    | v3_pre_topc(sK3,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4027])).

cnf(c_7657,plain,
    ( r2_hidden(sK2,k3_tarski(k2_tarski(sK3,sK4))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7552,c_32,c_33,c_34,c_1373,c_1376,c_1389,c_1392,c_1461,c_1487,c_1796,c_1848,c_3888,c_4028])).

cnf(c_14423,plain,
    ( r2_hidden(sK2,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_14411,c_7657])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_14423,c_1379,c_34,c_32])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:48:24 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.45/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.45/0.99  
% 3.45/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.45/0.99  
% 3.45/0.99  ------  iProver source info
% 3.45/0.99  
% 3.45/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.45/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.45/0.99  git: non_committed_changes: false
% 3.45/0.99  git: last_make_outside_of_git: false
% 3.45/0.99  
% 3.45/0.99  ------ 
% 3.45/0.99  
% 3.45/0.99  ------ Input Options
% 3.45/0.99  
% 3.45/0.99  --out_options                           all
% 3.45/0.99  --tptp_safe_out                         true
% 3.45/0.99  --problem_path                          ""
% 3.45/0.99  --include_path                          ""
% 3.45/0.99  --clausifier                            res/vclausify_rel
% 3.45/0.99  --clausifier_options                    --mode clausify
% 3.45/0.99  --stdin                                 false
% 3.45/0.99  --stats_out                             all
% 3.45/0.99  
% 3.45/0.99  ------ General Options
% 3.45/0.99  
% 3.45/0.99  --fof                                   false
% 3.45/0.99  --time_out_real                         305.
% 3.45/0.99  --time_out_virtual                      -1.
% 3.45/0.99  --symbol_type_check                     false
% 3.45/0.99  --clausify_out                          false
% 3.45/0.99  --sig_cnt_out                           false
% 3.45/0.99  --trig_cnt_out                          false
% 3.45/0.99  --trig_cnt_out_tolerance                1.
% 3.45/0.99  --trig_cnt_out_sk_spl                   false
% 3.45/0.99  --abstr_cl_out                          false
% 3.45/0.99  
% 3.45/0.99  ------ Global Options
% 3.45/0.99  
% 3.45/0.99  --schedule                              default
% 3.45/0.99  --add_important_lit                     false
% 3.45/0.99  --prop_solver_per_cl                    1000
% 3.45/0.99  --min_unsat_core                        false
% 3.45/0.99  --soft_assumptions                      false
% 3.45/0.99  --soft_lemma_size                       3
% 3.45/0.99  --prop_impl_unit_size                   0
% 3.45/0.99  --prop_impl_unit                        []
% 3.45/0.99  --share_sel_clauses                     true
% 3.45/0.99  --reset_solvers                         false
% 3.45/0.99  --bc_imp_inh                            [conj_cone]
% 3.45/0.99  --conj_cone_tolerance                   3.
% 3.45/0.99  --extra_neg_conj                        none
% 3.45/0.99  --large_theory_mode                     true
% 3.45/0.99  --prolific_symb_bound                   200
% 3.45/0.99  --lt_threshold                          2000
% 3.45/0.99  --clause_weak_htbl                      true
% 3.45/0.99  --gc_record_bc_elim                     false
% 3.45/0.99  
% 3.45/0.99  ------ Preprocessing Options
% 3.45/0.99  
% 3.45/0.99  --preprocessing_flag                    true
% 3.45/0.99  --time_out_prep_mult                    0.1
% 3.45/0.99  --splitting_mode                        input
% 3.45/0.99  --splitting_grd                         true
% 3.45/0.99  --splitting_cvd                         false
% 3.45/0.99  --splitting_cvd_svl                     false
% 3.45/0.99  --splitting_nvd                         32
% 3.45/0.99  --sub_typing                            true
% 3.45/0.99  --prep_gs_sim                           true
% 3.45/0.99  --prep_unflatten                        true
% 3.45/0.99  --prep_res_sim                          true
% 3.45/0.99  --prep_upred                            true
% 3.45/0.99  --prep_sem_filter                       exhaustive
% 3.45/0.99  --prep_sem_filter_out                   false
% 3.45/0.99  --pred_elim                             true
% 3.45/0.99  --res_sim_input                         true
% 3.45/0.99  --eq_ax_congr_red                       true
% 3.45/0.99  --pure_diseq_elim                       true
% 3.45/0.99  --brand_transform                       false
% 3.45/0.99  --non_eq_to_eq                          false
% 3.45/0.99  --prep_def_merge                        true
% 3.45/0.99  --prep_def_merge_prop_impl              false
% 3.45/0.99  --prep_def_merge_mbd                    true
% 3.45/0.99  --prep_def_merge_tr_red                 false
% 3.45/0.99  --prep_def_merge_tr_cl                  false
% 3.45/0.99  --smt_preprocessing                     true
% 3.45/0.99  --smt_ac_axioms                         fast
% 3.45/0.99  --preprocessed_out                      false
% 3.45/0.99  --preprocessed_stats                    false
% 3.45/0.99  
% 3.45/0.99  ------ Abstraction refinement Options
% 3.45/0.99  
% 3.45/0.99  --abstr_ref                             []
% 3.45/0.99  --abstr_ref_prep                        false
% 3.45/0.99  --abstr_ref_until_sat                   false
% 3.45/0.99  --abstr_ref_sig_restrict                funpre
% 3.45/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.45/0.99  --abstr_ref_under                       []
% 3.45/0.99  
% 3.45/0.99  ------ SAT Options
% 3.45/0.99  
% 3.45/0.99  --sat_mode                              false
% 3.45/0.99  --sat_fm_restart_options                ""
% 3.45/0.99  --sat_gr_def                            false
% 3.45/0.99  --sat_epr_types                         true
% 3.45/0.99  --sat_non_cyclic_types                  false
% 3.45/0.99  --sat_finite_models                     false
% 3.45/0.99  --sat_fm_lemmas                         false
% 3.45/0.99  --sat_fm_prep                           false
% 3.45/0.99  --sat_fm_uc_incr                        true
% 3.45/0.99  --sat_out_model                         small
% 3.45/0.99  --sat_out_clauses                       false
% 3.45/0.99  
% 3.45/0.99  ------ QBF Options
% 3.45/0.99  
% 3.45/0.99  --qbf_mode                              false
% 3.45/0.99  --qbf_elim_univ                         false
% 3.45/0.99  --qbf_dom_inst                          none
% 3.45/0.99  --qbf_dom_pre_inst                      false
% 3.45/0.99  --qbf_sk_in                             false
% 3.45/0.99  --qbf_pred_elim                         true
% 3.45/0.99  --qbf_split                             512
% 3.45/0.99  
% 3.45/0.99  ------ BMC1 Options
% 3.45/0.99  
% 3.45/0.99  --bmc1_incremental                      false
% 3.45/0.99  --bmc1_axioms                           reachable_all
% 3.45/0.99  --bmc1_min_bound                        0
% 3.45/0.99  --bmc1_max_bound                        -1
% 3.45/0.99  --bmc1_max_bound_default                -1
% 3.45/0.99  --bmc1_symbol_reachability              true
% 3.45/0.99  --bmc1_property_lemmas                  false
% 3.45/0.99  --bmc1_k_induction                      false
% 3.45/0.99  --bmc1_non_equiv_states                 false
% 3.45/0.99  --bmc1_deadlock                         false
% 3.45/0.99  --bmc1_ucm                              false
% 3.45/0.99  --bmc1_add_unsat_core                   none
% 3.45/0.99  --bmc1_unsat_core_children              false
% 3.45/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.45/0.99  --bmc1_out_stat                         full
% 3.45/0.99  --bmc1_ground_init                      false
% 3.45/0.99  --bmc1_pre_inst_next_state              false
% 3.45/0.99  --bmc1_pre_inst_state                   false
% 3.45/0.99  --bmc1_pre_inst_reach_state             false
% 3.45/0.99  --bmc1_out_unsat_core                   false
% 3.45/0.99  --bmc1_aig_witness_out                  false
% 3.45/0.99  --bmc1_verbose                          false
% 3.45/0.99  --bmc1_dump_clauses_tptp                false
% 3.45/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.45/0.99  --bmc1_dump_file                        -
% 3.45/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.45/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.45/0.99  --bmc1_ucm_extend_mode                  1
% 3.45/0.99  --bmc1_ucm_init_mode                    2
% 3.45/0.99  --bmc1_ucm_cone_mode                    none
% 3.45/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.45/0.99  --bmc1_ucm_relax_model                  4
% 3.45/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.45/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.45/0.99  --bmc1_ucm_layered_model                none
% 3.45/0.99  --bmc1_ucm_max_lemma_size               10
% 3.45/0.99  
% 3.45/0.99  ------ AIG Options
% 3.45/0.99  
% 3.45/0.99  --aig_mode                              false
% 3.45/0.99  
% 3.45/0.99  ------ Instantiation Options
% 3.45/0.99  
% 3.45/0.99  --instantiation_flag                    true
% 3.45/0.99  --inst_sos_flag                         false
% 3.45/0.99  --inst_sos_phase                        true
% 3.45/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.45/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.45/0.99  --inst_lit_sel_side                     num_symb
% 3.45/0.99  --inst_solver_per_active                1400
% 3.45/0.99  --inst_solver_calls_frac                1.
% 3.45/0.99  --inst_passive_queue_type               priority_queues
% 3.45/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.45/0.99  --inst_passive_queues_freq              [25;2]
% 3.45/0.99  --inst_dismatching                      true
% 3.45/0.99  --inst_eager_unprocessed_to_passive     true
% 3.45/0.99  --inst_prop_sim_given                   true
% 3.45/0.99  --inst_prop_sim_new                     false
% 3.45/0.99  --inst_subs_new                         false
% 3.45/0.99  --inst_eq_res_simp                      false
% 3.45/0.99  --inst_subs_given                       false
% 3.45/0.99  --inst_orphan_elimination               true
% 3.45/0.99  --inst_learning_loop_flag               true
% 3.45/0.99  --inst_learning_start                   3000
% 3.45/0.99  --inst_learning_factor                  2
% 3.45/0.99  --inst_start_prop_sim_after_learn       3
% 3.45/0.99  --inst_sel_renew                        solver
% 3.45/0.99  --inst_lit_activity_flag                true
% 3.45/0.99  --inst_restr_to_given                   false
% 3.45/0.99  --inst_activity_threshold               500
% 3.45/0.99  --inst_out_proof                        true
% 3.45/0.99  
% 3.45/0.99  ------ Resolution Options
% 3.45/0.99  
% 3.45/0.99  --resolution_flag                       true
% 3.45/0.99  --res_lit_sel                           adaptive
% 3.45/0.99  --res_lit_sel_side                      none
% 3.45/0.99  --res_ordering                          kbo
% 3.45/0.99  --res_to_prop_solver                    active
% 3.45/0.99  --res_prop_simpl_new                    false
% 3.45/0.99  --res_prop_simpl_given                  true
% 3.45/0.99  --res_passive_queue_type                priority_queues
% 3.45/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.45/0.99  --res_passive_queues_freq               [15;5]
% 3.45/0.99  --res_forward_subs                      full
% 3.45/0.99  --res_backward_subs                     full
% 3.45/0.99  --res_forward_subs_resolution           true
% 3.45/0.99  --res_backward_subs_resolution          true
% 3.45/0.99  --res_orphan_elimination                true
% 3.45/0.99  --res_time_limit                        2.
% 3.45/0.99  --res_out_proof                         true
% 3.45/0.99  
% 3.45/0.99  ------ Superposition Options
% 3.45/0.99  
% 3.45/0.99  --superposition_flag                    true
% 3.45/0.99  --sup_passive_queue_type                priority_queues
% 3.45/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.45/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.45/0.99  --demod_completeness_check              fast
% 3.45/0.99  --demod_use_ground                      true
% 3.45/0.99  --sup_to_prop_solver                    passive
% 3.45/0.99  --sup_prop_simpl_new                    true
% 3.45/0.99  --sup_prop_simpl_given                  true
% 3.45/0.99  --sup_fun_splitting                     false
% 3.45/0.99  --sup_smt_interval                      50000
% 3.45/0.99  
% 3.45/0.99  ------ Superposition Simplification Setup
% 3.45/0.99  
% 3.45/0.99  --sup_indices_passive                   []
% 3.45/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.45/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.45/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.45/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.45/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.45/0.99  --sup_full_bw                           [BwDemod]
% 3.45/0.99  --sup_immed_triv                        [TrivRules]
% 3.45/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.45/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.45/0.99  --sup_immed_bw_main                     []
% 3.45/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.45/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.45/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.45/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.45/0.99  
% 3.45/0.99  ------ Combination Options
% 3.45/0.99  
% 3.45/0.99  --comb_res_mult                         3
% 3.45/0.99  --comb_sup_mult                         2
% 3.45/0.99  --comb_inst_mult                        10
% 3.45/0.99  
% 3.45/0.99  ------ Debug Options
% 3.45/0.99  
% 3.45/0.99  --dbg_backtrace                         false
% 3.45/0.99  --dbg_dump_prop_clauses                 false
% 3.45/0.99  --dbg_dump_prop_clauses_file            -
% 3.45/0.99  --dbg_out_stat                          false
% 3.45/0.99  ------ Parsing...
% 3.45/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.45/0.99  
% 3.45/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.45/0.99  
% 3.45/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.45/0.99  
% 3.45/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.45/0.99  ------ Proving...
% 3.45/0.99  ------ Problem Properties 
% 3.45/0.99  
% 3.45/0.99  
% 3.45/0.99  clauses                                 23
% 3.45/0.99  conjectures                             4
% 3.45/0.99  EPR                                     5
% 3.45/0.99  Horn                                    21
% 3.45/0.99  unary                                   4
% 3.45/0.99  binary                                  6
% 3.45/0.99  lits                                    60
% 3.45/0.99  lits eq                                 1
% 3.45/0.99  fd_pure                                 0
% 3.45/0.99  fd_pseudo                               0
% 3.45/0.99  fd_cond                                 0
% 3.45/0.99  fd_pseudo_cond                          0
% 3.45/0.99  AC symbols                              0
% 3.45/0.99  
% 3.45/0.99  ------ Schedule dynamic 5 is on 
% 3.45/0.99  
% 3.45/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.45/0.99  
% 3.45/0.99  
% 3.45/0.99  ------ 
% 3.45/0.99  Current options:
% 3.45/0.99  ------ 
% 3.45/0.99  
% 3.45/0.99  ------ Input Options
% 3.45/0.99  
% 3.45/0.99  --out_options                           all
% 3.45/0.99  --tptp_safe_out                         true
% 3.45/0.99  --problem_path                          ""
% 3.45/0.99  --include_path                          ""
% 3.45/0.99  --clausifier                            res/vclausify_rel
% 3.45/0.99  --clausifier_options                    --mode clausify
% 3.45/0.99  --stdin                                 false
% 3.45/0.99  --stats_out                             all
% 3.45/0.99  
% 3.45/0.99  ------ General Options
% 3.45/0.99  
% 3.45/0.99  --fof                                   false
% 3.45/0.99  --time_out_real                         305.
% 3.45/0.99  --time_out_virtual                      -1.
% 3.45/0.99  --symbol_type_check                     false
% 3.45/0.99  --clausify_out                          false
% 3.45/0.99  --sig_cnt_out                           false
% 3.45/0.99  --trig_cnt_out                          false
% 3.45/0.99  --trig_cnt_out_tolerance                1.
% 3.45/0.99  --trig_cnt_out_sk_spl                   false
% 3.45/0.99  --abstr_cl_out                          false
% 3.45/0.99  
% 3.45/0.99  ------ Global Options
% 3.45/0.99  
% 3.45/0.99  --schedule                              default
% 3.45/0.99  --add_important_lit                     false
% 3.45/0.99  --prop_solver_per_cl                    1000
% 3.45/0.99  --min_unsat_core                        false
% 3.45/0.99  --soft_assumptions                      false
% 3.45/0.99  --soft_lemma_size                       3
% 3.45/0.99  --prop_impl_unit_size                   0
% 3.45/0.99  --prop_impl_unit                        []
% 3.45/0.99  --share_sel_clauses                     true
% 3.45/0.99  --reset_solvers                         false
% 3.45/0.99  --bc_imp_inh                            [conj_cone]
% 3.45/0.99  --conj_cone_tolerance                   3.
% 3.45/0.99  --extra_neg_conj                        none
% 3.45/0.99  --large_theory_mode                     true
% 3.45/0.99  --prolific_symb_bound                   200
% 3.45/0.99  --lt_threshold                          2000
% 3.45/0.99  --clause_weak_htbl                      true
% 3.45/0.99  --gc_record_bc_elim                     false
% 3.45/0.99  
% 3.45/0.99  ------ Preprocessing Options
% 3.45/0.99  
% 3.45/0.99  --preprocessing_flag                    true
% 3.45/0.99  --time_out_prep_mult                    0.1
% 3.45/0.99  --splitting_mode                        input
% 3.45/0.99  --splitting_grd                         true
% 3.45/0.99  --splitting_cvd                         false
% 3.45/0.99  --splitting_cvd_svl                     false
% 3.45/0.99  --splitting_nvd                         32
% 3.45/0.99  --sub_typing                            true
% 3.45/0.99  --prep_gs_sim                           true
% 3.45/0.99  --prep_unflatten                        true
% 3.45/0.99  --prep_res_sim                          true
% 3.45/0.99  --prep_upred                            true
% 3.45/0.99  --prep_sem_filter                       exhaustive
% 3.45/0.99  --prep_sem_filter_out                   false
% 3.45/0.99  --pred_elim                             true
% 3.45/0.99  --res_sim_input                         true
% 3.45/0.99  --eq_ax_congr_red                       true
% 3.45/0.99  --pure_diseq_elim                       true
% 3.45/0.99  --brand_transform                       false
% 3.45/0.99  --non_eq_to_eq                          false
% 3.45/0.99  --prep_def_merge                        true
% 3.45/0.99  --prep_def_merge_prop_impl              false
% 3.45/0.99  --prep_def_merge_mbd                    true
% 3.45/0.99  --prep_def_merge_tr_red                 false
% 3.45/0.99  --prep_def_merge_tr_cl                  false
% 3.45/0.99  --smt_preprocessing                     true
% 3.45/0.99  --smt_ac_axioms                         fast
% 3.45/0.99  --preprocessed_out                      false
% 3.45/0.99  --preprocessed_stats                    false
% 3.45/0.99  
% 3.45/0.99  ------ Abstraction refinement Options
% 3.45/0.99  
% 3.45/0.99  --abstr_ref                             []
% 3.45/0.99  --abstr_ref_prep                        false
% 3.45/0.99  --abstr_ref_until_sat                   false
% 3.45/0.99  --abstr_ref_sig_restrict                funpre
% 3.45/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.45/0.99  --abstr_ref_under                       []
% 3.45/0.99  
% 3.45/0.99  ------ SAT Options
% 3.45/0.99  
% 3.45/0.99  --sat_mode                              false
% 3.45/0.99  --sat_fm_restart_options                ""
% 3.45/0.99  --sat_gr_def                            false
% 3.45/0.99  --sat_epr_types                         true
% 3.45/0.99  --sat_non_cyclic_types                  false
% 3.45/0.99  --sat_finite_models                     false
% 3.45/0.99  --sat_fm_lemmas                         false
% 3.45/0.99  --sat_fm_prep                           false
% 3.45/0.99  --sat_fm_uc_incr                        true
% 3.45/0.99  --sat_out_model                         small
% 3.45/0.99  --sat_out_clauses                       false
% 3.45/0.99  
% 3.45/0.99  ------ QBF Options
% 3.45/0.99  
% 3.45/0.99  --qbf_mode                              false
% 3.45/0.99  --qbf_elim_univ                         false
% 3.45/0.99  --qbf_dom_inst                          none
% 3.45/0.99  --qbf_dom_pre_inst                      false
% 3.45/0.99  --qbf_sk_in                             false
% 3.45/0.99  --qbf_pred_elim                         true
% 3.45/0.99  --qbf_split                             512
% 3.45/0.99  
% 3.45/0.99  ------ BMC1 Options
% 3.45/0.99  
% 3.45/0.99  --bmc1_incremental                      false
% 3.45/0.99  --bmc1_axioms                           reachable_all
% 3.45/0.99  --bmc1_min_bound                        0
% 3.45/0.99  --bmc1_max_bound                        -1
% 3.45/0.99  --bmc1_max_bound_default                -1
% 3.45/0.99  --bmc1_symbol_reachability              true
% 3.45/0.99  --bmc1_property_lemmas                  false
% 3.45/0.99  --bmc1_k_induction                      false
% 3.45/0.99  --bmc1_non_equiv_states                 false
% 3.45/0.99  --bmc1_deadlock                         false
% 3.45/0.99  --bmc1_ucm                              false
% 3.45/0.99  --bmc1_add_unsat_core                   none
% 3.45/0.99  --bmc1_unsat_core_children              false
% 3.45/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.45/0.99  --bmc1_out_stat                         full
% 3.45/0.99  --bmc1_ground_init                      false
% 3.45/0.99  --bmc1_pre_inst_next_state              false
% 3.45/0.99  --bmc1_pre_inst_state                   false
% 3.45/0.99  --bmc1_pre_inst_reach_state             false
% 3.45/0.99  --bmc1_out_unsat_core                   false
% 3.45/0.99  --bmc1_aig_witness_out                  false
% 3.45/0.99  --bmc1_verbose                          false
% 3.45/0.99  --bmc1_dump_clauses_tptp                false
% 3.45/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.45/0.99  --bmc1_dump_file                        -
% 3.45/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.45/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.45/0.99  --bmc1_ucm_extend_mode                  1
% 3.45/0.99  --bmc1_ucm_init_mode                    2
% 3.45/0.99  --bmc1_ucm_cone_mode                    none
% 3.45/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.45/0.99  --bmc1_ucm_relax_model                  4
% 3.45/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.45/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.45/0.99  --bmc1_ucm_layered_model                none
% 3.45/0.99  --bmc1_ucm_max_lemma_size               10
% 3.45/0.99  
% 3.45/0.99  ------ AIG Options
% 3.45/0.99  
% 3.45/0.99  --aig_mode                              false
% 3.45/0.99  
% 3.45/0.99  ------ Instantiation Options
% 3.45/0.99  
% 3.45/0.99  --instantiation_flag                    true
% 3.45/0.99  --inst_sos_flag                         false
% 3.45/0.99  --inst_sos_phase                        true
% 3.45/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.45/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.45/0.99  --inst_lit_sel_side                     none
% 3.45/0.99  --inst_solver_per_active                1400
% 3.45/0.99  --inst_solver_calls_frac                1.
% 3.45/0.99  --inst_passive_queue_type               priority_queues
% 3.45/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.45/0.99  --inst_passive_queues_freq              [25;2]
% 3.45/0.99  --inst_dismatching                      true
% 3.45/0.99  --inst_eager_unprocessed_to_passive     true
% 3.45/0.99  --inst_prop_sim_given                   true
% 3.45/0.99  --inst_prop_sim_new                     false
% 3.45/0.99  --inst_subs_new                         false
% 3.45/0.99  --inst_eq_res_simp                      false
% 3.45/0.99  --inst_subs_given                       false
% 3.45/0.99  --inst_orphan_elimination               true
% 3.45/0.99  --inst_learning_loop_flag               true
% 3.45/0.99  --inst_learning_start                   3000
% 3.45/0.99  --inst_learning_factor                  2
% 3.45/0.99  --inst_start_prop_sim_after_learn       3
% 3.45/0.99  --inst_sel_renew                        solver
% 3.45/0.99  --inst_lit_activity_flag                true
% 3.45/0.99  --inst_restr_to_given                   false
% 3.45/0.99  --inst_activity_threshold               500
% 3.45/0.99  --inst_out_proof                        true
% 3.45/0.99  
% 3.45/0.99  ------ Resolution Options
% 3.45/0.99  
% 3.45/0.99  --resolution_flag                       false
% 3.45/0.99  --res_lit_sel                           adaptive
% 3.45/0.99  --res_lit_sel_side                      none
% 3.45/0.99  --res_ordering                          kbo
% 3.45/0.99  --res_to_prop_solver                    active
% 3.45/0.99  --res_prop_simpl_new                    false
% 3.45/0.99  --res_prop_simpl_given                  true
% 3.45/0.99  --res_passive_queue_type                priority_queues
% 3.45/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.45/0.99  --res_passive_queues_freq               [15;5]
% 3.45/0.99  --res_forward_subs                      full
% 3.45/0.99  --res_backward_subs                     full
% 3.45/0.99  --res_forward_subs_resolution           true
% 3.45/0.99  --res_backward_subs_resolution          true
% 3.45/0.99  --res_orphan_elimination                true
% 3.45/0.99  --res_time_limit                        2.
% 3.45/0.99  --res_out_proof                         true
% 3.45/0.99  
% 3.45/0.99  ------ Superposition Options
% 3.45/0.99  
% 3.45/0.99  --superposition_flag                    true
% 3.45/0.99  --sup_passive_queue_type                priority_queues
% 3.45/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.45/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.45/0.99  --demod_completeness_check              fast
% 3.45/0.99  --demod_use_ground                      true
% 3.45/0.99  --sup_to_prop_solver                    passive
% 3.45/0.99  --sup_prop_simpl_new                    true
% 3.45/0.99  --sup_prop_simpl_given                  true
% 3.45/0.99  --sup_fun_splitting                     false
% 3.45/0.99  --sup_smt_interval                      50000
% 3.45/0.99  
% 3.45/0.99  ------ Superposition Simplification Setup
% 3.45/0.99  
% 3.45/0.99  --sup_indices_passive                   []
% 3.45/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.45/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.45/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.45/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.45/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.45/0.99  --sup_full_bw                           [BwDemod]
% 3.45/0.99  --sup_immed_triv                        [TrivRules]
% 3.45/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.45/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.45/0.99  --sup_immed_bw_main                     []
% 3.45/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.45/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.45/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.45/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.45/0.99  
% 3.45/0.99  ------ Combination Options
% 3.45/0.99  
% 3.45/0.99  --comb_res_mult                         3
% 3.45/0.99  --comb_sup_mult                         2
% 3.45/0.99  --comb_inst_mult                        10
% 3.45/0.99  
% 3.45/0.99  ------ Debug Options
% 3.45/0.99  
% 3.45/0.99  --dbg_backtrace                         false
% 3.45/0.99  --dbg_dump_prop_clauses                 false
% 3.45/0.99  --dbg_dump_prop_clauses_file            -
% 3.45/0.99  --dbg_out_stat                          false
% 3.45/0.99  
% 3.45/0.99  
% 3.45/0.99  
% 3.45/0.99  
% 3.45/0.99  ------ Proving...
% 3.45/0.99  
% 3.45/0.99  
% 3.45/0.99  % SZS status Theorem for theBenchmark.p
% 3.45/0.99  
% 3.45/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.45/0.99  
% 3.45/0.99  fof(f1,axiom,(
% 3.45/0.99    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.45/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f41,plain,(
% 3.45/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.45/0.99    inference(nnf_transformation,[],[f1])).
% 3.45/0.99  
% 3.45/0.99  fof(f42,plain,(
% 3.45/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.45/0.99    inference(rectify,[],[f41])).
% 3.45/0.99  
% 3.45/0.99  fof(f43,plain,(
% 3.45/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.45/0.99    introduced(choice_axiom,[])).
% 3.45/0.99  
% 3.45/0.99  fof(f44,plain,(
% 3.45/0.99    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.45/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f42,f43])).
% 3.45/0.99  
% 3.45/0.99  fof(f56,plain,(
% 3.45/0.99    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 3.45/0.99    inference(cnf_transformation,[],[f44])).
% 3.45/0.99  
% 3.45/0.99  fof(f4,axiom,(
% 3.45/0.99    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 3.45/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f45,plain,(
% 3.45/0.99    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 3.45/0.99    inference(nnf_transformation,[],[f4])).
% 3.45/0.99  
% 3.45/0.99  fof(f46,plain,(
% 3.45/0.99    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 3.45/0.99    inference(flattening,[],[f45])).
% 3.45/0.99  
% 3.45/0.99  fof(f61,plain,(
% 3.45/0.99    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 3.45/0.99    inference(cnf_transformation,[],[f46])).
% 3.45/0.99  
% 3.45/0.99  fof(f2,axiom,(
% 3.45/0.99    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 3.45/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f18,plain,(
% 3.45/0.99    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 3.45/0.99    inference(ennf_transformation,[],[f2])).
% 3.45/0.99  
% 3.45/0.99  fof(f57,plain,(
% 3.45/0.99    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 3.45/0.99    inference(cnf_transformation,[],[f18])).
% 3.45/0.99  
% 3.45/0.99  fof(f3,axiom,(
% 3.45/0.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.45/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f58,plain,(
% 3.45/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.45/0.99    inference(cnf_transformation,[],[f3])).
% 3.45/0.99  
% 3.45/0.99  fof(f85,plain,(
% 3.45/0.99    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X2,X1))) | ~r1_tarski(X0,X1)) )),
% 3.45/0.99    inference(definition_unfolding,[],[f57,f58])).
% 3.45/0.99  
% 3.45/0.99  fof(f60,plain,(
% 3.45/0.99    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 3.45/0.99    inference(cnf_transformation,[],[f46])).
% 3.45/0.99  
% 3.45/0.99  fof(f55,plain,(
% 3.45/0.99    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 3.45/0.99    inference(cnf_transformation,[],[f44])).
% 3.45/0.99  
% 3.45/0.99  fof(f14,axiom,(
% 3.45/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))))))),
% 3.45/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f35,plain,(
% 3.45/0.99    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.45/0.99    inference(ennf_transformation,[],[f14])).
% 3.45/0.99  
% 3.45/0.99  fof(f36,plain,(
% 3.45/0.99    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.45/0.99    inference(flattening,[],[f35])).
% 3.45/0.99  
% 3.45/0.99  fof(f48,plain,(
% 3.45/0.99    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | (~v3_pre_topc(X2,X0) | ~r2_hidden(X1,X2))) & ((v3_pre_topc(X2,X0) & r2_hidden(X1,X2)) | ~r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.45/0.99    inference(nnf_transformation,[],[f36])).
% 3.45/0.99  
% 3.45/0.99  fof(f49,plain,(
% 3.45/0.99    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~v3_pre_topc(X2,X0) | ~r2_hidden(X1,X2)) & ((v3_pre_topc(X2,X0) & r2_hidden(X1,X2)) | ~r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.45/0.99    inference(flattening,[],[f48])).
% 3.45/0.99  
% 3.45/0.99  fof(f76,plain,(
% 3.45/0.99    ( ! [X2,X0,X1] : (r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~v3_pre_topc(X2,X0) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.45/0.99    inference(cnf_transformation,[],[f49])).
% 3.45/0.99  
% 3.45/0.99  fof(f16,conjecture,(
% 3.45/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) => m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))))))),
% 3.45/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f17,negated_conjecture,(
% 3.45/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) => m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))))))),
% 3.45/0.99    inference(negated_conjecture,[],[f16])).
% 3.45/0.99  
% 3.45/0.99  fof(f39,plain,(
% 3.45/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.45/0.99    inference(ennf_transformation,[],[f17])).
% 3.45/0.99  
% 3.45/0.99  fof(f40,plain,(
% 3.45/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.45/0.99    inference(flattening,[],[f39])).
% 3.45/0.99  
% 3.45/0.99  fof(f53,plain,(
% 3.45/0.99    ( ! [X2,X0,X1] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) => (~m1_subset_1(k2_xboole_0(X2,sK4),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(sK4,u1_struct_0(k9_yellow_6(X0,X1))))) )),
% 3.45/0.99    introduced(choice_axiom,[])).
% 3.45/0.99  
% 3.45/0.99  fof(f52,plain,(
% 3.45/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) => (? [X3] : (~m1_subset_1(k2_xboole_0(sK3,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(sK3,u1_struct_0(k9_yellow_6(X0,X1))))) )),
% 3.45/0.99    introduced(choice_axiom,[])).
% 3.45/0.99  
% 3.45/0.99  fof(f51,plain,(
% 3.45/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,sK2))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,sK2)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,sK2)))) & m1_subset_1(sK2,u1_struct_0(X0)))) )),
% 3.45/0.99    introduced(choice_axiom,[])).
% 3.45/0.99  
% 3.45/0.99  fof(f50,plain,(
% 3.45/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK1,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK1,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK1,X1)))) & m1_subset_1(X1,u1_struct_0(sK1))) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 3.45/0.99    introduced(choice_axiom,[])).
% 3.45/0.99  
% 3.45/0.99  fof(f54,plain,(
% 3.45/0.99    (((~m1_subset_1(k2_xboole_0(sK3,sK4),u1_struct_0(k9_yellow_6(sK1,sK2))) & m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK1,sK2)))) & m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK1,sK2)))) & m1_subset_1(sK2,u1_struct_0(sK1))) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 3.45/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f40,f53,f52,f51,f50])).
% 3.45/0.99  
% 3.45/0.99  fof(f78,plain,(
% 3.45/0.99    ~v2_struct_0(sK1)),
% 3.45/0.99    inference(cnf_transformation,[],[f54])).
% 3.45/0.99  
% 3.45/0.99  fof(f79,plain,(
% 3.45/0.99    v2_pre_topc(sK1)),
% 3.45/0.99    inference(cnf_transformation,[],[f54])).
% 3.45/0.99  
% 3.45/0.99  fof(f80,plain,(
% 3.45/0.99    l1_pre_topc(sK1)),
% 3.45/0.99    inference(cnf_transformation,[],[f54])).
% 3.45/0.99  
% 3.45/0.99  fof(f10,axiom,(
% 3.45/0.99    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 3.45/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f27,plain,(
% 3.45/0.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 3.45/0.99    inference(ennf_transformation,[],[f10])).
% 3.45/0.99  
% 3.45/0.99  fof(f28,plain,(
% 3.45/0.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.45/0.99    inference(flattening,[],[f27])).
% 3.45/0.99  
% 3.45/0.99  fof(f70,plain,(
% 3.45/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.45/0.99    inference(cnf_transformation,[],[f28])).
% 3.45/0.99  
% 3.45/0.99  fof(f8,axiom,(
% 3.45/0.99    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 3.45/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f24,plain,(
% 3.45/0.99    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 3.45/0.99    inference(ennf_transformation,[],[f8])).
% 3.45/0.99  
% 3.45/0.99  fof(f68,plain,(
% 3.45/0.99    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 3.45/0.99    inference(cnf_transformation,[],[f24])).
% 3.45/0.99  
% 3.45/0.99  fof(f84,plain,(
% 3.45/0.99    ~m1_subset_1(k2_xboole_0(sK3,sK4),u1_struct_0(k9_yellow_6(sK1,sK2)))),
% 3.45/0.99    inference(cnf_transformation,[],[f54])).
% 3.45/0.99  
% 3.45/0.99  fof(f88,plain,(
% 3.45/0.99    ~m1_subset_1(k3_tarski(k2_tarski(sK3,sK4)),u1_struct_0(k9_yellow_6(sK1,sK2)))),
% 3.45/0.99    inference(definition_unfolding,[],[f84,f58])).
% 3.45/0.99  
% 3.45/0.99  fof(f81,plain,(
% 3.45/0.99    m1_subset_1(sK2,u1_struct_0(sK1))),
% 3.45/0.99    inference(cnf_transformation,[],[f54])).
% 3.45/0.99  
% 3.45/0.99  fof(f82,plain,(
% 3.45/0.99    m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK1,sK2)))),
% 3.45/0.99    inference(cnf_transformation,[],[f54])).
% 3.45/0.99  
% 3.45/0.99  fof(f83,plain,(
% 3.45/0.99    m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK1,sK2)))),
% 3.45/0.99    inference(cnf_transformation,[],[f54])).
% 3.45/0.99  
% 3.45/0.99  fof(f15,axiom,(
% 3.45/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => m1_connsp_2(X2,X0,X1))))),
% 3.45/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f37,plain,(
% 3.45/0.99    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.45/0.99    inference(ennf_transformation,[],[f15])).
% 3.45/0.99  
% 3.45/0.99  fof(f38,plain,(
% 3.45/0.99    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.45/0.99    inference(flattening,[],[f37])).
% 3.45/0.99  
% 3.45/0.99  fof(f77,plain,(
% 3.45/0.99    ( ! [X2,X0,X1] : (m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.45/0.99    inference(cnf_transformation,[],[f38])).
% 3.45/0.99  
% 3.45/0.99  fof(f12,axiom,(
% 3.45/0.99    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.45/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f31,plain,(
% 3.45/0.99    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.45/0.99    inference(ennf_transformation,[],[f12])).
% 3.45/0.99  
% 3.45/0.99  fof(f32,plain,(
% 3.45/0.99    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.45/0.99    inference(flattening,[],[f31])).
% 3.45/0.99  
% 3.45/0.99  fof(f72,plain,(
% 3.45/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.45/0.99    inference(cnf_transformation,[],[f32])).
% 3.45/0.99  
% 3.45/0.99  fof(f9,axiom,(
% 3.45/0.99    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 3.45/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f25,plain,(
% 3.45/0.99    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 3.45/0.99    inference(ennf_transformation,[],[f9])).
% 3.45/0.99  
% 3.45/0.99  fof(f26,plain,(
% 3.45/0.99    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 3.45/0.99    inference(flattening,[],[f25])).
% 3.45/0.99  
% 3.45/0.99  fof(f69,plain,(
% 3.45/0.99    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 3.45/0.99    inference(cnf_transformation,[],[f26])).
% 3.45/0.99  
% 3.45/0.99  fof(f75,plain,(
% 3.45/0.99    ( ! [X2,X0,X1] : (v3_pre_topc(X2,X0) | ~r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.45/0.99    inference(cnf_transformation,[],[f49])).
% 3.45/0.99  
% 3.45/0.99  fof(f13,axiom,(
% 3.45/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (m1_connsp_2(X1,X0,X2) => r2_hidden(X2,X1)))))),
% 3.45/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f33,plain,(
% 3.45/0.99    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.45/0.99    inference(ennf_transformation,[],[f13])).
% 3.45/0.99  
% 3.45/0.99  fof(f34,plain,(
% 3.45/0.99    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.45/0.99    inference(flattening,[],[f33])).
% 3.45/0.99  
% 3.45/0.99  fof(f73,plain,(
% 3.45/0.99    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.45/0.99    inference(cnf_transformation,[],[f34])).
% 3.45/0.99  
% 3.45/0.99  fof(f5,axiom,(
% 3.45/0.99    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 3.45/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f19,plain,(
% 3.45/0.99    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 3.45/0.99    inference(ennf_transformation,[],[f5])).
% 3.45/0.99  
% 3.45/0.99  fof(f47,plain,(
% 3.45/0.99    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 3.45/0.99    inference(nnf_transformation,[],[f19])).
% 3.45/0.99  
% 3.45/0.99  fof(f64,plain,(
% 3.45/0.99    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,X0) | ~v1_xboole_0(X0)) )),
% 3.45/0.99    inference(cnf_transformation,[],[f47])).
% 3.45/0.99  
% 3.45/0.99  fof(f7,axiom,(
% 3.45/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 3.45/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f22,plain,(
% 3.45/0.99    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 3.45/0.99    inference(ennf_transformation,[],[f7])).
% 3.45/0.99  
% 3.45/0.99  fof(f23,plain,(
% 3.45/0.99    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.45/0.99    inference(flattening,[],[f22])).
% 3.45/0.99  
% 3.45/0.99  fof(f67,plain,(
% 3.45/0.99    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.45/0.99    inference(cnf_transformation,[],[f23])).
% 3.45/0.99  
% 3.45/0.99  fof(f86,plain,(
% 3.45/0.99    ( ! [X2,X0,X1] : (k3_tarski(k2_tarski(X1,X2)) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.45/0.99    inference(definition_unfolding,[],[f67,f58])).
% 3.45/0.99  
% 3.45/0.99  fof(f6,axiom,(
% 3.45/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 3.45/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f20,plain,(
% 3.45/0.99    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 3.45/0.99    inference(ennf_transformation,[],[f6])).
% 3.45/0.99  
% 3.45/0.99  fof(f21,plain,(
% 3.45/0.99    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.45/0.99    inference(flattening,[],[f20])).
% 3.45/0.99  
% 3.45/0.99  fof(f66,plain,(
% 3.45/0.99    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.45/0.99    inference(cnf_transformation,[],[f21])).
% 3.45/0.99  
% 3.45/0.99  fof(f11,axiom,(
% 3.45/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X2,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_xboole_0(X1,X2),X0))),
% 3.45/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f29,plain,(
% 3.45/0.99    ! [X0,X1,X2] : (v3_pre_topc(k2_xboole_0(X1,X2),X0) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.45/0.99    inference(ennf_transformation,[],[f11])).
% 3.45/0.99  
% 3.45/0.99  fof(f30,plain,(
% 3.45/0.99    ! [X0,X1,X2] : (v3_pre_topc(k2_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.45/0.99    inference(flattening,[],[f29])).
% 3.45/0.99  
% 3.45/0.99  fof(f71,plain,(
% 3.45/0.99    ( ! [X2,X0,X1] : (v3_pre_topc(k2_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.45/0.99    inference(cnf_transformation,[],[f30])).
% 3.45/0.99  
% 3.45/0.99  fof(f87,plain,(
% 3.45/0.99    ( ! [X2,X0,X1] : (v3_pre_topc(k3_tarski(k2_tarski(X1,X2)),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.45/0.99    inference(definition_unfolding,[],[f71,f58])).
% 3.45/0.99  
% 3.45/0.99  cnf(c_0,plain,
% 3.45/0.99      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 3.45/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_733,plain,
% 3.45/0.99      ( r2_hidden(sK0(X0_48),X0_48) | v1_xboole_0(X0_48) ),
% 3.45/0.99      inference(subtyping,[status(esa)],[c_0]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_1179,plain,
% 3.45/0.99      ( r2_hidden(sK0(X0_48),X0_48) = iProver_top
% 3.45/0.99      | v1_xboole_0(X0_48) = iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_733]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_3,plain,
% 3.45/0.99      ( r1_tarski(k2_tarski(X0,X1),X2)
% 3.45/0.99      | ~ r2_hidden(X0,X2)
% 3.45/0.99      | ~ r2_hidden(X1,X2) ),
% 3.45/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_730,plain,
% 3.45/0.99      ( r1_tarski(k2_tarski(X0_48,X1_48),X2_48)
% 3.45/0.99      | ~ r2_hidden(X0_48,X2_48)
% 3.45/0.99      | ~ r2_hidden(X1_48,X2_48) ),
% 3.45/0.99      inference(subtyping,[status(esa)],[c_3]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_1182,plain,
% 3.45/0.99      ( r1_tarski(k2_tarski(X0_48,X1_48),X2_48) = iProver_top
% 3.45/0.99      | r2_hidden(X0_48,X2_48) != iProver_top
% 3.45/0.99      | r2_hidden(X1_48,X2_48) != iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_730]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_2,plain,
% 3.45/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X0,k3_tarski(k2_tarski(X2,X1))) ),
% 3.45/0.99      inference(cnf_transformation,[],[f85]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_731,plain,
% 3.45/0.99      ( ~ r1_tarski(X0_50,X0_48)
% 3.45/0.99      | r1_tarski(X0_50,k3_tarski(k2_tarski(X1_48,X0_48))) ),
% 3.45/0.99      inference(subtyping,[status(esa)],[c_2]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_1181,plain,
% 3.45/0.99      ( r1_tarski(X0_50,X0_48) != iProver_top
% 3.45/0.99      | r1_tarski(X0_50,k3_tarski(k2_tarski(X1_48,X0_48))) = iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_731]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_4,plain,
% 3.45/0.99      ( ~ r1_tarski(k2_tarski(X0,X1),X2) | r2_hidden(X1,X2) ),
% 3.45/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_729,plain,
% 3.45/0.99      ( ~ r1_tarski(k2_tarski(X0_48,X1_48),X2_48)
% 3.45/0.99      | r2_hidden(X1_48,X2_48) ),
% 3.45/0.99      inference(subtyping,[status(esa)],[c_4]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_1183,plain,
% 3.45/0.99      ( r1_tarski(k2_tarski(X0_48,X1_48),X2_48) != iProver_top
% 3.45/0.99      | r2_hidden(X1_48,X2_48) = iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_729]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_1896,plain,
% 3.45/0.99      ( r1_tarski(k2_tarski(X0_48,X1_48),X2_48) != iProver_top
% 3.45/0.99      | r2_hidden(X1_48,k3_tarski(k2_tarski(X3_48,X2_48))) = iProver_top ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_1181,c_1183]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_4172,plain,
% 3.45/0.99      ( r2_hidden(X0_48,X1_48) != iProver_top
% 3.45/0.99      | r2_hidden(X2_48,X1_48) != iProver_top
% 3.45/0.99      | r2_hidden(X2_48,k3_tarski(k2_tarski(X3_48,X1_48))) = iProver_top ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_1182,c_1896]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_14096,plain,
% 3.45/0.99      ( r2_hidden(X0_48,X1_48) != iProver_top
% 3.45/0.99      | r2_hidden(X0_48,k3_tarski(k2_tarski(X2_48,X1_48))) = iProver_top
% 3.45/0.99      | v1_xboole_0(X1_48) = iProver_top ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_1179,c_4172]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_1,plain,
% 3.45/0.99      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.45/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_732,plain,
% 3.45/0.99      ( ~ r2_hidden(X0_48,X1_48) | ~ v1_xboole_0(X1_48) ),
% 3.45/0.99      inference(subtyping,[status(esa)],[c_1]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_764,plain,
% 3.45/0.99      ( r2_hidden(X0_48,X1_48) != iProver_top
% 3.45/0.99      | v1_xboole_0(X1_48) != iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_732]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_14410,plain,
% 3.45/0.99      ( r2_hidden(X0_48,k3_tarski(k2_tarski(X2_48,X1_48))) = iProver_top
% 3.45/0.99      | r2_hidden(X0_48,X1_48) != iProver_top ),
% 3.45/0.99      inference(global_propositional_subsumption,
% 3.45/0.99                [status(thm)],
% 3.45/0.99                [c_14096,c_764]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_14411,plain,
% 3.45/0.99      ( r2_hidden(X0_48,X1_48) != iProver_top
% 3.45/0.99      | r2_hidden(X0_48,k3_tarski(k2_tarski(X2_48,X1_48))) = iProver_top ),
% 3.45/0.99      inference(renaming,[status(thm)],[c_14410]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_18,plain,
% 3.45/0.99      ( ~ v3_pre_topc(X0,X1)
% 3.45/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.45/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.45/0.99      | ~ r2_hidden(X2,X0)
% 3.45/0.99      | r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
% 3.45/0.99      | v2_struct_0(X1)
% 3.45/0.99      | ~ v2_pre_topc(X1)
% 3.45/0.99      | ~ l1_pre_topc(X1) ),
% 3.45/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_28,negated_conjecture,
% 3.45/0.99      ( ~ v2_struct_0(sK1) ),
% 3.45/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_470,plain,
% 3.45/0.99      ( ~ v3_pre_topc(X0,X1)
% 3.45/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.45/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.45/0.99      | ~ r2_hidden(X2,X0)
% 3.45/0.99      | r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
% 3.45/0.99      | ~ v2_pre_topc(X1)
% 3.45/0.99      | ~ l1_pre_topc(X1)
% 3.45/0.99      | sK1 != X1 ),
% 3.45/0.99      inference(resolution_lifted,[status(thm)],[c_18,c_28]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_471,plain,
% 3.45/0.99      ( ~ v3_pre_topc(X0,sK1)
% 3.45/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 3.45/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.45/0.99      | ~ r2_hidden(X1,X0)
% 3.45/0.99      | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK1,X1)))
% 3.45/0.99      | ~ v2_pre_topc(sK1)
% 3.45/0.99      | ~ l1_pre_topc(sK1) ),
% 3.45/0.99      inference(unflattening,[status(thm)],[c_470]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_27,negated_conjecture,
% 3.45/0.99      ( v2_pre_topc(sK1) ),
% 3.45/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_26,negated_conjecture,
% 3.45/0.99      ( l1_pre_topc(sK1) ),
% 3.45/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_475,plain,
% 3.45/0.99      ( ~ v3_pre_topc(X0,sK1)
% 3.45/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 3.45/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.45/0.99      | ~ r2_hidden(X1,X0)
% 3.45/0.99      | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK1,X1))) ),
% 3.45/0.99      inference(global_propositional_subsumption,
% 3.45/0.99                [status(thm)],
% 3.45/0.99                [c_471,c_27,c_26]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_14,plain,
% 3.45/0.99      ( m1_subset_1(X0,X1)
% 3.45/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.45/0.99      | ~ r2_hidden(X0,X2) ),
% 3.45/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_491,plain,
% 3.45/0.99      ( ~ v3_pre_topc(X0,sK1)
% 3.45/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.45/0.99      | ~ r2_hidden(X1,X0)
% 3.45/0.99      | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK1,X1))) ),
% 3.45/0.99      inference(forward_subsumption_resolution,
% 3.45/0.99                [status(thm)],
% 3.45/0.99                [c_475,c_14]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_712,plain,
% 3.45/0.99      ( ~ v3_pre_topc(X0_48,sK1)
% 3.45/0.99      | ~ m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.45/0.99      | ~ r2_hidden(X1_48,X0_48)
% 3.45/0.99      | r2_hidden(X0_48,u1_struct_0(k9_yellow_6(sK1,X1_48))) ),
% 3.45/0.99      inference(subtyping,[status(esa)],[c_491]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_1200,plain,
% 3.45/0.99      ( v3_pre_topc(X0_48,sK1) != iProver_top
% 3.45/0.99      | m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.45/0.99      | r2_hidden(X1_48,X0_48) != iProver_top
% 3.45/0.99      | r2_hidden(X0_48,u1_struct_0(k9_yellow_6(sK1,X1_48))) = iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_712]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_12,plain,
% 3.45/0.99      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 3.45/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_722,plain,
% 3.45/0.99      ( m1_subset_1(X0_48,X1_48) | ~ r2_hidden(X0_48,X1_48) ),
% 3.45/0.99      inference(subtyping,[status(esa)],[c_12]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_1190,plain,
% 3.45/0.99      ( m1_subset_1(X0_48,X1_48) = iProver_top
% 3.45/0.99      | r2_hidden(X0_48,X1_48) != iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_722]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_4053,plain,
% 3.45/0.99      ( v3_pre_topc(X0_48,sK1) != iProver_top
% 3.45/0.99      | m1_subset_1(X0_48,u1_struct_0(k9_yellow_6(sK1,X1_48))) = iProver_top
% 3.45/0.99      | m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.45/0.99      | r2_hidden(X1_48,X0_48) != iProver_top ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_1200,c_1190]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_22,negated_conjecture,
% 3.45/0.99      ( ~ m1_subset_1(k3_tarski(k2_tarski(sK3,sK4)),u1_struct_0(k9_yellow_6(sK1,sK2))) ),
% 3.45/0.99      inference(cnf_transformation,[],[f88]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_720,negated_conjecture,
% 3.45/0.99      ( ~ m1_subset_1(k3_tarski(k2_tarski(sK3,sK4)),u1_struct_0(k9_yellow_6(sK1,sK2))) ),
% 3.45/0.99      inference(subtyping,[status(esa)],[c_22]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_1192,plain,
% 3.45/0.99      ( m1_subset_1(k3_tarski(k2_tarski(sK3,sK4)),u1_struct_0(k9_yellow_6(sK1,sK2))) != iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_720]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_7552,plain,
% 3.45/0.99      ( v3_pre_topc(k3_tarski(k2_tarski(sK3,sK4)),sK1) != iProver_top
% 3.45/0.99      | m1_subset_1(k3_tarski(k2_tarski(sK3,sK4)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.45/0.99      | r2_hidden(sK2,k3_tarski(k2_tarski(sK3,sK4))) != iProver_top ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_4053,c_1192]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_25,negated_conjecture,
% 3.45/0.99      ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 3.45/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_32,plain,
% 3.45/0.99      ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_24,negated_conjecture,
% 3.45/0.99      ( m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK1,sK2))) ),
% 3.45/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_33,plain,
% 3.45/0.99      ( m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK1,sK2))) = iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_23,negated_conjecture,
% 3.45/0.99      ( m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK1,sK2))) ),
% 3.45/0.99      inference(cnf_transformation,[],[f83]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_34,plain,
% 3.45/0.99      ( m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK1,sK2))) = iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_21,plain,
% 3.45/0.99      ( m1_connsp_2(X0,X1,X2)
% 3.45/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.45/0.99      | ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(X1,X2)))
% 3.45/0.99      | v2_struct_0(X1)
% 3.45/0.99      | ~ v2_pre_topc(X1)
% 3.45/0.99      | ~ l1_pre_topc(X1) ),
% 3.45/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_16,plain,
% 3.45/0.99      ( ~ m1_connsp_2(X0,X1,X2)
% 3.45/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.45/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.45/0.99      | v2_struct_0(X1)
% 3.45/0.99      | ~ v2_pre_topc(X1)
% 3.45/0.99      | ~ l1_pre_topc(X1) ),
% 3.45/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_343,plain,
% 3.45/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.45/0.99      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
% 3.45/0.99      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.45/0.99      | v2_struct_0(X1)
% 3.45/0.99      | ~ v2_pre_topc(X1)
% 3.45/0.99      | ~ l1_pre_topc(X1) ),
% 3.45/0.99      inference(resolution,[status(thm)],[c_21,c_16]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_380,plain,
% 3.45/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.45/0.99      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
% 3.45/0.99      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.45/0.99      | ~ v2_pre_topc(X1)
% 3.45/0.99      | ~ l1_pre_topc(X1)
% 3.45/0.99      | sK1 != X1 ),
% 3.45/0.99      inference(resolution_lifted,[status(thm)],[c_343,c_28]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_381,plain,
% 3.45/0.99      ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK1,X1)))
% 3.45/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 3.45/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.45/0.99      | ~ v2_pre_topc(sK1)
% 3.45/0.99      | ~ l1_pre_topc(sK1) ),
% 3.45/0.99      inference(unflattening,[status(thm)],[c_380]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_385,plain,
% 3.45/0.99      ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK1,X1)))
% 3.45/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 3.45/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 3.45/0.99      inference(global_propositional_subsumption,
% 3.45/0.99                [status(thm)],
% 3.45/0.99                [c_381,c_27,c_26]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_716,plain,
% 3.45/0.99      ( ~ m1_subset_1(X0_48,u1_struct_0(k9_yellow_6(sK1,X1_48)))
% 3.45/0.99      | ~ m1_subset_1(X1_48,u1_struct_0(sK1))
% 3.45/0.99      | m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 3.45/0.99      inference(subtyping,[status(esa)],[c_385]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_1372,plain,
% 3.45/0.99      ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 3.45/0.99      | ~ m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK1,sK2)))
% 3.45/0.99      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 3.45/0.99      inference(instantiation,[status(thm)],[c_716]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_1373,plain,
% 3.45/0.99      ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 3.45/0.99      | m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK1,sK2))) != iProver_top
% 3.45/0.99      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_1372]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_1375,plain,
% 3.45/0.99      ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 3.45/0.99      | ~ m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK1,sK2)))
% 3.45/0.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 3.45/0.99      inference(instantiation,[status(thm)],[c_716]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_1376,plain,
% 3.45/0.99      ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 3.45/0.99      | m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK1,sK2))) != iProver_top
% 3.45/0.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_1375]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_13,plain,
% 3.45/0.99      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.45/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_725,plain,
% 3.45/0.99      ( ~ m1_subset_1(X0_48,X1_48)
% 3.45/0.99      | r2_hidden(X0_48,X1_48)
% 3.45/0.99      | v1_xboole_0(X1_48) ),
% 3.45/0.99      inference(subtyping,[status(esa)],[c_13]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_1388,plain,
% 3.45/0.99      ( ~ m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK1,sK2)))
% 3.45/0.99      | r2_hidden(sK4,u1_struct_0(k9_yellow_6(sK1,sK2)))
% 3.45/0.99      | v1_xboole_0(u1_struct_0(k9_yellow_6(sK1,sK2))) ),
% 3.45/0.99      inference(instantiation,[status(thm)],[c_725]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_1389,plain,
% 3.45/0.99      ( m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK1,sK2))) != iProver_top
% 3.45/0.99      | r2_hidden(sK4,u1_struct_0(k9_yellow_6(sK1,sK2))) = iProver_top
% 3.45/0.99      | v1_xboole_0(u1_struct_0(k9_yellow_6(sK1,sK2))) = iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_1388]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_1391,plain,
% 3.45/0.99      ( ~ m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK1,sK2)))
% 3.45/0.99      | r2_hidden(sK3,u1_struct_0(k9_yellow_6(sK1,sK2)))
% 3.45/0.99      | v1_xboole_0(u1_struct_0(k9_yellow_6(sK1,sK2))) ),
% 3.45/0.99      inference(instantiation,[status(thm)],[c_725]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_1392,plain,
% 3.45/0.99      ( m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK1,sK2))) != iProver_top
% 3.45/0.99      | r2_hidden(sK3,u1_struct_0(k9_yellow_6(sK1,sK2))) = iProver_top
% 3.45/0.99      | v1_xboole_0(u1_struct_0(k9_yellow_6(sK1,sK2))) = iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_1391]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_19,plain,
% 3.45/0.99      ( v3_pre_topc(X0,X1)
% 3.45/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.45/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.45/0.99      | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
% 3.45/0.99      | v2_struct_0(X1)
% 3.45/0.99      | ~ v2_pre_topc(X1)
% 3.45/0.99      | ~ l1_pre_topc(X1) ),
% 3.45/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_446,plain,
% 3.45/0.99      ( v3_pre_topc(X0,X1)
% 3.45/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.45/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.45/0.99      | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
% 3.45/0.99      | ~ v2_pre_topc(X1)
% 3.45/0.99      | ~ l1_pre_topc(X1)
% 3.45/0.99      | sK1 != X1 ),
% 3.45/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_28]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_447,plain,
% 3.45/0.99      ( v3_pre_topc(X0,sK1)
% 3.45/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 3.45/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.45/0.99      | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(sK1,X1)))
% 3.45/0.99      | ~ v2_pre_topc(sK1)
% 3.45/0.99      | ~ l1_pre_topc(sK1) ),
% 3.45/0.99      inference(unflattening,[status(thm)],[c_446]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_451,plain,
% 3.45/0.99      ( v3_pre_topc(X0,sK1)
% 3.45/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 3.45/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.45/0.99      | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(sK1,X1))) ),
% 3.45/0.99      inference(global_propositional_subsumption,
% 3.45/0.99                [status(thm)],
% 3.45/0.99                [c_447,c_27,c_26]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_713,plain,
% 3.45/0.99      ( v3_pre_topc(X0_48,sK1)
% 3.45/0.99      | ~ m1_subset_1(X1_48,u1_struct_0(sK1))
% 3.45/0.99      | ~ m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.45/0.99      | ~ r2_hidden(X0_48,u1_struct_0(k9_yellow_6(sK1,X1_48))) ),
% 3.45/0.99      inference(subtyping,[status(esa)],[c_451]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_1458,plain,
% 3.45/0.99      ( v3_pre_topc(sK4,sK1)
% 3.45/0.99      | ~ m1_subset_1(X0_48,u1_struct_0(sK1))
% 3.45/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.45/0.99      | ~ r2_hidden(sK4,u1_struct_0(k9_yellow_6(sK1,X0_48))) ),
% 3.45/0.99      inference(instantiation,[status(thm)],[c_713]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_1459,plain,
% 3.45/0.99      ( v3_pre_topc(sK4,sK1) = iProver_top
% 3.45/0.99      | m1_subset_1(X0_48,u1_struct_0(sK1)) != iProver_top
% 3.45/0.99      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.45/0.99      | r2_hidden(sK4,u1_struct_0(k9_yellow_6(sK1,X0_48))) != iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_1458]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_1461,plain,
% 3.45/0.99      ( v3_pre_topc(sK4,sK1) = iProver_top
% 3.45/0.99      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 3.45/0.99      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.45/0.99      | r2_hidden(sK4,u1_struct_0(k9_yellow_6(sK1,sK2))) != iProver_top ),
% 3.45/0.99      inference(instantiation,[status(thm)],[c_1459]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_1484,plain,
% 3.45/0.99      ( v3_pre_topc(sK3,sK1)
% 3.45/0.99      | ~ m1_subset_1(X0_48,u1_struct_0(sK1))
% 3.45/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.45/0.99      | ~ r2_hidden(sK3,u1_struct_0(k9_yellow_6(sK1,X0_48))) ),
% 3.45/0.99      inference(instantiation,[status(thm)],[c_713]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_1485,plain,
% 3.45/0.99      ( v3_pre_topc(sK3,sK1) = iProver_top
% 3.45/0.99      | m1_subset_1(X0_48,u1_struct_0(sK1)) != iProver_top
% 3.45/0.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.45/0.99      | r2_hidden(sK3,u1_struct_0(k9_yellow_6(sK1,X0_48))) != iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_1484]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_1487,plain,
% 3.45/0.99      ( v3_pre_topc(sK3,sK1) = iProver_top
% 3.45/0.99      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 3.45/0.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.45/0.99      | r2_hidden(sK3,u1_struct_0(k9_yellow_6(sK1,sK2))) != iProver_top ),
% 3.45/0.99      inference(instantiation,[status(thm)],[c_1485]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_719,negated_conjecture,
% 3.45/0.99      ( m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK1,sK2))) ),
% 3.45/0.99      inference(subtyping,[status(esa)],[c_23]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_1193,plain,
% 3.45/0.99      ( m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK1,sK2))) = iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_719]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_17,plain,
% 3.45/0.99      ( ~ m1_connsp_2(X0,X1,X2)
% 3.45/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.45/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.45/0.99      | r2_hidden(X2,X0)
% 3.45/0.99      | v2_struct_0(X1)
% 3.45/0.99      | ~ v2_pre_topc(X1)
% 3.45/0.99      | ~ l1_pre_topc(X1) ),
% 3.45/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_164,plain,
% 3.45/0.99      ( ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.45/0.99      | ~ m1_connsp_2(X0,X1,X2)
% 3.45/0.99      | r2_hidden(X2,X0)
% 3.45/0.99      | v2_struct_0(X1)
% 3.45/0.99      | ~ v2_pre_topc(X1)
% 3.45/0.99      | ~ l1_pre_topc(X1) ),
% 3.45/0.99      inference(global_propositional_subsumption,
% 3.45/0.99                [status(thm)],
% 3.45/0.99                [c_17,c_16]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_165,plain,
% 3.45/0.99      ( ~ m1_connsp_2(X0,X1,X2)
% 3.45/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.45/0.99      | r2_hidden(X2,X0)
% 3.45/0.99      | v2_struct_0(X1)
% 3.45/0.99      | ~ v2_pre_topc(X1)
% 3.45/0.99      | ~ l1_pre_topc(X1) ),
% 3.45/0.99      inference(renaming,[status(thm)],[c_164]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_320,plain,
% 3.45/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.45/0.99      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
% 3.45/0.99      | r2_hidden(X0,X2)
% 3.45/0.99      | v2_struct_0(X1)
% 3.45/0.99      | ~ v2_pre_topc(X1)
% 3.45/0.99      | ~ l1_pre_topc(X1) ),
% 3.45/0.99      inference(resolution,[status(thm)],[c_21,c_165]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_401,plain,
% 3.45/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.45/0.99      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
% 3.45/0.99      | r2_hidden(X0,X2)
% 3.45/0.99      | ~ v2_pre_topc(X1)
% 3.45/0.99      | ~ l1_pre_topc(X1)
% 3.45/0.99      | sK1 != X1 ),
% 3.45/0.99      inference(resolution_lifted,[status(thm)],[c_320,c_28]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_402,plain,
% 3.45/0.99      ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK1,X1)))
% 3.45/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 3.45/0.99      | r2_hidden(X1,X0)
% 3.45/0.99      | ~ v2_pre_topc(sK1)
% 3.45/0.99      | ~ l1_pre_topc(sK1) ),
% 3.45/0.99      inference(unflattening,[status(thm)],[c_401]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_406,plain,
% 3.45/0.99      ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK1,X1)))
% 3.45/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 3.45/0.99      | r2_hidden(X1,X0) ),
% 3.45/0.99      inference(global_propositional_subsumption,
% 3.45/0.99                [status(thm)],
% 3.45/0.99                [c_402,c_27,c_26]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_715,plain,
% 3.45/0.99      ( ~ m1_subset_1(X0_48,u1_struct_0(k9_yellow_6(sK1,X1_48)))
% 3.45/0.99      | ~ m1_subset_1(X1_48,u1_struct_0(sK1))
% 3.45/0.99      | r2_hidden(X1_48,X0_48) ),
% 3.45/0.99      inference(subtyping,[status(esa)],[c_406]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_1197,plain,
% 3.45/0.99      ( m1_subset_1(X0_48,u1_struct_0(k9_yellow_6(sK1,X1_48))) != iProver_top
% 3.45/0.99      | m1_subset_1(X1_48,u1_struct_0(sK1)) != iProver_top
% 3.45/0.99      | r2_hidden(X1_48,X0_48) = iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_715]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_1420,plain,
% 3.45/0.99      ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 3.45/0.99      | r2_hidden(sK2,sK4) = iProver_top ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_1193,c_1197]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_1378,plain,
% 3.45/0.99      ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 3.45/0.99      | ~ m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK1,sK2)))
% 3.45/0.99      | r2_hidden(sK2,sK4) ),
% 3.45/0.99      inference(instantiation,[status(thm)],[c_715]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_1379,plain,
% 3.45/0.99      ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 3.45/0.99      | m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK1,sK2))) != iProver_top
% 3.45/0.99      | r2_hidden(sK2,sK4) = iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_1378]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_1433,plain,
% 3.45/0.99      ( r2_hidden(sK2,sK4) = iProver_top ),
% 3.45/0.99      inference(global_propositional_subsumption,
% 3.45/0.99                [status(thm)],
% 3.45/0.99                [c_1420,c_32,c_34,c_1379]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_1180,plain,
% 3.45/0.99      ( r2_hidden(X0_48,X1_48) != iProver_top
% 3.45/0.99      | v1_xboole_0(X1_48) != iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_732]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_1796,plain,
% 3.45/0.99      ( v1_xboole_0(sK4) != iProver_top ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_1433,c_1180]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_7,plain,
% 3.45/0.99      ( ~ m1_subset_1(X0,X1) | ~ v1_xboole_0(X1) | v1_xboole_0(X0) ),
% 3.45/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_726,plain,
% 3.45/0.99      ( ~ m1_subset_1(X0_48,X1_48)
% 3.45/0.99      | ~ v1_xboole_0(X1_48)
% 3.45/0.99      | v1_xboole_0(X0_48) ),
% 3.45/0.99      inference(subtyping,[status(esa)],[c_7]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_1572,plain,
% 3.45/0.99      ( ~ m1_subset_1(X0_48,u1_struct_0(k9_yellow_6(sK1,sK2)))
% 3.45/0.99      | v1_xboole_0(X0_48)
% 3.45/0.99      | ~ v1_xboole_0(u1_struct_0(k9_yellow_6(sK1,sK2))) ),
% 3.45/0.99      inference(instantiation,[status(thm)],[c_726]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_1847,plain,
% 3.45/0.99      ( ~ m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK1,sK2)))
% 3.45/0.99      | ~ v1_xboole_0(u1_struct_0(k9_yellow_6(sK1,sK2)))
% 3.45/0.99      | v1_xboole_0(sK4) ),
% 3.45/0.99      inference(instantiation,[status(thm)],[c_1572]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_1848,plain,
% 3.45/0.99      ( m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK1,sK2))) != iProver_top
% 3.45/0.99      | v1_xboole_0(u1_struct_0(k9_yellow_6(sK1,sK2))) != iProver_top
% 3.45/0.99      | v1_xboole_0(sK4) = iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_1847]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_1196,plain,
% 3.45/0.99      ( m1_subset_1(X0_48,u1_struct_0(k9_yellow_6(sK1,X1_48))) != iProver_top
% 3.45/0.99      | m1_subset_1(X1_48,u1_struct_0(sK1)) != iProver_top
% 3.45/0.99      | m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_716]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_1540,plain,
% 3.45/0.99      ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 3.45/0.99      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_1193,c_1196]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_1901,plain,
% 3.45/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 3.45/0.99      inference(global_propositional_subsumption,
% 3.45/0.99                [status(thm)],
% 3.45/0.99                [c_1540,c_32,c_34,c_1373]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_718,negated_conjecture,
% 3.45/0.99      ( m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK1,sK2))) ),
% 3.45/0.99      inference(subtyping,[status(esa)],[c_24]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_1194,plain,
% 3.45/0.99      ( m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK1,sK2))) = iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_718]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_1541,plain,
% 3.45/0.99      ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 3.45/0.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_1194,c_1196]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_2134,plain,
% 3.45/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 3.45/0.99      inference(global_propositional_subsumption,
% 3.45/0.99                [status(thm)],
% 3.45/0.99                [c_1541,c_32,c_33,c_1376]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_11,plain,
% 3.45/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.45/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.45/0.99      | k4_subset_1(X1,X2,X0) = k3_tarski(k2_tarski(X2,X0)) ),
% 3.45/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_723,plain,
% 3.45/0.99      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(X1_48))
% 3.45/0.99      | ~ m1_subset_1(X2_48,k1_zfmisc_1(X1_48))
% 3.45/0.99      | k4_subset_1(X1_48,X2_48,X0_48) = k3_tarski(k2_tarski(X2_48,X0_48)) ),
% 3.45/0.99      inference(subtyping,[status(esa)],[c_11]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_1189,plain,
% 3.45/0.99      ( k4_subset_1(X0_48,X1_48,X2_48) = k3_tarski(k2_tarski(X1_48,X2_48))
% 3.45/0.99      | m1_subset_1(X1_48,k1_zfmisc_1(X0_48)) != iProver_top
% 3.45/0.99      | m1_subset_1(X2_48,k1_zfmisc_1(X0_48)) != iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_723]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_3252,plain,
% 3.45/0.99      ( k4_subset_1(u1_struct_0(sK1),sK3,X0_48) = k3_tarski(k2_tarski(sK3,X0_48))
% 3.45/0.99      | m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_2134,c_1189]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_3866,plain,
% 3.45/0.99      ( k4_subset_1(u1_struct_0(sK1),sK3,sK4) = k3_tarski(k2_tarski(sK3,sK4)) ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_1901,c_3252]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_10,plain,
% 3.45/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.45/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.45/0.99      | m1_subset_1(k4_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 3.45/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_724,plain,
% 3.45/0.99      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(X1_48))
% 3.45/0.99      | ~ m1_subset_1(X2_48,k1_zfmisc_1(X1_48))
% 3.45/0.99      | m1_subset_1(k4_subset_1(X1_48,X2_48,X0_48),k1_zfmisc_1(X1_48)) ),
% 3.45/0.99      inference(subtyping,[status(esa)],[c_10]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_1188,plain,
% 3.45/0.99      ( m1_subset_1(X0_48,k1_zfmisc_1(X1_48)) != iProver_top
% 3.45/0.99      | m1_subset_1(X2_48,k1_zfmisc_1(X1_48)) != iProver_top
% 3.45/0.99      | m1_subset_1(k4_subset_1(X1_48,X0_48,X2_48),k1_zfmisc_1(X1_48)) = iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_724]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_3888,plain,
% 3.45/0.99      ( m1_subset_1(k3_tarski(k2_tarski(sK3,sK4)),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 3.45/0.99      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.45/0.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_3866,c_1188]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_15,plain,
% 3.45/0.99      ( ~ v3_pre_topc(X0,X1)
% 3.45/0.99      | ~ v3_pre_topc(X2,X1)
% 3.45/0.99      | v3_pre_topc(k3_tarski(k2_tarski(X2,X0)),X1)
% 3.45/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.45/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.45/0.99      | ~ v2_pre_topc(X1)
% 3.45/0.99      | ~ l1_pre_topc(X1) ),
% 3.45/0.99      inference(cnf_transformation,[],[f87]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_522,plain,
% 3.45/0.99      ( ~ v3_pre_topc(X0,X1)
% 3.45/0.99      | ~ v3_pre_topc(X2,X1)
% 3.45/0.99      | v3_pre_topc(k3_tarski(k2_tarski(X2,X0)),X1)
% 3.45/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.45/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.45/0.99      | ~ v2_pre_topc(X1)
% 3.45/0.99      | sK1 != X1 ),
% 3.45/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_26]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_523,plain,
% 3.45/0.99      ( ~ v3_pre_topc(X0,sK1)
% 3.45/0.99      | ~ v3_pre_topc(X1,sK1)
% 3.45/0.99      | v3_pre_topc(k3_tarski(k2_tarski(X1,X0)),sK1)
% 3.45/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.45/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.45/0.99      | ~ v2_pre_topc(sK1) ),
% 3.45/0.99      inference(unflattening,[status(thm)],[c_522]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_527,plain,
% 3.45/0.99      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.45/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.45/0.99      | v3_pre_topc(k3_tarski(k2_tarski(X1,X0)),sK1)
% 3.45/0.99      | ~ v3_pre_topc(X1,sK1)
% 3.45/0.99      | ~ v3_pre_topc(X0,sK1) ),
% 3.45/0.99      inference(global_propositional_subsumption,
% 3.45/0.99                [status(thm)],
% 3.45/0.99                [c_523,c_27]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_528,plain,
% 3.45/0.99      ( ~ v3_pre_topc(X0,sK1)
% 3.45/0.99      | ~ v3_pre_topc(X1,sK1)
% 3.45/0.99      | v3_pre_topc(k3_tarski(k2_tarski(X1,X0)),sK1)
% 3.45/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.45/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 3.45/0.99      inference(renaming,[status(thm)],[c_527]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_711,plain,
% 3.45/0.99      ( ~ v3_pre_topc(X0_48,sK1)
% 3.45/0.99      | ~ v3_pre_topc(X1_48,sK1)
% 3.45/0.99      | v3_pre_topc(k3_tarski(k2_tarski(X1_48,X0_48)),sK1)
% 3.45/0.99      | ~ m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.45/0.99      | ~ m1_subset_1(X1_48,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 3.45/0.99      inference(subtyping,[status(esa)],[c_528]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_2252,plain,
% 3.45/0.99      ( ~ v3_pre_topc(X0_48,sK1)
% 3.45/0.99      | v3_pre_topc(k3_tarski(k2_tarski(X0_48,sK4)),sK1)
% 3.45/0.99      | ~ v3_pre_topc(sK4,sK1)
% 3.45/0.99      | ~ m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.45/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 3.45/0.99      inference(instantiation,[status(thm)],[c_711]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_4027,plain,
% 3.45/0.99      ( v3_pre_topc(k3_tarski(k2_tarski(sK3,sK4)),sK1)
% 3.45/0.99      | ~ v3_pre_topc(sK4,sK1)
% 3.45/0.99      | ~ v3_pre_topc(sK3,sK1)
% 3.45/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.45/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 3.45/0.99      inference(instantiation,[status(thm)],[c_2252]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_4028,plain,
% 3.45/0.99      ( v3_pre_topc(k3_tarski(k2_tarski(sK3,sK4)),sK1) = iProver_top
% 3.45/0.99      | v3_pre_topc(sK4,sK1) != iProver_top
% 3.45/0.99      | v3_pre_topc(sK3,sK1) != iProver_top
% 3.45/0.99      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.45/0.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_4027]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_7657,plain,
% 3.45/0.99      ( r2_hidden(sK2,k3_tarski(k2_tarski(sK3,sK4))) != iProver_top ),
% 3.45/0.99      inference(global_propositional_subsumption,
% 3.45/0.99                [status(thm)],
% 3.45/0.99                [c_7552,c_32,c_33,c_34,c_1373,c_1376,c_1389,c_1392,
% 3.45/0.99                 c_1461,c_1487,c_1796,c_1848,c_3888,c_4028]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_14423,plain,
% 3.45/0.99      ( r2_hidden(sK2,sK4) != iProver_top ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_14411,c_7657]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(contradiction,plain,
% 3.45/0.99      ( $false ),
% 3.45/0.99      inference(minisat,[status(thm)],[c_14423,c_1379,c_34,c_32]) ).
% 3.45/0.99  
% 3.45/0.99  
% 3.45/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.45/0.99  
% 3.45/0.99  ------                               Statistics
% 3.45/0.99  
% 3.45/0.99  ------ General
% 3.45/0.99  
% 3.45/0.99  abstr_ref_over_cycles:                  0
% 3.45/0.99  abstr_ref_under_cycles:                 0
% 3.45/0.99  gc_basic_clause_elim:                   0
% 3.45/0.99  forced_gc_time:                         0
% 3.45/0.99  parsing_time:                           0.009
% 3.45/0.99  unif_index_cands_time:                  0.
% 3.45/0.99  unif_index_add_time:                    0.
% 3.45/0.99  orderings_time:                         0.
% 3.45/0.99  out_proof_time:                         0.013
% 3.45/0.99  total_time:                             0.379
% 3.45/0.99  num_of_symbols:                         51
% 3.45/0.99  num_of_terms:                           12762
% 3.45/0.99  
% 3.45/0.99  ------ Preprocessing
% 3.45/0.99  
% 3.45/0.99  num_of_splits:                          0
% 3.45/0.99  num_of_split_atoms:                     0
% 3.45/0.99  num_of_reused_defs:                     0
% 3.45/0.99  num_eq_ax_congr_red:                    19
% 3.45/0.99  num_of_sem_filtered_clauses:            1
% 3.45/0.99  num_of_subtypes:                        3
% 3.45/0.99  monotx_restored_types:                  0
% 3.45/0.99  sat_num_of_epr_types:                   0
% 3.45/0.99  sat_num_of_non_cyclic_types:            0
% 3.45/0.99  sat_guarded_non_collapsed_types:        0
% 3.45/0.99  num_pure_diseq_elim:                    0
% 3.45/0.99  simp_replaced_by:                       0
% 3.45/0.99  res_preprocessed:                       123
% 3.45/0.99  prep_upred:                             0
% 3.45/0.99  prep_unflattend:                        6
% 3.45/0.99  smt_new_axioms:                         0
% 3.45/0.99  pred_elim_cands:                        5
% 3.45/0.99  pred_elim:                              4
% 3.45/0.99  pred_elim_cl:                           4
% 3.45/0.99  pred_elim_cycles:                       6
% 3.45/0.99  merged_defs:                            0
% 3.45/0.99  merged_defs_ncl:                        0
% 3.45/0.99  bin_hyper_res:                          0
% 3.45/0.99  prep_cycles:                            4
% 3.45/0.99  pred_elim_time:                         0.005
% 3.45/0.99  splitting_time:                         0.
% 3.45/0.99  sem_filter_time:                        0.
% 3.45/0.99  monotx_time:                            0.
% 3.45/0.99  subtype_inf_time:                       0.001
% 3.45/0.99  
% 3.45/0.99  ------ Problem properties
% 3.45/0.99  
% 3.45/0.99  clauses:                                23
% 3.45/0.99  conjectures:                            4
% 3.45/0.99  epr:                                    5
% 3.45/0.99  horn:                                   21
% 3.45/0.99  ground:                                 4
% 3.45/0.99  unary:                                  4
% 3.45/0.99  binary:                                 6
% 3.45/0.99  lits:                                   60
% 3.45/0.99  lits_eq:                                1
% 3.45/0.99  fd_pure:                                0
% 3.45/0.99  fd_pseudo:                              0
% 3.45/0.99  fd_cond:                                0
% 3.45/0.99  fd_pseudo_cond:                         0
% 3.45/0.99  ac_symbols:                             0
% 3.45/0.99  
% 3.45/0.99  ------ Propositional Solver
% 3.45/0.99  
% 3.45/0.99  prop_solver_calls:                      28
% 3.45/0.99  prop_fast_solver_calls:                 1104
% 3.45/0.99  smt_solver_calls:                       0
% 3.45/0.99  smt_fast_solver_calls:                  0
% 3.45/0.99  prop_num_of_clauses:                    5448
% 3.45/0.99  prop_preprocess_simplified:             12673
% 3.45/0.99  prop_fo_subsumed:                       47
% 3.45/0.99  prop_solver_time:                       0.
% 3.45/0.99  smt_solver_time:                        0.
% 3.45/0.99  smt_fast_solver_time:                   0.
% 3.45/0.99  prop_fast_solver_time:                  0.
% 3.45/0.99  prop_unsat_core_time:                   0.
% 3.45/0.99  
% 3.45/0.99  ------ QBF
% 3.45/0.99  
% 3.45/0.99  qbf_q_res:                              0
% 3.45/0.99  qbf_num_tautologies:                    0
% 3.45/0.99  qbf_prep_cycles:                        0
% 3.45/0.99  
% 3.45/0.99  ------ BMC1
% 3.45/0.99  
% 3.45/0.99  bmc1_current_bound:                     -1
% 3.45/0.99  bmc1_last_solved_bound:                 -1
% 3.45/0.99  bmc1_unsat_core_size:                   -1
% 3.45/0.99  bmc1_unsat_core_parents_size:           -1
% 3.45/0.99  bmc1_merge_next_fun:                    0
% 3.45/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.45/0.99  
% 3.45/0.99  ------ Instantiation
% 3.45/0.99  
% 3.45/0.99  inst_num_of_clauses:                    1460
% 3.45/0.99  inst_num_in_passive:                    783
% 3.45/0.99  inst_num_in_active:                     512
% 3.45/0.99  inst_num_in_unprocessed:                165
% 3.45/0.99  inst_num_of_loops:                      620
% 3.45/0.99  inst_num_of_learning_restarts:          0
% 3.45/0.99  inst_num_moves_active_passive:          106
% 3.45/0.99  inst_lit_activity:                      0
% 3.45/0.99  inst_lit_activity_moves:                0
% 3.45/0.99  inst_num_tautologies:                   0
% 3.45/0.99  inst_num_prop_implied:                  0
% 3.45/0.99  inst_num_existing_simplified:           0
% 3.45/0.99  inst_num_eq_res_simplified:             0
% 3.45/0.99  inst_num_child_elim:                    0
% 3.45/0.99  inst_num_of_dismatching_blockings:      1472
% 3.45/0.99  inst_num_of_non_proper_insts:           1538
% 3.45/0.99  inst_num_of_duplicates:                 0
% 3.45/0.99  inst_inst_num_from_inst_to_res:         0
% 3.45/0.99  inst_dismatching_checking_time:         0.
% 3.45/0.99  
% 3.45/0.99  ------ Resolution
% 3.45/0.99  
% 3.45/0.99  res_num_of_clauses:                     0
% 3.45/0.99  res_num_in_passive:                     0
% 3.45/0.99  res_num_in_active:                      0
% 3.45/0.99  res_num_of_loops:                       127
% 3.45/0.99  res_forward_subset_subsumed:            87
% 3.45/0.99  res_backward_subset_subsumed:           0
% 3.45/0.99  res_forward_subsumed:                   0
% 3.45/0.99  res_backward_subsumed:                  0
% 3.45/0.99  res_forward_subsumption_resolution:     1
% 3.45/0.99  res_backward_subsumption_resolution:    0
% 3.45/0.99  res_clause_to_clause_subsumption:       1215
% 3.45/0.99  res_orphan_elimination:                 0
% 3.45/0.99  res_tautology_del:                      45
% 3.45/0.99  res_num_eq_res_simplified:              0
% 3.45/0.99  res_num_sel_changes:                    0
% 3.45/0.99  res_moves_from_active_to_pass:          0
% 3.45/0.99  
% 3.45/0.99  ------ Superposition
% 3.45/0.99  
% 3.45/0.99  sup_time_total:                         0.
% 3.45/0.99  sup_time_generating:                    0.
% 3.45/0.99  sup_time_sim_full:                      0.
% 3.45/0.99  sup_time_sim_immed:                     0.
% 3.45/0.99  
% 3.45/0.99  sup_num_of_clauses:                     379
% 3.45/0.99  sup_num_in_active:                      123
% 3.45/0.99  sup_num_in_passive:                     256
% 3.45/0.99  sup_num_of_loops:                       122
% 3.45/0.99  sup_fw_superposition:                   352
% 3.45/0.99  sup_bw_superposition:                   151
% 3.45/0.99  sup_immediate_simplified:               156
% 3.45/0.99  sup_given_eliminated:                   0
% 3.45/0.99  comparisons_done:                       0
% 3.45/0.99  comparisons_avoided:                    0
% 3.45/0.99  
% 3.45/0.99  ------ Simplifications
% 3.45/0.99  
% 3.45/0.99  
% 3.45/0.99  sim_fw_subset_subsumed:                 62
% 3.45/0.99  sim_bw_subset_subsumed:                 3
% 3.45/0.99  sim_fw_subsumed:                        6
% 3.45/0.99  sim_bw_subsumed:                        4
% 3.45/0.99  sim_fw_subsumption_res:                 2
% 3.45/0.99  sim_bw_subsumption_res:                 0
% 3.45/0.99  sim_tautology_del:                      16
% 3.45/0.99  sim_eq_tautology_del:                   8
% 3.45/0.99  sim_eq_res_simp:                        0
% 3.45/0.99  sim_fw_demodulated:                     0
% 3.45/0.99  sim_bw_demodulated:                     0
% 3.45/0.99  sim_light_normalised:                   84
% 3.45/0.99  sim_joinable_taut:                      0
% 3.45/0.99  sim_joinable_simp:                      0
% 3.45/0.99  sim_ac_normalised:                      0
% 3.45/0.99  sim_smt_subsumption:                    0
% 3.45/0.99  
%------------------------------------------------------------------------------
