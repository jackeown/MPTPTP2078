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

% Result     : Theorem 2.71s
% Output     : CNFRefutation 2.71s
% Verified   : 
% Statistics : Number of formulae       :  201 ( 939 expanded)
%              Number of clauses        :  116 ( 243 expanded)
%              Number of leaves         :   22 ( 308 expanded)
%              Depth                    :   19
%              Number of atoms          :  746 (5247 expanded)
%              Number of equality atoms :  116 ( 153 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tarski(X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f60,f58])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k2_tarski(X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f57,f61])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f87,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k2_tarski(X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f59,f58])).

fof(f15,axiom,(
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
    inference(ennf_transformation,[],[f15])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

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
    inference(nnf_transformation,[],[f37])).

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

fof(f17,conjecture,(
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

fof(f18,negated_conjecture,(
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
    inference(negated_conjecture,[],[f17])).

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
    inference(ennf_transformation,[],[f18])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f41,f53,f52,f51,f50])).

fof(f78,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f79,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f80,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f28])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f84,plain,(
    ~ m1_subset_1(k2_xboole_0(sK3,sK4),u1_struct_0(k9_yellow_6(sK1,sK2))) ),
    inference(cnf_transformation,[],[f54])).

fof(f90,plain,(
    ~ m1_subset_1(k3_tarski(k2_tarski(sK3,sK4)),u1_struct_0(k9_yellow_6(sK1,sK2))) ),
    inference(definition_unfolding,[],[f84,f61])).

fof(f81,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f54])).

fof(f82,plain,(
    m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK1,sK2))) ),
    inference(cnf_transformation,[],[f54])).

fof(f83,plain,(
    m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK1,sK2))) ),
    inference(cnf_transformation,[],[f54])).

fof(f16,axiom,(
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
    inference(ennf_transformation,[],[f16])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X2,X0,X1)
              | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

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

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

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

fof(f14,axiom,(
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
    inference(ennf_transformation,[],[f14])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ m1_connsp_2(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f43,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f42])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f43,f44])).

fof(f55,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f6,axiom,(
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
    inference(ennf_transformation,[],[f6])).

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

fof(f64,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_pre_topc(X2,X0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_xboole_0(X1,X2),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v3_pre_topc(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v3_pre_topc(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(k3_tarski(k2_tarski(X1,X2)),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(definition_unfolding,[],[f71,f61])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f23])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k2_tarski(X1,X2)) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f67,f61])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f21])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_3,plain,
    ( r1_tarski(k2_tarski(X0,X0),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_809,plain,
    ( r1_tarski(k2_tarski(X0_48,X0_48),X1_48)
    | ~ r2_hidden(X0_48,X1_48) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1384,plain,
    ( r1_tarski(k2_tarski(X0_48,X0_48),X1_48) = iProver_top
    | r2_hidden(X0_48,X1_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_809])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k3_tarski(k2_tarski(X2,X1))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_810,plain,
    ( ~ r1_tarski(X0_50,X0_48)
    | r1_tarski(X0_50,k3_tarski(k2_tarski(X1_48,X0_48))) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1383,plain,
    ( r1_tarski(X0_50,X0_48) != iProver_top
    | r1_tarski(X0_50,k3_tarski(k2_tarski(X1_48,X0_48))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_810])).

cnf(c_4,plain,
    ( ~ r1_tarski(k2_tarski(X0,X0),X1)
    | r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_808,plain,
    ( ~ r1_tarski(k2_tarski(X0_48,X0_48),X1_48)
    | r2_hidden(X0_48,X1_48) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1385,plain,
    ( r1_tarski(k2_tarski(X0_48,X0_48),X1_48) != iProver_top
    | r2_hidden(X0_48,X1_48) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_808])).

cnf(c_2500,plain,
    ( r1_tarski(k2_tarski(X0_48,X0_48),X1_48) != iProver_top
    | r2_hidden(X0_48,k3_tarski(k2_tarski(X2_48,X1_48))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1383,c_1385])).

cnf(c_4305,plain,
    ( r2_hidden(X0_48,X1_48) != iProver_top
    | r2_hidden(X0_48,k3_tarski(k2_tarski(X2_48,X1_48))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1384,c_2500])).

cnf(c_17,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_27,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_513,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_27])).

cnf(c_514,plain,
    ( ~ v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X1,X0)
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK1,X1)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_513])).

cnf(c_26,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_25,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_518,plain,
    ( ~ v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X1,X0)
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK1,X1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_514,c_26,c_25])).

cnf(c_13,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_534,plain,
    ( ~ v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X1,X0)
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK1,X1))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_518,c_13])).

cnf(c_792,plain,
    ( ~ v3_pre_topc(X0_48,sK1)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X1_48,X0_48)
    | r2_hidden(X0_48,u1_struct_0(k9_yellow_6(sK1,X1_48))) ),
    inference(subtyping,[status(esa)],[c_534])).

cnf(c_1401,plain,
    ( v3_pre_topc(X0_48,sK1) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(X1_48,X0_48) != iProver_top
    | r2_hidden(X0_48,u1_struct_0(k9_yellow_6(sK1,X1_48))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_792])).

cnf(c_11,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_802,plain,
    ( m1_subset_1(X0_48,X1_48)
    | ~ r2_hidden(X0_48,X1_48) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1391,plain,
    ( m1_subset_1(X0_48,X1_48) = iProver_top
    | r2_hidden(X0_48,X1_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_802])).

cnf(c_4176,plain,
    ( v3_pre_topc(X0_48,sK1) != iProver_top
    | m1_subset_1(X0_48,u1_struct_0(k9_yellow_6(sK1,X1_48))) = iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(X1_48,X0_48) != iProver_top ),
    inference(superposition,[status(thm)],[c_1401,c_1391])).

cnf(c_21,negated_conjecture,
    ( ~ m1_subset_1(k3_tarski(k2_tarski(sK3,sK4)),u1_struct_0(k9_yellow_6(sK1,sK2))) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_800,negated_conjecture,
    ( ~ m1_subset_1(k3_tarski(k2_tarski(sK3,sK4)),u1_struct_0(k9_yellow_6(sK1,sK2))) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1393,plain,
    ( m1_subset_1(k3_tarski(k2_tarski(sK3,sK4)),u1_struct_0(k9_yellow_6(sK1,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_800])).

cnf(c_7934,plain,
    ( v3_pre_topc(k3_tarski(k2_tarski(sK3,sK4)),sK1) != iProver_top
    | m1_subset_1(k3_tarski(k2_tarski(sK3,sK4)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(sK2,k3_tarski(k2_tarski(sK3,sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4176,c_1393])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_31,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK1,sK2))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_32,plain,
    ( m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK1,sK2))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_33,plain,
    ( m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_20,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(X1,X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_15,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_386,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(resolution,[status(thm)],[c_20,c_15])).

cnf(c_423,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_386,c_27])).

cnf(c_424,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK1,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_423])).

cnf(c_428,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK1,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_424,c_26,c_25])).

cnf(c_796,plain,
    ( ~ m1_subset_1(X0_48,u1_struct_0(k9_yellow_6(sK1,X1_48)))
    | ~ m1_subset_1(X1_48,u1_struct_0(sK1))
    | m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subtyping,[status(esa)],[c_428])).

cnf(c_1565,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK1,sK2)))
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_796])).

cnf(c_1566,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK1,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1565])).

cnf(c_1568,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK1,sK2)))
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_796])).

cnf(c_1569,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK1,sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1568])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_805,plain,
    ( ~ m1_subset_1(X0_48,X1_48)
    | r2_hidden(X0_48,X1_48)
    | v1_xboole_0(X1_48) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1581,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK1,sK2)))
    | r2_hidden(sK4,u1_struct_0(k9_yellow_6(sK1,sK2)))
    | v1_xboole_0(u1_struct_0(k9_yellow_6(sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_805])).

cnf(c_1582,plain,
    ( m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK1,sK2))) != iProver_top
    | r2_hidden(sK4,u1_struct_0(k9_yellow_6(sK1,sK2))) = iProver_top
    | v1_xboole_0(u1_struct_0(k9_yellow_6(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1581])).

cnf(c_1584,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK1,sK2)))
    | r2_hidden(sK3,u1_struct_0(k9_yellow_6(sK1,sK2)))
    | v1_xboole_0(u1_struct_0(k9_yellow_6(sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_805])).

cnf(c_1585,plain,
    ( m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK1,sK2))) != iProver_top
    | r2_hidden(sK3,u1_struct_0(k9_yellow_6(sK1,sK2))) = iProver_top
    | v1_xboole_0(u1_struct_0(k9_yellow_6(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1584])).

cnf(c_18,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_489,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_27])).

cnf(c_490,plain,
    ( v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(sK1,X1)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_489])).

cnf(c_494,plain,
    ( v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(sK1,X1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_490,c_26,c_25])).

cnf(c_793,plain,
    ( v3_pre_topc(X0_48,sK1)
    | ~ m1_subset_1(X1_48,u1_struct_0(sK1))
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X0_48,u1_struct_0(k9_yellow_6(sK1,X1_48))) ),
    inference(subtyping,[status(esa)],[c_494])).

cnf(c_1651,plain,
    ( v3_pre_topc(sK4,sK1)
    | ~ m1_subset_1(X0_48,u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK4,u1_struct_0(k9_yellow_6(sK1,X0_48))) ),
    inference(instantiation,[status(thm)],[c_793])).

cnf(c_1652,plain,
    ( v3_pre_topc(sK4,sK1) = iProver_top
    | m1_subset_1(X0_48,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(sK4,u1_struct_0(k9_yellow_6(sK1,X0_48))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1651])).

cnf(c_1654,plain,
    ( v3_pre_topc(sK4,sK1) = iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(sK4,u1_struct_0(k9_yellow_6(sK1,sK2))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1652])).

cnf(c_1677,plain,
    ( v3_pre_topc(sK3,sK1)
    | ~ m1_subset_1(X0_48,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK3,u1_struct_0(k9_yellow_6(sK1,X0_48))) ),
    inference(instantiation,[status(thm)],[c_793])).

cnf(c_1678,plain,
    ( v3_pre_topc(sK3,sK1) = iProver_top
    | m1_subset_1(X0_48,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(sK3,u1_struct_0(k9_yellow_6(sK1,X0_48))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1677])).

cnf(c_1680,plain,
    ( v3_pre_topc(sK3,sK1) = iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(sK3,u1_struct_0(k9_yellow_6(sK1,sK2))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1678])).

cnf(c_799,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK1,sK2))) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1394,plain,
    ( m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_799])).

cnf(c_16,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X2,X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_160,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_connsp_2(X0,X1,X2)
    | r2_hidden(X2,X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_16,c_15])).

cnf(c_161,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_160])).

cnf(c_363,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
    | r2_hidden(X0,X2)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(resolution,[status(thm)],[c_20,c_161])).

cnf(c_444,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
    | r2_hidden(X0,X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_363,c_27])).

cnf(c_445,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK1,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | r2_hidden(X1,X0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_444])).

cnf(c_449,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK1,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | r2_hidden(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_445,c_26,c_25])).

cnf(c_795,plain,
    ( ~ m1_subset_1(X0_48,u1_struct_0(k9_yellow_6(sK1,X1_48)))
    | ~ m1_subset_1(X1_48,u1_struct_0(sK1))
    | r2_hidden(X1_48,X0_48) ),
    inference(subtyping,[status(esa)],[c_449])).

cnf(c_1398,plain,
    ( m1_subset_1(X0_48,u1_struct_0(k9_yellow_6(sK1,X1_48))) != iProver_top
    | m1_subset_1(X1_48,u1_struct_0(sK1)) != iProver_top
    | r2_hidden(X1_48,X0_48) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_795])).

cnf(c_1628,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | r2_hidden(sK2,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1394,c_1398])).

cnf(c_1571,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK1,sK2)))
    | r2_hidden(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_795])).

cnf(c_1572,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK1,sK2))) != iProver_top
    | r2_hidden(sK2,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1571])).

cnf(c_1641,plain,
    ( r2_hidden(sK2,sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1628,c_31,c_33,c_1572])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_811,plain,
    ( ~ r2_hidden(X0_48,X1_48)
    | ~ v1_xboole_0(X1_48) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1382,plain,
    ( r2_hidden(X0_48,X1_48) != iProver_top
    | v1_xboole_0(X1_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_811])).

cnf(c_1993,plain,
    ( v1_xboole_0(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1641,c_1382])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_806,plain,
    ( ~ m1_subset_1(X0_48,X1_48)
    | ~ v1_xboole_0(X1_48)
    | v1_xboole_0(X0_48) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1761,plain,
    ( ~ m1_subset_1(X0_48,u1_struct_0(k9_yellow_6(sK1,sK2)))
    | v1_xboole_0(X0_48)
    | ~ v1_xboole_0(u1_struct_0(k9_yellow_6(sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_806])).

cnf(c_2027,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK1,sK2)))
    | ~ v1_xboole_0(u1_struct_0(k9_yellow_6(sK1,sK2)))
    | v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_1761])).

cnf(c_2028,plain,
    ( m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK1,sK2))) != iProver_top
    | v1_xboole_0(u1_struct_0(k9_yellow_6(sK1,sK2))) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2027])).

cnf(c_14,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ v3_pre_topc(X2,X1)
    | v3_pre_topc(k3_tarski(k2_tarski(X2,X0)),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_565,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ v3_pre_topc(X2,X1)
    | v3_pre_topc(k3_tarski(k2_tarski(X2,X0)),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_25])).

cnf(c_566,plain,
    ( ~ v3_pre_topc(X0,sK1)
    | ~ v3_pre_topc(X1,sK1)
    | v3_pre_topc(k3_tarski(k2_tarski(X1,X0)),sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_565])).

cnf(c_570,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v3_pre_topc(k3_tarski(k2_tarski(X1,X0)),sK1)
    | ~ v3_pre_topc(X1,sK1)
    | ~ v3_pre_topc(X0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_566,c_26])).

cnf(c_571,plain,
    ( ~ v3_pre_topc(X0,sK1)
    | ~ v3_pre_topc(X1,sK1)
    | v3_pre_topc(k3_tarski(k2_tarski(X1,X0)),sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(renaming,[status(thm)],[c_570])).

cnf(c_791,plain,
    ( ~ v3_pre_topc(X0_48,sK1)
    | ~ v3_pre_topc(X1_48,sK1)
    | v3_pre_topc(k3_tarski(k2_tarski(X1_48,X0_48)),sK1)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1_48,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subtyping,[status(esa)],[c_571])).

cnf(c_2376,plain,
    ( ~ v3_pre_topc(X0_48,sK1)
    | v3_pre_topc(k3_tarski(k2_tarski(X0_48,sK4)),sK1)
    | ~ v3_pre_topc(sK4,sK1)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_791])).

cnf(c_3933,plain,
    ( v3_pre_topc(k3_tarski(k2_tarski(sK3,sK4)),sK1)
    | ~ v3_pre_topc(sK4,sK1)
    | ~ v3_pre_topc(sK3,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_2376])).

cnf(c_3934,plain,
    ( v3_pre_topc(k3_tarski(k2_tarski(sK3,sK4)),sK1) = iProver_top
    | v3_pre_topc(sK4,sK1) != iProver_top
    | v3_pre_topc(sK3,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3933])).

cnf(c_1397,plain,
    ( m1_subset_1(X0_48,u1_struct_0(k9_yellow_6(sK1,X1_48))) != iProver_top
    | m1_subset_1(X1_48,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_796])).

cnf(c_1747,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1394,c_1397])).

cnf(c_2088,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1747,c_31,c_33,c_1566])).

cnf(c_798,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK1,sK2))) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_1395,plain,
    ( m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_798])).

cnf(c_1748,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1395,c_1397])).

cnf(c_2285,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1748,c_31,c_32,c_1569])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X2,X0) = k3_tarski(k2_tarski(X2,X0)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_803,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(X1_48))
    | ~ m1_subset_1(X2_48,k1_zfmisc_1(X1_48))
    | k4_subset_1(X1_48,X2_48,X0_48) = k3_tarski(k2_tarski(X2_48,X0_48)) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1390,plain,
    ( k4_subset_1(X0_48,X1_48,X2_48) = k3_tarski(k2_tarski(X1_48,X2_48))
    | m1_subset_1(X1_48,k1_zfmisc_1(X0_48)) != iProver_top
    | m1_subset_1(X2_48,k1_zfmisc_1(X0_48)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_803])).

cnf(c_3311,plain,
    ( k4_subset_1(u1_struct_0(sK1),sK3,X0_48) = k3_tarski(k2_tarski(sK3,X0_48))
    | m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2285,c_1390])).

cnf(c_3994,plain,
    ( k4_subset_1(u1_struct_0(sK1),sK3,sK4) = k3_tarski(k2_tarski(sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_2088,c_3311])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | m1_subset_1(k4_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_804,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(X1_48))
    | ~ m1_subset_1(X2_48,k1_zfmisc_1(X1_48))
    | m1_subset_1(k4_subset_1(X1_48,X2_48,X0_48),k1_zfmisc_1(X1_48)) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1389,plain,
    ( m1_subset_1(X0_48,k1_zfmisc_1(X1_48)) != iProver_top
    | m1_subset_1(X2_48,k1_zfmisc_1(X1_48)) != iProver_top
    | m1_subset_1(k4_subset_1(X1_48,X0_48,X2_48),k1_zfmisc_1(X1_48)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_804])).

cnf(c_4080,plain,
    ( m1_subset_1(k3_tarski(k2_tarski(sK3,sK4)),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3994,c_1389])).

cnf(c_7958,plain,
    ( r2_hidden(sK2,k3_tarski(k2_tarski(sK3,sK4))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7934,c_31,c_32,c_33,c_1566,c_1569,c_1582,c_1585,c_1654,c_1680,c_1993,c_2028,c_3934,c_4080])).

cnf(c_7963,plain,
    ( r2_hidden(sK2,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4305,c_7958])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7963,c_1572,c_33,c_31])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:50:56 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  % Running in FOF mode
% 2.71/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.71/1.01  
% 2.71/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.71/1.01  
% 2.71/1.01  ------  iProver source info
% 2.71/1.01  
% 2.71/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.71/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.71/1.01  git: non_committed_changes: false
% 2.71/1.01  git: last_make_outside_of_git: false
% 2.71/1.01  
% 2.71/1.01  ------ 
% 2.71/1.01  
% 2.71/1.01  ------ Input Options
% 2.71/1.01  
% 2.71/1.01  --out_options                           all
% 2.71/1.01  --tptp_safe_out                         true
% 2.71/1.01  --problem_path                          ""
% 2.71/1.01  --include_path                          ""
% 2.71/1.01  --clausifier                            res/vclausify_rel
% 2.71/1.01  --clausifier_options                    --mode clausify
% 2.71/1.01  --stdin                                 false
% 2.71/1.01  --stats_out                             all
% 2.71/1.01  
% 2.71/1.01  ------ General Options
% 2.71/1.01  
% 2.71/1.01  --fof                                   false
% 2.71/1.01  --time_out_real                         305.
% 2.71/1.01  --time_out_virtual                      -1.
% 2.71/1.01  --symbol_type_check                     false
% 2.71/1.01  --clausify_out                          false
% 2.71/1.01  --sig_cnt_out                           false
% 2.71/1.01  --trig_cnt_out                          false
% 2.71/1.01  --trig_cnt_out_tolerance                1.
% 2.71/1.01  --trig_cnt_out_sk_spl                   false
% 2.71/1.01  --abstr_cl_out                          false
% 2.71/1.01  
% 2.71/1.01  ------ Global Options
% 2.71/1.01  
% 2.71/1.01  --schedule                              default
% 2.71/1.01  --add_important_lit                     false
% 2.71/1.01  --prop_solver_per_cl                    1000
% 2.71/1.01  --min_unsat_core                        false
% 2.71/1.01  --soft_assumptions                      false
% 2.71/1.01  --soft_lemma_size                       3
% 2.71/1.01  --prop_impl_unit_size                   0
% 2.71/1.01  --prop_impl_unit                        []
% 2.71/1.01  --share_sel_clauses                     true
% 2.71/1.01  --reset_solvers                         false
% 2.71/1.01  --bc_imp_inh                            [conj_cone]
% 2.71/1.01  --conj_cone_tolerance                   3.
% 2.71/1.01  --extra_neg_conj                        none
% 2.71/1.01  --large_theory_mode                     true
% 2.71/1.01  --prolific_symb_bound                   200
% 2.71/1.01  --lt_threshold                          2000
% 2.71/1.01  --clause_weak_htbl                      true
% 2.71/1.01  --gc_record_bc_elim                     false
% 2.71/1.01  
% 2.71/1.01  ------ Preprocessing Options
% 2.71/1.01  
% 2.71/1.01  --preprocessing_flag                    true
% 2.71/1.01  --time_out_prep_mult                    0.1
% 2.71/1.01  --splitting_mode                        input
% 2.71/1.01  --splitting_grd                         true
% 2.71/1.01  --splitting_cvd                         false
% 2.71/1.01  --splitting_cvd_svl                     false
% 2.71/1.01  --splitting_nvd                         32
% 2.71/1.01  --sub_typing                            true
% 2.71/1.01  --prep_gs_sim                           true
% 2.71/1.01  --prep_unflatten                        true
% 2.71/1.01  --prep_res_sim                          true
% 2.71/1.01  --prep_upred                            true
% 2.71/1.01  --prep_sem_filter                       exhaustive
% 2.71/1.01  --prep_sem_filter_out                   false
% 2.71/1.01  --pred_elim                             true
% 2.71/1.01  --res_sim_input                         true
% 2.71/1.01  --eq_ax_congr_red                       true
% 2.71/1.01  --pure_diseq_elim                       true
% 2.71/1.01  --brand_transform                       false
% 2.71/1.01  --non_eq_to_eq                          false
% 2.71/1.01  --prep_def_merge                        true
% 2.71/1.01  --prep_def_merge_prop_impl              false
% 2.71/1.01  --prep_def_merge_mbd                    true
% 2.71/1.01  --prep_def_merge_tr_red                 false
% 2.71/1.01  --prep_def_merge_tr_cl                  false
% 2.71/1.01  --smt_preprocessing                     true
% 2.71/1.01  --smt_ac_axioms                         fast
% 2.71/1.01  --preprocessed_out                      false
% 2.71/1.01  --preprocessed_stats                    false
% 2.71/1.01  
% 2.71/1.01  ------ Abstraction refinement Options
% 2.71/1.01  
% 2.71/1.01  --abstr_ref                             []
% 2.71/1.01  --abstr_ref_prep                        false
% 2.71/1.01  --abstr_ref_until_sat                   false
% 2.71/1.01  --abstr_ref_sig_restrict                funpre
% 2.71/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.71/1.01  --abstr_ref_under                       []
% 2.71/1.01  
% 2.71/1.01  ------ SAT Options
% 2.71/1.01  
% 2.71/1.01  --sat_mode                              false
% 2.71/1.01  --sat_fm_restart_options                ""
% 2.71/1.01  --sat_gr_def                            false
% 2.71/1.01  --sat_epr_types                         true
% 2.71/1.01  --sat_non_cyclic_types                  false
% 2.71/1.01  --sat_finite_models                     false
% 2.71/1.01  --sat_fm_lemmas                         false
% 2.71/1.01  --sat_fm_prep                           false
% 2.71/1.01  --sat_fm_uc_incr                        true
% 2.71/1.01  --sat_out_model                         small
% 2.71/1.01  --sat_out_clauses                       false
% 2.71/1.01  
% 2.71/1.01  ------ QBF Options
% 2.71/1.01  
% 2.71/1.01  --qbf_mode                              false
% 2.71/1.01  --qbf_elim_univ                         false
% 2.71/1.01  --qbf_dom_inst                          none
% 2.71/1.01  --qbf_dom_pre_inst                      false
% 2.71/1.01  --qbf_sk_in                             false
% 2.71/1.01  --qbf_pred_elim                         true
% 2.71/1.01  --qbf_split                             512
% 2.71/1.01  
% 2.71/1.01  ------ BMC1 Options
% 2.71/1.01  
% 2.71/1.01  --bmc1_incremental                      false
% 2.71/1.01  --bmc1_axioms                           reachable_all
% 2.71/1.01  --bmc1_min_bound                        0
% 2.71/1.01  --bmc1_max_bound                        -1
% 2.71/1.01  --bmc1_max_bound_default                -1
% 2.71/1.01  --bmc1_symbol_reachability              true
% 2.71/1.01  --bmc1_property_lemmas                  false
% 2.71/1.01  --bmc1_k_induction                      false
% 2.71/1.01  --bmc1_non_equiv_states                 false
% 2.71/1.01  --bmc1_deadlock                         false
% 2.71/1.01  --bmc1_ucm                              false
% 2.71/1.01  --bmc1_add_unsat_core                   none
% 2.71/1.01  --bmc1_unsat_core_children              false
% 2.71/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.71/1.01  --bmc1_out_stat                         full
% 2.71/1.01  --bmc1_ground_init                      false
% 2.71/1.01  --bmc1_pre_inst_next_state              false
% 2.71/1.01  --bmc1_pre_inst_state                   false
% 2.71/1.01  --bmc1_pre_inst_reach_state             false
% 2.71/1.01  --bmc1_out_unsat_core                   false
% 2.71/1.01  --bmc1_aig_witness_out                  false
% 2.71/1.01  --bmc1_verbose                          false
% 2.71/1.01  --bmc1_dump_clauses_tptp                false
% 2.71/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.71/1.01  --bmc1_dump_file                        -
% 2.71/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.71/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.71/1.01  --bmc1_ucm_extend_mode                  1
% 2.71/1.01  --bmc1_ucm_init_mode                    2
% 2.71/1.01  --bmc1_ucm_cone_mode                    none
% 2.71/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.71/1.01  --bmc1_ucm_relax_model                  4
% 2.71/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.71/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.71/1.01  --bmc1_ucm_layered_model                none
% 2.71/1.01  --bmc1_ucm_max_lemma_size               10
% 2.71/1.01  
% 2.71/1.01  ------ AIG Options
% 2.71/1.01  
% 2.71/1.01  --aig_mode                              false
% 2.71/1.01  
% 2.71/1.01  ------ Instantiation Options
% 2.71/1.01  
% 2.71/1.01  --instantiation_flag                    true
% 2.71/1.01  --inst_sos_flag                         false
% 2.71/1.01  --inst_sos_phase                        true
% 2.71/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.71/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.71/1.01  --inst_lit_sel_side                     num_symb
% 2.71/1.01  --inst_solver_per_active                1400
% 2.71/1.01  --inst_solver_calls_frac                1.
% 2.71/1.01  --inst_passive_queue_type               priority_queues
% 2.71/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.71/1.01  --inst_passive_queues_freq              [25;2]
% 2.71/1.01  --inst_dismatching                      true
% 2.71/1.01  --inst_eager_unprocessed_to_passive     true
% 2.71/1.01  --inst_prop_sim_given                   true
% 2.71/1.01  --inst_prop_sim_new                     false
% 2.71/1.01  --inst_subs_new                         false
% 2.71/1.01  --inst_eq_res_simp                      false
% 2.71/1.01  --inst_subs_given                       false
% 2.71/1.01  --inst_orphan_elimination               true
% 2.71/1.01  --inst_learning_loop_flag               true
% 2.71/1.01  --inst_learning_start                   3000
% 2.71/1.01  --inst_learning_factor                  2
% 2.71/1.01  --inst_start_prop_sim_after_learn       3
% 2.71/1.01  --inst_sel_renew                        solver
% 2.71/1.01  --inst_lit_activity_flag                true
% 2.71/1.01  --inst_restr_to_given                   false
% 2.71/1.01  --inst_activity_threshold               500
% 2.71/1.01  --inst_out_proof                        true
% 2.71/1.01  
% 2.71/1.01  ------ Resolution Options
% 2.71/1.01  
% 2.71/1.01  --resolution_flag                       true
% 2.71/1.01  --res_lit_sel                           adaptive
% 2.71/1.01  --res_lit_sel_side                      none
% 2.71/1.01  --res_ordering                          kbo
% 2.71/1.01  --res_to_prop_solver                    active
% 2.71/1.01  --res_prop_simpl_new                    false
% 2.71/1.01  --res_prop_simpl_given                  true
% 2.71/1.01  --res_passive_queue_type                priority_queues
% 2.71/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.71/1.01  --res_passive_queues_freq               [15;5]
% 2.71/1.01  --res_forward_subs                      full
% 2.71/1.01  --res_backward_subs                     full
% 2.71/1.01  --res_forward_subs_resolution           true
% 2.71/1.01  --res_backward_subs_resolution          true
% 2.71/1.01  --res_orphan_elimination                true
% 2.71/1.01  --res_time_limit                        2.
% 2.71/1.01  --res_out_proof                         true
% 2.71/1.01  
% 2.71/1.01  ------ Superposition Options
% 2.71/1.01  
% 2.71/1.01  --superposition_flag                    true
% 2.71/1.01  --sup_passive_queue_type                priority_queues
% 2.71/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.71/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.71/1.01  --demod_completeness_check              fast
% 2.71/1.01  --demod_use_ground                      true
% 2.71/1.01  --sup_to_prop_solver                    passive
% 2.71/1.01  --sup_prop_simpl_new                    true
% 2.71/1.01  --sup_prop_simpl_given                  true
% 2.71/1.01  --sup_fun_splitting                     false
% 2.71/1.01  --sup_smt_interval                      50000
% 2.71/1.01  
% 2.71/1.01  ------ Superposition Simplification Setup
% 2.71/1.01  
% 2.71/1.01  --sup_indices_passive                   []
% 2.71/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.71/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.71/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.71/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.71/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.71/1.01  --sup_full_bw                           [BwDemod]
% 2.71/1.01  --sup_immed_triv                        [TrivRules]
% 2.71/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.71/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.71/1.01  --sup_immed_bw_main                     []
% 2.71/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.71/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.71/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.71/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.71/1.01  
% 2.71/1.01  ------ Combination Options
% 2.71/1.01  
% 2.71/1.01  --comb_res_mult                         3
% 2.71/1.01  --comb_sup_mult                         2
% 2.71/1.01  --comb_inst_mult                        10
% 2.71/1.01  
% 2.71/1.01  ------ Debug Options
% 2.71/1.01  
% 2.71/1.01  --dbg_backtrace                         false
% 2.71/1.01  --dbg_dump_prop_clauses                 false
% 2.71/1.01  --dbg_dump_prop_clauses_file            -
% 2.71/1.01  --dbg_out_stat                          false
% 2.71/1.01  ------ Parsing...
% 2.71/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.71/1.01  
% 2.71/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.71/1.01  
% 2.71/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.71/1.01  
% 2.71/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.71/1.01  ------ Proving...
% 2.71/1.01  ------ Problem Properties 
% 2.71/1.01  
% 2.71/1.01  
% 2.71/1.01  clauses                                 22
% 2.71/1.01  conjectures                             4
% 2.71/1.01  EPR                                     5
% 2.71/1.01  Horn                                    20
% 2.71/1.01  unary                                   4
% 2.71/1.01  binary                                  6
% 2.71/1.01  lits                                    57
% 2.71/1.01  lits eq                                 1
% 2.71/1.01  fd_pure                                 0
% 2.71/1.01  fd_pseudo                               0
% 2.71/1.01  fd_cond                                 0
% 2.71/1.01  fd_pseudo_cond                          0
% 2.71/1.01  AC symbols                              0
% 2.71/1.01  
% 2.71/1.01  ------ Schedule dynamic 5 is on 
% 2.71/1.01  
% 2.71/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.71/1.01  
% 2.71/1.01  
% 2.71/1.01  ------ 
% 2.71/1.01  Current options:
% 2.71/1.01  ------ 
% 2.71/1.01  
% 2.71/1.01  ------ Input Options
% 2.71/1.01  
% 2.71/1.01  --out_options                           all
% 2.71/1.01  --tptp_safe_out                         true
% 2.71/1.01  --problem_path                          ""
% 2.71/1.01  --include_path                          ""
% 2.71/1.01  --clausifier                            res/vclausify_rel
% 2.71/1.01  --clausifier_options                    --mode clausify
% 2.71/1.01  --stdin                                 false
% 2.71/1.01  --stats_out                             all
% 2.71/1.01  
% 2.71/1.01  ------ General Options
% 2.71/1.01  
% 2.71/1.01  --fof                                   false
% 2.71/1.01  --time_out_real                         305.
% 2.71/1.01  --time_out_virtual                      -1.
% 2.71/1.01  --symbol_type_check                     false
% 2.71/1.01  --clausify_out                          false
% 2.71/1.01  --sig_cnt_out                           false
% 2.71/1.01  --trig_cnt_out                          false
% 2.71/1.01  --trig_cnt_out_tolerance                1.
% 2.71/1.01  --trig_cnt_out_sk_spl                   false
% 2.71/1.01  --abstr_cl_out                          false
% 2.71/1.01  
% 2.71/1.01  ------ Global Options
% 2.71/1.01  
% 2.71/1.01  --schedule                              default
% 2.71/1.01  --add_important_lit                     false
% 2.71/1.01  --prop_solver_per_cl                    1000
% 2.71/1.01  --min_unsat_core                        false
% 2.71/1.01  --soft_assumptions                      false
% 2.71/1.01  --soft_lemma_size                       3
% 2.71/1.01  --prop_impl_unit_size                   0
% 2.71/1.01  --prop_impl_unit                        []
% 2.71/1.01  --share_sel_clauses                     true
% 2.71/1.01  --reset_solvers                         false
% 2.71/1.01  --bc_imp_inh                            [conj_cone]
% 2.71/1.01  --conj_cone_tolerance                   3.
% 2.71/1.01  --extra_neg_conj                        none
% 2.71/1.01  --large_theory_mode                     true
% 2.71/1.01  --prolific_symb_bound                   200
% 2.71/1.01  --lt_threshold                          2000
% 2.71/1.01  --clause_weak_htbl                      true
% 2.71/1.01  --gc_record_bc_elim                     false
% 2.71/1.01  
% 2.71/1.01  ------ Preprocessing Options
% 2.71/1.01  
% 2.71/1.01  --preprocessing_flag                    true
% 2.71/1.01  --time_out_prep_mult                    0.1
% 2.71/1.01  --splitting_mode                        input
% 2.71/1.01  --splitting_grd                         true
% 2.71/1.01  --splitting_cvd                         false
% 2.71/1.01  --splitting_cvd_svl                     false
% 2.71/1.01  --splitting_nvd                         32
% 2.71/1.01  --sub_typing                            true
% 2.71/1.01  --prep_gs_sim                           true
% 2.71/1.01  --prep_unflatten                        true
% 2.71/1.01  --prep_res_sim                          true
% 2.71/1.01  --prep_upred                            true
% 2.71/1.01  --prep_sem_filter                       exhaustive
% 2.71/1.01  --prep_sem_filter_out                   false
% 2.71/1.01  --pred_elim                             true
% 2.71/1.01  --res_sim_input                         true
% 2.71/1.01  --eq_ax_congr_red                       true
% 2.71/1.01  --pure_diseq_elim                       true
% 2.71/1.01  --brand_transform                       false
% 2.71/1.01  --non_eq_to_eq                          false
% 2.71/1.01  --prep_def_merge                        true
% 2.71/1.01  --prep_def_merge_prop_impl              false
% 2.71/1.01  --prep_def_merge_mbd                    true
% 2.71/1.01  --prep_def_merge_tr_red                 false
% 2.71/1.01  --prep_def_merge_tr_cl                  false
% 2.71/1.01  --smt_preprocessing                     true
% 2.71/1.01  --smt_ac_axioms                         fast
% 2.71/1.01  --preprocessed_out                      false
% 2.71/1.01  --preprocessed_stats                    false
% 2.71/1.01  
% 2.71/1.01  ------ Abstraction refinement Options
% 2.71/1.01  
% 2.71/1.01  --abstr_ref                             []
% 2.71/1.01  --abstr_ref_prep                        false
% 2.71/1.01  --abstr_ref_until_sat                   false
% 2.71/1.01  --abstr_ref_sig_restrict                funpre
% 2.71/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.71/1.01  --abstr_ref_under                       []
% 2.71/1.01  
% 2.71/1.01  ------ SAT Options
% 2.71/1.01  
% 2.71/1.01  --sat_mode                              false
% 2.71/1.01  --sat_fm_restart_options                ""
% 2.71/1.01  --sat_gr_def                            false
% 2.71/1.01  --sat_epr_types                         true
% 2.71/1.01  --sat_non_cyclic_types                  false
% 2.71/1.01  --sat_finite_models                     false
% 2.71/1.01  --sat_fm_lemmas                         false
% 2.71/1.01  --sat_fm_prep                           false
% 2.71/1.01  --sat_fm_uc_incr                        true
% 2.71/1.01  --sat_out_model                         small
% 2.71/1.01  --sat_out_clauses                       false
% 2.71/1.01  
% 2.71/1.01  ------ QBF Options
% 2.71/1.01  
% 2.71/1.01  --qbf_mode                              false
% 2.71/1.01  --qbf_elim_univ                         false
% 2.71/1.01  --qbf_dom_inst                          none
% 2.71/1.01  --qbf_dom_pre_inst                      false
% 2.71/1.01  --qbf_sk_in                             false
% 2.71/1.01  --qbf_pred_elim                         true
% 2.71/1.01  --qbf_split                             512
% 2.71/1.01  
% 2.71/1.01  ------ BMC1 Options
% 2.71/1.01  
% 2.71/1.01  --bmc1_incremental                      false
% 2.71/1.01  --bmc1_axioms                           reachable_all
% 2.71/1.01  --bmc1_min_bound                        0
% 2.71/1.01  --bmc1_max_bound                        -1
% 2.71/1.01  --bmc1_max_bound_default                -1
% 2.71/1.01  --bmc1_symbol_reachability              true
% 2.71/1.01  --bmc1_property_lemmas                  false
% 2.71/1.01  --bmc1_k_induction                      false
% 2.71/1.01  --bmc1_non_equiv_states                 false
% 2.71/1.01  --bmc1_deadlock                         false
% 2.71/1.01  --bmc1_ucm                              false
% 2.71/1.01  --bmc1_add_unsat_core                   none
% 2.71/1.01  --bmc1_unsat_core_children              false
% 2.71/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.71/1.01  --bmc1_out_stat                         full
% 2.71/1.01  --bmc1_ground_init                      false
% 2.71/1.01  --bmc1_pre_inst_next_state              false
% 2.71/1.01  --bmc1_pre_inst_state                   false
% 2.71/1.01  --bmc1_pre_inst_reach_state             false
% 2.71/1.01  --bmc1_out_unsat_core                   false
% 2.71/1.01  --bmc1_aig_witness_out                  false
% 2.71/1.01  --bmc1_verbose                          false
% 2.71/1.01  --bmc1_dump_clauses_tptp                false
% 2.71/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.71/1.01  --bmc1_dump_file                        -
% 2.71/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.71/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.71/1.01  --bmc1_ucm_extend_mode                  1
% 2.71/1.01  --bmc1_ucm_init_mode                    2
% 2.71/1.01  --bmc1_ucm_cone_mode                    none
% 2.71/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.71/1.01  --bmc1_ucm_relax_model                  4
% 2.71/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.71/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.71/1.01  --bmc1_ucm_layered_model                none
% 2.71/1.01  --bmc1_ucm_max_lemma_size               10
% 2.71/1.01  
% 2.71/1.01  ------ AIG Options
% 2.71/1.01  
% 2.71/1.01  --aig_mode                              false
% 2.71/1.01  
% 2.71/1.01  ------ Instantiation Options
% 2.71/1.01  
% 2.71/1.01  --instantiation_flag                    true
% 2.71/1.01  --inst_sos_flag                         false
% 2.71/1.01  --inst_sos_phase                        true
% 2.71/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.71/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.71/1.01  --inst_lit_sel_side                     none
% 2.71/1.01  --inst_solver_per_active                1400
% 2.71/1.01  --inst_solver_calls_frac                1.
% 2.71/1.01  --inst_passive_queue_type               priority_queues
% 2.71/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.71/1.01  --inst_passive_queues_freq              [25;2]
% 2.71/1.01  --inst_dismatching                      true
% 2.71/1.01  --inst_eager_unprocessed_to_passive     true
% 2.71/1.01  --inst_prop_sim_given                   true
% 2.71/1.01  --inst_prop_sim_new                     false
% 2.71/1.01  --inst_subs_new                         false
% 2.71/1.01  --inst_eq_res_simp                      false
% 2.71/1.01  --inst_subs_given                       false
% 2.71/1.01  --inst_orphan_elimination               true
% 2.71/1.01  --inst_learning_loop_flag               true
% 2.71/1.01  --inst_learning_start                   3000
% 2.71/1.01  --inst_learning_factor                  2
% 2.71/1.01  --inst_start_prop_sim_after_learn       3
% 2.71/1.01  --inst_sel_renew                        solver
% 2.71/1.01  --inst_lit_activity_flag                true
% 2.71/1.01  --inst_restr_to_given                   false
% 2.71/1.01  --inst_activity_threshold               500
% 2.71/1.01  --inst_out_proof                        true
% 2.71/1.01  
% 2.71/1.01  ------ Resolution Options
% 2.71/1.01  
% 2.71/1.01  --resolution_flag                       false
% 2.71/1.01  --res_lit_sel                           adaptive
% 2.71/1.01  --res_lit_sel_side                      none
% 2.71/1.01  --res_ordering                          kbo
% 2.71/1.01  --res_to_prop_solver                    active
% 2.71/1.01  --res_prop_simpl_new                    false
% 2.71/1.01  --res_prop_simpl_given                  true
% 2.71/1.01  --res_passive_queue_type                priority_queues
% 2.71/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.71/1.01  --res_passive_queues_freq               [15;5]
% 2.71/1.01  --res_forward_subs                      full
% 2.71/1.01  --res_backward_subs                     full
% 2.71/1.01  --res_forward_subs_resolution           true
% 2.71/1.01  --res_backward_subs_resolution          true
% 2.71/1.01  --res_orphan_elimination                true
% 2.71/1.01  --res_time_limit                        2.
% 2.71/1.01  --res_out_proof                         true
% 2.71/1.01  
% 2.71/1.01  ------ Superposition Options
% 2.71/1.01  
% 2.71/1.01  --superposition_flag                    true
% 2.71/1.01  --sup_passive_queue_type                priority_queues
% 2.71/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.71/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.71/1.01  --demod_completeness_check              fast
% 2.71/1.01  --demod_use_ground                      true
% 2.71/1.01  --sup_to_prop_solver                    passive
% 2.71/1.01  --sup_prop_simpl_new                    true
% 2.71/1.01  --sup_prop_simpl_given                  true
% 2.71/1.01  --sup_fun_splitting                     false
% 2.71/1.01  --sup_smt_interval                      50000
% 2.71/1.01  
% 2.71/1.01  ------ Superposition Simplification Setup
% 2.71/1.01  
% 2.71/1.01  --sup_indices_passive                   []
% 2.71/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.71/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.71/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.71/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.71/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.71/1.01  --sup_full_bw                           [BwDemod]
% 2.71/1.01  --sup_immed_triv                        [TrivRules]
% 2.71/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.71/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.71/1.01  --sup_immed_bw_main                     []
% 2.71/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.71/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.71/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.71/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.71/1.01  
% 2.71/1.01  ------ Combination Options
% 2.71/1.01  
% 2.71/1.01  --comb_res_mult                         3
% 2.71/1.01  --comb_sup_mult                         2
% 2.71/1.01  --comb_inst_mult                        10
% 2.71/1.01  
% 2.71/1.01  ------ Debug Options
% 2.71/1.01  
% 2.71/1.01  --dbg_backtrace                         false
% 2.71/1.01  --dbg_dump_prop_clauses                 false
% 2.71/1.01  --dbg_dump_prop_clauses_file            -
% 2.71/1.01  --dbg_out_stat                          false
% 2.71/1.01  
% 2.71/1.01  
% 2.71/1.01  
% 2.71/1.01  
% 2.71/1.01  ------ Proving...
% 2.71/1.01  
% 2.71/1.01  
% 2.71/1.01  % SZS status Theorem for theBenchmark.p
% 2.71/1.01  
% 2.71/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.71/1.01  
% 2.71/1.01  fof(f4,axiom,(
% 2.71/1.01    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 2.71/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.71/1.01  
% 2.71/1.01  fof(f46,plain,(
% 2.71/1.01    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 2.71/1.01    inference(nnf_transformation,[],[f4])).
% 2.71/1.01  
% 2.71/1.01  fof(f60,plain,(
% 2.71/1.01    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 2.71/1.01    inference(cnf_transformation,[],[f46])).
% 2.71/1.01  
% 2.71/1.01  fof(f3,axiom,(
% 2.71/1.01    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.71/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.71/1.01  
% 2.71/1.01  fof(f58,plain,(
% 2.71/1.01    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.71/1.01    inference(cnf_transformation,[],[f3])).
% 2.71/1.01  
% 2.71/1.01  fof(f86,plain,(
% 2.71/1.01    ( ! [X0,X1] : (r1_tarski(k2_tarski(X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 2.71/1.01    inference(definition_unfolding,[],[f60,f58])).
% 2.71/1.01  
% 2.71/1.01  fof(f2,axiom,(
% 2.71/1.01    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 2.71/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.71/1.01  
% 2.71/1.01  fof(f19,plain,(
% 2.71/1.01    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 2.71/1.01    inference(ennf_transformation,[],[f2])).
% 2.71/1.01  
% 2.71/1.01  fof(f57,plain,(
% 2.71/1.01    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 2.71/1.01    inference(cnf_transformation,[],[f19])).
% 2.71/1.01  
% 2.71/1.01  fof(f5,axiom,(
% 2.71/1.01    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.71/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.71/1.01  
% 2.71/1.01  fof(f61,plain,(
% 2.71/1.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.71/1.01    inference(cnf_transformation,[],[f5])).
% 2.71/1.01  
% 2.71/1.01  fof(f85,plain,(
% 2.71/1.01    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X2,X1))) | ~r1_tarski(X0,X1)) )),
% 2.71/1.01    inference(definition_unfolding,[],[f57,f61])).
% 2.71/1.01  
% 2.71/1.01  fof(f59,plain,(
% 2.71/1.01    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)) )),
% 2.71/1.01    inference(cnf_transformation,[],[f46])).
% 2.71/1.01  
% 2.71/1.01  fof(f87,plain,(
% 2.71/1.01    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k2_tarski(X0,X0),X1)) )),
% 2.71/1.01    inference(definition_unfolding,[],[f59,f58])).
% 2.71/1.01  
% 2.71/1.01  fof(f15,axiom,(
% 2.71/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))))))),
% 2.71/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.71/1.01  
% 2.71/1.01  fof(f36,plain,(
% 2.71/1.01    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.71/1.01    inference(ennf_transformation,[],[f15])).
% 2.71/1.01  
% 2.71/1.01  fof(f37,plain,(
% 2.71/1.01    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.71/1.01    inference(flattening,[],[f36])).
% 2.71/1.01  
% 2.71/1.01  fof(f48,plain,(
% 2.71/1.01    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | (~v3_pre_topc(X2,X0) | ~r2_hidden(X1,X2))) & ((v3_pre_topc(X2,X0) & r2_hidden(X1,X2)) | ~r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.71/1.01    inference(nnf_transformation,[],[f37])).
% 2.71/1.01  
% 2.71/1.01  fof(f49,plain,(
% 2.71/1.01    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~v3_pre_topc(X2,X0) | ~r2_hidden(X1,X2)) & ((v3_pre_topc(X2,X0) & r2_hidden(X1,X2)) | ~r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.71/1.01    inference(flattening,[],[f48])).
% 2.71/1.01  
% 2.71/1.01  fof(f76,plain,(
% 2.71/1.01    ( ! [X2,X0,X1] : (r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~v3_pre_topc(X2,X0) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.71/1.01    inference(cnf_transformation,[],[f49])).
% 2.71/1.01  
% 2.71/1.01  fof(f17,conjecture,(
% 2.71/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) => m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))))))),
% 2.71/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.71/1.01  
% 2.71/1.01  fof(f18,negated_conjecture,(
% 2.71/1.01    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) => m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))))))),
% 2.71/1.01    inference(negated_conjecture,[],[f17])).
% 2.71/1.01  
% 2.71/1.01  fof(f40,plain,(
% 2.71/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.71/1.01    inference(ennf_transformation,[],[f18])).
% 2.71/1.01  
% 2.71/1.01  fof(f41,plain,(
% 2.71/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.71/1.01    inference(flattening,[],[f40])).
% 2.71/1.01  
% 2.71/1.01  fof(f53,plain,(
% 2.71/1.01    ( ! [X2,X0,X1] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) => (~m1_subset_1(k2_xboole_0(X2,sK4),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(sK4,u1_struct_0(k9_yellow_6(X0,X1))))) )),
% 2.71/1.01    introduced(choice_axiom,[])).
% 2.71/1.01  
% 2.71/1.01  fof(f52,plain,(
% 2.71/1.01    ( ! [X0,X1] : (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) => (? [X3] : (~m1_subset_1(k2_xboole_0(sK3,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(sK3,u1_struct_0(k9_yellow_6(X0,X1))))) )),
% 2.71/1.01    introduced(choice_axiom,[])).
% 2.71/1.01  
% 2.71/1.01  fof(f51,plain,(
% 2.71/1.01    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,sK2))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,sK2)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,sK2)))) & m1_subset_1(sK2,u1_struct_0(X0)))) )),
% 2.71/1.01    introduced(choice_axiom,[])).
% 2.71/1.01  
% 2.71/1.01  fof(f50,plain,(
% 2.71/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK1,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK1,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK1,X1)))) & m1_subset_1(X1,u1_struct_0(sK1))) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 2.71/1.01    introduced(choice_axiom,[])).
% 2.71/1.01  
% 2.71/1.01  fof(f54,plain,(
% 2.71/1.01    (((~m1_subset_1(k2_xboole_0(sK3,sK4),u1_struct_0(k9_yellow_6(sK1,sK2))) & m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK1,sK2)))) & m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK1,sK2)))) & m1_subset_1(sK2,u1_struct_0(sK1))) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 2.71/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f41,f53,f52,f51,f50])).
% 2.71/1.01  
% 2.71/1.01  fof(f78,plain,(
% 2.71/1.01    ~v2_struct_0(sK1)),
% 2.71/1.01    inference(cnf_transformation,[],[f54])).
% 2.71/1.01  
% 2.71/1.01  fof(f79,plain,(
% 2.71/1.01    v2_pre_topc(sK1)),
% 2.71/1.01    inference(cnf_transformation,[],[f54])).
% 2.71/1.01  
% 2.71/1.01  fof(f80,plain,(
% 2.71/1.01    l1_pre_topc(sK1)),
% 2.71/1.01    inference(cnf_transformation,[],[f54])).
% 2.71/1.01  
% 2.71/1.01  fof(f11,axiom,(
% 2.71/1.01    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 2.71/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.71/1.01  
% 2.71/1.01  fof(f28,plain,(
% 2.71/1.01    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 2.71/1.01    inference(ennf_transformation,[],[f11])).
% 2.71/1.01  
% 2.71/1.01  fof(f29,plain,(
% 2.71/1.01    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.71/1.01    inference(flattening,[],[f28])).
% 2.71/1.01  
% 2.71/1.01  fof(f70,plain,(
% 2.71/1.01    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.71/1.01    inference(cnf_transformation,[],[f29])).
% 2.71/1.01  
% 2.71/1.01  fof(f9,axiom,(
% 2.71/1.01    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 2.71/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.71/1.01  
% 2.71/1.01  fof(f25,plain,(
% 2.71/1.01    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 2.71/1.01    inference(ennf_transformation,[],[f9])).
% 2.71/1.01  
% 2.71/1.01  fof(f68,plain,(
% 2.71/1.01    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 2.71/1.01    inference(cnf_transformation,[],[f25])).
% 2.71/1.01  
% 2.71/1.01  fof(f84,plain,(
% 2.71/1.01    ~m1_subset_1(k2_xboole_0(sK3,sK4),u1_struct_0(k9_yellow_6(sK1,sK2)))),
% 2.71/1.01    inference(cnf_transformation,[],[f54])).
% 2.71/1.01  
% 2.71/1.01  fof(f90,plain,(
% 2.71/1.01    ~m1_subset_1(k3_tarski(k2_tarski(sK3,sK4)),u1_struct_0(k9_yellow_6(sK1,sK2)))),
% 2.71/1.01    inference(definition_unfolding,[],[f84,f61])).
% 2.71/1.01  
% 2.71/1.01  fof(f81,plain,(
% 2.71/1.01    m1_subset_1(sK2,u1_struct_0(sK1))),
% 2.71/1.01    inference(cnf_transformation,[],[f54])).
% 2.71/1.01  
% 2.71/1.01  fof(f82,plain,(
% 2.71/1.01    m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK1,sK2)))),
% 2.71/1.01    inference(cnf_transformation,[],[f54])).
% 2.71/1.01  
% 2.71/1.01  fof(f83,plain,(
% 2.71/1.01    m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK1,sK2)))),
% 2.71/1.01    inference(cnf_transformation,[],[f54])).
% 2.71/1.01  
% 2.71/1.01  fof(f16,axiom,(
% 2.71/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => m1_connsp_2(X2,X0,X1))))),
% 2.71/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.71/1.01  
% 2.71/1.01  fof(f38,plain,(
% 2.71/1.01    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.71/1.01    inference(ennf_transformation,[],[f16])).
% 2.71/1.01  
% 2.71/1.01  fof(f39,plain,(
% 2.71/1.01    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.71/1.01    inference(flattening,[],[f38])).
% 2.71/1.01  
% 2.71/1.01  fof(f77,plain,(
% 2.71/1.01    ( ! [X2,X0,X1] : (m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.71/1.01    inference(cnf_transformation,[],[f39])).
% 2.71/1.01  
% 2.71/1.01  fof(f13,axiom,(
% 2.71/1.01    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.71/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.71/1.01  
% 2.71/1.01  fof(f32,plain,(
% 2.71/1.01    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.71/1.01    inference(ennf_transformation,[],[f13])).
% 2.71/1.01  
% 2.71/1.01  fof(f33,plain,(
% 2.71/1.01    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.71/1.01    inference(flattening,[],[f32])).
% 2.71/1.01  
% 2.71/1.01  fof(f72,plain,(
% 2.71/1.01    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.71/1.01    inference(cnf_transformation,[],[f33])).
% 2.71/1.01  
% 2.71/1.01  fof(f10,axiom,(
% 2.71/1.01    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.71/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.71/1.01  
% 2.71/1.01  fof(f26,plain,(
% 2.71/1.01    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.71/1.01    inference(ennf_transformation,[],[f10])).
% 2.71/1.01  
% 2.71/1.01  fof(f27,plain,(
% 2.71/1.01    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.71/1.01    inference(flattening,[],[f26])).
% 2.71/1.01  
% 2.71/1.01  fof(f69,plain,(
% 2.71/1.01    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 2.71/1.01    inference(cnf_transformation,[],[f27])).
% 2.71/1.01  
% 2.71/1.01  fof(f75,plain,(
% 2.71/1.01    ( ! [X2,X0,X1] : (v3_pre_topc(X2,X0) | ~r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.71/1.01    inference(cnf_transformation,[],[f49])).
% 2.71/1.01  
% 2.71/1.01  fof(f14,axiom,(
% 2.71/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (m1_connsp_2(X1,X0,X2) => r2_hidden(X2,X1)))))),
% 2.71/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.71/1.01  
% 2.71/1.01  fof(f34,plain,(
% 2.71/1.01    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.71/1.01    inference(ennf_transformation,[],[f14])).
% 2.71/1.01  
% 2.71/1.01  fof(f35,plain,(
% 2.71/1.01    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.71/1.01    inference(flattening,[],[f34])).
% 2.71/1.01  
% 2.71/1.01  fof(f73,plain,(
% 2.71/1.01    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.71/1.01    inference(cnf_transformation,[],[f35])).
% 2.71/1.01  
% 2.71/1.01  fof(f1,axiom,(
% 2.71/1.01    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.71/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.71/1.01  
% 2.71/1.01  fof(f42,plain,(
% 2.71/1.01    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.71/1.01    inference(nnf_transformation,[],[f1])).
% 2.71/1.01  
% 2.71/1.01  fof(f43,plain,(
% 2.71/1.01    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.71/1.01    inference(rectify,[],[f42])).
% 2.71/1.01  
% 2.71/1.01  fof(f44,plain,(
% 2.71/1.01    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.71/1.01    introduced(choice_axiom,[])).
% 2.71/1.01  
% 2.71/1.01  fof(f45,plain,(
% 2.71/1.01    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.71/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f43,f44])).
% 2.71/1.01  
% 2.71/1.01  fof(f55,plain,(
% 2.71/1.01    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 2.71/1.01    inference(cnf_transformation,[],[f45])).
% 2.71/1.01  
% 2.71/1.01  fof(f6,axiom,(
% 2.71/1.01    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 2.71/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.71/1.01  
% 2.71/1.01  fof(f20,plain,(
% 2.71/1.01    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 2.71/1.01    inference(ennf_transformation,[],[f6])).
% 2.71/1.01  
% 2.71/1.01  fof(f47,plain,(
% 2.71/1.01    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 2.71/1.02    inference(nnf_transformation,[],[f20])).
% 2.71/1.02  
% 2.71/1.02  fof(f64,plain,(
% 2.71/1.02    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,X0) | ~v1_xboole_0(X0)) )),
% 2.71/1.02    inference(cnf_transformation,[],[f47])).
% 2.71/1.02  
% 2.71/1.02  fof(f12,axiom,(
% 2.71/1.02    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X2,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_xboole_0(X1,X2),X0))),
% 2.71/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.71/1.02  
% 2.71/1.02  fof(f30,plain,(
% 2.71/1.02    ! [X0,X1,X2] : (v3_pre_topc(k2_xboole_0(X1,X2),X0) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.71/1.02    inference(ennf_transformation,[],[f12])).
% 2.71/1.02  
% 2.71/1.02  fof(f31,plain,(
% 2.71/1.02    ! [X0,X1,X2] : (v3_pre_topc(k2_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.71/1.02    inference(flattening,[],[f30])).
% 2.71/1.02  
% 2.71/1.02  fof(f71,plain,(
% 2.71/1.02    ( ! [X2,X0,X1] : (v3_pre_topc(k2_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.71/1.02    inference(cnf_transformation,[],[f31])).
% 2.71/1.02  
% 2.71/1.02  fof(f89,plain,(
% 2.71/1.02    ( ! [X2,X0,X1] : (v3_pre_topc(k3_tarski(k2_tarski(X1,X2)),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.71/1.02    inference(definition_unfolding,[],[f71,f61])).
% 2.71/1.02  
% 2.71/1.02  fof(f8,axiom,(
% 2.71/1.02    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 2.71/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.71/1.02  
% 2.71/1.02  fof(f23,plain,(
% 2.71/1.02    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 2.71/1.02    inference(ennf_transformation,[],[f8])).
% 2.71/1.02  
% 2.71/1.02  fof(f24,plain,(
% 2.71/1.02    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.71/1.02    inference(flattening,[],[f23])).
% 2.71/1.02  
% 2.71/1.02  fof(f67,plain,(
% 2.71/1.02    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.71/1.02    inference(cnf_transformation,[],[f24])).
% 2.71/1.02  
% 2.71/1.02  fof(f88,plain,(
% 2.71/1.02    ( ! [X2,X0,X1] : (k3_tarski(k2_tarski(X1,X2)) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.71/1.02    inference(definition_unfolding,[],[f67,f61])).
% 2.71/1.02  
% 2.71/1.02  fof(f7,axiom,(
% 2.71/1.02    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 2.71/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.71/1.02  
% 2.71/1.02  fof(f21,plain,(
% 2.71/1.02    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 2.71/1.02    inference(ennf_transformation,[],[f7])).
% 2.71/1.02  
% 2.71/1.02  fof(f22,plain,(
% 2.71/1.02    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.71/1.02    inference(flattening,[],[f21])).
% 2.71/1.02  
% 2.71/1.02  fof(f66,plain,(
% 2.71/1.02    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.71/1.02    inference(cnf_transformation,[],[f22])).
% 2.71/1.02  
% 2.71/1.02  cnf(c_3,plain,
% 2.71/1.02      ( r1_tarski(k2_tarski(X0,X0),X1) | ~ r2_hidden(X0,X1) ),
% 2.71/1.02      inference(cnf_transformation,[],[f86]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_809,plain,
% 2.71/1.02      ( r1_tarski(k2_tarski(X0_48,X0_48),X1_48)
% 2.71/1.02      | ~ r2_hidden(X0_48,X1_48) ),
% 2.71/1.02      inference(subtyping,[status(esa)],[c_3]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_1384,plain,
% 2.71/1.02      ( r1_tarski(k2_tarski(X0_48,X0_48),X1_48) = iProver_top
% 2.71/1.02      | r2_hidden(X0_48,X1_48) != iProver_top ),
% 2.71/1.02      inference(predicate_to_equality,[status(thm)],[c_809]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_2,plain,
% 2.71/1.02      ( ~ r1_tarski(X0,X1) | r1_tarski(X0,k3_tarski(k2_tarski(X2,X1))) ),
% 2.71/1.02      inference(cnf_transformation,[],[f85]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_810,plain,
% 2.71/1.02      ( ~ r1_tarski(X0_50,X0_48)
% 2.71/1.02      | r1_tarski(X0_50,k3_tarski(k2_tarski(X1_48,X0_48))) ),
% 2.71/1.02      inference(subtyping,[status(esa)],[c_2]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_1383,plain,
% 2.71/1.02      ( r1_tarski(X0_50,X0_48) != iProver_top
% 2.71/1.02      | r1_tarski(X0_50,k3_tarski(k2_tarski(X1_48,X0_48))) = iProver_top ),
% 2.71/1.02      inference(predicate_to_equality,[status(thm)],[c_810]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_4,plain,
% 2.71/1.02      ( ~ r1_tarski(k2_tarski(X0,X0),X1) | r2_hidden(X0,X1) ),
% 2.71/1.02      inference(cnf_transformation,[],[f87]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_808,plain,
% 2.71/1.02      ( ~ r1_tarski(k2_tarski(X0_48,X0_48),X1_48)
% 2.71/1.02      | r2_hidden(X0_48,X1_48) ),
% 2.71/1.02      inference(subtyping,[status(esa)],[c_4]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_1385,plain,
% 2.71/1.02      ( r1_tarski(k2_tarski(X0_48,X0_48),X1_48) != iProver_top
% 2.71/1.02      | r2_hidden(X0_48,X1_48) = iProver_top ),
% 2.71/1.02      inference(predicate_to_equality,[status(thm)],[c_808]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_2500,plain,
% 2.71/1.02      ( r1_tarski(k2_tarski(X0_48,X0_48),X1_48) != iProver_top
% 2.71/1.02      | r2_hidden(X0_48,k3_tarski(k2_tarski(X2_48,X1_48))) = iProver_top ),
% 2.71/1.02      inference(superposition,[status(thm)],[c_1383,c_1385]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_4305,plain,
% 2.71/1.02      ( r2_hidden(X0_48,X1_48) != iProver_top
% 2.71/1.02      | r2_hidden(X0_48,k3_tarski(k2_tarski(X2_48,X1_48))) = iProver_top ),
% 2.71/1.02      inference(superposition,[status(thm)],[c_1384,c_2500]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_17,plain,
% 2.71/1.02      ( ~ v3_pre_topc(X0,X1)
% 2.71/1.02      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.71/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.71/1.02      | ~ r2_hidden(X2,X0)
% 2.71/1.02      | r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
% 2.71/1.02      | v2_struct_0(X1)
% 2.71/1.02      | ~ v2_pre_topc(X1)
% 2.71/1.02      | ~ l1_pre_topc(X1) ),
% 2.71/1.02      inference(cnf_transformation,[],[f76]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_27,negated_conjecture,
% 2.71/1.02      ( ~ v2_struct_0(sK1) ),
% 2.71/1.02      inference(cnf_transformation,[],[f78]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_513,plain,
% 2.71/1.02      ( ~ v3_pre_topc(X0,X1)
% 2.71/1.02      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.71/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.71/1.02      | ~ r2_hidden(X2,X0)
% 2.71/1.02      | r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
% 2.71/1.02      | ~ v2_pre_topc(X1)
% 2.71/1.02      | ~ l1_pre_topc(X1)
% 2.71/1.02      | sK1 != X1 ),
% 2.71/1.02      inference(resolution_lifted,[status(thm)],[c_17,c_27]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_514,plain,
% 2.71/1.02      ( ~ v3_pre_topc(X0,sK1)
% 2.71/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.71/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.71/1.02      | ~ r2_hidden(X1,X0)
% 2.71/1.02      | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK1,X1)))
% 2.71/1.02      | ~ v2_pre_topc(sK1)
% 2.71/1.02      | ~ l1_pre_topc(sK1) ),
% 2.71/1.02      inference(unflattening,[status(thm)],[c_513]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_26,negated_conjecture,
% 2.71/1.02      ( v2_pre_topc(sK1) ),
% 2.71/1.02      inference(cnf_transformation,[],[f79]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_25,negated_conjecture,
% 2.71/1.02      ( l1_pre_topc(sK1) ),
% 2.71/1.02      inference(cnf_transformation,[],[f80]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_518,plain,
% 2.71/1.02      ( ~ v3_pre_topc(X0,sK1)
% 2.71/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.71/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.71/1.02      | ~ r2_hidden(X1,X0)
% 2.71/1.02      | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK1,X1))) ),
% 2.71/1.02      inference(global_propositional_subsumption,
% 2.71/1.02                [status(thm)],
% 2.71/1.02                [c_514,c_26,c_25]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_13,plain,
% 2.71/1.02      ( m1_subset_1(X0,X1)
% 2.71/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 2.71/1.02      | ~ r2_hidden(X0,X2) ),
% 2.71/1.02      inference(cnf_transformation,[],[f70]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_534,plain,
% 2.71/1.02      ( ~ v3_pre_topc(X0,sK1)
% 2.71/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.71/1.02      | ~ r2_hidden(X1,X0)
% 2.71/1.02      | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK1,X1))) ),
% 2.71/1.02      inference(forward_subsumption_resolution,
% 2.71/1.02                [status(thm)],
% 2.71/1.02                [c_518,c_13]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_792,plain,
% 2.71/1.02      ( ~ v3_pre_topc(X0_48,sK1)
% 2.71/1.02      | ~ m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.71/1.02      | ~ r2_hidden(X1_48,X0_48)
% 2.71/1.02      | r2_hidden(X0_48,u1_struct_0(k9_yellow_6(sK1,X1_48))) ),
% 2.71/1.02      inference(subtyping,[status(esa)],[c_534]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_1401,plain,
% 2.71/1.02      ( v3_pre_topc(X0_48,sK1) != iProver_top
% 2.71/1.02      | m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.71/1.02      | r2_hidden(X1_48,X0_48) != iProver_top
% 2.71/1.02      | r2_hidden(X0_48,u1_struct_0(k9_yellow_6(sK1,X1_48))) = iProver_top ),
% 2.71/1.02      inference(predicate_to_equality,[status(thm)],[c_792]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_11,plain,
% 2.71/1.02      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 2.71/1.02      inference(cnf_transformation,[],[f68]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_802,plain,
% 2.71/1.02      ( m1_subset_1(X0_48,X1_48) | ~ r2_hidden(X0_48,X1_48) ),
% 2.71/1.02      inference(subtyping,[status(esa)],[c_11]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_1391,plain,
% 2.71/1.02      ( m1_subset_1(X0_48,X1_48) = iProver_top
% 2.71/1.02      | r2_hidden(X0_48,X1_48) != iProver_top ),
% 2.71/1.02      inference(predicate_to_equality,[status(thm)],[c_802]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_4176,plain,
% 2.71/1.02      ( v3_pre_topc(X0_48,sK1) != iProver_top
% 2.71/1.02      | m1_subset_1(X0_48,u1_struct_0(k9_yellow_6(sK1,X1_48))) = iProver_top
% 2.71/1.02      | m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.71/1.02      | r2_hidden(X1_48,X0_48) != iProver_top ),
% 2.71/1.02      inference(superposition,[status(thm)],[c_1401,c_1391]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_21,negated_conjecture,
% 2.71/1.02      ( ~ m1_subset_1(k3_tarski(k2_tarski(sK3,sK4)),u1_struct_0(k9_yellow_6(sK1,sK2))) ),
% 2.71/1.02      inference(cnf_transformation,[],[f90]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_800,negated_conjecture,
% 2.71/1.02      ( ~ m1_subset_1(k3_tarski(k2_tarski(sK3,sK4)),u1_struct_0(k9_yellow_6(sK1,sK2))) ),
% 2.71/1.02      inference(subtyping,[status(esa)],[c_21]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_1393,plain,
% 2.71/1.02      ( m1_subset_1(k3_tarski(k2_tarski(sK3,sK4)),u1_struct_0(k9_yellow_6(sK1,sK2))) != iProver_top ),
% 2.71/1.02      inference(predicate_to_equality,[status(thm)],[c_800]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_7934,plain,
% 2.71/1.02      ( v3_pre_topc(k3_tarski(k2_tarski(sK3,sK4)),sK1) != iProver_top
% 2.71/1.02      | m1_subset_1(k3_tarski(k2_tarski(sK3,sK4)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.71/1.02      | r2_hidden(sK2,k3_tarski(k2_tarski(sK3,sK4))) != iProver_top ),
% 2.71/1.02      inference(superposition,[status(thm)],[c_4176,c_1393]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_24,negated_conjecture,
% 2.71/1.02      ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 2.71/1.02      inference(cnf_transformation,[],[f81]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_31,plain,
% 2.71/1.02      ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
% 2.71/1.02      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_23,negated_conjecture,
% 2.71/1.02      ( m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK1,sK2))) ),
% 2.71/1.02      inference(cnf_transformation,[],[f82]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_32,plain,
% 2.71/1.02      ( m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK1,sK2))) = iProver_top ),
% 2.71/1.02      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_22,negated_conjecture,
% 2.71/1.02      ( m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK1,sK2))) ),
% 2.71/1.02      inference(cnf_transformation,[],[f83]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_33,plain,
% 2.71/1.02      ( m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK1,sK2))) = iProver_top ),
% 2.71/1.02      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_20,plain,
% 2.71/1.02      ( m1_connsp_2(X0,X1,X2)
% 2.71/1.02      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.71/1.02      | ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(X1,X2)))
% 2.71/1.02      | v2_struct_0(X1)
% 2.71/1.02      | ~ v2_pre_topc(X1)
% 2.71/1.02      | ~ l1_pre_topc(X1) ),
% 2.71/1.02      inference(cnf_transformation,[],[f77]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_15,plain,
% 2.71/1.02      ( ~ m1_connsp_2(X0,X1,X2)
% 2.71/1.02      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.71/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.71/1.02      | v2_struct_0(X1)
% 2.71/1.02      | ~ v2_pre_topc(X1)
% 2.71/1.02      | ~ l1_pre_topc(X1) ),
% 2.71/1.02      inference(cnf_transformation,[],[f72]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_386,plain,
% 2.71/1.02      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.71/1.02      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
% 2.71/1.02      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.71/1.02      | v2_struct_0(X1)
% 2.71/1.02      | ~ v2_pre_topc(X1)
% 2.71/1.02      | ~ l1_pre_topc(X1) ),
% 2.71/1.02      inference(resolution,[status(thm)],[c_20,c_15]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_423,plain,
% 2.71/1.02      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.71/1.02      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
% 2.71/1.02      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.71/1.02      | ~ v2_pre_topc(X1)
% 2.71/1.02      | ~ l1_pre_topc(X1)
% 2.71/1.02      | sK1 != X1 ),
% 2.71/1.02      inference(resolution_lifted,[status(thm)],[c_386,c_27]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_424,plain,
% 2.71/1.02      ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK1,X1)))
% 2.71/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.71/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.71/1.02      | ~ v2_pre_topc(sK1)
% 2.71/1.02      | ~ l1_pre_topc(sK1) ),
% 2.71/1.02      inference(unflattening,[status(thm)],[c_423]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_428,plain,
% 2.71/1.02      ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK1,X1)))
% 2.71/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.71/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.71/1.02      inference(global_propositional_subsumption,
% 2.71/1.02                [status(thm)],
% 2.71/1.02                [c_424,c_26,c_25]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_796,plain,
% 2.71/1.02      ( ~ m1_subset_1(X0_48,u1_struct_0(k9_yellow_6(sK1,X1_48)))
% 2.71/1.02      | ~ m1_subset_1(X1_48,u1_struct_0(sK1))
% 2.71/1.02      | m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.71/1.02      inference(subtyping,[status(esa)],[c_428]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_1565,plain,
% 2.71/1.02      ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 2.71/1.02      | ~ m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK1,sK2)))
% 2.71/1.02      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.71/1.02      inference(instantiation,[status(thm)],[c_796]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_1566,plain,
% 2.71/1.02      ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 2.71/1.02      | m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK1,sK2))) != iProver_top
% 2.71/1.02      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.71/1.02      inference(predicate_to_equality,[status(thm)],[c_1565]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_1568,plain,
% 2.71/1.02      ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 2.71/1.02      | ~ m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK1,sK2)))
% 2.71/1.02      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.71/1.02      inference(instantiation,[status(thm)],[c_796]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_1569,plain,
% 2.71/1.02      ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 2.71/1.02      | m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK1,sK2))) != iProver_top
% 2.71/1.02      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.71/1.02      inference(predicate_to_equality,[status(thm)],[c_1568]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_12,plain,
% 2.71/1.02      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.71/1.02      inference(cnf_transformation,[],[f69]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_805,plain,
% 2.71/1.02      ( ~ m1_subset_1(X0_48,X1_48)
% 2.71/1.02      | r2_hidden(X0_48,X1_48)
% 2.71/1.02      | v1_xboole_0(X1_48) ),
% 2.71/1.02      inference(subtyping,[status(esa)],[c_12]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_1581,plain,
% 2.71/1.02      ( ~ m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK1,sK2)))
% 2.71/1.02      | r2_hidden(sK4,u1_struct_0(k9_yellow_6(sK1,sK2)))
% 2.71/1.02      | v1_xboole_0(u1_struct_0(k9_yellow_6(sK1,sK2))) ),
% 2.71/1.02      inference(instantiation,[status(thm)],[c_805]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_1582,plain,
% 2.71/1.02      ( m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK1,sK2))) != iProver_top
% 2.71/1.02      | r2_hidden(sK4,u1_struct_0(k9_yellow_6(sK1,sK2))) = iProver_top
% 2.71/1.02      | v1_xboole_0(u1_struct_0(k9_yellow_6(sK1,sK2))) = iProver_top ),
% 2.71/1.02      inference(predicate_to_equality,[status(thm)],[c_1581]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_1584,plain,
% 2.71/1.02      ( ~ m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK1,sK2)))
% 2.71/1.02      | r2_hidden(sK3,u1_struct_0(k9_yellow_6(sK1,sK2)))
% 2.71/1.02      | v1_xboole_0(u1_struct_0(k9_yellow_6(sK1,sK2))) ),
% 2.71/1.02      inference(instantiation,[status(thm)],[c_805]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_1585,plain,
% 2.71/1.02      ( m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK1,sK2))) != iProver_top
% 2.71/1.02      | r2_hidden(sK3,u1_struct_0(k9_yellow_6(sK1,sK2))) = iProver_top
% 2.71/1.02      | v1_xboole_0(u1_struct_0(k9_yellow_6(sK1,sK2))) = iProver_top ),
% 2.71/1.02      inference(predicate_to_equality,[status(thm)],[c_1584]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_18,plain,
% 2.71/1.02      ( v3_pre_topc(X0,X1)
% 2.71/1.02      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.71/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.71/1.02      | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
% 2.71/1.02      | v2_struct_0(X1)
% 2.71/1.02      | ~ v2_pre_topc(X1)
% 2.71/1.02      | ~ l1_pre_topc(X1) ),
% 2.71/1.02      inference(cnf_transformation,[],[f75]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_489,plain,
% 2.71/1.02      ( v3_pre_topc(X0,X1)
% 2.71/1.02      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.71/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.71/1.02      | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
% 2.71/1.02      | ~ v2_pre_topc(X1)
% 2.71/1.02      | ~ l1_pre_topc(X1)
% 2.71/1.02      | sK1 != X1 ),
% 2.71/1.02      inference(resolution_lifted,[status(thm)],[c_18,c_27]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_490,plain,
% 2.71/1.02      ( v3_pre_topc(X0,sK1)
% 2.71/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.71/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.71/1.02      | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(sK1,X1)))
% 2.71/1.02      | ~ v2_pre_topc(sK1)
% 2.71/1.02      | ~ l1_pre_topc(sK1) ),
% 2.71/1.02      inference(unflattening,[status(thm)],[c_489]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_494,plain,
% 2.71/1.02      ( v3_pre_topc(X0,sK1)
% 2.71/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.71/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.71/1.02      | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(sK1,X1))) ),
% 2.71/1.02      inference(global_propositional_subsumption,
% 2.71/1.02                [status(thm)],
% 2.71/1.02                [c_490,c_26,c_25]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_793,plain,
% 2.71/1.02      ( v3_pre_topc(X0_48,sK1)
% 2.71/1.02      | ~ m1_subset_1(X1_48,u1_struct_0(sK1))
% 2.71/1.02      | ~ m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.71/1.02      | ~ r2_hidden(X0_48,u1_struct_0(k9_yellow_6(sK1,X1_48))) ),
% 2.71/1.02      inference(subtyping,[status(esa)],[c_494]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_1651,plain,
% 2.71/1.02      ( v3_pre_topc(sK4,sK1)
% 2.71/1.02      | ~ m1_subset_1(X0_48,u1_struct_0(sK1))
% 2.71/1.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.71/1.02      | ~ r2_hidden(sK4,u1_struct_0(k9_yellow_6(sK1,X0_48))) ),
% 2.71/1.02      inference(instantiation,[status(thm)],[c_793]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_1652,plain,
% 2.71/1.02      ( v3_pre_topc(sK4,sK1) = iProver_top
% 2.71/1.02      | m1_subset_1(X0_48,u1_struct_0(sK1)) != iProver_top
% 2.71/1.02      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.71/1.02      | r2_hidden(sK4,u1_struct_0(k9_yellow_6(sK1,X0_48))) != iProver_top ),
% 2.71/1.02      inference(predicate_to_equality,[status(thm)],[c_1651]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_1654,plain,
% 2.71/1.02      ( v3_pre_topc(sK4,sK1) = iProver_top
% 2.71/1.02      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 2.71/1.02      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.71/1.02      | r2_hidden(sK4,u1_struct_0(k9_yellow_6(sK1,sK2))) != iProver_top ),
% 2.71/1.02      inference(instantiation,[status(thm)],[c_1652]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_1677,plain,
% 2.71/1.02      ( v3_pre_topc(sK3,sK1)
% 2.71/1.02      | ~ m1_subset_1(X0_48,u1_struct_0(sK1))
% 2.71/1.02      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.71/1.02      | ~ r2_hidden(sK3,u1_struct_0(k9_yellow_6(sK1,X0_48))) ),
% 2.71/1.02      inference(instantiation,[status(thm)],[c_793]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_1678,plain,
% 2.71/1.02      ( v3_pre_topc(sK3,sK1) = iProver_top
% 2.71/1.02      | m1_subset_1(X0_48,u1_struct_0(sK1)) != iProver_top
% 2.71/1.02      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.71/1.02      | r2_hidden(sK3,u1_struct_0(k9_yellow_6(sK1,X0_48))) != iProver_top ),
% 2.71/1.02      inference(predicate_to_equality,[status(thm)],[c_1677]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_1680,plain,
% 2.71/1.02      ( v3_pre_topc(sK3,sK1) = iProver_top
% 2.71/1.02      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 2.71/1.02      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.71/1.02      | r2_hidden(sK3,u1_struct_0(k9_yellow_6(sK1,sK2))) != iProver_top ),
% 2.71/1.02      inference(instantiation,[status(thm)],[c_1678]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_799,negated_conjecture,
% 2.71/1.02      ( m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK1,sK2))) ),
% 2.71/1.02      inference(subtyping,[status(esa)],[c_22]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_1394,plain,
% 2.71/1.02      ( m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK1,sK2))) = iProver_top ),
% 2.71/1.02      inference(predicate_to_equality,[status(thm)],[c_799]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_16,plain,
% 2.71/1.02      ( ~ m1_connsp_2(X0,X1,X2)
% 2.71/1.02      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.71/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.71/1.02      | r2_hidden(X2,X0)
% 2.71/1.02      | v2_struct_0(X1)
% 2.71/1.02      | ~ v2_pre_topc(X1)
% 2.71/1.02      | ~ l1_pre_topc(X1) ),
% 2.71/1.02      inference(cnf_transformation,[],[f73]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_160,plain,
% 2.71/1.02      ( ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.71/1.02      | ~ m1_connsp_2(X0,X1,X2)
% 2.71/1.02      | r2_hidden(X2,X0)
% 2.71/1.02      | v2_struct_0(X1)
% 2.71/1.02      | ~ v2_pre_topc(X1)
% 2.71/1.02      | ~ l1_pre_topc(X1) ),
% 2.71/1.02      inference(global_propositional_subsumption,
% 2.71/1.02                [status(thm)],
% 2.71/1.02                [c_16,c_15]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_161,plain,
% 2.71/1.02      ( ~ m1_connsp_2(X0,X1,X2)
% 2.71/1.02      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.71/1.02      | r2_hidden(X2,X0)
% 2.71/1.02      | v2_struct_0(X1)
% 2.71/1.02      | ~ v2_pre_topc(X1)
% 2.71/1.02      | ~ l1_pre_topc(X1) ),
% 2.71/1.02      inference(renaming,[status(thm)],[c_160]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_363,plain,
% 2.71/1.02      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.71/1.02      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
% 2.71/1.02      | r2_hidden(X0,X2)
% 2.71/1.02      | v2_struct_0(X1)
% 2.71/1.02      | ~ v2_pre_topc(X1)
% 2.71/1.02      | ~ l1_pre_topc(X1) ),
% 2.71/1.02      inference(resolution,[status(thm)],[c_20,c_161]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_444,plain,
% 2.71/1.02      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.71/1.02      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
% 2.71/1.02      | r2_hidden(X0,X2)
% 2.71/1.02      | ~ v2_pre_topc(X1)
% 2.71/1.02      | ~ l1_pre_topc(X1)
% 2.71/1.02      | sK1 != X1 ),
% 2.71/1.02      inference(resolution_lifted,[status(thm)],[c_363,c_27]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_445,plain,
% 2.71/1.02      ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK1,X1)))
% 2.71/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.71/1.02      | r2_hidden(X1,X0)
% 2.71/1.02      | ~ v2_pre_topc(sK1)
% 2.71/1.02      | ~ l1_pre_topc(sK1) ),
% 2.71/1.02      inference(unflattening,[status(thm)],[c_444]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_449,plain,
% 2.71/1.02      ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK1,X1)))
% 2.71/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.71/1.02      | r2_hidden(X1,X0) ),
% 2.71/1.02      inference(global_propositional_subsumption,
% 2.71/1.02                [status(thm)],
% 2.71/1.02                [c_445,c_26,c_25]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_795,plain,
% 2.71/1.02      ( ~ m1_subset_1(X0_48,u1_struct_0(k9_yellow_6(sK1,X1_48)))
% 2.71/1.02      | ~ m1_subset_1(X1_48,u1_struct_0(sK1))
% 2.71/1.02      | r2_hidden(X1_48,X0_48) ),
% 2.71/1.02      inference(subtyping,[status(esa)],[c_449]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_1398,plain,
% 2.71/1.02      ( m1_subset_1(X0_48,u1_struct_0(k9_yellow_6(sK1,X1_48))) != iProver_top
% 2.71/1.02      | m1_subset_1(X1_48,u1_struct_0(sK1)) != iProver_top
% 2.71/1.02      | r2_hidden(X1_48,X0_48) = iProver_top ),
% 2.71/1.02      inference(predicate_to_equality,[status(thm)],[c_795]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_1628,plain,
% 2.71/1.02      ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 2.71/1.02      | r2_hidden(sK2,sK4) = iProver_top ),
% 2.71/1.02      inference(superposition,[status(thm)],[c_1394,c_1398]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_1571,plain,
% 2.71/1.02      ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 2.71/1.02      | ~ m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK1,sK2)))
% 2.71/1.02      | r2_hidden(sK2,sK4) ),
% 2.71/1.02      inference(instantiation,[status(thm)],[c_795]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_1572,plain,
% 2.71/1.02      ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 2.71/1.02      | m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK1,sK2))) != iProver_top
% 2.71/1.02      | r2_hidden(sK2,sK4) = iProver_top ),
% 2.71/1.02      inference(predicate_to_equality,[status(thm)],[c_1571]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_1641,plain,
% 2.71/1.02      ( r2_hidden(sK2,sK4) = iProver_top ),
% 2.71/1.02      inference(global_propositional_subsumption,
% 2.71/1.02                [status(thm)],
% 2.71/1.02                [c_1628,c_31,c_33,c_1572]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_1,plain,
% 2.71/1.02      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 2.71/1.02      inference(cnf_transformation,[],[f55]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_811,plain,
% 2.71/1.02      ( ~ r2_hidden(X0_48,X1_48) | ~ v1_xboole_0(X1_48) ),
% 2.71/1.02      inference(subtyping,[status(esa)],[c_1]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_1382,plain,
% 2.71/1.02      ( r2_hidden(X0_48,X1_48) != iProver_top
% 2.71/1.02      | v1_xboole_0(X1_48) != iProver_top ),
% 2.71/1.02      inference(predicate_to_equality,[status(thm)],[c_811]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_1993,plain,
% 2.71/1.02      ( v1_xboole_0(sK4) != iProver_top ),
% 2.71/1.02      inference(superposition,[status(thm)],[c_1641,c_1382]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_6,plain,
% 2.71/1.02      ( ~ m1_subset_1(X0,X1) | ~ v1_xboole_0(X1) | v1_xboole_0(X0) ),
% 2.71/1.02      inference(cnf_transformation,[],[f64]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_806,plain,
% 2.71/1.02      ( ~ m1_subset_1(X0_48,X1_48)
% 2.71/1.02      | ~ v1_xboole_0(X1_48)
% 2.71/1.02      | v1_xboole_0(X0_48) ),
% 2.71/1.02      inference(subtyping,[status(esa)],[c_6]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_1761,plain,
% 2.71/1.02      ( ~ m1_subset_1(X0_48,u1_struct_0(k9_yellow_6(sK1,sK2)))
% 2.71/1.02      | v1_xboole_0(X0_48)
% 2.71/1.02      | ~ v1_xboole_0(u1_struct_0(k9_yellow_6(sK1,sK2))) ),
% 2.71/1.02      inference(instantiation,[status(thm)],[c_806]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_2027,plain,
% 2.71/1.02      ( ~ m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK1,sK2)))
% 2.71/1.02      | ~ v1_xboole_0(u1_struct_0(k9_yellow_6(sK1,sK2)))
% 2.71/1.02      | v1_xboole_0(sK4) ),
% 2.71/1.02      inference(instantiation,[status(thm)],[c_1761]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_2028,plain,
% 2.71/1.02      ( m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK1,sK2))) != iProver_top
% 2.71/1.02      | v1_xboole_0(u1_struct_0(k9_yellow_6(sK1,sK2))) != iProver_top
% 2.71/1.02      | v1_xboole_0(sK4) = iProver_top ),
% 2.71/1.02      inference(predicate_to_equality,[status(thm)],[c_2027]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_14,plain,
% 2.71/1.02      ( ~ v3_pre_topc(X0,X1)
% 2.71/1.02      | ~ v3_pre_topc(X2,X1)
% 2.71/1.02      | v3_pre_topc(k3_tarski(k2_tarski(X2,X0)),X1)
% 2.71/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.71/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.71/1.02      | ~ v2_pre_topc(X1)
% 2.71/1.02      | ~ l1_pre_topc(X1) ),
% 2.71/1.02      inference(cnf_transformation,[],[f89]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_565,plain,
% 2.71/1.02      ( ~ v3_pre_topc(X0,X1)
% 2.71/1.02      | ~ v3_pre_topc(X2,X1)
% 2.71/1.02      | v3_pre_topc(k3_tarski(k2_tarski(X2,X0)),X1)
% 2.71/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.71/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.71/1.02      | ~ v2_pre_topc(X1)
% 2.71/1.02      | sK1 != X1 ),
% 2.71/1.02      inference(resolution_lifted,[status(thm)],[c_14,c_25]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_566,plain,
% 2.71/1.02      ( ~ v3_pre_topc(X0,sK1)
% 2.71/1.02      | ~ v3_pre_topc(X1,sK1)
% 2.71/1.02      | v3_pre_topc(k3_tarski(k2_tarski(X1,X0)),sK1)
% 2.71/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.71/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.71/1.02      | ~ v2_pre_topc(sK1) ),
% 2.71/1.02      inference(unflattening,[status(thm)],[c_565]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_570,plain,
% 2.71/1.02      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.71/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.71/1.02      | v3_pre_topc(k3_tarski(k2_tarski(X1,X0)),sK1)
% 2.71/1.02      | ~ v3_pre_topc(X1,sK1)
% 2.71/1.02      | ~ v3_pre_topc(X0,sK1) ),
% 2.71/1.02      inference(global_propositional_subsumption,
% 2.71/1.02                [status(thm)],
% 2.71/1.02                [c_566,c_26]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_571,plain,
% 2.71/1.02      ( ~ v3_pre_topc(X0,sK1)
% 2.71/1.02      | ~ v3_pre_topc(X1,sK1)
% 2.71/1.02      | v3_pre_topc(k3_tarski(k2_tarski(X1,X0)),sK1)
% 2.71/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.71/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.71/1.02      inference(renaming,[status(thm)],[c_570]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_791,plain,
% 2.71/1.02      ( ~ v3_pre_topc(X0_48,sK1)
% 2.71/1.02      | ~ v3_pre_topc(X1_48,sK1)
% 2.71/1.02      | v3_pre_topc(k3_tarski(k2_tarski(X1_48,X0_48)),sK1)
% 2.71/1.02      | ~ m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.71/1.02      | ~ m1_subset_1(X1_48,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.71/1.02      inference(subtyping,[status(esa)],[c_571]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_2376,plain,
% 2.71/1.02      ( ~ v3_pre_topc(X0_48,sK1)
% 2.71/1.02      | v3_pre_topc(k3_tarski(k2_tarski(X0_48,sK4)),sK1)
% 2.71/1.02      | ~ v3_pre_topc(sK4,sK1)
% 2.71/1.02      | ~ m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.71/1.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.71/1.02      inference(instantiation,[status(thm)],[c_791]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_3933,plain,
% 2.71/1.02      ( v3_pre_topc(k3_tarski(k2_tarski(sK3,sK4)),sK1)
% 2.71/1.02      | ~ v3_pre_topc(sK4,sK1)
% 2.71/1.02      | ~ v3_pre_topc(sK3,sK1)
% 2.71/1.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.71/1.02      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.71/1.02      inference(instantiation,[status(thm)],[c_2376]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_3934,plain,
% 2.71/1.02      ( v3_pre_topc(k3_tarski(k2_tarski(sK3,sK4)),sK1) = iProver_top
% 2.71/1.02      | v3_pre_topc(sK4,sK1) != iProver_top
% 2.71/1.02      | v3_pre_topc(sK3,sK1) != iProver_top
% 2.71/1.02      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.71/1.02      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.71/1.02      inference(predicate_to_equality,[status(thm)],[c_3933]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_1397,plain,
% 2.71/1.02      ( m1_subset_1(X0_48,u1_struct_0(k9_yellow_6(sK1,X1_48))) != iProver_top
% 2.71/1.02      | m1_subset_1(X1_48,u1_struct_0(sK1)) != iProver_top
% 2.71/1.02      | m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.71/1.02      inference(predicate_to_equality,[status(thm)],[c_796]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_1747,plain,
% 2.71/1.02      ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 2.71/1.02      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.71/1.02      inference(superposition,[status(thm)],[c_1394,c_1397]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_2088,plain,
% 2.71/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.71/1.02      inference(global_propositional_subsumption,
% 2.71/1.02                [status(thm)],
% 2.71/1.02                [c_1747,c_31,c_33,c_1566]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_798,negated_conjecture,
% 2.71/1.02      ( m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK1,sK2))) ),
% 2.71/1.02      inference(subtyping,[status(esa)],[c_23]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_1395,plain,
% 2.71/1.02      ( m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK1,sK2))) = iProver_top ),
% 2.71/1.02      inference(predicate_to_equality,[status(thm)],[c_798]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_1748,plain,
% 2.71/1.02      ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 2.71/1.02      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.71/1.02      inference(superposition,[status(thm)],[c_1395,c_1397]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_2285,plain,
% 2.71/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.71/1.02      inference(global_propositional_subsumption,
% 2.71/1.02                [status(thm)],
% 2.71/1.02                [c_1748,c_31,c_32,c_1569]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_10,plain,
% 2.71/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.71/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 2.71/1.02      | k4_subset_1(X1,X2,X0) = k3_tarski(k2_tarski(X2,X0)) ),
% 2.71/1.02      inference(cnf_transformation,[],[f88]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_803,plain,
% 2.71/1.02      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(X1_48))
% 2.71/1.02      | ~ m1_subset_1(X2_48,k1_zfmisc_1(X1_48))
% 2.71/1.02      | k4_subset_1(X1_48,X2_48,X0_48) = k3_tarski(k2_tarski(X2_48,X0_48)) ),
% 2.71/1.02      inference(subtyping,[status(esa)],[c_10]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_1390,plain,
% 2.71/1.02      ( k4_subset_1(X0_48,X1_48,X2_48) = k3_tarski(k2_tarski(X1_48,X2_48))
% 2.71/1.02      | m1_subset_1(X1_48,k1_zfmisc_1(X0_48)) != iProver_top
% 2.71/1.02      | m1_subset_1(X2_48,k1_zfmisc_1(X0_48)) != iProver_top ),
% 2.71/1.02      inference(predicate_to_equality,[status(thm)],[c_803]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_3311,plain,
% 2.71/1.02      ( k4_subset_1(u1_struct_0(sK1),sK3,X0_48) = k3_tarski(k2_tarski(sK3,X0_48))
% 2.71/1.02      | m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.71/1.02      inference(superposition,[status(thm)],[c_2285,c_1390]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_3994,plain,
% 2.71/1.02      ( k4_subset_1(u1_struct_0(sK1),sK3,sK4) = k3_tarski(k2_tarski(sK3,sK4)) ),
% 2.71/1.02      inference(superposition,[status(thm)],[c_2088,c_3311]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_9,plain,
% 2.71/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.71/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 2.71/1.02      | m1_subset_1(k4_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 2.71/1.02      inference(cnf_transformation,[],[f66]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_804,plain,
% 2.71/1.02      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(X1_48))
% 2.71/1.02      | ~ m1_subset_1(X2_48,k1_zfmisc_1(X1_48))
% 2.71/1.02      | m1_subset_1(k4_subset_1(X1_48,X2_48,X0_48),k1_zfmisc_1(X1_48)) ),
% 2.71/1.02      inference(subtyping,[status(esa)],[c_9]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_1389,plain,
% 2.71/1.02      ( m1_subset_1(X0_48,k1_zfmisc_1(X1_48)) != iProver_top
% 2.71/1.02      | m1_subset_1(X2_48,k1_zfmisc_1(X1_48)) != iProver_top
% 2.71/1.02      | m1_subset_1(k4_subset_1(X1_48,X0_48,X2_48),k1_zfmisc_1(X1_48)) = iProver_top ),
% 2.71/1.02      inference(predicate_to_equality,[status(thm)],[c_804]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_4080,plain,
% 2.71/1.02      ( m1_subset_1(k3_tarski(k2_tarski(sK3,sK4)),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 2.71/1.02      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.71/1.02      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.71/1.02      inference(superposition,[status(thm)],[c_3994,c_1389]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_7958,plain,
% 2.71/1.02      ( r2_hidden(sK2,k3_tarski(k2_tarski(sK3,sK4))) != iProver_top ),
% 2.71/1.02      inference(global_propositional_subsumption,
% 2.71/1.02                [status(thm)],
% 2.71/1.02                [c_7934,c_31,c_32,c_33,c_1566,c_1569,c_1582,c_1585,
% 2.71/1.02                 c_1654,c_1680,c_1993,c_2028,c_3934,c_4080]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(c_7963,plain,
% 2.71/1.02      ( r2_hidden(sK2,sK4) != iProver_top ),
% 2.71/1.02      inference(superposition,[status(thm)],[c_4305,c_7958]) ).
% 2.71/1.02  
% 2.71/1.02  cnf(contradiction,plain,
% 2.71/1.02      ( $false ),
% 2.71/1.02      inference(minisat,[status(thm)],[c_7963,c_1572,c_33,c_31]) ).
% 2.71/1.02  
% 2.71/1.02  
% 2.71/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 2.71/1.02  
% 2.71/1.02  ------                               Statistics
% 2.71/1.02  
% 2.71/1.02  ------ General
% 2.71/1.02  
% 2.71/1.02  abstr_ref_over_cycles:                  0
% 2.71/1.02  abstr_ref_under_cycles:                 0
% 2.71/1.02  gc_basic_clause_elim:                   0
% 2.71/1.02  forced_gc_time:                         0
% 2.71/1.02  parsing_time:                           0.016
% 2.71/1.02  unif_index_cands_time:                  0.
% 2.71/1.02  unif_index_add_time:                    0.
% 2.71/1.02  orderings_time:                         0.
% 2.71/1.02  out_proof_time:                         0.018
% 2.71/1.02  total_time:                             0.342
% 2.71/1.02  num_of_symbols:                         51
% 2.71/1.02  num_of_terms:                           6851
% 2.71/1.02  
% 2.71/1.02  ------ Preprocessing
% 2.71/1.02  
% 2.71/1.02  num_of_splits:                          0
% 2.71/1.02  num_of_split_atoms:                     0
% 2.71/1.02  num_of_reused_defs:                     0
% 2.71/1.02  num_eq_ax_congr_red:                    19
% 2.71/1.02  num_of_sem_filtered_clauses:            1
% 2.71/1.02  num_of_subtypes:                        3
% 2.71/1.02  monotx_restored_types:                  0
% 2.71/1.02  sat_num_of_epr_types:                   0
% 2.71/1.02  sat_num_of_non_cyclic_types:            0
% 2.71/1.02  sat_guarded_non_collapsed_types:        0
% 2.71/1.02  num_pure_diseq_elim:                    0
% 2.71/1.02  simp_replaced_by:                       0
% 2.71/1.02  res_preprocessed:                       119
% 2.71/1.02  prep_upred:                             0
% 2.71/1.02  prep_unflattend:                        6
% 2.71/1.02  smt_new_axioms:                         0
% 2.71/1.02  pred_elim_cands:                        5
% 2.71/1.02  pred_elim:                              4
% 2.71/1.02  pred_elim_cl:                           4
% 2.71/1.02  pred_elim_cycles:                       6
% 2.71/1.02  merged_defs:                            8
% 2.71/1.02  merged_defs_ncl:                        0
% 2.71/1.02  bin_hyper_res:                          8
% 2.71/1.02  prep_cycles:                            4
% 2.71/1.02  pred_elim_time:                         0.022
% 2.71/1.02  splitting_time:                         0.
% 2.71/1.02  sem_filter_time:                        0.
% 2.71/1.02  monotx_time:                            0.
% 2.71/1.02  subtype_inf_time:                       0.001
% 2.71/1.02  
% 2.71/1.02  ------ Problem properties
% 2.71/1.02  
% 2.71/1.02  clauses:                                22
% 2.71/1.02  conjectures:                            4
% 2.71/1.02  epr:                                    5
% 2.71/1.02  horn:                                   20
% 2.71/1.02  ground:                                 4
% 2.71/1.02  unary:                                  4
% 2.71/1.02  binary:                                 6
% 2.71/1.02  lits:                                   57
% 2.71/1.02  lits_eq:                                1
% 2.71/1.02  fd_pure:                                0
% 2.71/1.02  fd_pseudo:                              0
% 2.71/1.02  fd_cond:                                0
% 2.71/1.02  fd_pseudo_cond:                         0
% 2.71/1.02  ac_symbols:                             0
% 2.71/1.02  
% 2.71/1.02  ------ Propositional Solver
% 2.71/1.02  
% 2.71/1.02  prop_solver_calls:                      27
% 2.71/1.02  prop_fast_solver_calls:                 951
% 2.71/1.02  smt_solver_calls:                       0
% 2.71/1.02  smt_fast_solver_calls:                  0
% 2.71/1.02  prop_num_of_clauses:                    2959
% 2.71/1.02  prop_preprocess_simplified:             7719
% 2.71/1.02  prop_fo_subsumed:                       40
% 2.71/1.02  prop_solver_time:                       0.
% 2.71/1.02  smt_solver_time:                        0.
% 2.71/1.02  smt_fast_solver_time:                   0.
% 2.71/1.02  prop_fast_solver_time:                  0.
% 2.71/1.02  prop_unsat_core_time:                   0.
% 2.71/1.02  
% 2.71/1.02  ------ QBF
% 2.71/1.02  
% 2.71/1.02  qbf_q_res:                              0
% 2.71/1.02  qbf_num_tautologies:                    0
% 2.71/1.02  qbf_prep_cycles:                        0
% 2.71/1.02  
% 2.71/1.02  ------ BMC1
% 2.71/1.02  
% 2.71/1.02  bmc1_current_bound:                     -1
% 2.71/1.02  bmc1_last_solved_bound:                 -1
% 2.71/1.02  bmc1_unsat_core_size:                   -1
% 2.71/1.02  bmc1_unsat_core_parents_size:           -1
% 2.71/1.02  bmc1_merge_next_fun:                    0
% 2.71/1.02  bmc1_unsat_core_clauses_time:           0.
% 2.71/1.02  
% 2.71/1.02  ------ Instantiation
% 2.71/1.02  
% 2.71/1.02  inst_num_of_clauses:                    881
% 2.71/1.02  inst_num_in_passive:                    229
% 2.71/1.02  inst_num_in_active:                     371
% 2.71/1.02  inst_num_in_unprocessed:                281
% 2.71/1.02  inst_num_of_loops:                      400
% 2.71/1.02  inst_num_of_learning_restarts:          0
% 2.71/1.02  inst_num_moves_active_passive:          27
% 2.71/1.02  inst_lit_activity:                      0
% 2.71/1.02  inst_lit_activity_moves:                0
% 2.71/1.02  inst_num_tautologies:                   0
% 2.71/1.02  inst_num_prop_implied:                  0
% 2.71/1.02  inst_num_existing_simplified:           0
% 2.71/1.02  inst_num_eq_res_simplified:             0
% 2.71/1.02  inst_num_child_elim:                    0
% 2.71/1.02  inst_num_of_dismatching_blockings:      781
% 2.71/1.02  inst_num_of_non_proper_insts:           799
% 2.71/1.02  inst_num_of_duplicates:                 0
% 2.71/1.02  inst_inst_num_from_inst_to_res:         0
% 2.71/1.02  inst_dismatching_checking_time:         0.
% 2.71/1.02  
% 2.71/1.02  ------ Resolution
% 2.71/1.02  
% 2.71/1.02  res_num_of_clauses:                     0
% 2.71/1.02  res_num_in_passive:                     0
% 2.71/1.02  res_num_in_active:                      0
% 2.71/1.02  res_num_of_loops:                       123
% 2.71/1.02  res_forward_subset_subsumed:            47
% 2.71/1.02  res_backward_subset_subsumed:           0
% 2.71/1.02  res_forward_subsumed:                   0
% 2.71/1.02  res_backward_subsumed:                  0
% 2.71/1.02  res_forward_subsumption_resolution:     1
% 2.71/1.02  res_backward_subsumption_resolution:    0
% 2.71/1.02  res_clause_to_clause_subsumption:       299
% 2.71/1.02  res_orphan_elimination:                 0
% 2.71/1.02  res_tautology_del:                      46
% 2.71/1.02  res_num_eq_res_simplified:              0
% 2.71/1.02  res_num_sel_changes:                    0
% 2.71/1.02  res_moves_from_active_to_pass:          0
% 2.71/1.02  
% 2.71/1.02  ------ Superposition
% 2.71/1.02  
% 2.71/1.02  sup_time_total:                         0.
% 2.71/1.02  sup_time_generating:                    0.
% 2.71/1.02  sup_time_sim_full:                      0.
% 2.71/1.02  sup_time_sim_immed:                     0.
% 2.71/1.02  
% 2.71/1.02  sup_num_of_clauses:                     133
% 2.71/1.02  sup_num_in_active:                      80
% 2.71/1.02  sup_num_in_passive:                     53
% 2.71/1.02  sup_num_of_loops:                       79
% 2.71/1.02  sup_fw_superposition:                   66
% 2.71/1.02  sup_bw_superposition:                   105
% 2.71/1.02  sup_immediate_simplified:               30
% 2.71/1.02  sup_given_eliminated:                   0
% 2.71/1.02  comparisons_done:                       0
% 2.71/1.02  comparisons_avoided:                    0
% 2.71/1.02  
% 2.71/1.02  ------ Simplifications
% 2.71/1.02  
% 2.71/1.02  
% 2.71/1.02  sim_fw_subset_subsumed:                 29
% 2.71/1.02  sim_bw_subset_subsumed:                 3
% 2.71/1.02  sim_fw_subsumed:                        1
% 2.71/1.02  sim_bw_subsumed:                        0
% 2.71/1.02  sim_fw_subsumption_res:                 1
% 2.71/1.02  sim_bw_subsumption_res:                 0
% 2.71/1.02  sim_tautology_del:                      11
% 2.71/1.02  sim_eq_tautology_del:                   0
% 2.71/1.02  sim_eq_res_simp:                        0
% 2.71/1.02  sim_fw_demodulated:                     0
% 2.71/1.02  sim_bw_demodulated:                     0
% 2.71/1.02  sim_light_normalised:                   0
% 2.71/1.02  sim_joinable_taut:                      0
% 2.71/1.02  sim_joinable_simp:                      0
% 2.71/1.02  sim_ac_normalised:                      0
% 2.71/1.02  sim_smt_subsumption:                    0
% 2.71/1.02  
%------------------------------------------------------------------------------
