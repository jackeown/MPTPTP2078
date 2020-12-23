%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:28:51 EST 2020

% Result     : Theorem 2.97s
% Output     : CNFRefutation 2.97s
% Verified   : 
% Statistics : Number of formulae       :  136 (1118 expanded)
%              Number of clauses        :   82 ( 240 expanded)
%              Number of leaves         :   14 ( 417 expanded)
%              Depth                    :   24
%              Number of atoms          :  583 (6672 expanded)
%              Number of equality atoms :  124 ( 320 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f23,plain,(
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
    inference(rectify,[],[f22])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            & ~ r2_hidden(sK0(X0,X1,X2),X0) )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( r2_hidden(sK0(X0,X1,X2),X1)
          | r2_hidden(sK0(X0,X1,X2),X0)
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
              & ~ r2_hidden(sK0(X0,X1,X2),X0) )
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( r2_hidden(sK0(X0,X1,X2),X1)
            | r2_hidden(sK0(X0,X1,X2),X0)
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).

fof(f38,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f61,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f38])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f10])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f7,axiom,(
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

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ v3_pre_topc(X2,X0)
      | ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f8,conjecture,(
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

fof(f9,negated_conjecture,(
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
    inference(negated_conjecture,[],[f8])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))
          & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
     => ( ~ m1_subset_1(k2_xboole_0(X2,sK5),u1_struct_0(k9_yellow_6(X0,X1)))
        & m1_subset_1(sK5,u1_struct_0(k9_yellow_6(X0,X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))
              & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
          & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
     => ( ? [X3] :
            ( ~ m1_subset_1(k2_xboole_0(sK4,X3),u1_struct_0(k9_yellow_6(X0,X1)))
            & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
        & m1_subset_1(sK4,u1_struct_0(k9_yellow_6(X0,X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
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
                ( ~ m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,sK3)))
                & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,sK3))) )
            & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,sK3))) )
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
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
                  ( ~ m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK2,X1)))
                  & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK2,X1))) )
              & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK2,X1))) )
          & m1_subset_1(X1,u1_struct_0(sK2)) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK4,sK5),u1_struct_0(k9_yellow_6(sK2,sK3)))
    & m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3)))
    & m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3)))
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f20,f34,f33,f32,f31])).

fof(f54,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f55,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f56,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f60,plain,(
    ~ m1_subset_1(k2_xboole_0(sK4,sK5),u1_struct_0(k9_yellow_6(sK2,sK3))) ),
    inference(cnf_transformation,[],[f35])).

fof(f57,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f35])).

fof(f59,plain,(
    m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3))) ),
    inference(cnf_transformation,[],[f35])).

fof(f6,axiom,(
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

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f27,plain,(
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

fof(f28,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f27])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(sK1(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( sK1(X0,X1,X2) = X2
      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f58,plain,(
    m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))) ),
    inference(cnf_transformation,[],[f35])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_pre_topc(X2,X0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_xboole_0(X1,X2),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( v3_pre_topc(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( v3_pre_topc(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,sK1(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1299,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k2_xboole_0(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(k2_xboole_0(X2,X0),X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1296,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(k2_xboole_0(X2,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_8,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1294,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_15,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_24,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_403,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_24])).

cnf(c_404,plain,
    ( ~ v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X1,X0)
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK2,X1)))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_403])).

cnf(c_23,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_22,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_408,plain,
    ( ~ v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X1,X0)
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK2,X1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_404,c_23,c_22])).

cnf(c_1285,plain,
    ( v3_pre_topc(X0,sK2) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(X1,X0) != iProver_top
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK2,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_408])).

cnf(c_7,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1295,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2131,plain,
    ( v3_pre_topc(X0,sK2) != iProver_top
    | m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,X1))) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1285,c_1295])).

cnf(c_18,negated_conjecture,
    ( ~ m1_subset_1(k2_xboole_0(sK4,sK5),u1_struct_0(k9_yellow_6(sK2,sK3))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1292,plain,
    ( m1_subset_1(k2_xboole_0(sK4,sK5),u1_struct_0(k9_yellow_6(sK2,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_4308,plain,
    ( v3_pre_topc(k2_xboole_0(sK4,sK5),sK2) != iProver_top
    | m1_subset_1(k2_xboole_0(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK3,k2_xboole_0(sK4,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2131,c_1292])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_28,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1291,plain,
    ( m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_11,plain,
    ( v3_pre_topc(sK1(X0,X1,X2),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_334,plain,
    ( v3_pre_topc(sK1(X0,X1,X2),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_24])).

cnf(c_335,plain,
    ( v3_pre_topc(sK1(sK2,X0,X1),sK2)
    | ~ m1_subset_1(X1,u1_struct_0(k9_yellow_6(sK2,X0)))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_334])).

cnf(c_339,plain,
    ( v3_pre_topc(sK1(sK2,X0,X1),sK2)
    | ~ m1_subset_1(X1,u1_struct_0(k9_yellow_6(sK2,X0)))
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_335,c_23,c_22])).

cnf(c_1288,plain,
    ( v3_pre_topc(sK1(sK2,X0,X1),sK2) = iProver_top
    | m1_subset_1(X1,u1_struct_0(k9_yellow_6(sK2,X0))) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_339])).

cnf(c_1907,plain,
    ( v3_pre_topc(sK1(sK2,sK3,sK5),sK2) = iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1291,c_1288])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK1(X1,X0,X2) = X2 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_451,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK1(X1,X0,X2) = X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_24])).

cnf(c_452,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | sK1(sK2,X1,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_451])).

cnf(c_456,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | sK1(sK2,X1,X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_452,c_23,c_22])).

cnf(c_1283,plain,
    ( sK1(sK2,X0,X1) = X1
    | m1_subset_1(X1,u1_struct_0(k9_yellow_6(sK2,X0))) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_456])).

cnf(c_1528,plain,
    ( sK1(sK2,sK3,sK5) = sK5
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1291,c_1283])).

cnf(c_1541,plain,
    ( sK1(sK2,sK3,sK5) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1528,c_28])).

cnf(c_1916,plain,
    ( v3_pre_topc(sK5,sK2) = iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1907,c_1541])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
    | m1_subset_1(sK1(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_430,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
    | m1_subset_1(sK1(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_24])).

cnf(c_431,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(sK1(sK2,X1,X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_430])).

cnf(c_435,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(sK1(sK2,X1,X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_431,c_23,c_22])).

cnf(c_1284,plain,
    ( m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,X1))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK1(sK2,X1,X0),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_435])).

cnf(c_1958,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1541,c_1284])).

cnf(c_30,plain,
    ( m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2895,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1958,c_28,c_30])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1290,plain,
    ( m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1529,plain,
    ( sK1(sK2,sK3,sK4) = sK4
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1290,c_1283])).

cnf(c_1623,plain,
    ( sK1(sK2,sK3,sK4) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1529,c_28])).

cnf(c_1959,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1623,c_1284])).

cnf(c_29,plain,
    ( m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3022,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1959,c_28,c_29])).

cnf(c_10,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ v3_pre_topc(X2,X1)
    | v3_pre_topc(k2_xboole_0(X2,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_525,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ v3_pre_topc(X2,X1)
    | v3_pre_topc(k2_xboole_0(X2,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_22])).

cnf(c_526,plain,
    ( ~ v3_pre_topc(X0,sK2)
    | ~ v3_pre_topc(X1,sK2)
    | v3_pre_topc(k2_xboole_0(X1,X0),sK2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_525])).

cnf(c_530,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | v3_pre_topc(k2_xboole_0(X1,X0),sK2)
    | ~ v3_pre_topc(X1,sK2)
    | ~ v3_pre_topc(X0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_526,c_23])).

cnf(c_531,plain,
    ( ~ v3_pre_topc(X0,sK2)
    | ~ v3_pre_topc(X1,sK2)
    | v3_pre_topc(k2_xboole_0(X1,X0),sK2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(renaming,[status(thm)],[c_530])).

cnf(c_1281,plain,
    ( v3_pre_topc(X0,sK2) != iProver_top
    | v3_pre_topc(X1,sK2) != iProver_top
    | v3_pre_topc(k2_xboole_0(X1,X0),sK2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_531])).

cnf(c_3028,plain,
    ( v3_pre_topc(X0,sK2) != iProver_top
    | v3_pre_topc(k2_xboole_0(sK4,X0),sK2) = iProver_top
    | v3_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3022,c_1281])).

cnf(c_1908,plain,
    ( v3_pre_topc(sK1(sK2,sK3,sK4),sK2) = iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1290,c_1288])).

cnf(c_1911,plain,
    ( v3_pre_topc(sK4,sK2) = iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1908,c_1623])).

cnf(c_3166,plain,
    ( v3_pre_topc(k2_xboole_0(sK4,X0),sK2) = iProver_top
    | v3_pre_topc(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3028,c_28,c_1911])).

cnf(c_3167,plain,
    ( v3_pre_topc(X0,sK2) != iProver_top
    | v3_pre_topc(k2_xboole_0(sK4,X0),sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3166])).

cnf(c_3177,plain,
    ( v3_pre_topc(k2_xboole_0(sK4,sK5),sK2) = iProver_top
    | v3_pre_topc(sK5,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2895,c_3167])).

cnf(c_4361,plain,
    ( m1_subset_1(k2_xboole_0(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(sK3,k2_xboole_0(sK4,sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4308,c_28,c_1916,c_3177])).

cnf(c_4367,plain,
    ( r1_tarski(k2_xboole_0(sK4,sK5),u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK3,k2_xboole_0(sK4,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1294,c_4361])).

cnf(c_4469,plain,
    ( r1_tarski(sK5,u1_struct_0(sK2)) != iProver_top
    | r1_tarski(sK4,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK3,k2_xboole_0(sK4,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1296,c_4367])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1293,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2900,plain,
    ( r1_tarski(sK5,u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2895,c_1293])).

cnf(c_3027,plain,
    ( r1_tarski(sK4,u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3022,c_1293])).

cnf(c_5572,plain,
    ( r2_hidden(sK3,k2_xboole_0(sK4,sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4469,c_2900,c_3027])).

cnf(c_5577,plain,
    ( r2_hidden(sK3,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1299,c_5572])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
    | r2_hidden(X0,sK1(X1,X0,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_472,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
    | r2_hidden(X0,sK1(X1,X0,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_24])).

cnf(c_473,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | r2_hidden(X1,sK1(sK2,X1,X0))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_472])).

cnf(c_477,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | r2_hidden(X1,sK1(sK2,X1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_473,c_23,c_22])).

cnf(c_1282,plain,
    ( m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,X1))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X1,sK1(sK2,X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_477])).

cnf(c_1630,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK3,sK1(sK2,sK3,sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1291,c_1282])).

cnf(c_1639,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK3,sK5) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1630,c_1541])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5577,c_1639,c_28])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:21:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 2.97/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.97/0.99  
% 2.97/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.97/0.99  
% 2.97/0.99  ------  iProver source info
% 2.97/0.99  
% 2.97/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.97/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.97/0.99  git: non_committed_changes: false
% 2.97/0.99  git: last_make_outside_of_git: false
% 2.97/0.99  
% 2.97/0.99  ------ 
% 2.97/0.99  
% 2.97/0.99  ------ Input Options
% 2.97/0.99  
% 2.97/0.99  --out_options                           all
% 2.97/0.99  --tptp_safe_out                         true
% 2.97/0.99  --problem_path                          ""
% 2.97/0.99  --include_path                          ""
% 2.97/0.99  --clausifier                            res/vclausify_rel
% 2.97/0.99  --clausifier_options                    --mode clausify
% 2.97/0.99  --stdin                                 false
% 2.97/0.99  --stats_out                             all
% 2.97/0.99  
% 2.97/0.99  ------ General Options
% 2.97/0.99  
% 2.97/0.99  --fof                                   false
% 2.97/0.99  --time_out_real                         305.
% 2.97/0.99  --time_out_virtual                      -1.
% 2.97/0.99  --symbol_type_check                     false
% 2.97/0.99  --clausify_out                          false
% 2.97/0.99  --sig_cnt_out                           false
% 2.97/0.99  --trig_cnt_out                          false
% 2.97/0.99  --trig_cnt_out_tolerance                1.
% 2.97/0.99  --trig_cnt_out_sk_spl                   false
% 2.97/0.99  --abstr_cl_out                          false
% 2.97/0.99  
% 2.97/0.99  ------ Global Options
% 2.97/0.99  
% 2.97/0.99  --schedule                              default
% 2.97/0.99  --add_important_lit                     false
% 2.97/0.99  --prop_solver_per_cl                    1000
% 2.97/0.99  --min_unsat_core                        false
% 2.97/0.99  --soft_assumptions                      false
% 2.97/0.99  --soft_lemma_size                       3
% 2.97/0.99  --prop_impl_unit_size                   0
% 2.97/0.99  --prop_impl_unit                        []
% 2.97/0.99  --share_sel_clauses                     true
% 2.97/0.99  --reset_solvers                         false
% 2.97/0.99  --bc_imp_inh                            [conj_cone]
% 2.97/0.99  --conj_cone_tolerance                   3.
% 2.97/0.99  --extra_neg_conj                        none
% 2.97/0.99  --large_theory_mode                     true
% 2.97/0.99  --prolific_symb_bound                   200
% 2.97/0.99  --lt_threshold                          2000
% 2.97/0.99  --clause_weak_htbl                      true
% 2.97/0.99  --gc_record_bc_elim                     false
% 2.97/0.99  
% 2.97/0.99  ------ Preprocessing Options
% 2.97/0.99  
% 2.97/0.99  --preprocessing_flag                    true
% 2.97/0.99  --time_out_prep_mult                    0.1
% 2.97/0.99  --splitting_mode                        input
% 2.97/0.99  --splitting_grd                         true
% 2.97/0.99  --splitting_cvd                         false
% 2.97/0.99  --splitting_cvd_svl                     false
% 2.97/0.99  --splitting_nvd                         32
% 2.97/0.99  --sub_typing                            true
% 2.97/0.99  --prep_gs_sim                           true
% 2.97/0.99  --prep_unflatten                        true
% 2.97/0.99  --prep_res_sim                          true
% 2.97/0.99  --prep_upred                            true
% 2.97/0.99  --prep_sem_filter                       exhaustive
% 2.97/0.99  --prep_sem_filter_out                   false
% 2.97/0.99  --pred_elim                             true
% 2.97/0.99  --res_sim_input                         true
% 2.97/0.99  --eq_ax_congr_red                       true
% 2.97/0.99  --pure_diseq_elim                       true
% 2.97/0.99  --brand_transform                       false
% 2.97/0.99  --non_eq_to_eq                          false
% 2.97/0.99  --prep_def_merge                        true
% 2.97/0.99  --prep_def_merge_prop_impl              false
% 2.97/0.99  --prep_def_merge_mbd                    true
% 2.97/0.99  --prep_def_merge_tr_red                 false
% 2.97/0.99  --prep_def_merge_tr_cl                  false
% 2.97/0.99  --smt_preprocessing                     true
% 2.97/0.99  --smt_ac_axioms                         fast
% 2.97/0.99  --preprocessed_out                      false
% 2.97/0.99  --preprocessed_stats                    false
% 2.97/0.99  
% 2.97/0.99  ------ Abstraction refinement Options
% 2.97/0.99  
% 2.97/0.99  --abstr_ref                             []
% 2.97/0.99  --abstr_ref_prep                        false
% 2.97/0.99  --abstr_ref_until_sat                   false
% 2.97/0.99  --abstr_ref_sig_restrict                funpre
% 2.97/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.97/0.99  --abstr_ref_under                       []
% 2.97/0.99  
% 2.97/0.99  ------ SAT Options
% 2.97/0.99  
% 2.97/0.99  --sat_mode                              false
% 2.97/0.99  --sat_fm_restart_options                ""
% 2.97/0.99  --sat_gr_def                            false
% 2.97/0.99  --sat_epr_types                         true
% 2.97/0.99  --sat_non_cyclic_types                  false
% 2.97/0.99  --sat_finite_models                     false
% 2.97/0.99  --sat_fm_lemmas                         false
% 2.97/0.99  --sat_fm_prep                           false
% 2.97/0.99  --sat_fm_uc_incr                        true
% 2.97/0.99  --sat_out_model                         small
% 2.97/0.99  --sat_out_clauses                       false
% 2.97/0.99  
% 2.97/0.99  ------ QBF Options
% 2.97/0.99  
% 2.97/0.99  --qbf_mode                              false
% 2.97/0.99  --qbf_elim_univ                         false
% 2.97/0.99  --qbf_dom_inst                          none
% 2.97/0.99  --qbf_dom_pre_inst                      false
% 2.97/0.99  --qbf_sk_in                             false
% 2.97/0.99  --qbf_pred_elim                         true
% 2.97/0.99  --qbf_split                             512
% 2.97/0.99  
% 2.97/0.99  ------ BMC1 Options
% 2.97/0.99  
% 2.97/0.99  --bmc1_incremental                      false
% 2.97/0.99  --bmc1_axioms                           reachable_all
% 2.97/0.99  --bmc1_min_bound                        0
% 2.97/0.99  --bmc1_max_bound                        -1
% 2.97/0.99  --bmc1_max_bound_default                -1
% 2.97/0.99  --bmc1_symbol_reachability              true
% 2.97/0.99  --bmc1_property_lemmas                  false
% 2.97/0.99  --bmc1_k_induction                      false
% 2.97/0.99  --bmc1_non_equiv_states                 false
% 2.97/0.99  --bmc1_deadlock                         false
% 2.97/0.99  --bmc1_ucm                              false
% 2.97/0.99  --bmc1_add_unsat_core                   none
% 2.97/0.99  --bmc1_unsat_core_children              false
% 2.97/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.97/0.99  --bmc1_out_stat                         full
% 2.97/0.99  --bmc1_ground_init                      false
% 2.97/0.99  --bmc1_pre_inst_next_state              false
% 2.97/0.99  --bmc1_pre_inst_state                   false
% 2.97/0.99  --bmc1_pre_inst_reach_state             false
% 2.97/0.99  --bmc1_out_unsat_core                   false
% 2.97/0.99  --bmc1_aig_witness_out                  false
% 2.97/0.99  --bmc1_verbose                          false
% 2.97/0.99  --bmc1_dump_clauses_tptp                false
% 2.97/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.97/0.99  --bmc1_dump_file                        -
% 2.97/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.97/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.97/0.99  --bmc1_ucm_extend_mode                  1
% 2.97/0.99  --bmc1_ucm_init_mode                    2
% 2.97/0.99  --bmc1_ucm_cone_mode                    none
% 2.97/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.97/0.99  --bmc1_ucm_relax_model                  4
% 2.97/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.97/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.97/0.99  --bmc1_ucm_layered_model                none
% 2.97/0.99  --bmc1_ucm_max_lemma_size               10
% 2.97/0.99  
% 2.97/0.99  ------ AIG Options
% 2.97/0.99  
% 2.97/0.99  --aig_mode                              false
% 2.97/0.99  
% 2.97/0.99  ------ Instantiation Options
% 2.97/0.99  
% 2.97/0.99  --instantiation_flag                    true
% 2.97/0.99  --inst_sos_flag                         false
% 2.97/0.99  --inst_sos_phase                        true
% 2.97/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.97/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.97/0.99  --inst_lit_sel_side                     num_symb
% 2.97/0.99  --inst_solver_per_active                1400
% 2.97/0.99  --inst_solver_calls_frac                1.
% 2.97/0.99  --inst_passive_queue_type               priority_queues
% 2.97/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.97/0.99  --inst_passive_queues_freq              [25;2]
% 2.97/0.99  --inst_dismatching                      true
% 2.97/0.99  --inst_eager_unprocessed_to_passive     true
% 2.97/0.99  --inst_prop_sim_given                   true
% 2.97/0.99  --inst_prop_sim_new                     false
% 2.97/0.99  --inst_subs_new                         false
% 2.97/0.99  --inst_eq_res_simp                      false
% 2.97/0.99  --inst_subs_given                       false
% 2.97/0.99  --inst_orphan_elimination               true
% 2.97/0.99  --inst_learning_loop_flag               true
% 2.97/0.99  --inst_learning_start                   3000
% 2.97/0.99  --inst_learning_factor                  2
% 2.97/0.99  --inst_start_prop_sim_after_learn       3
% 2.97/0.99  --inst_sel_renew                        solver
% 2.97/0.99  --inst_lit_activity_flag                true
% 2.97/0.99  --inst_restr_to_given                   false
% 2.97/0.99  --inst_activity_threshold               500
% 2.97/0.99  --inst_out_proof                        true
% 2.97/0.99  
% 2.97/0.99  ------ Resolution Options
% 2.97/0.99  
% 2.97/0.99  --resolution_flag                       true
% 2.97/0.99  --res_lit_sel                           adaptive
% 2.97/0.99  --res_lit_sel_side                      none
% 2.97/0.99  --res_ordering                          kbo
% 2.97/0.99  --res_to_prop_solver                    active
% 2.97/0.99  --res_prop_simpl_new                    false
% 2.97/0.99  --res_prop_simpl_given                  true
% 2.97/0.99  --res_passive_queue_type                priority_queues
% 2.97/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.97/0.99  --res_passive_queues_freq               [15;5]
% 2.97/0.99  --res_forward_subs                      full
% 2.97/0.99  --res_backward_subs                     full
% 2.97/0.99  --res_forward_subs_resolution           true
% 2.97/0.99  --res_backward_subs_resolution          true
% 2.97/0.99  --res_orphan_elimination                true
% 2.97/0.99  --res_time_limit                        2.
% 2.97/0.99  --res_out_proof                         true
% 2.97/0.99  
% 2.97/0.99  ------ Superposition Options
% 2.97/0.99  
% 2.97/0.99  --superposition_flag                    true
% 2.97/0.99  --sup_passive_queue_type                priority_queues
% 2.97/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.97/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.97/0.99  --demod_completeness_check              fast
% 2.97/0.99  --demod_use_ground                      true
% 2.97/0.99  --sup_to_prop_solver                    passive
% 2.97/0.99  --sup_prop_simpl_new                    true
% 2.97/0.99  --sup_prop_simpl_given                  true
% 2.97/0.99  --sup_fun_splitting                     false
% 2.97/0.99  --sup_smt_interval                      50000
% 2.97/0.99  
% 2.97/0.99  ------ Superposition Simplification Setup
% 2.97/0.99  
% 2.97/0.99  --sup_indices_passive                   []
% 2.97/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.97/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/0.99  --sup_full_bw                           [BwDemod]
% 2.97/0.99  --sup_immed_triv                        [TrivRules]
% 2.97/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.97/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/0.99  --sup_immed_bw_main                     []
% 2.97/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.97/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.97/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.97/0.99  
% 2.97/0.99  ------ Combination Options
% 2.97/0.99  
% 2.97/0.99  --comb_res_mult                         3
% 2.97/0.99  --comb_sup_mult                         2
% 2.97/0.99  --comb_inst_mult                        10
% 2.97/0.99  
% 2.97/0.99  ------ Debug Options
% 2.97/0.99  
% 2.97/0.99  --dbg_backtrace                         false
% 2.97/0.99  --dbg_dump_prop_clauses                 false
% 2.97/0.99  --dbg_dump_prop_clauses_file            -
% 2.97/0.99  --dbg_out_stat                          false
% 2.97/0.99  ------ Parsing...
% 2.97/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.97/0.99  
% 2.97/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.97/0.99  
% 2.97/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.97/0.99  
% 2.97/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.97/0.99  ------ Proving...
% 2.97/0.99  ------ Problem Properties 
% 2.97/0.99  
% 2.97/0.99  
% 2.97/0.99  clauses                                 22
% 2.97/0.99  conjectures                             4
% 2.97/0.99  EPR                                     1
% 2.97/0.99  Horn                                    20
% 2.97/0.99  unary                                   4
% 2.97/0.99  binary                                  5
% 2.97/0.99  lits                                    60
% 2.97/0.99  lits eq                                 4
% 2.97/0.99  fd_pure                                 0
% 2.97/0.99  fd_pseudo                               0
% 2.97/0.99  fd_cond                                 0
% 2.97/0.99  fd_pseudo_cond                          3
% 2.97/0.99  AC symbols                              0
% 2.97/0.99  
% 2.97/0.99  ------ Schedule dynamic 5 is on 
% 2.97/0.99  
% 2.97/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.97/0.99  
% 2.97/0.99  
% 2.97/0.99  ------ 
% 2.97/0.99  Current options:
% 2.97/0.99  ------ 
% 2.97/0.99  
% 2.97/0.99  ------ Input Options
% 2.97/0.99  
% 2.97/0.99  --out_options                           all
% 2.97/0.99  --tptp_safe_out                         true
% 2.97/0.99  --problem_path                          ""
% 2.97/0.99  --include_path                          ""
% 2.97/0.99  --clausifier                            res/vclausify_rel
% 2.97/0.99  --clausifier_options                    --mode clausify
% 2.97/0.99  --stdin                                 false
% 2.97/0.99  --stats_out                             all
% 2.97/0.99  
% 2.97/0.99  ------ General Options
% 2.97/0.99  
% 2.97/0.99  --fof                                   false
% 2.97/0.99  --time_out_real                         305.
% 2.97/0.99  --time_out_virtual                      -1.
% 2.97/0.99  --symbol_type_check                     false
% 2.97/0.99  --clausify_out                          false
% 2.97/0.99  --sig_cnt_out                           false
% 2.97/0.99  --trig_cnt_out                          false
% 2.97/0.99  --trig_cnt_out_tolerance                1.
% 2.97/0.99  --trig_cnt_out_sk_spl                   false
% 2.97/0.99  --abstr_cl_out                          false
% 2.97/0.99  
% 2.97/0.99  ------ Global Options
% 2.97/0.99  
% 2.97/0.99  --schedule                              default
% 2.97/0.99  --add_important_lit                     false
% 2.97/0.99  --prop_solver_per_cl                    1000
% 2.97/0.99  --min_unsat_core                        false
% 2.97/0.99  --soft_assumptions                      false
% 2.97/0.99  --soft_lemma_size                       3
% 2.97/0.99  --prop_impl_unit_size                   0
% 2.97/0.99  --prop_impl_unit                        []
% 2.97/0.99  --share_sel_clauses                     true
% 2.97/0.99  --reset_solvers                         false
% 2.97/0.99  --bc_imp_inh                            [conj_cone]
% 2.97/0.99  --conj_cone_tolerance                   3.
% 2.97/0.99  --extra_neg_conj                        none
% 2.97/0.99  --large_theory_mode                     true
% 2.97/0.99  --prolific_symb_bound                   200
% 2.97/0.99  --lt_threshold                          2000
% 2.97/0.99  --clause_weak_htbl                      true
% 2.97/0.99  --gc_record_bc_elim                     false
% 2.97/0.99  
% 2.97/0.99  ------ Preprocessing Options
% 2.97/0.99  
% 2.97/0.99  --preprocessing_flag                    true
% 2.97/0.99  --time_out_prep_mult                    0.1
% 2.97/0.99  --splitting_mode                        input
% 2.97/0.99  --splitting_grd                         true
% 2.97/0.99  --splitting_cvd                         false
% 2.97/0.99  --splitting_cvd_svl                     false
% 2.97/0.99  --splitting_nvd                         32
% 2.97/0.99  --sub_typing                            true
% 2.97/0.99  --prep_gs_sim                           true
% 2.97/0.99  --prep_unflatten                        true
% 2.97/0.99  --prep_res_sim                          true
% 2.97/0.99  --prep_upred                            true
% 2.97/0.99  --prep_sem_filter                       exhaustive
% 2.97/0.99  --prep_sem_filter_out                   false
% 2.97/0.99  --pred_elim                             true
% 2.97/0.99  --res_sim_input                         true
% 2.97/0.99  --eq_ax_congr_red                       true
% 2.97/0.99  --pure_diseq_elim                       true
% 2.97/0.99  --brand_transform                       false
% 2.97/0.99  --non_eq_to_eq                          false
% 2.97/0.99  --prep_def_merge                        true
% 2.97/0.99  --prep_def_merge_prop_impl              false
% 2.97/0.99  --prep_def_merge_mbd                    true
% 2.97/0.99  --prep_def_merge_tr_red                 false
% 2.97/0.99  --prep_def_merge_tr_cl                  false
% 2.97/0.99  --smt_preprocessing                     true
% 2.97/0.99  --smt_ac_axioms                         fast
% 2.97/0.99  --preprocessed_out                      false
% 2.97/0.99  --preprocessed_stats                    false
% 2.97/0.99  
% 2.97/0.99  ------ Abstraction refinement Options
% 2.97/0.99  
% 2.97/0.99  --abstr_ref                             []
% 2.97/0.99  --abstr_ref_prep                        false
% 2.97/0.99  --abstr_ref_until_sat                   false
% 2.97/0.99  --abstr_ref_sig_restrict                funpre
% 2.97/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.97/0.99  --abstr_ref_under                       []
% 2.97/0.99  
% 2.97/0.99  ------ SAT Options
% 2.97/0.99  
% 2.97/0.99  --sat_mode                              false
% 2.97/0.99  --sat_fm_restart_options                ""
% 2.97/0.99  --sat_gr_def                            false
% 2.97/0.99  --sat_epr_types                         true
% 2.97/0.99  --sat_non_cyclic_types                  false
% 2.97/0.99  --sat_finite_models                     false
% 2.97/0.99  --sat_fm_lemmas                         false
% 2.97/0.99  --sat_fm_prep                           false
% 2.97/0.99  --sat_fm_uc_incr                        true
% 2.97/0.99  --sat_out_model                         small
% 2.97/0.99  --sat_out_clauses                       false
% 2.97/0.99  
% 2.97/0.99  ------ QBF Options
% 2.97/0.99  
% 2.97/0.99  --qbf_mode                              false
% 2.97/0.99  --qbf_elim_univ                         false
% 2.97/0.99  --qbf_dom_inst                          none
% 2.97/0.99  --qbf_dom_pre_inst                      false
% 2.97/0.99  --qbf_sk_in                             false
% 2.97/0.99  --qbf_pred_elim                         true
% 2.97/0.99  --qbf_split                             512
% 2.97/0.99  
% 2.97/0.99  ------ BMC1 Options
% 2.97/0.99  
% 2.97/0.99  --bmc1_incremental                      false
% 2.97/0.99  --bmc1_axioms                           reachable_all
% 2.97/0.99  --bmc1_min_bound                        0
% 2.97/0.99  --bmc1_max_bound                        -1
% 2.97/0.99  --bmc1_max_bound_default                -1
% 2.97/0.99  --bmc1_symbol_reachability              true
% 2.97/0.99  --bmc1_property_lemmas                  false
% 2.97/0.99  --bmc1_k_induction                      false
% 2.97/0.99  --bmc1_non_equiv_states                 false
% 2.97/0.99  --bmc1_deadlock                         false
% 2.97/0.99  --bmc1_ucm                              false
% 2.97/0.99  --bmc1_add_unsat_core                   none
% 2.97/0.99  --bmc1_unsat_core_children              false
% 2.97/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.97/0.99  --bmc1_out_stat                         full
% 2.97/0.99  --bmc1_ground_init                      false
% 2.97/0.99  --bmc1_pre_inst_next_state              false
% 2.97/0.99  --bmc1_pre_inst_state                   false
% 2.97/0.99  --bmc1_pre_inst_reach_state             false
% 2.97/0.99  --bmc1_out_unsat_core                   false
% 2.97/0.99  --bmc1_aig_witness_out                  false
% 2.97/0.99  --bmc1_verbose                          false
% 2.97/0.99  --bmc1_dump_clauses_tptp                false
% 2.97/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.97/0.99  --bmc1_dump_file                        -
% 2.97/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.97/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.97/0.99  --bmc1_ucm_extend_mode                  1
% 2.97/0.99  --bmc1_ucm_init_mode                    2
% 2.97/0.99  --bmc1_ucm_cone_mode                    none
% 2.97/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.97/0.99  --bmc1_ucm_relax_model                  4
% 2.97/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.97/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.97/0.99  --bmc1_ucm_layered_model                none
% 2.97/0.99  --bmc1_ucm_max_lemma_size               10
% 2.97/0.99  
% 2.97/0.99  ------ AIG Options
% 2.97/0.99  
% 2.97/0.99  --aig_mode                              false
% 2.97/0.99  
% 2.97/0.99  ------ Instantiation Options
% 2.97/0.99  
% 2.97/0.99  --instantiation_flag                    true
% 2.97/0.99  --inst_sos_flag                         false
% 2.97/0.99  --inst_sos_phase                        true
% 2.97/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.97/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.97/0.99  --inst_lit_sel_side                     none
% 2.97/0.99  --inst_solver_per_active                1400
% 2.97/0.99  --inst_solver_calls_frac                1.
% 2.97/0.99  --inst_passive_queue_type               priority_queues
% 2.97/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.97/0.99  --inst_passive_queues_freq              [25;2]
% 2.97/0.99  --inst_dismatching                      true
% 2.97/0.99  --inst_eager_unprocessed_to_passive     true
% 2.97/0.99  --inst_prop_sim_given                   true
% 2.97/0.99  --inst_prop_sim_new                     false
% 2.97/0.99  --inst_subs_new                         false
% 2.97/0.99  --inst_eq_res_simp                      false
% 2.97/0.99  --inst_subs_given                       false
% 2.97/0.99  --inst_orphan_elimination               true
% 2.97/0.99  --inst_learning_loop_flag               true
% 2.97/0.99  --inst_learning_start                   3000
% 2.97/0.99  --inst_learning_factor                  2
% 2.97/0.99  --inst_start_prop_sim_after_learn       3
% 2.97/0.99  --inst_sel_renew                        solver
% 2.97/0.99  --inst_lit_activity_flag                true
% 2.97/0.99  --inst_restr_to_given                   false
% 2.97/0.99  --inst_activity_threshold               500
% 2.97/0.99  --inst_out_proof                        true
% 2.97/0.99  
% 2.97/0.99  ------ Resolution Options
% 2.97/0.99  
% 2.97/0.99  --resolution_flag                       false
% 2.97/0.99  --res_lit_sel                           adaptive
% 2.97/0.99  --res_lit_sel_side                      none
% 2.97/0.99  --res_ordering                          kbo
% 2.97/0.99  --res_to_prop_solver                    active
% 2.97/0.99  --res_prop_simpl_new                    false
% 2.97/0.99  --res_prop_simpl_given                  true
% 2.97/0.99  --res_passive_queue_type                priority_queues
% 2.97/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.97/0.99  --res_passive_queues_freq               [15;5]
% 2.97/0.99  --res_forward_subs                      full
% 2.97/0.99  --res_backward_subs                     full
% 2.97/0.99  --res_forward_subs_resolution           true
% 2.97/0.99  --res_backward_subs_resolution          true
% 2.97/0.99  --res_orphan_elimination                true
% 2.97/0.99  --res_time_limit                        2.
% 2.97/0.99  --res_out_proof                         true
% 2.97/0.99  
% 2.97/0.99  ------ Superposition Options
% 2.97/0.99  
% 2.97/0.99  --superposition_flag                    true
% 2.97/0.99  --sup_passive_queue_type                priority_queues
% 2.97/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.97/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.97/0.99  --demod_completeness_check              fast
% 2.97/0.99  --demod_use_ground                      true
% 2.97/0.99  --sup_to_prop_solver                    passive
% 2.97/0.99  --sup_prop_simpl_new                    true
% 2.97/0.99  --sup_prop_simpl_given                  true
% 2.97/0.99  --sup_fun_splitting                     false
% 2.97/0.99  --sup_smt_interval                      50000
% 2.97/0.99  
% 2.97/0.99  ------ Superposition Simplification Setup
% 2.97/0.99  
% 2.97/0.99  --sup_indices_passive                   []
% 2.97/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.97/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/0.99  --sup_full_bw                           [BwDemod]
% 2.97/0.99  --sup_immed_triv                        [TrivRules]
% 2.97/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.97/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/0.99  --sup_immed_bw_main                     []
% 2.97/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.97/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.97/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.97/0.99  
% 2.97/0.99  ------ Combination Options
% 2.97/0.99  
% 2.97/0.99  --comb_res_mult                         3
% 2.97/0.99  --comb_sup_mult                         2
% 2.97/0.99  --comb_inst_mult                        10
% 2.97/0.99  
% 2.97/0.99  ------ Debug Options
% 2.97/0.99  
% 2.97/0.99  --dbg_backtrace                         false
% 2.97/0.99  --dbg_dump_prop_clauses                 false
% 2.97/0.99  --dbg_dump_prop_clauses_file            -
% 2.97/0.99  --dbg_out_stat                          false
% 2.97/0.99  
% 2.97/0.99  
% 2.97/0.99  
% 2.97/0.99  
% 2.97/0.99  ------ Proving...
% 2.97/0.99  
% 2.97/0.99  
% 2.97/0.99  % SZS status Theorem for theBenchmark.p
% 2.97/0.99  
% 2.97/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.97/0.99  
% 2.97/0.99  fof(f1,axiom,(
% 2.97/0.99    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 2.97/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/0.99  
% 2.97/0.99  fof(f21,plain,(
% 2.97/0.99    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.97/0.99    inference(nnf_transformation,[],[f1])).
% 2.97/0.99  
% 2.97/0.99  fof(f22,plain,(
% 2.97/0.99    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.97/0.99    inference(flattening,[],[f21])).
% 2.97/0.99  
% 2.97/0.99  fof(f23,plain,(
% 2.97/0.99    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.97/0.99    inference(rectify,[],[f22])).
% 2.97/0.99  
% 2.97/0.99  fof(f24,plain,(
% 2.97/0.99    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 2.97/0.99    introduced(choice_axiom,[])).
% 2.97/0.99  
% 2.97/0.99  fof(f25,plain,(
% 2.97/0.99    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.97/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).
% 2.97/0.99  
% 2.97/0.99  fof(f38,plain,(
% 2.97/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 2.97/0.99    inference(cnf_transformation,[],[f25])).
% 2.97/0.99  
% 2.97/0.99  fof(f61,plain,(
% 2.97/0.99    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 2.97/0.99    inference(equality_resolution,[],[f38])).
% 2.97/0.99  
% 2.97/0.99  fof(f2,axiom,(
% 2.97/0.99    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 2.97/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/0.99  
% 2.97/0.99  fof(f10,plain,(
% 2.97/0.99    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 2.97/0.99    inference(ennf_transformation,[],[f2])).
% 2.97/0.99  
% 2.97/0.99  fof(f11,plain,(
% 2.97/0.99    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 2.97/0.99    inference(flattening,[],[f10])).
% 2.97/0.99  
% 2.97/0.99  fof(f42,plain,(
% 2.97/0.99    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 2.97/0.99    inference(cnf_transformation,[],[f11])).
% 2.97/0.99  
% 2.97/0.99  fof(f4,axiom,(
% 2.97/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.97/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/0.99  
% 2.97/0.99  fof(f26,plain,(
% 2.97/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.97/0.99    inference(nnf_transformation,[],[f4])).
% 2.97/0.99  
% 2.97/0.99  fof(f45,plain,(
% 2.97/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.97/0.99    inference(cnf_transformation,[],[f26])).
% 2.97/0.99  
% 2.97/0.99  fof(f7,axiom,(
% 2.97/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))))))),
% 2.97/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/0.99  
% 2.97/0.99  fof(f17,plain,(
% 2.97/0.99    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.97/0.99    inference(ennf_transformation,[],[f7])).
% 2.97/0.99  
% 2.97/0.99  fof(f18,plain,(
% 2.97/0.99    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.97/0.99    inference(flattening,[],[f17])).
% 2.97/0.99  
% 2.97/0.99  fof(f29,plain,(
% 2.97/0.99    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | (~v3_pre_topc(X2,X0) | ~r2_hidden(X1,X2))) & ((v3_pre_topc(X2,X0) & r2_hidden(X1,X2)) | ~r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.97/0.99    inference(nnf_transformation,[],[f18])).
% 2.97/0.99  
% 2.97/0.99  fof(f30,plain,(
% 2.97/0.99    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~v3_pre_topc(X2,X0) | ~r2_hidden(X1,X2)) & ((v3_pre_topc(X2,X0) & r2_hidden(X1,X2)) | ~r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.97/0.99    inference(flattening,[],[f29])).
% 2.97/0.99  
% 2.97/0.99  fof(f53,plain,(
% 2.97/0.99    ( ! [X2,X0,X1] : (r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~v3_pre_topc(X2,X0) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.97/0.99    inference(cnf_transformation,[],[f30])).
% 2.97/0.99  
% 2.97/0.99  fof(f8,conjecture,(
% 2.97/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) => m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))))))),
% 2.97/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/0.99  
% 2.97/0.99  fof(f9,negated_conjecture,(
% 2.97/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) => m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))))))),
% 2.97/0.99    inference(negated_conjecture,[],[f8])).
% 2.97/0.99  
% 2.97/0.99  fof(f19,plain,(
% 2.97/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.97/0.99    inference(ennf_transformation,[],[f9])).
% 2.97/0.99  
% 2.97/0.99  fof(f20,plain,(
% 2.97/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.97/0.99    inference(flattening,[],[f19])).
% 2.97/0.99  
% 2.97/0.99  fof(f34,plain,(
% 2.97/0.99    ( ! [X2,X0,X1] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) => (~m1_subset_1(k2_xboole_0(X2,sK5),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(sK5,u1_struct_0(k9_yellow_6(X0,X1))))) )),
% 2.97/0.99    introduced(choice_axiom,[])).
% 2.97/0.99  
% 2.97/0.99  fof(f33,plain,(
% 2.97/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) => (? [X3] : (~m1_subset_1(k2_xboole_0(sK4,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(sK4,u1_struct_0(k9_yellow_6(X0,X1))))) )),
% 2.97/0.99    introduced(choice_axiom,[])).
% 2.97/0.99  
% 2.97/0.99  fof(f32,plain,(
% 2.97/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,sK3))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,sK3)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,sK3)))) & m1_subset_1(sK3,u1_struct_0(X0)))) )),
% 2.97/1.00    introduced(choice_axiom,[])).
% 2.97/1.00  
% 2.97/1.00  fof(f31,plain,(
% 2.97/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK2,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK2,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK2,X1)))) & m1_subset_1(X1,u1_struct_0(sK2))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 2.97/1.00    introduced(choice_axiom,[])).
% 2.97/1.00  
% 2.97/1.00  fof(f35,plain,(
% 2.97/1.00    (((~m1_subset_1(k2_xboole_0(sK4,sK5),u1_struct_0(k9_yellow_6(sK2,sK3))) & m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3)))) & m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3)))) & m1_subset_1(sK3,u1_struct_0(sK2))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 2.97/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f20,f34,f33,f32,f31])).
% 2.97/1.00  
% 2.97/1.00  fof(f54,plain,(
% 2.97/1.00    ~v2_struct_0(sK2)),
% 2.97/1.00    inference(cnf_transformation,[],[f35])).
% 2.97/1.00  
% 2.97/1.00  fof(f55,plain,(
% 2.97/1.00    v2_pre_topc(sK2)),
% 2.97/1.00    inference(cnf_transformation,[],[f35])).
% 2.97/1.00  
% 2.97/1.00  fof(f56,plain,(
% 2.97/1.00    l1_pre_topc(sK2)),
% 2.97/1.00    inference(cnf_transformation,[],[f35])).
% 2.97/1.00  
% 2.97/1.00  fof(f3,axiom,(
% 2.97/1.00    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 2.97/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/1.00  
% 2.97/1.00  fof(f12,plain,(
% 2.97/1.00    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 2.97/1.00    inference(ennf_transformation,[],[f3])).
% 2.97/1.00  
% 2.97/1.00  fof(f43,plain,(
% 2.97/1.00    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 2.97/1.00    inference(cnf_transformation,[],[f12])).
% 2.97/1.00  
% 2.97/1.00  fof(f60,plain,(
% 2.97/1.00    ~m1_subset_1(k2_xboole_0(sK4,sK5),u1_struct_0(k9_yellow_6(sK2,sK3)))),
% 2.97/1.00    inference(cnf_transformation,[],[f35])).
% 2.97/1.00  
% 2.97/1.00  fof(f57,plain,(
% 2.97/1.00    m1_subset_1(sK3,u1_struct_0(sK2))),
% 2.97/1.00    inference(cnf_transformation,[],[f35])).
% 2.97/1.00  
% 2.97/1.00  fof(f59,plain,(
% 2.97/1.00    m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3)))),
% 2.97/1.00    inference(cnf_transformation,[],[f35])).
% 2.97/1.00  
% 2.97/1.00  fof(f6,axiom,(
% 2.97/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ? [X3] : (v3_pre_topc(X3,X0) & r2_hidden(X1,X3) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))))),
% 2.97/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/1.00  
% 2.97/1.00  fof(f15,plain,(
% 2.97/1.00    ! [X0] : (! [X1] : (! [X2] : (? [X3] : (v3_pre_topc(X3,X0) & r2_hidden(X1,X3) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.97/1.00    inference(ennf_transformation,[],[f6])).
% 2.97/1.00  
% 2.97/1.00  fof(f16,plain,(
% 2.97/1.00    ! [X0] : (! [X1] : (! [X2] : (? [X3] : (v3_pre_topc(X3,X0) & r2_hidden(X1,X3) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.97/1.00    inference(flattening,[],[f15])).
% 2.97/1.00  
% 2.97/1.00  fof(f27,plain,(
% 2.97/1.00    ! [X2,X1,X0] : (? [X3] : (v3_pre_topc(X3,X0) & r2_hidden(X1,X3) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (v3_pre_topc(sK1(X0,X1,X2),X0) & r2_hidden(X1,sK1(X0,X1,X2)) & sK1(X0,X1,X2) = X2 & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.97/1.00    introduced(choice_axiom,[])).
% 2.97/1.00  
% 2.97/1.00  fof(f28,plain,(
% 2.97/1.00    ! [X0] : (! [X1] : (! [X2] : ((v3_pre_topc(sK1(X0,X1,X2),X0) & r2_hidden(X1,sK1(X0,X1,X2)) & sK1(X0,X1,X2) = X2 & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.97/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f27])).
% 2.97/1.00  
% 2.97/1.00  fof(f50,plain,(
% 2.97/1.00    ( ! [X2,X0,X1] : (v3_pre_topc(sK1(X0,X1,X2),X0) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.97/1.00    inference(cnf_transformation,[],[f28])).
% 2.97/1.00  
% 2.97/1.00  fof(f48,plain,(
% 2.97/1.00    ( ! [X2,X0,X1] : (sK1(X0,X1,X2) = X2 | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.97/1.00    inference(cnf_transformation,[],[f28])).
% 2.97/1.00  
% 2.97/1.00  fof(f47,plain,(
% 2.97/1.00    ( ! [X2,X0,X1] : (m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.97/1.00    inference(cnf_transformation,[],[f28])).
% 2.97/1.00  
% 2.97/1.00  fof(f58,plain,(
% 2.97/1.00    m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3)))),
% 2.97/1.00    inference(cnf_transformation,[],[f35])).
% 2.97/1.00  
% 2.97/1.00  fof(f5,axiom,(
% 2.97/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X2,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_xboole_0(X1,X2),X0))),
% 2.97/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/1.00  
% 2.97/1.00  fof(f13,plain,(
% 2.97/1.00    ! [X0,X1,X2] : (v3_pre_topc(k2_xboole_0(X1,X2),X0) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.97/1.00    inference(ennf_transformation,[],[f5])).
% 2.97/1.00  
% 2.97/1.00  fof(f14,plain,(
% 2.97/1.00    ! [X0,X1,X2] : (v3_pre_topc(k2_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.97/1.00    inference(flattening,[],[f13])).
% 2.97/1.00  
% 2.97/1.00  fof(f46,plain,(
% 2.97/1.00    ( ! [X2,X0,X1] : (v3_pre_topc(k2_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.97/1.00    inference(cnf_transformation,[],[f14])).
% 2.97/1.00  
% 2.97/1.00  fof(f44,plain,(
% 2.97/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.97/1.00    inference(cnf_transformation,[],[f26])).
% 2.97/1.00  
% 2.97/1.00  fof(f49,plain,(
% 2.97/1.00    ( ! [X2,X0,X1] : (r2_hidden(X1,sK1(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.97/1.00    inference(cnf_transformation,[],[f28])).
% 2.97/1.00  
% 2.97/1.00  cnf(c_3,plain,
% 2.97/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,k2_xboole_0(X2,X1)) ),
% 2.97/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1299,plain,
% 2.97/1.00      ( r2_hidden(X0,X1) != iProver_top
% 2.97/1.00      | r2_hidden(X0,k2_xboole_0(X2,X1)) = iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_6,plain,
% 2.97/1.00      ( ~ r1_tarski(X0,X1)
% 2.97/1.00      | ~ r1_tarski(X2,X1)
% 2.97/1.00      | r1_tarski(k2_xboole_0(X2,X0),X1) ),
% 2.97/1.00      inference(cnf_transformation,[],[f42]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1296,plain,
% 2.97/1.00      ( r1_tarski(X0,X1) != iProver_top
% 2.97/1.00      | r1_tarski(X2,X1) != iProver_top
% 2.97/1.00      | r1_tarski(k2_xboole_0(X2,X0),X1) = iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_8,plain,
% 2.97/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.97/1.00      inference(cnf_transformation,[],[f45]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1294,plain,
% 2.97/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 2.97/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_15,plain,
% 2.97/1.00      ( ~ v3_pre_topc(X0,X1)
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.97/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.97/1.00      | ~ r2_hidden(X2,X0)
% 2.97/1.00      | r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
% 2.97/1.00      | v2_struct_0(X1)
% 2.97/1.00      | ~ v2_pre_topc(X1)
% 2.97/1.00      | ~ l1_pre_topc(X1) ),
% 2.97/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_24,negated_conjecture,
% 2.97/1.00      ( ~ v2_struct_0(sK2) ),
% 2.97/1.00      inference(cnf_transformation,[],[f54]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_403,plain,
% 2.97/1.00      ( ~ v3_pre_topc(X0,X1)
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.97/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.97/1.00      | ~ r2_hidden(X2,X0)
% 2.97/1.00      | r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
% 2.97/1.00      | ~ v2_pre_topc(X1)
% 2.97/1.00      | ~ l1_pre_topc(X1)
% 2.97/1.00      | sK2 != X1 ),
% 2.97/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_24]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_404,plain,
% 2.97/1.00      ( ~ v3_pre_topc(X0,sK2)
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.97/1.00      | ~ r2_hidden(X1,X0)
% 2.97/1.00      | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK2,X1)))
% 2.97/1.00      | ~ v2_pre_topc(sK2)
% 2.97/1.00      | ~ l1_pre_topc(sK2) ),
% 2.97/1.00      inference(unflattening,[status(thm)],[c_403]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_23,negated_conjecture,
% 2.97/1.00      ( v2_pre_topc(sK2) ),
% 2.97/1.00      inference(cnf_transformation,[],[f55]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_22,negated_conjecture,
% 2.97/1.00      ( l1_pre_topc(sK2) ),
% 2.97/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_408,plain,
% 2.97/1.00      ( ~ v3_pre_topc(X0,sK2)
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.97/1.00      | ~ r2_hidden(X1,X0)
% 2.97/1.00      | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK2,X1))) ),
% 2.97/1.00      inference(global_propositional_subsumption,
% 2.97/1.00                [status(thm)],
% 2.97/1.00                [c_404,c_23,c_22]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1285,plain,
% 2.97/1.00      ( v3_pre_topc(X0,sK2) != iProver_top
% 2.97/1.00      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
% 2.97/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.97/1.00      | r2_hidden(X1,X0) != iProver_top
% 2.97/1.00      | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK2,X1))) = iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_408]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_7,plain,
% 2.97/1.00      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 2.97/1.00      inference(cnf_transformation,[],[f43]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1295,plain,
% 2.97/1.00      ( m1_subset_1(X0,X1) = iProver_top
% 2.97/1.00      | r2_hidden(X0,X1) != iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_2131,plain,
% 2.97/1.00      ( v3_pre_topc(X0,sK2) != iProver_top
% 2.97/1.00      | m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,X1))) = iProver_top
% 2.97/1.00      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
% 2.97/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.97/1.00      | r2_hidden(X1,X0) != iProver_top ),
% 2.97/1.00      inference(superposition,[status(thm)],[c_1285,c_1295]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_18,negated_conjecture,
% 2.97/1.00      ( ~ m1_subset_1(k2_xboole_0(sK4,sK5),u1_struct_0(k9_yellow_6(sK2,sK3))) ),
% 2.97/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1292,plain,
% 2.97/1.00      ( m1_subset_1(k2_xboole_0(sK4,sK5),u1_struct_0(k9_yellow_6(sK2,sK3))) != iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_4308,plain,
% 2.97/1.00      ( v3_pre_topc(k2_xboole_0(sK4,sK5),sK2) != iProver_top
% 2.97/1.00      | m1_subset_1(k2_xboole_0(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.97/1.00      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 2.97/1.00      | r2_hidden(sK3,k2_xboole_0(sK4,sK5)) != iProver_top ),
% 2.97/1.00      inference(superposition,[status(thm)],[c_2131,c_1292]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_21,negated_conjecture,
% 2.97/1.00      ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 2.97/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_28,plain,
% 2.97/1.00      ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_19,negated_conjecture,
% 2.97/1.00      ( m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3))) ),
% 2.97/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1291,plain,
% 2.97/1.00      ( m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3))) = iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_11,plain,
% 2.97/1.00      ( v3_pre_topc(sK1(X0,X1,X2),X0)
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
% 2.97/1.00      | v2_struct_0(X0)
% 2.97/1.00      | ~ v2_pre_topc(X0)
% 2.97/1.00      | ~ l1_pre_topc(X0) ),
% 2.97/1.00      inference(cnf_transformation,[],[f50]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_334,plain,
% 2.97/1.00      ( v3_pre_topc(sK1(X0,X1,X2),X0)
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
% 2.97/1.00      | ~ v2_pre_topc(X0)
% 2.97/1.00      | ~ l1_pre_topc(X0)
% 2.97/1.00      | sK2 != X0 ),
% 2.97/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_24]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_335,plain,
% 2.97/1.00      ( v3_pre_topc(sK1(sK2,X0,X1),sK2)
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(k9_yellow_6(sK2,X0)))
% 2.97/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.97/1.00      | ~ v2_pre_topc(sK2)
% 2.97/1.00      | ~ l1_pre_topc(sK2) ),
% 2.97/1.00      inference(unflattening,[status(thm)],[c_334]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_339,plain,
% 2.97/1.00      ( v3_pre_topc(sK1(sK2,X0,X1),sK2)
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(k9_yellow_6(sK2,X0)))
% 2.97/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
% 2.97/1.00      inference(global_propositional_subsumption,
% 2.97/1.00                [status(thm)],
% 2.97/1.00                [c_335,c_23,c_22]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1288,plain,
% 2.97/1.00      ( v3_pre_topc(sK1(sK2,X0,X1),sK2) = iProver_top
% 2.97/1.00      | m1_subset_1(X1,u1_struct_0(k9_yellow_6(sK2,X0))) != iProver_top
% 2.97/1.00      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_339]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1907,plain,
% 2.97/1.00      ( v3_pre_topc(sK1(sK2,sK3,sK5),sK2) = iProver_top
% 2.97/1.00      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
% 2.97/1.00      inference(superposition,[status(thm)],[c_1291,c_1288]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_13,plain,
% 2.97/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
% 2.97/1.00      | v2_struct_0(X1)
% 2.97/1.00      | ~ v2_pre_topc(X1)
% 2.97/1.00      | ~ l1_pre_topc(X1)
% 2.97/1.00      | sK1(X1,X0,X2) = X2 ),
% 2.97/1.00      inference(cnf_transformation,[],[f48]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_451,plain,
% 2.97/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
% 2.97/1.00      | ~ v2_pre_topc(X1)
% 2.97/1.00      | ~ l1_pre_topc(X1)
% 2.97/1.00      | sK1(X1,X0,X2) = X2
% 2.97/1.00      | sK2 != X1 ),
% 2.97/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_24]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_452,plain,
% 2.97/1.00      ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,X1)))
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.97/1.00      | ~ v2_pre_topc(sK2)
% 2.97/1.00      | ~ l1_pre_topc(sK2)
% 2.97/1.00      | sK1(sK2,X1,X0) = X0 ),
% 2.97/1.00      inference(unflattening,[status(thm)],[c_451]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_456,plain,
% 2.97/1.00      ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,X1)))
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.97/1.00      | sK1(sK2,X1,X0) = X0 ),
% 2.97/1.00      inference(global_propositional_subsumption,
% 2.97/1.00                [status(thm)],
% 2.97/1.00                [c_452,c_23,c_22]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1283,plain,
% 2.97/1.00      ( sK1(sK2,X0,X1) = X1
% 2.97/1.00      | m1_subset_1(X1,u1_struct_0(k9_yellow_6(sK2,X0))) != iProver_top
% 2.97/1.00      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_456]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1528,plain,
% 2.97/1.00      ( sK1(sK2,sK3,sK5) = sK5
% 2.97/1.00      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
% 2.97/1.00      inference(superposition,[status(thm)],[c_1291,c_1283]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1541,plain,
% 2.97/1.00      ( sK1(sK2,sK3,sK5) = sK5 ),
% 2.97/1.00      inference(global_propositional_subsumption,
% 2.97/1.00                [status(thm)],
% 2.97/1.00                [c_1528,c_28]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1916,plain,
% 2.97/1.00      ( v3_pre_topc(sK5,sK2) = iProver_top
% 2.97/1.00      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
% 2.97/1.00      inference(light_normalisation,[status(thm)],[c_1907,c_1541]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_14,plain,
% 2.97/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
% 2.97/1.00      | m1_subset_1(sK1(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
% 2.97/1.00      | v2_struct_0(X1)
% 2.97/1.00      | ~ v2_pre_topc(X1)
% 2.97/1.00      | ~ l1_pre_topc(X1) ),
% 2.97/1.00      inference(cnf_transformation,[],[f47]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_430,plain,
% 2.97/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
% 2.97/1.00      | m1_subset_1(sK1(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
% 2.97/1.00      | ~ v2_pre_topc(X1)
% 2.97/1.00      | ~ l1_pre_topc(X1)
% 2.97/1.00      | sK2 != X1 ),
% 2.97/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_24]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_431,plain,
% 2.97/1.00      ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,X1)))
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.97/1.00      | m1_subset_1(sK1(sK2,X1,X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.97/1.00      | ~ v2_pre_topc(sK2)
% 2.97/1.00      | ~ l1_pre_topc(sK2) ),
% 2.97/1.00      inference(unflattening,[status(thm)],[c_430]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_435,plain,
% 2.97/1.00      ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,X1)))
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.97/1.00      | m1_subset_1(sK1(sK2,X1,X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.97/1.00      inference(global_propositional_subsumption,
% 2.97/1.00                [status(thm)],
% 2.97/1.00                [c_431,c_23,c_22]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1284,plain,
% 2.97/1.00      ( m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,X1))) != iProver_top
% 2.97/1.00      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
% 2.97/1.00      | m1_subset_1(sK1(sK2,X1,X0),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_435]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1958,plain,
% 2.97/1.00      ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 2.97/1.00      | m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3))) != iProver_top
% 2.97/1.00      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 2.97/1.00      inference(superposition,[status(thm)],[c_1541,c_1284]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_30,plain,
% 2.97/1.00      ( m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3))) = iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_2895,plain,
% 2.97/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 2.97/1.00      inference(global_propositional_subsumption,
% 2.97/1.00                [status(thm)],
% 2.97/1.00                [c_1958,c_28,c_30]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_20,negated_conjecture,
% 2.97/1.00      ( m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))) ),
% 2.97/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1290,plain,
% 2.97/1.00      ( m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))) = iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1529,plain,
% 2.97/1.00      ( sK1(sK2,sK3,sK4) = sK4
% 2.97/1.00      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
% 2.97/1.00      inference(superposition,[status(thm)],[c_1290,c_1283]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1623,plain,
% 2.97/1.00      ( sK1(sK2,sK3,sK4) = sK4 ),
% 2.97/1.00      inference(global_propositional_subsumption,
% 2.97/1.00                [status(thm)],
% 2.97/1.00                [c_1529,c_28]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1959,plain,
% 2.97/1.00      ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 2.97/1.00      | m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))) != iProver_top
% 2.97/1.00      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 2.97/1.00      inference(superposition,[status(thm)],[c_1623,c_1284]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_29,plain,
% 2.97/1.00      ( m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))) = iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_3022,plain,
% 2.97/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 2.97/1.00      inference(global_propositional_subsumption,
% 2.97/1.00                [status(thm)],
% 2.97/1.00                [c_1959,c_28,c_29]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_10,plain,
% 2.97/1.00      ( ~ v3_pre_topc(X0,X1)
% 2.97/1.00      | ~ v3_pre_topc(X2,X1)
% 2.97/1.00      | v3_pre_topc(k2_xboole_0(X2,X0),X1)
% 2.97/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.97/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.97/1.00      | ~ v2_pre_topc(X1)
% 2.97/1.00      | ~ l1_pre_topc(X1) ),
% 2.97/1.00      inference(cnf_transformation,[],[f46]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_525,plain,
% 2.97/1.00      ( ~ v3_pre_topc(X0,X1)
% 2.97/1.00      | ~ v3_pre_topc(X2,X1)
% 2.97/1.00      | v3_pre_topc(k2_xboole_0(X2,X0),X1)
% 2.97/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.97/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.97/1.00      | ~ v2_pre_topc(X1)
% 2.97/1.00      | sK2 != X1 ),
% 2.97/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_22]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_526,plain,
% 2.97/1.00      ( ~ v3_pre_topc(X0,sK2)
% 2.97/1.00      | ~ v3_pre_topc(X1,sK2)
% 2.97/1.00      | v3_pre_topc(k2_xboole_0(X1,X0),sK2)
% 2.97/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.97/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.97/1.00      | ~ v2_pre_topc(sK2) ),
% 2.97/1.00      inference(unflattening,[status(thm)],[c_525]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_530,plain,
% 2.97/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.97/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.97/1.00      | v3_pre_topc(k2_xboole_0(X1,X0),sK2)
% 2.97/1.00      | ~ v3_pre_topc(X1,sK2)
% 2.97/1.00      | ~ v3_pre_topc(X0,sK2) ),
% 2.97/1.00      inference(global_propositional_subsumption,
% 2.97/1.00                [status(thm)],
% 2.97/1.00                [c_526,c_23]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_531,plain,
% 2.97/1.00      ( ~ v3_pre_topc(X0,sK2)
% 2.97/1.00      | ~ v3_pre_topc(X1,sK2)
% 2.97/1.00      | v3_pre_topc(k2_xboole_0(X1,X0),sK2)
% 2.97/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.97/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.97/1.00      inference(renaming,[status(thm)],[c_530]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1281,plain,
% 2.97/1.00      ( v3_pre_topc(X0,sK2) != iProver_top
% 2.97/1.00      | v3_pre_topc(X1,sK2) != iProver_top
% 2.97/1.00      | v3_pre_topc(k2_xboole_0(X1,X0),sK2) = iProver_top
% 2.97/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.97/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_531]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_3028,plain,
% 2.97/1.00      ( v3_pre_topc(X0,sK2) != iProver_top
% 2.97/1.00      | v3_pre_topc(k2_xboole_0(sK4,X0),sK2) = iProver_top
% 2.97/1.00      | v3_pre_topc(sK4,sK2) != iProver_top
% 2.97/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 2.97/1.00      inference(superposition,[status(thm)],[c_3022,c_1281]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1908,plain,
% 2.97/1.00      ( v3_pre_topc(sK1(sK2,sK3,sK4),sK2) = iProver_top
% 2.97/1.00      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
% 2.97/1.00      inference(superposition,[status(thm)],[c_1290,c_1288]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1911,plain,
% 2.97/1.00      ( v3_pre_topc(sK4,sK2) = iProver_top
% 2.97/1.00      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
% 2.97/1.00      inference(light_normalisation,[status(thm)],[c_1908,c_1623]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_3166,plain,
% 2.97/1.00      ( v3_pre_topc(k2_xboole_0(sK4,X0),sK2) = iProver_top
% 2.97/1.00      | v3_pre_topc(X0,sK2) != iProver_top
% 2.97/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 2.97/1.00      inference(global_propositional_subsumption,
% 2.97/1.00                [status(thm)],
% 2.97/1.00                [c_3028,c_28,c_1911]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_3167,plain,
% 2.97/1.00      ( v3_pre_topc(X0,sK2) != iProver_top
% 2.97/1.00      | v3_pre_topc(k2_xboole_0(sK4,X0),sK2) = iProver_top
% 2.97/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 2.97/1.00      inference(renaming,[status(thm)],[c_3166]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_3177,plain,
% 2.97/1.00      ( v3_pre_topc(k2_xboole_0(sK4,sK5),sK2) = iProver_top
% 2.97/1.00      | v3_pre_topc(sK5,sK2) != iProver_top ),
% 2.97/1.00      inference(superposition,[status(thm)],[c_2895,c_3167]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_4361,plain,
% 2.97/1.00      ( m1_subset_1(k2_xboole_0(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.97/1.00      | r2_hidden(sK3,k2_xboole_0(sK4,sK5)) != iProver_top ),
% 2.97/1.00      inference(global_propositional_subsumption,
% 2.97/1.00                [status(thm)],
% 2.97/1.00                [c_4308,c_28,c_1916,c_3177]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_4367,plain,
% 2.97/1.00      ( r1_tarski(k2_xboole_0(sK4,sK5),u1_struct_0(sK2)) != iProver_top
% 2.97/1.00      | r2_hidden(sK3,k2_xboole_0(sK4,sK5)) != iProver_top ),
% 2.97/1.00      inference(superposition,[status(thm)],[c_1294,c_4361]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_4469,plain,
% 2.97/1.00      ( r1_tarski(sK5,u1_struct_0(sK2)) != iProver_top
% 2.97/1.00      | r1_tarski(sK4,u1_struct_0(sK2)) != iProver_top
% 2.97/1.00      | r2_hidden(sK3,k2_xboole_0(sK4,sK5)) != iProver_top ),
% 2.97/1.00      inference(superposition,[status(thm)],[c_1296,c_4367]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_9,plain,
% 2.97/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.97/1.00      inference(cnf_transformation,[],[f44]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1293,plain,
% 2.97/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.97/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_2900,plain,
% 2.97/1.00      ( r1_tarski(sK5,u1_struct_0(sK2)) = iProver_top ),
% 2.97/1.00      inference(superposition,[status(thm)],[c_2895,c_1293]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_3027,plain,
% 2.97/1.00      ( r1_tarski(sK4,u1_struct_0(sK2)) = iProver_top ),
% 2.97/1.00      inference(superposition,[status(thm)],[c_3022,c_1293]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_5572,plain,
% 2.97/1.00      ( r2_hidden(sK3,k2_xboole_0(sK4,sK5)) != iProver_top ),
% 2.97/1.00      inference(global_propositional_subsumption,
% 2.97/1.00                [status(thm)],
% 2.97/1.00                [c_4469,c_2900,c_3027]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_5577,plain,
% 2.97/1.00      ( r2_hidden(sK3,sK5) != iProver_top ),
% 2.97/1.00      inference(superposition,[status(thm)],[c_1299,c_5572]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_12,plain,
% 2.97/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
% 2.97/1.00      | r2_hidden(X0,sK1(X1,X0,X2))
% 2.97/1.00      | v2_struct_0(X1)
% 2.97/1.00      | ~ v2_pre_topc(X1)
% 2.97/1.00      | ~ l1_pre_topc(X1) ),
% 2.97/1.00      inference(cnf_transformation,[],[f49]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_472,plain,
% 2.97/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
% 2.97/1.00      | r2_hidden(X0,sK1(X1,X0,X2))
% 2.97/1.00      | ~ v2_pre_topc(X1)
% 2.97/1.00      | ~ l1_pre_topc(X1)
% 2.97/1.00      | sK2 != X1 ),
% 2.97/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_24]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_473,plain,
% 2.97/1.00      ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,X1)))
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.97/1.00      | r2_hidden(X1,sK1(sK2,X1,X0))
% 2.97/1.00      | ~ v2_pre_topc(sK2)
% 2.97/1.00      | ~ l1_pre_topc(sK2) ),
% 2.97/1.00      inference(unflattening,[status(thm)],[c_472]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_477,plain,
% 2.97/1.00      ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,X1)))
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.97/1.00      | r2_hidden(X1,sK1(sK2,X1,X0)) ),
% 2.97/1.00      inference(global_propositional_subsumption,
% 2.97/1.00                [status(thm)],
% 2.97/1.00                [c_473,c_23,c_22]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1282,plain,
% 2.97/1.00      ( m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,X1))) != iProver_top
% 2.97/1.00      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
% 2.97/1.00      | r2_hidden(X1,sK1(sK2,X1,X0)) = iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_477]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1630,plain,
% 2.97/1.00      ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 2.97/1.00      | r2_hidden(sK3,sK1(sK2,sK3,sK5)) = iProver_top ),
% 2.97/1.00      inference(superposition,[status(thm)],[c_1291,c_1282]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1639,plain,
% 2.97/1.00      ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 2.97/1.00      | r2_hidden(sK3,sK5) = iProver_top ),
% 2.97/1.00      inference(light_normalisation,[status(thm)],[c_1630,c_1541]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(contradiction,plain,
% 2.97/1.00      ( $false ),
% 2.97/1.00      inference(minisat,[status(thm)],[c_5577,c_1639,c_28]) ).
% 2.97/1.00  
% 2.97/1.00  
% 2.97/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.97/1.00  
% 2.97/1.00  ------                               Statistics
% 2.97/1.00  
% 2.97/1.00  ------ General
% 2.97/1.00  
% 2.97/1.00  abstr_ref_over_cycles:                  0
% 2.97/1.00  abstr_ref_under_cycles:                 0
% 2.97/1.00  gc_basic_clause_elim:                   0
% 2.97/1.00  forced_gc_time:                         0
% 2.97/1.00  parsing_time:                           0.01
% 2.97/1.00  unif_index_cands_time:                  0.
% 2.97/1.00  unif_index_add_time:                    0.
% 2.97/1.00  orderings_time:                         0.
% 2.97/1.00  out_proof_time:                         0.01
% 2.97/1.00  total_time:                             0.179
% 2.97/1.00  num_of_symbols:                         48
% 2.97/1.00  num_of_terms:                           4859
% 2.97/1.00  
% 2.97/1.00  ------ Preprocessing
% 2.97/1.00  
% 2.97/1.00  num_of_splits:                          0
% 2.97/1.00  num_of_split_atoms:                     0
% 2.97/1.00  num_of_reused_defs:                     0
% 2.97/1.00  num_eq_ax_congr_red:                    20
% 2.97/1.00  num_of_sem_filtered_clauses:            1
% 2.97/1.00  num_of_subtypes:                        0
% 2.97/1.00  monotx_restored_types:                  0
% 2.97/1.00  sat_num_of_epr_types:                   0
% 2.97/1.00  sat_num_of_non_cyclic_types:            0
% 2.97/1.00  sat_guarded_non_collapsed_types:        0
% 2.97/1.00  num_pure_diseq_elim:                    0
% 2.97/1.00  simp_replaced_by:                       0
% 2.97/1.00  res_preprocessed:                       114
% 2.97/1.00  prep_upred:                             0
% 2.97/1.00  prep_unflattend:                        8
% 2.97/1.00  smt_new_axioms:                         0
% 2.97/1.00  pred_elim_cands:                        4
% 2.97/1.00  pred_elim:                              3
% 2.97/1.00  pred_elim_cl:                           3
% 2.97/1.00  pred_elim_cycles:                       5
% 2.97/1.00  merged_defs:                            8
% 2.97/1.00  merged_defs_ncl:                        0
% 2.97/1.00  bin_hyper_res:                          8
% 2.97/1.00  prep_cycles:                            4
% 2.97/1.00  pred_elim_time:                         0.006
% 2.97/1.00  splitting_time:                         0.
% 2.97/1.00  sem_filter_time:                        0.
% 2.97/1.00  monotx_time:                            0.
% 2.97/1.00  subtype_inf_time:                       0.
% 2.97/1.00  
% 2.97/1.00  ------ Problem properties
% 2.97/1.00  
% 2.97/1.00  clauses:                                22
% 2.97/1.00  conjectures:                            4
% 2.97/1.00  epr:                                    1
% 2.97/1.00  horn:                                   20
% 2.97/1.00  ground:                                 4
% 2.97/1.00  unary:                                  4
% 2.97/1.00  binary:                                 5
% 2.97/1.00  lits:                                   60
% 2.97/1.00  lits_eq:                                4
% 2.97/1.00  fd_pure:                                0
% 2.97/1.00  fd_pseudo:                              0
% 2.97/1.00  fd_cond:                                0
% 2.97/1.00  fd_pseudo_cond:                         3
% 2.97/1.00  ac_symbols:                             0
% 2.97/1.00  
% 2.97/1.00  ------ Propositional Solver
% 2.97/1.00  
% 2.97/1.00  prop_solver_calls:                      27
% 2.97/1.00  prop_fast_solver_calls:                 969
% 2.97/1.00  smt_solver_calls:                       0
% 2.97/1.00  smt_fast_solver_calls:                  0
% 2.97/1.00  prop_num_of_clauses:                    2141
% 2.97/1.00  prop_preprocess_simplified:             5460
% 2.97/1.00  prop_fo_subsumed:                       45
% 2.97/1.00  prop_solver_time:                       0.
% 2.97/1.00  smt_solver_time:                        0.
% 2.97/1.00  smt_fast_solver_time:                   0.
% 2.97/1.00  prop_fast_solver_time:                  0.
% 2.97/1.00  prop_unsat_core_time:                   0.
% 2.97/1.00  
% 2.97/1.00  ------ QBF
% 2.97/1.00  
% 2.97/1.00  qbf_q_res:                              0
% 2.97/1.00  qbf_num_tautologies:                    0
% 2.97/1.00  qbf_prep_cycles:                        0
% 2.97/1.00  
% 2.97/1.00  ------ BMC1
% 2.97/1.00  
% 2.97/1.00  bmc1_current_bound:                     -1
% 2.97/1.00  bmc1_last_solved_bound:                 -1
% 2.97/1.00  bmc1_unsat_core_size:                   -1
% 2.97/1.00  bmc1_unsat_core_parents_size:           -1
% 2.97/1.00  bmc1_merge_next_fun:                    0
% 2.97/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.97/1.00  
% 2.97/1.00  ------ Instantiation
% 2.97/1.00  
% 2.97/1.00  inst_num_of_clauses:                    548
% 2.97/1.00  inst_num_in_passive:                    26
% 2.97/1.00  inst_num_in_active:                     280
% 2.97/1.00  inst_num_in_unprocessed:                242
% 2.97/1.00  inst_num_of_loops:                      310
% 2.97/1.00  inst_num_of_learning_restarts:          0
% 2.97/1.00  inst_num_moves_active_passive:          27
% 2.97/1.00  inst_lit_activity:                      0
% 2.97/1.00  inst_lit_activity_moves:                0
% 2.97/1.00  inst_num_tautologies:                   0
% 2.97/1.00  inst_num_prop_implied:                  0
% 2.97/1.00  inst_num_existing_simplified:           0
% 2.97/1.00  inst_num_eq_res_simplified:             0
% 2.97/1.00  inst_num_child_elim:                    0
% 2.97/1.00  inst_num_of_dismatching_blockings:      148
% 2.97/1.00  inst_num_of_non_proper_insts:           486
% 2.97/1.00  inst_num_of_duplicates:                 0
% 2.97/1.00  inst_inst_num_from_inst_to_res:         0
% 2.97/1.00  inst_dismatching_checking_time:         0.
% 2.97/1.00  
% 2.97/1.00  ------ Resolution
% 2.97/1.00  
% 2.97/1.00  res_num_of_clauses:                     0
% 2.97/1.00  res_num_in_passive:                     0
% 2.97/1.00  res_num_in_active:                      0
% 2.97/1.00  res_num_of_loops:                       118
% 2.97/1.00  res_forward_subset_subsumed:            20
% 2.97/1.00  res_backward_subset_subsumed:           0
% 2.97/1.00  res_forward_subsumed:                   0
% 2.97/1.00  res_backward_subsumed:                  0
% 2.97/1.00  res_forward_subsumption_resolution:     0
% 2.97/1.00  res_backward_subsumption_resolution:    0
% 2.97/1.00  res_clause_to_clause_subsumption:       446
% 2.97/1.00  res_orphan_elimination:                 0
% 2.97/1.00  res_tautology_del:                      59
% 2.97/1.00  res_num_eq_res_simplified:              0
% 2.97/1.00  res_num_sel_changes:                    0
% 2.97/1.00  res_moves_from_active_to_pass:          0
% 2.97/1.00  
% 2.97/1.00  ------ Superposition
% 2.97/1.00  
% 2.97/1.00  sup_time_total:                         0.
% 2.97/1.00  sup_time_generating:                    0.
% 2.97/1.00  sup_time_sim_full:                      0.
% 2.97/1.00  sup_time_sim_immed:                     0.
% 2.97/1.00  
% 2.97/1.00  sup_num_of_clauses:                     96
% 2.97/1.00  sup_num_in_active:                      61
% 2.97/1.00  sup_num_in_passive:                     35
% 2.97/1.00  sup_num_of_loops:                       60
% 2.97/1.00  sup_fw_superposition:                   58
% 2.97/1.00  sup_bw_superposition:                   38
% 2.97/1.00  sup_immediate_simplified:               11
% 2.97/1.00  sup_given_eliminated:                   0
% 2.97/1.00  comparisons_done:                       0
% 2.97/1.00  comparisons_avoided:                    0
% 2.97/1.00  
% 2.97/1.00  ------ Simplifications
% 2.97/1.00  
% 2.97/1.00  
% 2.97/1.00  sim_fw_subset_subsumed:                 7
% 2.97/1.00  sim_bw_subset_subsumed:                 4
% 2.97/1.00  sim_fw_subsumed:                        1
% 2.97/1.00  sim_bw_subsumed:                        0
% 2.97/1.00  sim_fw_subsumption_res:                 3
% 2.97/1.00  sim_bw_subsumption_res:                 0
% 2.97/1.00  sim_tautology_del:                      15
% 2.97/1.00  sim_eq_tautology_del:                   0
% 2.97/1.00  sim_eq_res_simp:                        6
% 2.97/1.00  sim_fw_demodulated:                     0
% 2.97/1.00  sim_bw_demodulated:                     0
% 2.97/1.00  sim_light_normalised:                   6
% 2.97/1.00  sim_joinable_taut:                      0
% 2.97/1.00  sim_joinable_simp:                      0
% 2.97/1.00  sim_ac_normalised:                      0
% 2.97/1.00  sim_smt_subsumption:                    0
% 2.97/1.00  
%------------------------------------------------------------------------------
