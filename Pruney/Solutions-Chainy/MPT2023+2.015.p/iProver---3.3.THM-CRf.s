%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:28:48 EST 2020

% Result     : Theorem 3.83s
% Output     : CNFRefutation 3.83s
% Verified   : 
% Statistics : Number of formulae       :  148 (2102 expanded)
%              Number of clauses        :   91 ( 399 expanded)
%              Number of leaves         :   17 ( 801 expanded)
%              Depth                    :   23
%              Number of atoms          :  620 (12934 expanded)
%              Number of equality atoms :  158 ( 738 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,conjecture,(
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

fof(f10,negated_conjecture,(
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
    inference(negated_conjecture,[],[f9])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))
          & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
     => ( ~ m1_subset_1(k3_xboole_0(X2,sK5),u1_struct_0(k9_yellow_6(X0,X1)))
        & m1_subset_1(sK5,u1_struct_0(k9_yellow_6(X0,X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
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

fof(f33,plain,(
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

fof(f32,plain,
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

fof(f36,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK4,sK5),u1_struct_0(k9_yellow_6(sK2,sK3)))
    & m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3)))
    & m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3)))
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f21,f35,f34,f33,f32])).

fof(f62,plain,(
    ~ m1_subset_1(k3_xboole_0(sK4,sK5),u1_struct_0(k9_yellow_6(sK2,sK3))) ),
    inference(cnf_transformation,[],[f36])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f8,axiom,(
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
    inference(ennf_transformation,[],[f8])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

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
    inference(nnf_transformation,[],[f19])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ v3_pre_topc(X2,X0)
      | ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f56,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f57,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f58,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f59,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f36])).

fof(f61,plain,(
    m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3))) ),
    inference(cnf_transformation,[],[f36])).

fof(f7,axiom,(
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
    inference(ennf_transformation,[],[f7])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f28,plain,(
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

fof(f29,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f17,f28])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(sK1(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( sK1(X0,X1,X2) = X2
      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f60,plain,(
    m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))) ),
    inference(cnf_transformation,[],[f36])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_pre_topc(X2,X0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k3_xboole_0(X1,X2),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( v3_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( v3_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
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

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f23])).

fof(f25,plain,(
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

fof(f26,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f39,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f63,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f39])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,sK1(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_19,negated_conjecture,
    ( ~ m1_subset_1(k3_xboole_0(sK4,sK5),u1_struct_0(k9_yellow_6(sK2,sK3))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_8,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_4286,plain,
    ( ~ r2_hidden(k3_xboole_0(sK4,sK5),u1_struct_0(k9_yellow_6(sK2,sK3))) ),
    inference(resolution,[status(thm)],[c_19,c_8])).

cnf(c_16,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_12687,plain,
    ( ~ v3_pre_topc(k3_xboole_0(sK4,sK5),sK2)
    | ~ m1_subset_1(k3_xboole_0(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ r2_hidden(sK3,k3_xboole_0(sK4,sK5))
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[status(thm)],[c_4286,c_16])).

cnf(c_25,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_24,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_23,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_916,plain,
    ( m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_12,plain,
    ( v3_pre_topc(sK1(X0,X1,X2),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_924,plain,
    ( v3_pre_topc(sK1(X0,X1,X2),X0) = iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4248,plain,
    ( v3_pre_topc(sK1(sK2,sK3,sK5),sK2) = iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_916,c_924])).

cnf(c_26,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_27,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_28,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_29,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_31,plain,
    ( m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1236,plain,
    ( v3_pre_topc(sK1(sK2,sK3,sK5),sK2)
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3)))
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1237,plain,
    ( v3_pre_topc(sK1(sK2,sK3,sK5),sK2) = iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3))) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1236])).

cnf(c_4779,plain,
    ( v3_pre_topc(sK1(sK2,sK3,sK5),sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4248,c_26,c_27,c_28,c_29,c_31,c_1237])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK1(X1,X0,X2) = X2 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_922,plain,
    ( sK1(X0,X1,X2) = X2
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_4010,plain,
    ( sK1(sK2,sK3,sK5) = sK5
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_916,c_922])).

cnf(c_1251,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3)))
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | sK1(sK2,sK3,sK5) = sK5 ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_4458,plain,
    ( sK1(sK2,sK3,sK5) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4010,c_25,c_24,c_23,c_22,c_20,c_1251])).

cnf(c_4783,plain,
    ( v3_pre_topc(sK5,sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4779,c_4458])).

cnf(c_4785,plain,
    ( v3_pre_topc(sK5,sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4783])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
    | m1_subset_1(sK1(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_921,plain,
    ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0))) != iProver_top
    | m1_subset_1(sK1(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4461,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4458,c_921])).

cnf(c_5107,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4461,c_26,c_27,c_28,c_29,c_31])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_915,plain,
    ( m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_4011,plain,
    ( sK1(sK2,sK3,sK4) = sK4
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_915,c_922])).

cnf(c_1254,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3)))
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | sK1(sK2,sK3,sK4) = sK4 ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_4464,plain,
    ( sK1(sK2,sK3,sK4) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4011,c_25,c_24,c_23,c_22,c_21,c_1254])).

cnf(c_4467,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4464,c_921])).

cnf(c_30,plain,
    ( m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_5115,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4467,c_26,c_27,c_28,c_29,c_30])).

cnf(c_11,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ v3_pre_topc(X2,X1)
    | v3_pre_topc(k3_xboole_0(X2,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_925,plain,
    ( v3_pre_topc(X0,X1) != iProver_top
    | v3_pre_topc(X2,X1) != iProver_top
    | v3_pre_topc(k3_xboole_0(X2,X0),X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_5383,plain,
    ( v3_pre_topc(X0,sK2) != iProver_top
    | v3_pre_topc(k3_xboole_0(sK4,X0),sK2) = iProver_top
    | v3_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5115,c_925])).

cnf(c_4249,plain,
    ( v3_pre_topc(sK1(sK2,sK3,sK4),sK2) = iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_915,c_924])).

cnf(c_1239,plain,
    ( v3_pre_topc(sK1(sK2,sK3,sK4),sK2)
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3)))
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1240,plain,
    ( v3_pre_topc(sK1(sK2,sK3,sK4),sK2) = iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1239])).

cnf(c_4787,plain,
    ( v3_pre_topc(sK1(sK2,sK3,sK4),sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4249,c_26,c_27,c_28,c_29,c_30,c_1240])).

cnf(c_4791,plain,
    ( v3_pre_topc(sK4,sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4787,c_4464])).

cnf(c_6255,plain,
    ( v3_pre_topc(k3_xboole_0(sK4,X0),sK2) = iProver_top
    | v3_pre_topc(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5383,c_27,c_28,c_4791])).

cnf(c_6256,plain,
    ( v3_pre_topc(X0,sK2) != iProver_top
    | v3_pre_topc(k3_xboole_0(sK4,X0),sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_6255])).

cnf(c_6266,plain,
    ( v3_pre_topc(k3_xboole_0(sK4,sK5),sK2) = iProver_top
    | v3_pre_topc(sK5,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5107,c_6256])).

cnf(c_6302,plain,
    ( v3_pre_topc(k3_xboole_0(sK4,sK5),sK2)
    | ~ v3_pre_topc(sK5,sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6266])).

cnf(c_12690,plain,
    ( ~ r2_hidden(sK3,k3_xboole_0(sK4,sK5))
    | ~ m1_subset_1(k3_xboole_0(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12687,c_25,c_24,c_23,c_22,c_4785,c_6302])).

cnf(c_12691,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(sK3,k3_xboole_0(sK4,sK5)) ),
    inference(renaming,[status(thm)],[c_12690])).

cnf(c_12706,plain,
    ( ~ r2_hidden(k3_xboole_0(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(sK3,k3_xboole_0(sK4,sK5)) ),
    inference(resolution,[status(thm)],[c_12691,c_8])).

cnf(c_4468,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3)))
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4467])).

cnf(c_9,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_12708,plain,
    ( ~ r1_tarski(k3_xboole_0(sK4,sK5),u1_struct_0(sK2))
    | ~ r2_hidden(sK3,k3_xboole_0(sK4,sK5)) ),
    inference(resolution,[status(thm)],[c_12691,c_9])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X0)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_5734,plain,
    ( r2_hidden(sK0(X0,X1,X0),X0)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(factoring,[status(thm)],[c_2])).

cnf(c_299,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_294,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2125,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_299,c_294])).

cnf(c_6043,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k3_xboole_0(X0,X2),X1)
    | r2_hidden(sK0(X0,X2,X0),X0) ),
    inference(resolution,[status(thm)],[c_5734,c_2125])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_6338,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(k3_xboole_0(X0,X2),X1)
    | r2_hidden(sK0(X0,X2,X0),X0) ),
    inference(resolution,[status(thm)],[c_6043,c_10])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_6,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1677,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k3_xboole_0(X0,X2),X1) ),
    inference(resolution,[status(thm)],[c_7,c_6])).

cnf(c_6881,plain,
    ( r1_tarski(k3_xboole_0(X0,X2),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6338,c_10,c_1677])).

cnf(c_6882,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(k3_xboole_0(X0,X2),X1) ),
    inference(renaming,[status(thm)],[c_6881])).

cnf(c_13091,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(sK3,k3_xboole_0(sK4,sK5)) ),
    inference(resolution,[status(thm)],[c_12708,c_6882])).

cnf(c_13097,plain,
    ( ~ r2_hidden(sK3,k3_xboole_0(sK4,sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12706,c_25,c_24,c_23,c_22,c_21,c_4468,c_13091])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_13316,plain,
    ( ~ r2_hidden(sK3,sK5)
    | ~ r2_hidden(sK3,sK4) ),
    inference(resolution,[status(thm)],[c_13097,c_3])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
    | r2_hidden(X0,sK1(X1,X0,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_923,plain,
    ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0))) != iProver_top
    | r2_hidden(X0,sK1(X1,X0,X2)) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_4042,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK3,sK1(sK2,sK3,sK4)) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_915,c_923])).

cnf(c_1245,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3)))
    | r2_hidden(sK3,sK1(sK2,sK3,sK4))
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1246,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))) != iProver_top
    | r2_hidden(sK3,sK1(sK2,sK3,sK4)) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1245])).

cnf(c_4619,plain,
    ( r2_hidden(sK3,sK1(sK2,sK3,sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4042,c_26,c_27,c_28,c_29,c_30,c_1246])).

cnf(c_4623,plain,
    ( r2_hidden(sK3,sK4) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4619,c_4464])).

cnf(c_4625,plain,
    ( r2_hidden(sK3,sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4623])).

cnf(c_4041,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK3,sK1(sK2,sK3,sK5)) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_916,c_923])).

cnf(c_1242,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3)))
    | r2_hidden(sK3,sK1(sK2,sK3,sK5))
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1243,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3))) != iProver_top
    | r2_hidden(sK3,sK1(sK2,sK3,sK5)) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1242])).

cnf(c_4609,plain,
    ( r2_hidden(sK3,sK1(sK2,sK3,sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4041,c_26,c_27,c_28,c_29,c_31,c_1243])).

cnf(c_4613,plain,
    ( r2_hidden(sK3,sK5) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4609,c_4458])).

cnf(c_4615,plain,
    ( r2_hidden(sK3,sK5) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4613])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13316,c_4625,c_4615])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.11/0.33  % Computer   : n004.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 18:26:38 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running in FOF mode
% 3.83/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.83/0.97  
% 3.83/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.83/0.97  
% 3.83/0.97  ------  iProver source info
% 3.83/0.97  
% 3.83/0.97  git: date: 2020-06-30 10:37:57 +0100
% 3.83/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.83/0.97  git: non_committed_changes: false
% 3.83/0.97  git: last_make_outside_of_git: false
% 3.83/0.97  
% 3.83/0.97  ------ 
% 3.83/0.97  ------ Parsing...
% 3.83/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.83/0.97  
% 3.83/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.83/0.97  
% 3.83/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.83/0.97  
% 3.83/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.83/0.97  ------ Proving...
% 3.83/0.97  ------ Problem Properties 
% 3.83/0.97  
% 3.83/0.97  
% 3.83/0.97  clauses                                 26
% 3.83/0.97  conjectures                             7
% 3.83/0.97  EPR                                     5
% 3.83/0.97  Horn                                    17
% 3.83/0.97  unary                                   8
% 3.83/0.97  binary                                  5
% 3.83/0.97  lits                                    87
% 3.83/0.97  lits eq                                 4
% 3.83/0.97  fd_pure                                 0
% 3.83/0.97  fd_pseudo                               0
% 3.83/0.97  fd_cond                                 0
% 3.83/0.97  fd_pseudo_cond                          3
% 3.83/0.97  AC symbols                              0
% 3.83/0.97  
% 3.83/0.97  ------ Input Options Time Limit: Unbounded
% 3.83/0.97  
% 3.83/0.97  
% 3.83/0.97  ------ 
% 3.83/0.97  Current options:
% 3.83/0.97  ------ 
% 3.83/0.97  
% 3.83/0.97  
% 3.83/0.97  
% 3.83/0.97  
% 3.83/0.97  ------ Proving...
% 3.83/0.97  
% 3.83/0.97  
% 3.83/0.97  % SZS status Theorem for theBenchmark.p
% 3.83/0.97  
% 3.83/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 3.83/0.97  
% 3.83/0.97  fof(f9,conjecture,(
% 3.83/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) => m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))))))),
% 3.83/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/0.97  
% 3.83/0.97  fof(f10,negated_conjecture,(
% 3.83/0.97    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) => m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))))))),
% 3.83/0.97    inference(negated_conjecture,[],[f9])).
% 3.83/0.97  
% 3.83/0.97  fof(f20,plain,(
% 3.83/0.97    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.83/0.97    inference(ennf_transformation,[],[f10])).
% 3.83/0.97  
% 3.83/0.97  fof(f21,plain,(
% 3.83/0.97    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.83/0.97    inference(flattening,[],[f20])).
% 3.83/0.97  
% 3.83/0.97  fof(f35,plain,(
% 3.83/0.97    ( ! [X2,X0,X1] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) => (~m1_subset_1(k3_xboole_0(X2,sK5),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(sK5,u1_struct_0(k9_yellow_6(X0,X1))))) )),
% 3.83/0.97    introduced(choice_axiom,[])).
% 3.83/0.97  
% 3.83/0.97  fof(f34,plain,(
% 3.83/0.97    ( ! [X0,X1] : (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) => (? [X3] : (~m1_subset_1(k3_xboole_0(sK4,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(sK4,u1_struct_0(k9_yellow_6(X0,X1))))) )),
% 3.83/0.97    introduced(choice_axiom,[])).
% 3.83/0.97  
% 3.83/0.97  fof(f33,plain,(
% 3.83/0.97    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,sK3))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,sK3)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,sK3)))) & m1_subset_1(sK3,u1_struct_0(X0)))) )),
% 3.83/0.97    introduced(choice_axiom,[])).
% 3.83/0.97  
% 3.83/0.97  fof(f32,plain,(
% 3.83/0.97    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK2,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK2,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK2,X1)))) & m1_subset_1(X1,u1_struct_0(sK2))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 3.83/0.97    introduced(choice_axiom,[])).
% 3.83/0.97  
% 3.83/0.97  fof(f36,plain,(
% 3.83/0.97    (((~m1_subset_1(k3_xboole_0(sK4,sK5),u1_struct_0(k9_yellow_6(sK2,sK3))) & m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3)))) & m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3)))) & m1_subset_1(sK3,u1_struct_0(sK2))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 3.83/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f21,f35,f34,f33,f32])).
% 3.83/0.97  
% 3.83/0.97  fof(f62,plain,(
% 3.83/0.97    ~m1_subset_1(k3_xboole_0(sK4,sK5),u1_struct_0(k9_yellow_6(sK2,sK3)))),
% 3.83/0.97    inference(cnf_transformation,[],[f36])).
% 3.83/0.97  
% 3.83/0.97  fof(f4,axiom,(
% 3.83/0.97    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 3.83/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/0.97  
% 3.83/0.97  fof(f13,plain,(
% 3.83/0.97    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 3.83/0.97    inference(ennf_transformation,[],[f4])).
% 3.83/0.97  
% 3.83/0.97  fof(f45,plain,(
% 3.83/0.97    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 3.83/0.97    inference(cnf_transformation,[],[f13])).
% 3.83/0.97  
% 3.83/0.97  fof(f8,axiom,(
% 3.83/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))))))),
% 3.83/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/0.97  
% 3.83/0.97  fof(f18,plain,(
% 3.83/0.97    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.83/0.97    inference(ennf_transformation,[],[f8])).
% 3.83/0.97  
% 3.83/0.97  fof(f19,plain,(
% 3.83/0.97    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.83/0.97    inference(flattening,[],[f18])).
% 3.83/0.97  
% 3.83/0.97  fof(f30,plain,(
% 3.83/0.97    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | (~v3_pre_topc(X2,X0) | ~r2_hidden(X1,X2))) & ((v3_pre_topc(X2,X0) & r2_hidden(X1,X2)) | ~r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.83/0.97    inference(nnf_transformation,[],[f19])).
% 3.83/0.97  
% 3.83/0.97  fof(f31,plain,(
% 3.83/0.97    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~v3_pre_topc(X2,X0) | ~r2_hidden(X1,X2)) & ((v3_pre_topc(X2,X0) & r2_hidden(X1,X2)) | ~r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.83/0.97    inference(flattening,[],[f30])).
% 3.83/0.97  
% 3.83/0.97  fof(f55,plain,(
% 3.83/0.97    ( ! [X2,X0,X1] : (r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~v3_pre_topc(X2,X0) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.83/0.97    inference(cnf_transformation,[],[f31])).
% 3.83/0.97  
% 3.83/0.97  fof(f56,plain,(
% 3.83/0.97    ~v2_struct_0(sK2)),
% 3.83/0.97    inference(cnf_transformation,[],[f36])).
% 3.83/0.97  
% 3.83/0.97  fof(f57,plain,(
% 3.83/0.97    v2_pre_topc(sK2)),
% 3.83/0.97    inference(cnf_transformation,[],[f36])).
% 3.83/0.97  
% 3.83/0.97  fof(f58,plain,(
% 3.83/0.97    l1_pre_topc(sK2)),
% 3.83/0.97    inference(cnf_transformation,[],[f36])).
% 3.83/0.97  
% 3.83/0.97  fof(f59,plain,(
% 3.83/0.97    m1_subset_1(sK3,u1_struct_0(sK2))),
% 3.83/0.97    inference(cnf_transformation,[],[f36])).
% 3.83/0.97  
% 3.83/0.97  fof(f61,plain,(
% 3.83/0.97    m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3)))),
% 3.83/0.97    inference(cnf_transformation,[],[f36])).
% 3.83/0.97  
% 3.83/0.97  fof(f7,axiom,(
% 3.83/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ? [X3] : (v3_pre_topc(X3,X0) & r2_hidden(X1,X3) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))))),
% 3.83/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/0.97  
% 3.83/0.97  fof(f16,plain,(
% 3.83/0.97    ! [X0] : (! [X1] : (! [X2] : (? [X3] : (v3_pre_topc(X3,X0) & r2_hidden(X1,X3) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.83/0.97    inference(ennf_transformation,[],[f7])).
% 3.83/0.97  
% 3.83/0.97  fof(f17,plain,(
% 3.83/0.97    ! [X0] : (! [X1] : (! [X2] : (? [X3] : (v3_pre_topc(X3,X0) & r2_hidden(X1,X3) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.83/0.97    inference(flattening,[],[f16])).
% 3.83/0.97  
% 3.83/0.97  fof(f28,plain,(
% 3.83/0.97    ! [X2,X1,X0] : (? [X3] : (v3_pre_topc(X3,X0) & r2_hidden(X1,X3) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (v3_pre_topc(sK1(X0,X1,X2),X0) & r2_hidden(X1,sK1(X0,X1,X2)) & sK1(X0,X1,X2) = X2 & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.83/0.97    introduced(choice_axiom,[])).
% 3.83/0.97  
% 3.83/0.97  fof(f29,plain,(
% 3.83/0.97    ! [X0] : (! [X1] : (! [X2] : ((v3_pre_topc(sK1(X0,X1,X2),X0) & r2_hidden(X1,sK1(X0,X1,X2)) & sK1(X0,X1,X2) = X2 & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.83/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f17,f28])).
% 3.83/0.97  
% 3.83/0.97  fof(f52,plain,(
% 3.83/0.97    ( ! [X2,X0,X1] : (v3_pre_topc(sK1(X0,X1,X2),X0) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.83/0.97    inference(cnf_transformation,[],[f29])).
% 3.83/0.97  
% 3.83/0.97  fof(f50,plain,(
% 3.83/0.97    ( ! [X2,X0,X1] : (sK1(X0,X1,X2) = X2 | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.83/0.97    inference(cnf_transformation,[],[f29])).
% 3.83/0.97  
% 3.83/0.97  fof(f49,plain,(
% 3.83/0.97    ( ! [X2,X0,X1] : (m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.83/0.97    inference(cnf_transformation,[],[f29])).
% 3.83/0.97  
% 3.83/0.97  fof(f60,plain,(
% 3.83/0.97    m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3)))),
% 3.83/0.97    inference(cnf_transformation,[],[f36])).
% 3.83/0.97  
% 3.83/0.97  fof(f6,axiom,(
% 3.83/0.97    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X2,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k3_xboole_0(X1,X2),X0))),
% 3.83/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/0.97  
% 3.83/0.97  fof(f14,plain,(
% 3.83/0.97    ! [X0,X1,X2] : (v3_pre_topc(k3_xboole_0(X1,X2),X0) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.83/0.97    inference(ennf_transformation,[],[f6])).
% 3.83/0.97  
% 3.83/0.97  fof(f15,plain,(
% 3.83/0.97    ! [X0,X1,X2] : (v3_pre_topc(k3_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.83/0.97    inference(flattening,[],[f14])).
% 3.83/0.97  
% 3.83/0.97  fof(f48,plain,(
% 3.83/0.97    ( ! [X2,X0,X1] : (v3_pre_topc(k3_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.83/0.97    inference(cnf_transformation,[],[f15])).
% 3.83/0.97  
% 3.83/0.97  fof(f5,axiom,(
% 3.83/0.97    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.83/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/0.97  
% 3.83/0.97  fof(f27,plain,(
% 3.83/0.97    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.83/0.97    inference(nnf_transformation,[],[f5])).
% 3.83/0.97  
% 3.83/0.97  fof(f47,plain,(
% 3.83/0.97    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.83/0.97    inference(cnf_transformation,[],[f27])).
% 3.83/0.97  
% 3.83/0.97  fof(f1,axiom,(
% 3.83/0.97    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.83/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/0.97  
% 3.83/0.97  fof(f22,plain,(
% 3.83/0.97    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.83/0.97    inference(nnf_transformation,[],[f1])).
% 3.83/0.97  
% 3.83/0.97  fof(f23,plain,(
% 3.83/0.97    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.83/0.97    inference(flattening,[],[f22])).
% 3.83/0.97  
% 3.83/0.97  fof(f24,plain,(
% 3.83/0.97    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.83/0.97    inference(rectify,[],[f23])).
% 3.83/0.97  
% 3.83/0.97  fof(f25,plain,(
% 3.83/0.97    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 3.83/0.97    introduced(choice_axiom,[])).
% 3.83/0.97  
% 3.83/0.97  fof(f26,plain,(
% 3.83/0.97    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.83/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).
% 3.83/0.97  
% 3.83/0.97  fof(f40,plain,(
% 3.83/0.97    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.83/0.97    inference(cnf_transformation,[],[f26])).
% 3.83/0.97  
% 3.83/0.97  fof(f46,plain,(
% 3.83/0.97    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.83/0.97    inference(cnf_transformation,[],[f27])).
% 3.83/0.97  
% 3.83/0.97  fof(f3,axiom,(
% 3.83/0.97    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 3.83/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/0.97  
% 3.83/0.97  fof(f11,plain,(
% 3.83/0.97    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 3.83/0.97    inference(ennf_transformation,[],[f3])).
% 3.83/0.97  
% 3.83/0.97  fof(f12,plain,(
% 3.83/0.97    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 3.83/0.97    inference(flattening,[],[f11])).
% 3.83/0.97  
% 3.83/0.97  fof(f44,plain,(
% 3.83/0.97    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 3.83/0.97    inference(cnf_transformation,[],[f12])).
% 3.83/0.97  
% 3.83/0.97  fof(f2,axiom,(
% 3.83/0.97    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 3.83/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/0.97  
% 3.83/0.97  fof(f43,plain,(
% 3.83/0.97    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 3.83/0.97    inference(cnf_transformation,[],[f2])).
% 3.83/0.97  
% 3.83/0.97  fof(f39,plain,(
% 3.83/0.97    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k3_xboole_0(X0,X1) != X2) )),
% 3.83/0.97    inference(cnf_transformation,[],[f26])).
% 3.83/0.97  
% 3.83/0.97  fof(f63,plain,(
% 3.83/0.97    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_xboole_0(X0,X1)) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 3.83/0.97    inference(equality_resolution,[],[f39])).
% 3.83/0.97  
% 3.83/0.97  fof(f51,plain,(
% 3.83/0.97    ( ! [X2,X0,X1] : (r2_hidden(X1,sK1(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.83/0.97    inference(cnf_transformation,[],[f29])).
% 3.83/0.97  
% 3.83/0.97  cnf(c_19,negated_conjecture,
% 3.83/0.97      ( ~ m1_subset_1(k3_xboole_0(sK4,sK5),u1_struct_0(k9_yellow_6(sK2,sK3))) ),
% 3.83/0.97      inference(cnf_transformation,[],[f62]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_8,plain,
% 3.83/0.97      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 3.83/0.97      inference(cnf_transformation,[],[f45]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_4286,plain,
% 3.83/0.97      ( ~ r2_hidden(k3_xboole_0(sK4,sK5),u1_struct_0(k9_yellow_6(sK2,sK3))) ),
% 3.83/0.97      inference(resolution,[status(thm)],[c_19,c_8]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_16,plain,
% 3.83/0.97      ( ~ v3_pre_topc(X0,X1)
% 3.83/0.97      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.83/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.83/0.97      | ~ r2_hidden(X2,X0)
% 3.83/0.97      | r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
% 3.83/0.97      | v2_struct_0(X1)
% 3.83/0.97      | ~ v2_pre_topc(X1)
% 3.83/0.97      | ~ l1_pre_topc(X1) ),
% 3.83/0.97      inference(cnf_transformation,[],[f55]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_12687,plain,
% 3.83/0.97      ( ~ v3_pre_topc(k3_xboole_0(sK4,sK5),sK2)
% 3.83/0.97      | ~ m1_subset_1(k3_xboole_0(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.83/0.97      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 3.83/0.97      | ~ r2_hidden(sK3,k3_xboole_0(sK4,sK5))
% 3.83/0.97      | v2_struct_0(sK2)
% 3.83/0.97      | ~ v2_pre_topc(sK2)
% 3.83/0.97      | ~ l1_pre_topc(sK2) ),
% 3.83/0.97      inference(resolution,[status(thm)],[c_4286,c_16]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_25,negated_conjecture,
% 3.83/0.97      ( ~ v2_struct_0(sK2) ),
% 3.83/0.97      inference(cnf_transformation,[],[f56]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_24,negated_conjecture,
% 3.83/0.97      ( v2_pre_topc(sK2) ),
% 3.83/0.97      inference(cnf_transformation,[],[f57]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_23,negated_conjecture,
% 3.83/0.97      ( l1_pre_topc(sK2) ),
% 3.83/0.97      inference(cnf_transformation,[],[f58]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_22,negated_conjecture,
% 3.83/0.97      ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 3.83/0.97      inference(cnf_transformation,[],[f59]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_20,negated_conjecture,
% 3.83/0.97      ( m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3))) ),
% 3.83/0.97      inference(cnf_transformation,[],[f61]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_916,plain,
% 3.83/0.97      ( m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3))) = iProver_top ),
% 3.83/0.97      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_12,plain,
% 3.83/0.97      ( v3_pre_topc(sK1(X0,X1,X2),X0)
% 3.83/0.97      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.83/0.97      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
% 3.83/0.97      | v2_struct_0(X0)
% 3.83/0.97      | ~ v2_pre_topc(X0)
% 3.83/0.97      | ~ l1_pre_topc(X0) ),
% 3.83/0.97      inference(cnf_transformation,[],[f52]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_924,plain,
% 3.83/0.97      ( v3_pre_topc(sK1(X0,X1,X2),X0) = iProver_top
% 3.83/0.97      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 3.83/0.97      | m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) != iProver_top
% 3.83/0.97      | v2_struct_0(X0) = iProver_top
% 3.83/0.97      | v2_pre_topc(X0) != iProver_top
% 3.83/0.97      | l1_pre_topc(X0) != iProver_top ),
% 3.83/0.97      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_4248,plain,
% 3.83/0.97      ( v3_pre_topc(sK1(sK2,sK3,sK5),sK2) = iProver_top
% 3.83/0.97      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 3.83/0.97      | v2_struct_0(sK2) = iProver_top
% 3.83/0.97      | v2_pre_topc(sK2) != iProver_top
% 3.83/0.97      | l1_pre_topc(sK2) != iProver_top ),
% 3.83/0.97      inference(superposition,[status(thm)],[c_916,c_924]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_26,plain,
% 3.83/0.97      ( v2_struct_0(sK2) != iProver_top ),
% 3.83/0.97      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_27,plain,
% 3.83/0.97      ( v2_pre_topc(sK2) = iProver_top ),
% 3.83/0.97      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_28,plain,
% 3.83/0.97      ( l1_pre_topc(sK2) = iProver_top ),
% 3.83/0.97      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_29,plain,
% 3.83/0.97      ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
% 3.83/0.97      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_31,plain,
% 3.83/0.97      ( m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3))) = iProver_top ),
% 3.83/0.97      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_1236,plain,
% 3.83/0.97      ( v3_pre_topc(sK1(sK2,sK3,sK5),sK2)
% 3.83/0.97      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 3.83/0.97      | ~ m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3)))
% 3.83/0.97      | v2_struct_0(sK2)
% 3.83/0.97      | ~ v2_pre_topc(sK2)
% 3.83/0.97      | ~ l1_pre_topc(sK2) ),
% 3.83/0.97      inference(instantiation,[status(thm)],[c_12]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_1237,plain,
% 3.83/0.97      ( v3_pre_topc(sK1(sK2,sK3,sK5),sK2) = iProver_top
% 3.83/0.97      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 3.83/0.97      | m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3))) != iProver_top
% 3.83/0.97      | v2_struct_0(sK2) = iProver_top
% 3.83/0.97      | v2_pre_topc(sK2) != iProver_top
% 3.83/0.97      | l1_pre_topc(sK2) != iProver_top ),
% 3.83/0.97      inference(predicate_to_equality,[status(thm)],[c_1236]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_4779,plain,
% 3.83/0.97      ( v3_pre_topc(sK1(sK2,sK3,sK5),sK2) = iProver_top ),
% 3.83/0.97      inference(global_propositional_subsumption,
% 3.83/0.97                [status(thm)],
% 3.83/0.97                [c_4248,c_26,c_27,c_28,c_29,c_31,c_1237]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_14,plain,
% 3.83/0.97      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.83/0.97      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
% 3.83/0.97      | v2_struct_0(X1)
% 3.83/0.97      | ~ v2_pre_topc(X1)
% 3.83/0.97      | ~ l1_pre_topc(X1)
% 3.83/0.97      | sK1(X1,X0,X2) = X2 ),
% 3.83/0.97      inference(cnf_transformation,[],[f50]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_922,plain,
% 3.83/0.97      ( sK1(X0,X1,X2) = X2
% 3.83/0.97      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 3.83/0.97      | m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) != iProver_top
% 3.83/0.97      | v2_struct_0(X0) = iProver_top
% 3.83/0.97      | v2_pre_topc(X0) != iProver_top
% 3.83/0.97      | l1_pre_topc(X0) != iProver_top ),
% 3.83/0.97      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_4010,plain,
% 3.83/0.97      ( sK1(sK2,sK3,sK5) = sK5
% 3.83/0.97      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 3.83/0.97      | v2_struct_0(sK2) = iProver_top
% 3.83/0.97      | v2_pre_topc(sK2) != iProver_top
% 3.83/0.97      | l1_pre_topc(sK2) != iProver_top ),
% 3.83/0.97      inference(superposition,[status(thm)],[c_916,c_922]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_1251,plain,
% 3.83/0.97      ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 3.83/0.97      | ~ m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3)))
% 3.83/0.97      | v2_struct_0(sK2)
% 3.83/0.97      | ~ v2_pre_topc(sK2)
% 3.83/0.97      | ~ l1_pre_topc(sK2)
% 3.83/0.97      | sK1(sK2,sK3,sK5) = sK5 ),
% 3.83/0.97      inference(instantiation,[status(thm)],[c_14]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_4458,plain,
% 3.83/0.97      ( sK1(sK2,sK3,sK5) = sK5 ),
% 3.83/0.97      inference(global_propositional_subsumption,
% 3.83/0.97                [status(thm)],
% 3.83/0.97                [c_4010,c_25,c_24,c_23,c_22,c_20,c_1251]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_4783,plain,
% 3.83/0.97      ( v3_pre_topc(sK5,sK2) = iProver_top ),
% 3.83/0.97      inference(light_normalisation,[status(thm)],[c_4779,c_4458]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_4785,plain,
% 3.83/0.97      ( v3_pre_topc(sK5,sK2) ),
% 3.83/0.97      inference(predicate_to_equality_rev,[status(thm)],[c_4783]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_15,plain,
% 3.83/0.97      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.83/0.97      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
% 3.83/0.97      | m1_subset_1(sK1(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
% 3.83/0.97      | v2_struct_0(X1)
% 3.83/0.97      | ~ v2_pre_topc(X1)
% 3.83/0.97      | ~ l1_pre_topc(X1) ),
% 3.83/0.97      inference(cnf_transformation,[],[f49]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_921,plain,
% 3.83/0.97      ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
% 3.83/0.97      | m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0))) != iProver_top
% 3.83/0.97      | m1_subset_1(sK1(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 3.83/0.97      | v2_struct_0(X1) = iProver_top
% 3.83/0.97      | v2_pre_topc(X1) != iProver_top
% 3.83/0.97      | l1_pre_topc(X1) != iProver_top ),
% 3.83/0.97      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_4461,plain,
% 3.83/0.97      ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 3.83/0.97      | m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3))) != iProver_top
% 3.83/0.97      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 3.83/0.97      | v2_struct_0(sK2) = iProver_top
% 3.83/0.97      | v2_pre_topc(sK2) != iProver_top
% 3.83/0.97      | l1_pre_topc(sK2) != iProver_top ),
% 3.83/0.97      inference(superposition,[status(thm)],[c_4458,c_921]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_5107,plain,
% 3.83/0.97      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.83/0.97      inference(global_propositional_subsumption,
% 3.83/0.97                [status(thm)],
% 3.83/0.97                [c_4461,c_26,c_27,c_28,c_29,c_31]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_21,negated_conjecture,
% 3.83/0.97      ( m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))) ),
% 3.83/0.97      inference(cnf_transformation,[],[f60]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_915,plain,
% 3.83/0.97      ( m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))) = iProver_top ),
% 3.83/0.97      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_4011,plain,
% 3.83/0.97      ( sK1(sK2,sK3,sK4) = sK4
% 3.83/0.97      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 3.83/0.97      | v2_struct_0(sK2) = iProver_top
% 3.83/0.97      | v2_pre_topc(sK2) != iProver_top
% 3.83/0.97      | l1_pre_topc(sK2) != iProver_top ),
% 3.83/0.97      inference(superposition,[status(thm)],[c_915,c_922]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_1254,plain,
% 3.83/0.97      ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 3.83/0.97      | ~ m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3)))
% 3.83/0.97      | v2_struct_0(sK2)
% 3.83/0.97      | ~ v2_pre_topc(sK2)
% 3.83/0.97      | ~ l1_pre_topc(sK2)
% 3.83/0.97      | sK1(sK2,sK3,sK4) = sK4 ),
% 3.83/0.97      inference(instantiation,[status(thm)],[c_14]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_4464,plain,
% 3.83/0.97      ( sK1(sK2,sK3,sK4) = sK4 ),
% 3.83/0.97      inference(global_propositional_subsumption,
% 3.83/0.97                [status(thm)],
% 3.83/0.97                [c_4011,c_25,c_24,c_23,c_22,c_21,c_1254]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_4467,plain,
% 3.83/0.97      ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 3.83/0.97      | m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))) != iProver_top
% 3.83/0.97      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 3.83/0.97      | v2_struct_0(sK2) = iProver_top
% 3.83/0.97      | v2_pre_topc(sK2) != iProver_top
% 3.83/0.97      | l1_pre_topc(sK2) != iProver_top ),
% 3.83/0.97      inference(superposition,[status(thm)],[c_4464,c_921]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_30,plain,
% 3.83/0.97      ( m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))) = iProver_top ),
% 3.83/0.97      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_5115,plain,
% 3.83/0.97      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.83/0.97      inference(global_propositional_subsumption,
% 3.83/0.97                [status(thm)],
% 3.83/0.97                [c_4467,c_26,c_27,c_28,c_29,c_30]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_11,plain,
% 3.83/0.97      ( ~ v3_pre_topc(X0,X1)
% 3.83/0.97      | ~ v3_pre_topc(X2,X1)
% 3.83/0.97      | v3_pre_topc(k3_xboole_0(X2,X0),X1)
% 3.83/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.83/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.83/0.97      | ~ v2_pre_topc(X1)
% 3.83/0.97      | ~ l1_pre_topc(X1) ),
% 3.83/0.97      inference(cnf_transformation,[],[f48]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_925,plain,
% 3.83/0.97      ( v3_pre_topc(X0,X1) != iProver_top
% 3.83/0.97      | v3_pre_topc(X2,X1) != iProver_top
% 3.83/0.97      | v3_pre_topc(k3_xboole_0(X2,X0),X1) = iProver_top
% 3.83/0.97      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.83/0.97      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.83/0.97      | v2_pre_topc(X1) != iProver_top
% 3.83/0.97      | l1_pre_topc(X1) != iProver_top ),
% 3.83/0.97      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_5383,plain,
% 3.83/0.97      ( v3_pre_topc(X0,sK2) != iProver_top
% 3.83/0.97      | v3_pre_topc(k3_xboole_0(sK4,X0),sK2) = iProver_top
% 3.83/0.97      | v3_pre_topc(sK4,sK2) != iProver_top
% 3.83/0.97      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.83/0.97      | v2_pre_topc(sK2) != iProver_top
% 3.83/0.97      | l1_pre_topc(sK2) != iProver_top ),
% 3.83/0.97      inference(superposition,[status(thm)],[c_5115,c_925]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_4249,plain,
% 3.83/0.97      ( v3_pre_topc(sK1(sK2,sK3,sK4),sK2) = iProver_top
% 3.83/0.97      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 3.83/0.97      | v2_struct_0(sK2) = iProver_top
% 3.83/0.97      | v2_pre_topc(sK2) != iProver_top
% 3.83/0.97      | l1_pre_topc(sK2) != iProver_top ),
% 3.83/0.97      inference(superposition,[status(thm)],[c_915,c_924]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_1239,plain,
% 3.83/0.97      ( v3_pre_topc(sK1(sK2,sK3,sK4),sK2)
% 3.83/0.97      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 3.83/0.97      | ~ m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3)))
% 3.83/0.97      | v2_struct_0(sK2)
% 3.83/0.97      | ~ v2_pre_topc(sK2)
% 3.83/0.97      | ~ l1_pre_topc(sK2) ),
% 3.83/0.97      inference(instantiation,[status(thm)],[c_12]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_1240,plain,
% 3.83/0.97      ( v3_pre_topc(sK1(sK2,sK3,sK4),sK2) = iProver_top
% 3.83/0.97      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 3.83/0.97      | m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))) != iProver_top
% 3.83/0.97      | v2_struct_0(sK2) = iProver_top
% 3.83/0.97      | v2_pre_topc(sK2) != iProver_top
% 3.83/0.97      | l1_pre_topc(sK2) != iProver_top ),
% 3.83/0.97      inference(predicate_to_equality,[status(thm)],[c_1239]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_4787,plain,
% 3.83/0.97      ( v3_pre_topc(sK1(sK2,sK3,sK4),sK2) = iProver_top ),
% 3.83/0.97      inference(global_propositional_subsumption,
% 3.83/0.97                [status(thm)],
% 3.83/0.97                [c_4249,c_26,c_27,c_28,c_29,c_30,c_1240]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_4791,plain,
% 3.83/0.97      ( v3_pre_topc(sK4,sK2) = iProver_top ),
% 3.83/0.97      inference(light_normalisation,[status(thm)],[c_4787,c_4464]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_6255,plain,
% 3.83/0.97      ( v3_pre_topc(k3_xboole_0(sK4,X0),sK2) = iProver_top
% 3.83/0.97      | v3_pre_topc(X0,sK2) != iProver_top
% 3.83/0.97      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 3.83/0.97      inference(global_propositional_subsumption,
% 3.83/0.97                [status(thm)],
% 3.83/0.97                [c_5383,c_27,c_28,c_4791]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_6256,plain,
% 3.83/0.97      ( v3_pre_topc(X0,sK2) != iProver_top
% 3.83/0.97      | v3_pre_topc(k3_xboole_0(sK4,X0),sK2) = iProver_top
% 3.83/0.97      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 3.83/0.97      inference(renaming,[status(thm)],[c_6255]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_6266,plain,
% 3.83/0.97      ( v3_pre_topc(k3_xboole_0(sK4,sK5),sK2) = iProver_top
% 3.83/0.97      | v3_pre_topc(sK5,sK2) != iProver_top ),
% 3.83/0.97      inference(superposition,[status(thm)],[c_5107,c_6256]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_6302,plain,
% 3.83/0.97      ( v3_pre_topc(k3_xboole_0(sK4,sK5),sK2) | ~ v3_pre_topc(sK5,sK2) ),
% 3.83/0.97      inference(predicate_to_equality_rev,[status(thm)],[c_6266]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_12690,plain,
% 3.83/0.97      ( ~ r2_hidden(sK3,k3_xboole_0(sK4,sK5))
% 3.83/0.97      | ~ m1_subset_1(k3_xboole_0(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.83/0.97      inference(global_propositional_subsumption,
% 3.83/0.97                [status(thm)],
% 3.83/0.97                [c_12687,c_25,c_24,c_23,c_22,c_4785,c_6302]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_12691,plain,
% 3.83/0.97      ( ~ m1_subset_1(k3_xboole_0(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.83/0.97      | ~ r2_hidden(sK3,k3_xboole_0(sK4,sK5)) ),
% 3.83/0.97      inference(renaming,[status(thm)],[c_12690]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_12706,plain,
% 3.83/0.97      ( ~ r2_hidden(k3_xboole_0(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.83/0.97      | ~ r2_hidden(sK3,k3_xboole_0(sK4,sK5)) ),
% 3.83/0.97      inference(resolution,[status(thm)],[c_12691,c_8]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_4468,plain,
% 3.83/0.97      ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 3.83/0.97      | ~ m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3)))
% 3.83/0.97      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.83/0.97      | v2_struct_0(sK2)
% 3.83/0.97      | ~ v2_pre_topc(sK2)
% 3.83/0.97      | ~ l1_pre_topc(sK2) ),
% 3.83/0.97      inference(predicate_to_equality_rev,[status(thm)],[c_4467]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_9,plain,
% 3.83/0.97      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.83/0.97      inference(cnf_transformation,[],[f47]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_12708,plain,
% 3.83/0.97      ( ~ r1_tarski(k3_xboole_0(sK4,sK5),u1_struct_0(sK2))
% 3.83/0.97      | ~ r2_hidden(sK3,k3_xboole_0(sK4,sK5)) ),
% 3.83/0.97      inference(resolution,[status(thm)],[c_12691,c_9]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_2,plain,
% 3.83/0.97      ( r2_hidden(sK0(X0,X1,X2),X0)
% 3.83/0.97      | r2_hidden(sK0(X0,X1,X2),X2)
% 3.83/0.97      | k3_xboole_0(X0,X1) = X2 ),
% 3.83/0.97      inference(cnf_transformation,[],[f40]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_5734,plain,
% 3.83/0.97      ( r2_hidden(sK0(X0,X1,X0),X0) | k3_xboole_0(X0,X1) = X0 ),
% 3.83/0.97      inference(factoring,[status(thm)],[c_2]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_299,plain,
% 3.83/0.97      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.83/0.97      theory(equality) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_294,plain,( X0 = X0 ),theory(equality) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_2125,plain,
% 3.83/0.97      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X1) | X2 != X0 ),
% 3.83/0.97      inference(resolution,[status(thm)],[c_299,c_294]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_6043,plain,
% 3.83/0.97      ( ~ m1_subset_1(X0,X1)
% 3.83/0.97      | m1_subset_1(k3_xboole_0(X0,X2),X1)
% 3.83/0.97      | r2_hidden(sK0(X0,X2,X0),X0) ),
% 3.83/0.97      inference(resolution,[status(thm)],[c_5734,c_2125]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_10,plain,
% 3.83/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.83/0.97      inference(cnf_transformation,[],[f46]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_6338,plain,
% 3.83/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.83/0.97      | r1_tarski(k3_xboole_0(X0,X2),X1)
% 3.83/0.97      | r2_hidden(sK0(X0,X2,X0),X0) ),
% 3.83/0.97      inference(resolution,[status(thm)],[c_6043,c_10]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_7,plain,
% 3.83/0.97      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 3.83/0.97      inference(cnf_transformation,[],[f44]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_6,plain,
% 3.83/0.97      ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
% 3.83/0.97      inference(cnf_transformation,[],[f43]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_1677,plain,
% 3.83/0.97      ( ~ r1_tarski(X0,X1) | r1_tarski(k3_xboole_0(X0,X2),X1) ),
% 3.83/0.97      inference(resolution,[status(thm)],[c_7,c_6]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_6881,plain,
% 3.83/0.97      ( r1_tarski(k3_xboole_0(X0,X2),X1)
% 3.83/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.83/0.97      inference(global_propositional_subsumption,
% 3.83/0.97                [status(thm)],
% 3.83/0.97                [c_6338,c_10,c_1677]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_6882,plain,
% 3.83/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.83/0.97      | r1_tarski(k3_xboole_0(X0,X2),X1) ),
% 3.83/0.97      inference(renaming,[status(thm)],[c_6881]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_13091,plain,
% 3.83/0.97      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.83/0.97      | ~ r2_hidden(sK3,k3_xboole_0(sK4,sK5)) ),
% 3.83/0.97      inference(resolution,[status(thm)],[c_12708,c_6882]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_13097,plain,
% 3.83/0.97      ( ~ r2_hidden(sK3,k3_xboole_0(sK4,sK5)) ),
% 3.83/0.97      inference(global_propositional_subsumption,
% 3.83/0.97                [status(thm)],
% 3.83/0.97                [c_12706,c_25,c_24,c_23,c_22,c_21,c_4468,c_13091]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_3,plain,
% 3.83/0.97      ( ~ r2_hidden(X0,X1)
% 3.83/0.97      | ~ r2_hidden(X0,X2)
% 3.83/0.97      | r2_hidden(X0,k3_xboole_0(X2,X1)) ),
% 3.83/0.97      inference(cnf_transformation,[],[f63]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_13316,plain,
% 3.83/0.97      ( ~ r2_hidden(sK3,sK5) | ~ r2_hidden(sK3,sK4) ),
% 3.83/0.97      inference(resolution,[status(thm)],[c_13097,c_3]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_13,plain,
% 3.83/0.97      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.83/0.97      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
% 3.83/0.97      | r2_hidden(X0,sK1(X1,X0,X2))
% 3.83/0.97      | v2_struct_0(X1)
% 3.83/0.97      | ~ v2_pre_topc(X1)
% 3.83/0.97      | ~ l1_pre_topc(X1) ),
% 3.83/0.97      inference(cnf_transformation,[],[f51]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_923,plain,
% 3.83/0.97      ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
% 3.83/0.97      | m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0))) != iProver_top
% 3.83/0.97      | r2_hidden(X0,sK1(X1,X0,X2)) = iProver_top
% 3.83/0.97      | v2_struct_0(X1) = iProver_top
% 3.83/0.97      | v2_pre_topc(X1) != iProver_top
% 3.83/0.97      | l1_pre_topc(X1) != iProver_top ),
% 3.83/0.97      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_4042,plain,
% 3.83/0.97      ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 3.83/0.97      | r2_hidden(sK3,sK1(sK2,sK3,sK4)) = iProver_top
% 3.83/0.97      | v2_struct_0(sK2) = iProver_top
% 3.83/0.97      | v2_pre_topc(sK2) != iProver_top
% 3.83/0.97      | l1_pre_topc(sK2) != iProver_top ),
% 3.83/0.97      inference(superposition,[status(thm)],[c_915,c_923]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_1245,plain,
% 3.83/0.97      ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 3.83/0.97      | ~ m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3)))
% 3.83/0.97      | r2_hidden(sK3,sK1(sK2,sK3,sK4))
% 3.83/0.97      | v2_struct_0(sK2)
% 3.83/0.97      | ~ v2_pre_topc(sK2)
% 3.83/0.97      | ~ l1_pre_topc(sK2) ),
% 3.83/0.97      inference(instantiation,[status(thm)],[c_13]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_1246,plain,
% 3.83/0.97      ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 3.83/0.97      | m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))) != iProver_top
% 3.83/0.97      | r2_hidden(sK3,sK1(sK2,sK3,sK4)) = iProver_top
% 3.83/0.97      | v2_struct_0(sK2) = iProver_top
% 3.83/0.97      | v2_pre_topc(sK2) != iProver_top
% 3.83/0.97      | l1_pre_topc(sK2) != iProver_top ),
% 3.83/0.97      inference(predicate_to_equality,[status(thm)],[c_1245]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_4619,plain,
% 3.83/0.97      ( r2_hidden(sK3,sK1(sK2,sK3,sK4)) = iProver_top ),
% 3.83/0.97      inference(global_propositional_subsumption,
% 3.83/0.97                [status(thm)],
% 3.83/0.97                [c_4042,c_26,c_27,c_28,c_29,c_30,c_1246]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_4623,plain,
% 3.83/0.97      ( r2_hidden(sK3,sK4) = iProver_top ),
% 3.83/0.97      inference(light_normalisation,[status(thm)],[c_4619,c_4464]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_4625,plain,
% 3.83/0.97      ( r2_hidden(sK3,sK4) ),
% 3.83/0.97      inference(predicate_to_equality_rev,[status(thm)],[c_4623]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_4041,plain,
% 3.83/0.97      ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 3.83/0.97      | r2_hidden(sK3,sK1(sK2,sK3,sK5)) = iProver_top
% 3.83/0.97      | v2_struct_0(sK2) = iProver_top
% 3.83/0.97      | v2_pre_topc(sK2) != iProver_top
% 3.83/0.97      | l1_pre_topc(sK2) != iProver_top ),
% 3.83/0.97      inference(superposition,[status(thm)],[c_916,c_923]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_1242,plain,
% 3.83/0.97      ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 3.83/0.97      | ~ m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3)))
% 3.83/0.97      | r2_hidden(sK3,sK1(sK2,sK3,sK5))
% 3.83/0.97      | v2_struct_0(sK2)
% 3.83/0.97      | ~ v2_pre_topc(sK2)
% 3.83/0.97      | ~ l1_pre_topc(sK2) ),
% 3.83/0.97      inference(instantiation,[status(thm)],[c_13]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_1243,plain,
% 3.83/0.97      ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 3.83/0.97      | m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3))) != iProver_top
% 3.83/0.97      | r2_hidden(sK3,sK1(sK2,sK3,sK5)) = iProver_top
% 3.83/0.97      | v2_struct_0(sK2) = iProver_top
% 3.83/0.97      | v2_pre_topc(sK2) != iProver_top
% 3.83/0.97      | l1_pre_topc(sK2) != iProver_top ),
% 3.83/0.97      inference(predicate_to_equality,[status(thm)],[c_1242]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_4609,plain,
% 3.83/0.97      ( r2_hidden(sK3,sK1(sK2,sK3,sK5)) = iProver_top ),
% 3.83/0.97      inference(global_propositional_subsumption,
% 3.83/0.97                [status(thm)],
% 3.83/0.97                [c_4041,c_26,c_27,c_28,c_29,c_31,c_1243]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_4613,plain,
% 3.83/0.97      ( r2_hidden(sK3,sK5) = iProver_top ),
% 3.83/0.97      inference(light_normalisation,[status(thm)],[c_4609,c_4458]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_4615,plain,
% 3.83/0.97      ( r2_hidden(sK3,sK5) ),
% 3.83/0.97      inference(predicate_to_equality_rev,[status(thm)],[c_4613]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(contradiction,plain,
% 3.83/0.97      ( $false ),
% 3.83/0.97      inference(minisat,[status(thm)],[c_13316,c_4625,c_4615]) ).
% 3.83/0.97  
% 3.83/0.97  
% 3.83/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 3.83/0.97  
% 3.83/0.97  ------                               Statistics
% 3.83/0.97  
% 3.83/0.97  ------ Selected
% 3.83/0.97  
% 3.83/0.97  total_time:                             0.396
% 3.83/0.97  
%------------------------------------------------------------------------------
