%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:27:31 EST 2020

% Result     : Theorem 7.51s
% Output     : CNFRefutation 7.51s
% Verified   : 
% Statistics : Number of formulae       :  165 (1719 expanded)
%              Number of clauses        :   92 ( 455 expanded)
%              Number of leaves         :   19 ( 486 expanded)
%              Depth                    :   21
%              Number of atoms          :  613 (9160 expanded)
%              Number of equality atoms :  204 (1630 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f17,f42])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f44])).

fof(f46,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK2(X0,X1) != X0
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( sK2(X0,X1) = X0
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK2(X0,X1) != X0
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( sK2(X0,X1) = X0
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f45,f46])).

fof(f61,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f88,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f61])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v3_pre_topc(X1,X0)
                  & r1_xboole_0(X1,X2) )
               => r1_xboole_0(X1,k2_pre_topc(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_xboole_0(X1,k2_pre_topc(X0,X2))
              | ~ v3_pre_topc(X1,X0)
              | ~ r1_xboole_0(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_xboole_0(X1,k2_pre_topc(X0,X2))
              | ~ v3_pre_topc(X1,X0)
              | ~ r1_xboole_0(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X1,k2_pre_topc(X0,X2))
      | ~ v3_pre_topc(X1,X0)
      | ~ r1_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))
                | r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v3_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))
                  | r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))
              & ~ r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))
              & ~ r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))
          & ~ r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK6)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
        & ~ r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK6)))
        & m1_subset_1(sK6,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))
              & ~ r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK5)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))
            & ~ r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK5)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK5,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))
                & ~ r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),X1)) != k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),X2))
              & ~ r1_xboole_0(k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),X1)),k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),X2)))
              & m1_subset_1(X2,u1_struct_0(sK4)) )
          & m1_subset_1(X1,u1_struct_0(sK4)) )
      & l1_pre_topc(sK4)
      & v3_tdlat_3(sK4)
      & v2_pre_topc(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,
    ( k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK5)) != k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK6))
    & ~ r1_xboole_0(k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK5)),k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK6)))
    & m1_subset_1(sK6,u1_struct_0(sK4))
    & m1_subset_1(sK5,u1_struct_0(sK4))
    & l1_pre_topc(sK4)
    & v3_tdlat_3(sK4)
    & v2_pre_topc(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f37,f54,f53,f52])).

fof(f82,plain,(
    m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f55])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f78,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f55])).

fof(f81,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f55])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f69,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f68,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f83,plain,(
    m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f55])).

fof(f84,plain,(
    ~ r1_xboole_0(k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK5)),k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK6))) ),
    inference(cnf_transformation,[],[f55])).

fof(f79,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f55])).

fof(f80,plain,(
    v3_tdlat_3(sK4) ),
    inference(cnf_transformation,[],[f55])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f71,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
             => v3_pre_topc(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f31,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f48,plain,(
    ! [X0] :
      ( ( ( v3_tdlat_3(X0)
          | ? [X1] :
              ( ~ v3_pre_topc(X1,X0)
              & v4_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X1] :
              ( v3_pre_topc(X1,X0)
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v3_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f49,plain,(
    ! [X0] :
      ( ( ( v3_tdlat_3(X0)
          | ? [X1] :
              ( ~ v3_pre_topc(X1,X0)
              & v4_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v3_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f48])).

fof(f50,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_pre_topc(X1,X0)
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK3(X0),X0)
        & v4_pre_topc(sK3(X0),X0)
        & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0] :
      ( ( ( v3_tdlat_3(X0)
          | ( ~ v3_pre_topc(sK3(X0),X0)
            & v4_pre_topc(sK3(X0),X0)
            & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v3_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f49,f50])).

fof(f72,plain,(
    ! [X2,X0] :
      ( v3_pre_topc(X2,X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
               => k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))
              | ~ r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))
              | ~ r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))
      | ~ r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f85,plain,(
    k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK5)) != k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK6)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_3,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_833,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_4,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_832,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k1_tarski(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_828,plain,
    ( X0 = X1
    | r2_hidden(X0,k1_tarski(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2237,plain,
    ( sK1(k1_tarski(X0),X1) = X0
    | r1_xboole_0(k1_tarski(X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_832,c_828])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_834,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_6108,plain,
    ( sK1(k1_tarski(X0),X1) = X0
    | r2_hidden(X2,X1) != iProver_top
    | r2_hidden(X2,k1_tarski(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2237,c_834])).

cnf(c_6757,plain,
    ( sK1(k1_tarski(X0),X1) = X0
    | r1_xboole_0(X2,k1_tarski(X0)) = iProver_top
    | r2_hidden(sK1(X2,k1_tarski(X0)),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_833,c_6108])).

cnf(c_13679,plain,
    ( sK1(k1_tarski(X0),X1) = X0
    | r1_xboole_0(X1,k1_tarski(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_832,c_6757])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_825,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_20,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_xboole_0(X0,X2)
    | r1_xboole_0(X0,k2_pre_topc(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_816,plain,
    ( v3_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_xboole_0(X0,X2) != iProver_top
    | r1_xboole_0(X0,k2_pre_topc(X1,X2)) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3327,plain,
    ( v3_pre_topc(k2_pre_topc(X0,X1),X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | r1_xboole_0(k2_pre_topc(X0,X1),X2) != iProver_top
    | r1_xboole_0(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_825,c_816])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_812,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_822,plain,
    ( k6_domain_1(X0,X1) = k1_tarski(X1)
    | m1_subset_1(X1,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2546,plain,
    ( k6_domain_1(u1_struct_0(sK4),sK5) = k1_tarski(sK5)
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_812,c_822])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_26,negated_conjecture,
    ( l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_13,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_56,plain,
    ( v2_struct_0(sK4)
    | ~ l1_struct_0(sK4)
    | ~ v1_xboole_0(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_12,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_59,plain,
    ( l1_struct_0(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1162,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | v1_xboole_0(u1_struct_0(sK4))
    | k6_domain_1(u1_struct_0(sK4),sK5) = k1_tarski(sK5) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_2967,plain,
    ( k6_domain_1(u1_struct_0(sK4),sK5) = k1_tarski(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2546,c_29,c_26,c_25,c_56,c_59,c_1162])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_813,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_2545,plain,
    ( k6_domain_1(u1_struct_0(sK4),sK6) = k1_tarski(sK6)
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_813,c_822])).

cnf(c_1159,plain,
    ( ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | v1_xboole_0(u1_struct_0(sK4))
    | k6_domain_1(u1_struct_0(sK4),sK6) = k1_tarski(sK6) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_2724,plain,
    ( k6_domain_1(u1_struct_0(sK4),sK6) = k1_tarski(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2545,c_29,c_26,c_24,c_56,c_59,c_1159])).

cnf(c_23,negated_conjecture,
    ( ~ r1_xboole_0(k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK5)),k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK6))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_814,plain,
    ( r1_xboole_0(k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK5)),k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK6))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2727,plain,
    ( r1_xboole_0(k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK5)),k2_pre_topc(sK4,k1_tarski(sK6))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2724,c_814])).

cnf(c_2970,plain,
    ( r1_xboole_0(k2_pre_topc(sK4,k1_tarski(sK5)),k2_pre_topc(sK4,k1_tarski(sK6))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2967,c_2727])).

cnf(c_17821,plain,
    ( v3_pre_topc(k2_pre_topc(sK4,k1_tarski(sK5)),sK4) != iProver_top
    | m1_subset_1(k1_tarski(sK6),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(k1_tarski(sK5),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r1_xboole_0(k2_pre_topc(sK4,k1_tarski(sK5)),k1_tarski(sK6)) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3327,c_2970])).

cnf(c_30,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_28,negated_conjecture,
    ( v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_31,plain,
    ( v2_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_27,negated_conjecture,
    ( v3_tdlat_3(sK4) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_32,plain,
    ( v3_tdlat_3(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_33,plain,
    ( l1_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_34,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_35,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_55,plain,
    ( v2_struct_0(X0) = iProver_top
    | l1_struct_0(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_57,plain,
    ( v2_struct_0(sK4) = iProver_top
    | l1_struct_0(sK4) != iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_55])).

cnf(c_58,plain,
    ( l1_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_60,plain,
    ( l1_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_58])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1120,plain,
    ( ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | r2_hidden(sK6,u1_struct_0(sK4))
    | v1_xboole_0(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1121,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK6,u1_struct_0(sK4)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1120])).

cnf(c_1123,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | r2_hidden(sK5,u1_struct_0(sK4))
    | v1_xboole_0(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1124,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK5,u1_struct_0(sK4)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1123])).

cnf(c_9,plain,
    ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1282,plain,
    ( m1_subset_1(k1_tarski(sK6),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK6,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1283,plain,
    ( m1_subset_1(k1_tarski(sK6),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | r2_hidden(sK6,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1282])).

cnf(c_1298,plain,
    ( m1_subset_1(k1_tarski(sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1299,plain,
    ( m1_subset_1(k1_tarski(sK5),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | r2_hidden(sK5,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1298])).

cnf(c_1607,plain,
    ( m1_subset_1(k2_pre_topc(sK4,k1_tarski(sK5)),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(k1_tarski(sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1608,plain,
    ( m1_subset_1(k2_pre_topc(sK4,k1_tarski(sK5)),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | m1_subset_1(k1_tarski(sK5),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1607])).

cnf(c_15,plain,
    ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1612,plain,
    ( v4_pre_topc(k2_pre_topc(sK4,k1_tarski(sK5)),sK4)
    | ~ m1_subset_1(k1_tarski(sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1613,plain,
    ( v4_pre_topc(k2_pre_topc(sK4,k1_tarski(sK5)),sK4) = iProver_top
    | m1_subset_1(k1_tarski(sK5),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1612])).

cnf(c_19,plain,
    ( v3_pre_topc(X0,X1)
    | ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2619,plain,
    ( v3_pre_topc(k2_pre_topc(sK4,k1_tarski(sK5)),sK4)
    | ~ v4_pre_topc(k2_pre_topc(sK4,k1_tarski(sK5)),sK4)
    | ~ m1_subset_1(k2_pre_topc(sK4,k1_tarski(sK5)),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v3_tdlat_3(sK4)
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_2623,plain,
    ( v3_pre_topc(k2_pre_topc(sK4,k1_tarski(sK5)),sK4) = iProver_top
    | v4_pre_topc(k2_pre_topc(sK4,k1_tarski(sK5)),sK4) != iProver_top
    | m1_subset_1(k2_pre_topc(sK4,k1_tarski(sK5)),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v3_tdlat_3(sK4) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2619])).

cnf(c_1538,plain,
    ( ~ v3_pre_topc(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(k1_tarski(sK6),k1_zfmisc_1(u1_struct_0(sK4)))
    | r1_xboole_0(X0,k2_pre_topc(sK4,k1_tarski(sK6)))
    | ~ r1_xboole_0(X0,k1_tarski(sK6))
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_5507,plain,
    ( ~ v3_pre_topc(k2_pre_topc(sK4,k1_tarski(sK5)),sK4)
    | ~ m1_subset_1(k2_pre_topc(sK4,k1_tarski(sK5)),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(k1_tarski(sK6),k1_zfmisc_1(u1_struct_0(sK4)))
    | r1_xboole_0(k2_pre_topc(sK4,k1_tarski(sK5)),k2_pre_topc(sK4,k1_tarski(sK6)))
    | ~ r1_xboole_0(k2_pre_topc(sK4,k1_tarski(sK5)),k1_tarski(sK6))
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_1538])).

cnf(c_5508,plain,
    ( v3_pre_topc(k2_pre_topc(sK4,k1_tarski(sK5)),sK4) != iProver_top
    | m1_subset_1(k2_pre_topc(sK4,k1_tarski(sK5)),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(k1_tarski(sK6),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r1_xboole_0(k2_pre_topc(sK4,k1_tarski(sK5)),k2_pre_topc(sK4,k1_tarski(sK6))) = iProver_top
    | r1_xboole_0(k2_pre_topc(sK4,k1_tarski(sK5)),k1_tarski(sK6)) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5507])).

cnf(c_19805,plain,
    ( r1_xboole_0(k2_pre_topc(sK4,k1_tarski(sK5)),k1_tarski(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_17821,c_30,c_31,c_32,c_33,c_34,c_35,c_57,c_60,c_1121,c_1124,c_1283,c_1299,c_1608,c_1613,c_2623,c_2970,c_5508])).

cnf(c_19819,plain,
    ( sK1(k1_tarski(sK6),k2_pre_topc(sK4,k1_tarski(sK5))) = sK6 ),
    inference(superposition,[status(thm)],[c_13679,c_19805])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X0)))
    | ~ v3_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X0)) = k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_815,plain,
    ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | r2_hidden(X2,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))) != iProver_top
    | v3_tdlat_3(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2977,plain,
    ( k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),X0)) = k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK5))
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0,k2_pre_topc(sK4,k1_tarski(sK5))) != iProver_top
    | v3_tdlat_3(sK4) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2967,c_815])).

cnf(c_2978,plain,
    ( k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),X0)) = k2_pre_topc(sK4,k1_tarski(sK5))
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0,k2_pre_topc(sK4,k1_tarski(sK5))) != iProver_top
    | v3_tdlat_3(sK4) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2977,c_2967])).

cnf(c_4057,plain,
    ( m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),X0)) = k2_pre_topc(sK4,k1_tarski(sK5))
    | r2_hidden(X0,k2_pre_topc(sK4,k1_tarski(sK5))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2978,c_30,c_31,c_32,c_33,c_34])).

cnf(c_4058,plain,
    ( k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),X0)) = k2_pre_topc(sK4,k1_tarski(sK5))
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0,k2_pre_topc(sK4,k1_tarski(sK5))) != iProver_top ),
    inference(renaming,[status(thm)],[c_4057])).

cnf(c_4067,plain,
    ( k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK1(X0,k2_pre_topc(sK4,k1_tarski(sK5))))) = k2_pre_topc(sK4,k1_tarski(sK5))
    | m1_subset_1(sK1(X0,k2_pre_topc(sK4,k1_tarski(sK5))),u1_struct_0(sK4)) != iProver_top
    | r1_xboole_0(X0,k2_pre_topc(sK4,k1_tarski(sK5))) = iProver_top ),
    inference(superposition,[status(thm)],[c_833,c_4058])).

cnf(c_20580,plain,
    ( k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK1(k1_tarski(sK6),k2_pre_topc(sK4,k1_tarski(sK5))))) = k2_pre_topc(sK4,k1_tarski(sK5))
    | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top
    | r1_xboole_0(k1_tarski(sK6),k2_pre_topc(sK4,k1_tarski(sK5))) = iProver_top ),
    inference(superposition,[status(thm)],[c_19819,c_4067])).

cnf(c_20592,plain,
    ( k2_pre_topc(sK4,k1_tarski(sK5)) = k2_pre_topc(sK4,k1_tarski(sK6))
    | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top
    | r1_xboole_0(k1_tarski(sK6),k2_pre_topc(sK4,k1_tarski(sK5))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_20580,c_2724,c_19819])).

cnf(c_22,negated_conjecture,
    ( k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK5)) != k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK6)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_2728,plain,
    ( k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK5)) != k2_pre_topc(sK4,k1_tarski(sK6)) ),
    inference(demodulation,[status(thm)],[c_2724,c_22])).

cnf(c_2971,plain,
    ( k2_pre_topc(sK4,k1_tarski(sK5)) != k2_pre_topc(sK4,k1_tarski(sK6)) ),
    inference(demodulation,[status(thm)],[c_2967,c_2728])).

cnf(c_20811,plain,
    ( r1_xboole_0(k1_tarski(sK6),k2_pre_topc(sK4,k1_tarski(sK5))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_20592,c_35,c_2971])).

cnf(c_20816,plain,
    ( r2_hidden(X0,k2_pre_topc(sK4,k1_tarski(sK5))) != iProver_top
    | r2_hidden(X0,k1_tarski(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_20811,c_834])).

cnf(c_20825,plain,
    ( r1_xboole_0(k2_pre_topc(sK4,k1_tarski(sK5)),X0) = iProver_top
    | r2_hidden(sK1(k2_pre_topc(sK4,k1_tarski(sK5)),X0),k1_tarski(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_832,c_20816])).

cnf(c_21555,plain,
    ( r1_xboole_0(k2_pre_topc(sK4,k1_tarski(sK5)),k1_tarski(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_833,c_20825])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_21555,c_5508,c_2970,c_2623,c_1613,c_1608,c_1299,c_1283,c_1124,c_1121,c_60,c_57,c_35,c_34,c_33,c_32,c_31,c_30])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:53:53 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 7.51/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.51/1.49  
% 7.51/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.51/1.49  
% 7.51/1.49  ------  iProver source info
% 7.51/1.49  
% 7.51/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.51/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.51/1.49  git: non_committed_changes: false
% 7.51/1.49  git: last_make_outside_of_git: false
% 7.51/1.49  
% 7.51/1.49  ------ 
% 7.51/1.49  ------ Parsing...
% 7.51/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.51/1.49  
% 7.51/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 7.51/1.49  
% 7.51/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.51/1.49  
% 7.51/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.51/1.49  ------ Proving...
% 7.51/1.49  ------ Problem Properties 
% 7.51/1.49  
% 7.51/1.49  
% 7.51/1.49  clauses                                 30
% 7.51/1.49  conjectures                             8
% 7.51/1.49  EPR                                     8
% 7.51/1.49  Horn                                    21
% 7.51/1.49  unary                                   9
% 7.51/1.49  binary                                  7
% 7.51/1.49  lits                                    81
% 7.51/1.49  lits eq                                 8
% 7.51/1.49  fd_pure                                 0
% 7.51/1.49  fd_pseudo                               0
% 7.51/1.49  fd_cond                                 0
% 7.51/1.49  fd_pseudo_cond                          2
% 7.51/1.49  AC symbols                              0
% 7.51/1.49  
% 7.51/1.49  ------ Input Options Time Limit: Unbounded
% 7.51/1.49  
% 7.51/1.49  
% 7.51/1.49  ------ 
% 7.51/1.49  Current options:
% 7.51/1.49  ------ 
% 7.51/1.49  
% 7.51/1.49  
% 7.51/1.49  
% 7.51/1.49  
% 7.51/1.49  ------ Proving...
% 7.51/1.49  
% 7.51/1.49  
% 7.51/1.49  % SZS status Theorem for theBenchmark.p
% 7.51/1.49  
% 7.51/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.51/1.49  
% 7.51/1.49  fof(f2,axiom,(
% 7.51/1.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 7.51/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.51/1.49  
% 7.51/1.49  fof(f16,plain,(
% 7.51/1.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 7.51/1.49    inference(rectify,[],[f2])).
% 7.51/1.49  
% 7.51/1.49  fof(f17,plain,(
% 7.51/1.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 7.51/1.49    inference(ennf_transformation,[],[f16])).
% 7.51/1.49  
% 7.51/1.49  fof(f42,plain,(
% 7.51/1.49    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 7.51/1.49    introduced(choice_axiom,[])).
% 7.51/1.49  
% 7.51/1.49  fof(f43,plain,(
% 7.51/1.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 7.51/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f17,f42])).
% 7.51/1.49  
% 7.51/1.49  fof(f59,plain,(
% 7.51/1.49    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 7.51/1.49    inference(cnf_transformation,[],[f43])).
% 7.51/1.49  
% 7.51/1.49  fof(f58,plain,(
% 7.51/1.49    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 7.51/1.49    inference(cnf_transformation,[],[f43])).
% 7.51/1.49  
% 7.51/1.49  fof(f3,axiom,(
% 7.51/1.49    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 7.51/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.51/1.49  
% 7.51/1.49  fof(f44,plain,(
% 7.51/1.49    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 7.51/1.49    inference(nnf_transformation,[],[f3])).
% 7.51/1.49  
% 7.51/1.49  fof(f45,plain,(
% 7.51/1.49    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 7.51/1.49    inference(rectify,[],[f44])).
% 7.51/1.49  
% 7.51/1.49  fof(f46,plain,(
% 7.51/1.49    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 7.51/1.49    introduced(choice_axiom,[])).
% 7.51/1.49  
% 7.51/1.49  fof(f47,plain,(
% 7.51/1.49    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 7.51/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f45,f46])).
% 7.51/1.49  
% 7.51/1.49  fof(f61,plain,(
% 7.51/1.49    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 7.51/1.49    inference(cnf_transformation,[],[f47])).
% 7.51/1.49  
% 7.51/1.49  fof(f88,plain,(
% 7.51/1.49    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k1_tarski(X0))) )),
% 7.51/1.49    inference(equality_resolution,[],[f61])).
% 7.51/1.49  
% 7.51/1.49  fof(f60,plain,(
% 7.51/1.49    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 7.51/1.49    inference(cnf_transformation,[],[f43])).
% 7.51/1.49  
% 7.51/1.49  fof(f6,axiom,(
% 7.51/1.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 7.51/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.51/1.49  
% 7.51/1.49  fof(f21,plain,(
% 7.51/1.49    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 7.51/1.49    inference(ennf_transformation,[],[f6])).
% 7.51/1.49  
% 7.51/1.49  fof(f22,plain,(
% 7.51/1.49    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 7.51/1.49    inference(flattening,[],[f21])).
% 7.51/1.49  
% 7.51/1.49  fof(f67,plain,(
% 7.51/1.49    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.51/1.49    inference(cnf_transformation,[],[f22])).
% 7.51/1.49  
% 7.51/1.49  fof(f12,axiom,(
% 7.51/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X1,X0) & r1_xboole_0(X1,X2)) => r1_xboole_0(X1,k2_pre_topc(X0,X2))))))),
% 7.51/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.51/1.49  
% 7.51/1.49  fof(f32,plain,(
% 7.51/1.49    ! [X0] : (! [X1] : (! [X2] : ((r1_xboole_0(X1,k2_pre_topc(X0,X2)) | (~v3_pre_topc(X1,X0) | ~r1_xboole_0(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.51/1.49    inference(ennf_transformation,[],[f12])).
% 7.51/1.49  
% 7.51/1.49  fof(f33,plain,(
% 7.51/1.49    ! [X0] : (! [X1] : (! [X2] : (r1_xboole_0(X1,k2_pre_topc(X0,X2)) | ~v3_pre_topc(X1,X0) | ~r1_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.51/1.49    inference(flattening,[],[f32])).
% 7.51/1.49  
% 7.51/1.49  fof(f76,plain,(
% 7.51/1.49    ( ! [X2,X0,X1] : (r1_xboole_0(X1,k2_pre_topc(X0,X2)) | ~v3_pre_topc(X1,X0) | ~r1_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.51/1.49    inference(cnf_transformation,[],[f33])).
% 7.51/1.49  
% 7.51/1.49  fof(f14,conjecture,(
% 7.51/1.49    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) | r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))))))),
% 7.51/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.51/1.49  
% 7.51/1.49  fof(f15,negated_conjecture,(
% 7.51/1.49    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) | r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))))))),
% 7.51/1.49    inference(negated_conjecture,[],[f14])).
% 7.51/1.49  
% 7.51/1.49  fof(f36,plain,(
% 7.51/1.49    ? [X0] : (? [X1] : (? [X2] : ((k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 7.51/1.49    inference(ennf_transformation,[],[f15])).
% 7.51/1.49  
% 7.51/1.49  fof(f37,plain,(
% 7.51/1.49    ? [X0] : (? [X1] : (? [X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.51/1.49    inference(flattening,[],[f36])).
% 7.51/1.49  
% 7.51/1.49  fof(f54,plain,(
% 7.51/1.49    ( ! [X0,X1] : (? [X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & m1_subset_1(X2,u1_struct_0(X0))) => (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK6)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK6))) & m1_subset_1(sK6,u1_struct_0(X0)))) )),
% 7.51/1.49    introduced(choice_axiom,[])).
% 7.51/1.49  
% 7.51/1.49  fof(f53,plain,(
% 7.51/1.49    ( ! [X0] : (? [X1] : (? [X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK5)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK5)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK5,u1_struct_0(X0)))) )),
% 7.51/1.49    introduced(choice_axiom,[])).
% 7.51/1.49  
% 7.51/1.49  fof(f52,plain,(
% 7.51/1.49    ? [X0] : (? [X1] : (? [X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),X1)) != k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),X2)) & ~r1_xboole_0(k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),X1)),k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),X2))) & m1_subset_1(X2,u1_struct_0(sK4))) & m1_subset_1(X1,u1_struct_0(sK4))) & l1_pre_topc(sK4) & v3_tdlat_3(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4))),
% 7.51/1.49    introduced(choice_axiom,[])).
% 7.51/1.49  
% 7.51/1.49  fof(f55,plain,(
% 7.51/1.49    ((k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK5)) != k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK6)) & ~r1_xboole_0(k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK5)),k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK6))) & m1_subset_1(sK6,u1_struct_0(sK4))) & m1_subset_1(sK5,u1_struct_0(sK4))) & l1_pre_topc(sK4) & v3_tdlat_3(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4)),
% 7.51/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f37,f54,f53,f52])).
% 7.51/1.49  
% 7.51/1.49  fof(f82,plain,(
% 7.51/1.49    m1_subset_1(sK5,u1_struct_0(sK4))),
% 7.51/1.49    inference(cnf_transformation,[],[f55])).
% 7.51/1.49  
% 7.51/1.49  fof(f9,axiom,(
% 7.51/1.49    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 7.51/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.51/1.49  
% 7.51/1.49  fof(f26,plain,(
% 7.51/1.49    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 7.51/1.49    inference(ennf_transformation,[],[f9])).
% 7.51/1.49  
% 7.51/1.49  fof(f27,plain,(
% 7.51/1.49    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 7.51/1.49    inference(flattening,[],[f26])).
% 7.51/1.49  
% 7.51/1.49  fof(f70,plain,(
% 7.51/1.49    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 7.51/1.49    inference(cnf_transformation,[],[f27])).
% 7.51/1.49  
% 7.51/1.49  fof(f78,plain,(
% 7.51/1.49    ~v2_struct_0(sK4)),
% 7.51/1.49    inference(cnf_transformation,[],[f55])).
% 7.51/1.49  
% 7.51/1.49  fof(f81,plain,(
% 7.51/1.49    l1_pre_topc(sK4)),
% 7.51/1.49    inference(cnf_transformation,[],[f55])).
% 7.51/1.49  
% 7.51/1.49  fof(f8,axiom,(
% 7.51/1.49    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 7.51/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.51/1.49  
% 7.51/1.49  fof(f24,plain,(
% 7.51/1.49    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 7.51/1.49    inference(ennf_transformation,[],[f8])).
% 7.51/1.49  
% 7.51/1.49  fof(f25,plain,(
% 7.51/1.49    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 7.51/1.49    inference(flattening,[],[f24])).
% 7.51/1.49  
% 7.51/1.49  fof(f69,plain,(
% 7.51/1.49    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 7.51/1.49    inference(cnf_transformation,[],[f25])).
% 7.51/1.49  
% 7.51/1.49  fof(f7,axiom,(
% 7.51/1.49    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 7.51/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.51/1.49  
% 7.51/1.49  fof(f23,plain,(
% 7.51/1.49    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 7.51/1.49    inference(ennf_transformation,[],[f7])).
% 7.51/1.49  
% 7.51/1.49  fof(f68,plain,(
% 7.51/1.49    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 7.51/1.49    inference(cnf_transformation,[],[f23])).
% 7.51/1.49  
% 7.51/1.49  fof(f83,plain,(
% 7.51/1.49    m1_subset_1(sK6,u1_struct_0(sK4))),
% 7.51/1.49    inference(cnf_transformation,[],[f55])).
% 7.51/1.49  
% 7.51/1.49  fof(f84,plain,(
% 7.51/1.49    ~r1_xboole_0(k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK5)),k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK6)))),
% 7.51/1.49    inference(cnf_transformation,[],[f55])).
% 7.51/1.49  
% 7.51/1.49  fof(f79,plain,(
% 7.51/1.49    v2_pre_topc(sK4)),
% 7.51/1.49    inference(cnf_transformation,[],[f55])).
% 7.51/1.49  
% 7.51/1.49  fof(f80,plain,(
% 7.51/1.49    v3_tdlat_3(sK4)),
% 7.51/1.49    inference(cnf_transformation,[],[f55])).
% 7.51/1.49  
% 7.51/1.49  fof(f5,axiom,(
% 7.51/1.49    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 7.51/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.51/1.49  
% 7.51/1.49  fof(f19,plain,(
% 7.51/1.49    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 7.51/1.49    inference(ennf_transformation,[],[f5])).
% 7.51/1.49  
% 7.51/1.49  fof(f20,plain,(
% 7.51/1.49    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 7.51/1.49    inference(flattening,[],[f19])).
% 7.51/1.49  
% 7.51/1.49  fof(f66,plain,(
% 7.51/1.49    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 7.51/1.49    inference(cnf_transformation,[],[f20])).
% 7.51/1.49  
% 7.51/1.49  fof(f4,axiom,(
% 7.51/1.49    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 7.51/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.51/1.49  
% 7.51/1.49  fof(f18,plain,(
% 7.51/1.49    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 7.51/1.49    inference(ennf_transformation,[],[f4])).
% 7.51/1.49  
% 7.51/1.49  fof(f65,plain,(
% 7.51/1.49    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 7.51/1.49    inference(cnf_transformation,[],[f18])).
% 7.51/1.49  
% 7.51/1.49  fof(f10,axiom,(
% 7.51/1.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_pre_topc(X0,X1),X0))),
% 7.51/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.51/1.49  
% 7.51/1.49  fof(f28,plain,(
% 7.51/1.49    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.51/1.49    inference(ennf_transformation,[],[f10])).
% 7.51/1.49  
% 7.51/1.49  fof(f29,plain,(
% 7.51/1.49    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.51/1.49    inference(flattening,[],[f28])).
% 7.51/1.49  
% 7.51/1.49  fof(f71,plain,(
% 7.51/1.49    ( ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.51/1.49    inference(cnf_transformation,[],[f29])).
% 7.51/1.49  
% 7.51/1.49  fof(f11,axiom,(
% 7.51/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v3_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => v3_pre_topc(X1,X0)))))),
% 7.51/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.51/1.49  
% 7.51/1.49  fof(f30,plain,(
% 7.51/1.49    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : ((v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.51/1.49    inference(ennf_transformation,[],[f11])).
% 7.51/1.49  
% 7.51/1.49  fof(f31,plain,(
% 7.51/1.49    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.51/1.49    inference(flattening,[],[f30])).
% 7.51/1.49  
% 7.51/1.49  fof(f48,plain,(
% 7.51/1.49    ! [X0] : (((v3_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X1] : (v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.51/1.49    inference(nnf_transformation,[],[f31])).
% 7.51/1.49  
% 7.51/1.49  fof(f49,plain,(
% 7.51/1.49    ! [X0] : (((v3_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.51/1.49    inference(rectify,[],[f48])).
% 7.51/1.49  
% 7.51/1.49  fof(f50,plain,(
% 7.51/1.49    ! [X0] : (? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK3(X0),X0) & v4_pre_topc(sK3(X0),X0) & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 7.51/1.49    introduced(choice_axiom,[])).
% 7.51/1.49  
% 7.51/1.49  fof(f51,plain,(
% 7.51/1.49    ! [X0] : (((v3_tdlat_3(X0) | (~v3_pre_topc(sK3(X0),X0) & v4_pre_topc(sK3(X0),X0) & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.51/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f49,f50])).
% 7.51/1.49  
% 7.51/1.49  fof(f72,plain,(
% 7.51/1.49    ( ! [X2,X0] : (v3_pre_topc(X2,X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tdlat_3(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.51/1.49    inference(cnf_transformation,[],[f51])).
% 7.51/1.49  
% 7.51/1.49  fof(f13,axiom,(
% 7.51/1.49    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) => k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))))))),
% 7.51/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.51/1.49  
% 7.51/1.49  fof(f34,plain,(
% 7.51/1.49    ! [X0] : (! [X1] : (! [X2] : ((k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) | ~r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.51/1.49    inference(ennf_transformation,[],[f13])).
% 7.51/1.49  
% 7.51/1.49  fof(f35,plain,(
% 7.51/1.49    ! [X0] : (! [X1] : (! [X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) | ~r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.51/1.49    inference(flattening,[],[f34])).
% 7.51/1.49  
% 7.51/1.49  fof(f77,plain,(
% 7.51/1.49    ( ! [X2,X0,X1] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) | ~r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.51/1.49    inference(cnf_transformation,[],[f35])).
% 7.51/1.49  
% 7.51/1.49  fof(f85,plain,(
% 7.51/1.49    k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK5)) != k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK6))),
% 7.51/1.49    inference(cnf_transformation,[],[f55])).
% 7.51/1.49  
% 7.51/1.49  cnf(c_3,plain,
% 7.51/1.49      ( r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X1) ),
% 7.51/1.49      inference(cnf_transformation,[],[f59]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_833,plain,
% 7.51/1.49      ( r1_xboole_0(X0,X1) = iProver_top
% 7.51/1.49      | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
% 7.51/1.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_4,plain,
% 7.51/1.49      ( r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 7.51/1.49      inference(cnf_transformation,[],[f58]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_832,plain,
% 7.51/1.49      ( r1_xboole_0(X0,X1) = iProver_top
% 7.51/1.49      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 7.51/1.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_8,plain,
% 7.51/1.49      ( ~ r2_hidden(X0,k1_tarski(X1)) | X0 = X1 ),
% 7.51/1.49      inference(cnf_transformation,[],[f88]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_828,plain,
% 7.51/1.49      ( X0 = X1 | r2_hidden(X0,k1_tarski(X1)) != iProver_top ),
% 7.51/1.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_2237,plain,
% 7.51/1.49      ( sK1(k1_tarski(X0),X1) = X0
% 7.51/1.49      | r1_xboole_0(k1_tarski(X0),X1) = iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_832,c_828]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_2,plain,
% 7.51/1.49      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,X0) | ~ r2_hidden(X2,X1) ),
% 7.51/1.49      inference(cnf_transformation,[],[f60]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_834,plain,
% 7.51/1.49      ( r1_xboole_0(X0,X1) != iProver_top
% 7.51/1.49      | r2_hidden(X2,X0) != iProver_top
% 7.51/1.49      | r2_hidden(X2,X1) != iProver_top ),
% 7.51/1.49      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_6108,plain,
% 7.51/1.49      ( sK1(k1_tarski(X0),X1) = X0
% 7.51/1.49      | r2_hidden(X2,X1) != iProver_top
% 7.51/1.49      | r2_hidden(X2,k1_tarski(X0)) != iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_2237,c_834]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_6757,plain,
% 7.51/1.49      ( sK1(k1_tarski(X0),X1) = X0
% 7.51/1.49      | r1_xboole_0(X2,k1_tarski(X0)) = iProver_top
% 7.51/1.49      | r2_hidden(sK1(X2,k1_tarski(X0)),X1) != iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_833,c_6108]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_13679,plain,
% 7.51/1.49      ( sK1(k1_tarski(X0),X1) = X0
% 7.51/1.49      | r1_xboole_0(X1,k1_tarski(X0)) = iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_832,c_6757]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_11,plain,
% 7.51/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.51/1.49      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.51/1.49      | ~ l1_pre_topc(X1) ),
% 7.51/1.49      inference(cnf_transformation,[],[f67]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_825,plain,
% 7.51/1.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 7.51/1.49      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 7.51/1.49      | l1_pre_topc(X1) != iProver_top ),
% 7.51/1.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_20,plain,
% 7.51/1.49      ( ~ v3_pre_topc(X0,X1)
% 7.51/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.51/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 7.51/1.49      | ~ r1_xboole_0(X0,X2)
% 7.51/1.49      | r1_xboole_0(X0,k2_pre_topc(X1,X2))
% 7.51/1.49      | ~ v2_pre_topc(X1)
% 7.51/1.49      | ~ l1_pre_topc(X1) ),
% 7.51/1.49      inference(cnf_transformation,[],[f76]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_816,plain,
% 7.51/1.49      ( v3_pre_topc(X0,X1) != iProver_top
% 7.51/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 7.51/1.49      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 7.51/1.49      | r1_xboole_0(X0,X2) != iProver_top
% 7.51/1.49      | r1_xboole_0(X0,k2_pre_topc(X1,X2)) = iProver_top
% 7.51/1.49      | v2_pre_topc(X1) != iProver_top
% 7.51/1.49      | l1_pre_topc(X1) != iProver_top ),
% 7.51/1.49      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_3327,plain,
% 7.51/1.49      ( v3_pre_topc(k2_pre_topc(X0,X1),X0) != iProver_top
% 7.51/1.49      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.51/1.49      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.51/1.49      | r1_xboole_0(k2_pre_topc(X0,X1),X2) != iProver_top
% 7.51/1.49      | r1_xboole_0(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) = iProver_top
% 7.51/1.49      | v2_pre_topc(X0) != iProver_top
% 7.51/1.49      | l1_pre_topc(X0) != iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_825,c_816]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_25,negated_conjecture,
% 7.51/1.49      ( m1_subset_1(sK5,u1_struct_0(sK4)) ),
% 7.51/1.49      inference(cnf_transformation,[],[f82]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_812,plain,
% 7.51/1.49      ( m1_subset_1(sK5,u1_struct_0(sK4)) = iProver_top ),
% 7.51/1.49      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_14,plain,
% 7.51/1.49      ( ~ m1_subset_1(X0,X1)
% 7.51/1.49      | v1_xboole_0(X1)
% 7.51/1.49      | k6_domain_1(X1,X0) = k1_tarski(X0) ),
% 7.51/1.49      inference(cnf_transformation,[],[f70]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_822,plain,
% 7.51/1.49      ( k6_domain_1(X0,X1) = k1_tarski(X1)
% 7.51/1.49      | m1_subset_1(X1,X0) != iProver_top
% 7.51/1.49      | v1_xboole_0(X0) = iProver_top ),
% 7.51/1.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_2546,plain,
% 7.51/1.49      ( k6_domain_1(u1_struct_0(sK4),sK5) = k1_tarski(sK5)
% 7.51/1.49      | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_812,c_822]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_29,negated_conjecture,
% 7.51/1.49      ( ~ v2_struct_0(sK4) ),
% 7.51/1.49      inference(cnf_transformation,[],[f78]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_26,negated_conjecture,
% 7.51/1.49      ( l1_pre_topc(sK4) ),
% 7.51/1.49      inference(cnf_transformation,[],[f81]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_13,plain,
% 7.51/1.49      ( v2_struct_0(X0)
% 7.51/1.49      | ~ l1_struct_0(X0)
% 7.51/1.49      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 7.51/1.49      inference(cnf_transformation,[],[f69]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_56,plain,
% 7.51/1.49      ( v2_struct_0(sK4)
% 7.51/1.49      | ~ l1_struct_0(sK4)
% 7.51/1.49      | ~ v1_xboole_0(u1_struct_0(sK4)) ),
% 7.51/1.49      inference(instantiation,[status(thm)],[c_13]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_12,plain,
% 7.51/1.49      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 7.51/1.49      inference(cnf_transformation,[],[f68]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_59,plain,
% 7.51/1.49      ( l1_struct_0(sK4) | ~ l1_pre_topc(sK4) ),
% 7.51/1.49      inference(instantiation,[status(thm)],[c_12]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_1162,plain,
% 7.51/1.49      ( ~ m1_subset_1(sK5,u1_struct_0(sK4))
% 7.51/1.49      | v1_xboole_0(u1_struct_0(sK4))
% 7.51/1.49      | k6_domain_1(u1_struct_0(sK4),sK5) = k1_tarski(sK5) ),
% 7.51/1.49      inference(instantiation,[status(thm)],[c_14]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_2967,plain,
% 7.51/1.49      ( k6_domain_1(u1_struct_0(sK4),sK5) = k1_tarski(sK5) ),
% 7.51/1.49      inference(global_propositional_subsumption,
% 7.51/1.49                [status(thm)],
% 7.51/1.49                [c_2546,c_29,c_26,c_25,c_56,c_59,c_1162]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_24,negated_conjecture,
% 7.51/1.49      ( m1_subset_1(sK6,u1_struct_0(sK4)) ),
% 7.51/1.49      inference(cnf_transformation,[],[f83]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_813,plain,
% 7.51/1.49      ( m1_subset_1(sK6,u1_struct_0(sK4)) = iProver_top ),
% 7.51/1.49      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_2545,plain,
% 7.51/1.49      ( k6_domain_1(u1_struct_0(sK4),sK6) = k1_tarski(sK6)
% 7.51/1.49      | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_813,c_822]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_1159,plain,
% 7.51/1.49      ( ~ m1_subset_1(sK6,u1_struct_0(sK4))
% 7.51/1.49      | v1_xboole_0(u1_struct_0(sK4))
% 7.51/1.49      | k6_domain_1(u1_struct_0(sK4),sK6) = k1_tarski(sK6) ),
% 7.51/1.49      inference(instantiation,[status(thm)],[c_14]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_2724,plain,
% 7.51/1.49      ( k6_domain_1(u1_struct_0(sK4),sK6) = k1_tarski(sK6) ),
% 7.51/1.49      inference(global_propositional_subsumption,
% 7.51/1.49                [status(thm)],
% 7.51/1.49                [c_2545,c_29,c_26,c_24,c_56,c_59,c_1159]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_23,negated_conjecture,
% 7.51/1.49      ( ~ r1_xboole_0(k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK5)),k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK6))) ),
% 7.51/1.49      inference(cnf_transformation,[],[f84]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_814,plain,
% 7.51/1.49      ( r1_xboole_0(k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK5)),k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK6))) != iProver_top ),
% 7.51/1.49      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_2727,plain,
% 7.51/1.49      ( r1_xboole_0(k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK5)),k2_pre_topc(sK4,k1_tarski(sK6))) != iProver_top ),
% 7.51/1.49      inference(demodulation,[status(thm)],[c_2724,c_814]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_2970,plain,
% 7.51/1.49      ( r1_xboole_0(k2_pre_topc(sK4,k1_tarski(sK5)),k2_pre_topc(sK4,k1_tarski(sK6))) != iProver_top ),
% 7.51/1.49      inference(demodulation,[status(thm)],[c_2967,c_2727]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_17821,plain,
% 7.51/1.49      ( v3_pre_topc(k2_pre_topc(sK4,k1_tarski(sK5)),sK4) != iProver_top
% 7.51/1.49      | m1_subset_1(k1_tarski(sK6),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 7.51/1.49      | m1_subset_1(k1_tarski(sK5),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 7.51/1.49      | r1_xboole_0(k2_pre_topc(sK4,k1_tarski(sK5)),k1_tarski(sK6)) != iProver_top
% 7.51/1.49      | v2_pre_topc(sK4) != iProver_top
% 7.51/1.49      | l1_pre_topc(sK4) != iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_3327,c_2970]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_30,plain,
% 7.51/1.49      ( v2_struct_0(sK4) != iProver_top ),
% 7.51/1.49      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_28,negated_conjecture,
% 7.51/1.49      ( v2_pre_topc(sK4) ),
% 7.51/1.49      inference(cnf_transformation,[],[f79]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_31,plain,
% 7.51/1.49      ( v2_pre_topc(sK4) = iProver_top ),
% 7.51/1.49      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_27,negated_conjecture,
% 7.51/1.49      ( v3_tdlat_3(sK4) ),
% 7.51/1.49      inference(cnf_transformation,[],[f80]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_32,plain,
% 7.51/1.49      ( v3_tdlat_3(sK4) = iProver_top ),
% 7.51/1.49      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_33,plain,
% 7.51/1.49      ( l1_pre_topc(sK4) = iProver_top ),
% 7.51/1.49      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_34,plain,
% 7.51/1.49      ( m1_subset_1(sK5,u1_struct_0(sK4)) = iProver_top ),
% 7.51/1.49      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_35,plain,
% 7.51/1.49      ( m1_subset_1(sK6,u1_struct_0(sK4)) = iProver_top ),
% 7.51/1.49      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_55,plain,
% 7.51/1.49      ( v2_struct_0(X0) = iProver_top
% 7.51/1.49      | l1_struct_0(X0) != iProver_top
% 7.51/1.49      | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
% 7.51/1.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_57,plain,
% 7.51/1.49      ( v2_struct_0(sK4) = iProver_top
% 7.51/1.49      | l1_struct_0(sK4) != iProver_top
% 7.51/1.49      | v1_xboole_0(u1_struct_0(sK4)) != iProver_top ),
% 7.51/1.49      inference(instantiation,[status(thm)],[c_55]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_58,plain,
% 7.51/1.49      ( l1_struct_0(X0) = iProver_top | l1_pre_topc(X0) != iProver_top ),
% 7.51/1.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_60,plain,
% 7.51/1.49      ( l1_struct_0(sK4) = iProver_top
% 7.51/1.49      | l1_pre_topc(sK4) != iProver_top ),
% 7.51/1.49      inference(instantiation,[status(thm)],[c_58]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_10,plain,
% 7.51/1.49      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 7.51/1.49      inference(cnf_transformation,[],[f66]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_1120,plain,
% 7.51/1.49      ( ~ m1_subset_1(sK6,u1_struct_0(sK4))
% 7.51/1.49      | r2_hidden(sK6,u1_struct_0(sK4))
% 7.51/1.49      | v1_xboole_0(u1_struct_0(sK4)) ),
% 7.51/1.49      inference(instantiation,[status(thm)],[c_10]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_1121,plain,
% 7.51/1.49      ( m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top
% 7.51/1.49      | r2_hidden(sK6,u1_struct_0(sK4)) = iProver_top
% 7.51/1.49      | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
% 7.51/1.49      inference(predicate_to_equality,[status(thm)],[c_1120]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_1123,plain,
% 7.51/1.49      ( ~ m1_subset_1(sK5,u1_struct_0(sK4))
% 7.51/1.49      | r2_hidden(sK5,u1_struct_0(sK4))
% 7.51/1.49      | v1_xboole_0(u1_struct_0(sK4)) ),
% 7.51/1.49      inference(instantiation,[status(thm)],[c_10]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_1124,plain,
% 7.51/1.49      ( m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
% 7.51/1.49      | r2_hidden(sK5,u1_struct_0(sK4)) = iProver_top
% 7.51/1.49      | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
% 7.51/1.49      inference(predicate_to_equality,[status(thm)],[c_1123]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_9,plain,
% 7.51/1.49      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~ r2_hidden(X0,X1) ),
% 7.51/1.49      inference(cnf_transformation,[],[f65]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_1282,plain,
% 7.51/1.49      ( m1_subset_1(k1_tarski(sK6),k1_zfmisc_1(u1_struct_0(sK4)))
% 7.51/1.49      | ~ r2_hidden(sK6,u1_struct_0(sK4)) ),
% 7.51/1.49      inference(instantiation,[status(thm)],[c_9]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_1283,plain,
% 7.51/1.49      ( m1_subset_1(k1_tarski(sK6),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
% 7.51/1.49      | r2_hidden(sK6,u1_struct_0(sK4)) != iProver_top ),
% 7.51/1.49      inference(predicate_to_equality,[status(thm)],[c_1282]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_1298,plain,
% 7.51/1.49      ( m1_subset_1(k1_tarski(sK5),k1_zfmisc_1(u1_struct_0(sK4)))
% 7.51/1.49      | ~ r2_hidden(sK5,u1_struct_0(sK4)) ),
% 7.51/1.49      inference(instantiation,[status(thm)],[c_9]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_1299,plain,
% 7.51/1.49      ( m1_subset_1(k1_tarski(sK5),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
% 7.51/1.49      | r2_hidden(sK5,u1_struct_0(sK4)) != iProver_top ),
% 7.51/1.49      inference(predicate_to_equality,[status(thm)],[c_1298]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_1607,plain,
% 7.51/1.49      ( m1_subset_1(k2_pre_topc(sK4,k1_tarski(sK5)),k1_zfmisc_1(u1_struct_0(sK4)))
% 7.51/1.49      | ~ m1_subset_1(k1_tarski(sK5),k1_zfmisc_1(u1_struct_0(sK4)))
% 7.51/1.49      | ~ l1_pre_topc(sK4) ),
% 7.51/1.49      inference(instantiation,[status(thm)],[c_11]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_1608,plain,
% 7.51/1.49      ( m1_subset_1(k2_pre_topc(sK4,k1_tarski(sK5)),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
% 7.51/1.49      | m1_subset_1(k1_tarski(sK5),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 7.51/1.49      | l1_pre_topc(sK4) != iProver_top ),
% 7.51/1.49      inference(predicate_to_equality,[status(thm)],[c_1607]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_15,plain,
% 7.51/1.49      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
% 7.51/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 7.51/1.49      | ~ v2_pre_topc(X0)
% 7.51/1.49      | ~ l1_pre_topc(X0) ),
% 7.51/1.49      inference(cnf_transformation,[],[f71]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_1612,plain,
% 7.51/1.49      ( v4_pre_topc(k2_pre_topc(sK4,k1_tarski(sK5)),sK4)
% 7.51/1.49      | ~ m1_subset_1(k1_tarski(sK5),k1_zfmisc_1(u1_struct_0(sK4)))
% 7.51/1.49      | ~ v2_pre_topc(sK4)
% 7.51/1.49      | ~ l1_pre_topc(sK4) ),
% 7.51/1.49      inference(instantiation,[status(thm)],[c_15]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_1613,plain,
% 7.51/1.49      ( v4_pre_topc(k2_pre_topc(sK4,k1_tarski(sK5)),sK4) = iProver_top
% 7.51/1.49      | m1_subset_1(k1_tarski(sK5),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 7.51/1.49      | v2_pre_topc(sK4) != iProver_top
% 7.51/1.49      | l1_pre_topc(sK4) != iProver_top ),
% 7.51/1.49      inference(predicate_to_equality,[status(thm)],[c_1612]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_19,plain,
% 7.51/1.49      ( v3_pre_topc(X0,X1)
% 7.51/1.49      | ~ v4_pre_topc(X0,X1)
% 7.51/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.51/1.49      | ~ v3_tdlat_3(X1)
% 7.51/1.49      | ~ v2_pre_topc(X1)
% 7.51/1.49      | ~ l1_pre_topc(X1) ),
% 7.51/1.49      inference(cnf_transformation,[],[f72]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_2619,plain,
% 7.51/1.49      ( v3_pre_topc(k2_pre_topc(sK4,k1_tarski(sK5)),sK4)
% 7.51/1.49      | ~ v4_pre_topc(k2_pre_topc(sK4,k1_tarski(sK5)),sK4)
% 7.51/1.49      | ~ m1_subset_1(k2_pre_topc(sK4,k1_tarski(sK5)),k1_zfmisc_1(u1_struct_0(sK4)))
% 7.51/1.49      | ~ v3_tdlat_3(sK4)
% 7.51/1.49      | ~ v2_pre_topc(sK4)
% 7.51/1.49      | ~ l1_pre_topc(sK4) ),
% 7.51/1.49      inference(instantiation,[status(thm)],[c_19]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_2623,plain,
% 7.51/1.49      ( v3_pre_topc(k2_pre_topc(sK4,k1_tarski(sK5)),sK4) = iProver_top
% 7.51/1.49      | v4_pre_topc(k2_pre_topc(sK4,k1_tarski(sK5)),sK4) != iProver_top
% 7.51/1.49      | m1_subset_1(k2_pre_topc(sK4,k1_tarski(sK5)),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 7.51/1.49      | v3_tdlat_3(sK4) != iProver_top
% 7.51/1.49      | v2_pre_topc(sK4) != iProver_top
% 7.51/1.49      | l1_pre_topc(sK4) != iProver_top ),
% 7.51/1.49      inference(predicate_to_equality,[status(thm)],[c_2619]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_1538,plain,
% 7.51/1.49      ( ~ v3_pre_topc(X0,sK4)
% 7.51/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 7.51/1.49      | ~ m1_subset_1(k1_tarski(sK6),k1_zfmisc_1(u1_struct_0(sK4)))
% 7.51/1.49      | r1_xboole_0(X0,k2_pre_topc(sK4,k1_tarski(sK6)))
% 7.51/1.49      | ~ r1_xboole_0(X0,k1_tarski(sK6))
% 7.51/1.49      | ~ v2_pre_topc(sK4)
% 7.51/1.49      | ~ l1_pre_topc(sK4) ),
% 7.51/1.49      inference(instantiation,[status(thm)],[c_20]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_5507,plain,
% 7.51/1.49      ( ~ v3_pre_topc(k2_pre_topc(sK4,k1_tarski(sK5)),sK4)
% 7.51/1.49      | ~ m1_subset_1(k2_pre_topc(sK4,k1_tarski(sK5)),k1_zfmisc_1(u1_struct_0(sK4)))
% 7.51/1.49      | ~ m1_subset_1(k1_tarski(sK6),k1_zfmisc_1(u1_struct_0(sK4)))
% 7.51/1.49      | r1_xboole_0(k2_pre_topc(sK4,k1_tarski(sK5)),k2_pre_topc(sK4,k1_tarski(sK6)))
% 7.51/1.49      | ~ r1_xboole_0(k2_pre_topc(sK4,k1_tarski(sK5)),k1_tarski(sK6))
% 7.51/1.49      | ~ v2_pre_topc(sK4)
% 7.51/1.49      | ~ l1_pre_topc(sK4) ),
% 7.51/1.49      inference(instantiation,[status(thm)],[c_1538]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_5508,plain,
% 7.51/1.49      ( v3_pre_topc(k2_pre_topc(sK4,k1_tarski(sK5)),sK4) != iProver_top
% 7.51/1.49      | m1_subset_1(k2_pre_topc(sK4,k1_tarski(sK5)),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 7.51/1.49      | m1_subset_1(k1_tarski(sK6),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 7.51/1.49      | r1_xboole_0(k2_pre_topc(sK4,k1_tarski(sK5)),k2_pre_topc(sK4,k1_tarski(sK6))) = iProver_top
% 7.51/1.49      | r1_xboole_0(k2_pre_topc(sK4,k1_tarski(sK5)),k1_tarski(sK6)) != iProver_top
% 7.51/1.49      | v2_pre_topc(sK4) != iProver_top
% 7.51/1.49      | l1_pre_topc(sK4) != iProver_top ),
% 7.51/1.49      inference(predicate_to_equality,[status(thm)],[c_5507]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_19805,plain,
% 7.51/1.49      ( r1_xboole_0(k2_pre_topc(sK4,k1_tarski(sK5)),k1_tarski(sK6)) != iProver_top ),
% 7.51/1.49      inference(global_propositional_subsumption,
% 7.51/1.49                [status(thm)],
% 7.51/1.49                [c_17821,c_30,c_31,c_32,c_33,c_34,c_35,c_57,c_60,c_1121,
% 7.51/1.49                 c_1124,c_1283,c_1299,c_1608,c_1613,c_2623,c_2970,c_5508]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_19819,plain,
% 7.51/1.49      ( sK1(k1_tarski(sK6),k2_pre_topc(sK4,k1_tarski(sK5))) = sK6 ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_13679,c_19805]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_21,plain,
% 7.51/1.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.51/1.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.51/1.49      | ~ r2_hidden(X2,k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X0)))
% 7.51/1.49      | ~ v3_tdlat_3(X1)
% 7.51/1.49      | ~ v2_pre_topc(X1)
% 7.51/1.49      | v2_struct_0(X1)
% 7.51/1.49      | ~ l1_pre_topc(X1)
% 7.51/1.49      | k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X0)) = k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2)) ),
% 7.51/1.49      inference(cnf_transformation,[],[f77]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_815,plain,
% 7.51/1.49      ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))
% 7.51/1.49      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 7.51/1.49      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 7.51/1.49      | r2_hidden(X2,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))) != iProver_top
% 7.51/1.49      | v3_tdlat_3(X0) != iProver_top
% 7.51/1.49      | v2_pre_topc(X0) != iProver_top
% 7.51/1.49      | v2_struct_0(X0) = iProver_top
% 7.51/1.49      | l1_pre_topc(X0) != iProver_top ),
% 7.51/1.49      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_2977,plain,
% 7.51/1.49      ( k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),X0)) = k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK5))
% 7.51/1.49      | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
% 7.51/1.49      | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
% 7.51/1.49      | r2_hidden(X0,k2_pre_topc(sK4,k1_tarski(sK5))) != iProver_top
% 7.51/1.49      | v3_tdlat_3(sK4) != iProver_top
% 7.51/1.49      | v2_pre_topc(sK4) != iProver_top
% 7.51/1.49      | v2_struct_0(sK4) = iProver_top
% 7.51/1.49      | l1_pre_topc(sK4) != iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_2967,c_815]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_2978,plain,
% 7.51/1.49      ( k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),X0)) = k2_pre_topc(sK4,k1_tarski(sK5))
% 7.51/1.49      | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
% 7.51/1.49      | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
% 7.51/1.49      | r2_hidden(X0,k2_pre_topc(sK4,k1_tarski(sK5))) != iProver_top
% 7.51/1.49      | v3_tdlat_3(sK4) != iProver_top
% 7.51/1.49      | v2_pre_topc(sK4) != iProver_top
% 7.51/1.49      | v2_struct_0(sK4) = iProver_top
% 7.51/1.49      | l1_pre_topc(sK4) != iProver_top ),
% 7.51/1.49      inference(light_normalisation,[status(thm)],[c_2977,c_2967]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_4057,plain,
% 7.51/1.49      ( m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
% 7.51/1.49      | k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),X0)) = k2_pre_topc(sK4,k1_tarski(sK5))
% 7.51/1.49      | r2_hidden(X0,k2_pre_topc(sK4,k1_tarski(sK5))) != iProver_top ),
% 7.51/1.49      inference(global_propositional_subsumption,
% 7.51/1.49                [status(thm)],
% 7.51/1.49                [c_2978,c_30,c_31,c_32,c_33,c_34]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_4058,plain,
% 7.51/1.49      ( k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),X0)) = k2_pre_topc(sK4,k1_tarski(sK5))
% 7.51/1.49      | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
% 7.51/1.49      | r2_hidden(X0,k2_pre_topc(sK4,k1_tarski(sK5))) != iProver_top ),
% 7.51/1.49      inference(renaming,[status(thm)],[c_4057]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_4067,plain,
% 7.51/1.49      ( k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK1(X0,k2_pre_topc(sK4,k1_tarski(sK5))))) = k2_pre_topc(sK4,k1_tarski(sK5))
% 7.51/1.49      | m1_subset_1(sK1(X0,k2_pre_topc(sK4,k1_tarski(sK5))),u1_struct_0(sK4)) != iProver_top
% 7.51/1.49      | r1_xboole_0(X0,k2_pre_topc(sK4,k1_tarski(sK5))) = iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_833,c_4058]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_20580,plain,
% 7.51/1.49      ( k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK1(k1_tarski(sK6),k2_pre_topc(sK4,k1_tarski(sK5))))) = k2_pre_topc(sK4,k1_tarski(sK5))
% 7.51/1.49      | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top
% 7.51/1.49      | r1_xboole_0(k1_tarski(sK6),k2_pre_topc(sK4,k1_tarski(sK5))) = iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_19819,c_4067]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_20592,plain,
% 7.51/1.49      ( k2_pre_topc(sK4,k1_tarski(sK5)) = k2_pre_topc(sK4,k1_tarski(sK6))
% 7.51/1.49      | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top
% 7.51/1.49      | r1_xboole_0(k1_tarski(sK6),k2_pre_topc(sK4,k1_tarski(sK5))) = iProver_top ),
% 7.51/1.49      inference(light_normalisation,
% 7.51/1.49                [status(thm)],
% 7.51/1.49                [c_20580,c_2724,c_19819]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_22,negated_conjecture,
% 7.51/1.49      ( k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK5)) != k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK6)) ),
% 7.51/1.49      inference(cnf_transformation,[],[f85]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_2728,plain,
% 7.51/1.49      ( k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK5)) != k2_pre_topc(sK4,k1_tarski(sK6)) ),
% 7.51/1.49      inference(demodulation,[status(thm)],[c_2724,c_22]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_2971,plain,
% 7.51/1.49      ( k2_pre_topc(sK4,k1_tarski(sK5)) != k2_pre_topc(sK4,k1_tarski(sK6)) ),
% 7.51/1.49      inference(demodulation,[status(thm)],[c_2967,c_2728]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_20811,plain,
% 7.51/1.49      ( r1_xboole_0(k1_tarski(sK6),k2_pre_topc(sK4,k1_tarski(sK5))) = iProver_top ),
% 7.51/1.49      inference(global_propositional_subsumption,
% 7.51/1.49                [status(thm)],
% 7.51/1.49                [c_20592,c_35,c_2971]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_20816,plain,
% 7.51/1.49      ( r2_hidden(X0,k2_pre_topc(sK4,k1_tarski(sK5))) != iProver_top
% 7.51/1.49      | r2_hidden(X0,k1_tarski(sK6)) != iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_20811,c_834]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_20825,plain,
% 7.51/1.49      ( r1_xboole_0(k2_pre_topc(sK4,k1_tarski(sK5)),X0) = iProver_top
% 7.51/1.49      | r2_hidden(sK1(k2_pre_topc(sK4,k1_tarski(sK5)),X0),k1_tarski(sK6)) != iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_832,c_20816]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_21555,plain,
% 7.51/1.49      ( r1_xboole_0(k2_pre_topc(sK4,k1_tarski(sK5)),k1_tarski(sK6)) = iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_833,c_20825]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(contradiction,plain,
% 7.51/1.49      ( $false ),
% 7.51/1.49      inference(minisat,
% 7.51/1.49                [status(thm)],
% 7.51/1.49                [c_21555,c_5508,c_2970,c_2623,c_1613,c_1608,c_1299,
% 7.51/1.49                 c_1283,c_1124,c_1121,c_60,c_57,c_35,c_34,c_33,c_32,c_31,
% 7.51/1.49                 c_30]) ).
% 7.51/1.49  
% 7.51/1.49  
% 7.51/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.51/1.49  
% 7.51/1.49  ------                               Statistics
% 7.51/1.49  
% 7.51/1.49  ------ Selected
% 7.51/1.49  
% 7.51/1.49  total_time:                             0.566
% 7.51/1.49  
%------------------------------------------------------------------------------
