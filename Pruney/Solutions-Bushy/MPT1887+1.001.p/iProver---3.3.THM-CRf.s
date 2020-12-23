%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1887+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:47 EST 2020

% Result     : Theorem 35.27s
% Output     : CNFRefutation 35.27s
% Verified   : 
% Statistics : Number of formulae       :  348 (8831 expanded)
%              Number of clauses        :  259 (3227 expanded)
%              Number of leaves         :   29 (1957 expanded)
%              Depth                    :   32
%              Number of atoms          : 1097 (38031 expanded)
%              Number of equality atoms :  572 (8433 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f87,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f21,conjecture,(
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

fof(f22,negated_conjecture,(
    ~ ! [X0] :
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
    inference(negated_conjecture,[],[f21])).

fof(f44,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))
              & r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f45,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))
              & r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))
          & r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK4)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
        & r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK4)))
        & m1_subset_1(sK4,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))
              & r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))
            & r2_hidden(sK3,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))
                & r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X1)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X2))
              & r2_hidden(X1,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X2)))
              & m1_subset_1(X2,u1_struct_0(sK2)) )
          & m1_subset_1(X1,u1_struct_0(sK2)) )
      & l1_pre_topc(sK2)
      & v3_tdlat_3(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,
    ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))
    & r2_hidden(sK3,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)))
    & m1_subset_1(sK4,u1_struct_0(sK2))
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & l1_pre_topc(sK2)
    & v3_tdlat_3(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f45,f59,f58,f57])).

fof(f93,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f60])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f35])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f89,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f60])).

fof(f92,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f60])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f72,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f68,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f84,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X2,X1)
                  & v4_pre_topc(X1,X0) )
               => r1_tarski(k2_pre_topc(X0,X2),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X2),X1)
              | ~ r1_tarski(X2,X1)
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X2),X1)
              | ~ r1_tarski(X2,X1)
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_pre_topc(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f46])).

fof(f64,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f98,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f62])).

fof(f90,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f60])).

fof(f94,plain,(
    m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f60])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f95,plain,(
    r2_hidden(sK3,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))) ),
    inference(cnf_transformation,[],[f60])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f96,plain,(
    k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)) ),
    inference(cnf_transformation,[],[f60])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f17,axiom,(
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

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X1,k2_pre_topc(X0,X2))
      | ~ v3_pre_topc(X1,X0)
      | ~ r1_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

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

fof(f32,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f33,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f51,plain,(
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
    inference(nnf_transformation,[],[f33])).

fof(f52,plain,(
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
    inference(rectify,[],[f51])).

fof(f53,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_pre_topc(X1,X0)
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK1(X0),X0)
        & v4_pre_topc(sK1(X0),X0)
        & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0] :
      ( ( ( v3_tdlat_3(X0)
          | ( ~ v3_pre_topc(sK1(X0),X0)
            & v4_pre_topc(sK1(X0),X0)
            & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v3_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f52,f53])).

fof(f74,plain,(
    ! [X2,X0] :
      ( v3_pre_topc(X2,X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f91,plain,(
    v3_tdlat_3(sK2) ),
    inference(cnf_transformation,[],[f60])).

fof(f8,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f20,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f81,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_26,plain,
    ( r2_hidden(X0,X1)
    | r1_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1449,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r1_xboole_0(k1_tarski(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_5,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1470,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2598,plain,
    ( k3_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
    | r2_hidden(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1449,c_1470])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1455,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(k1_tarski(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1445,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_18,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1457,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | m1_subset_1(X0,X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3506,plain,
    ( r2_hidden(sK3,u1_struct_0(sK2)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1445,c_1457])).

cnf(c_35,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_36,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_32,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_39,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_40,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_11,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_85,plain,
    ( v2_struct_0(X0) = iProver_top
    | v1_xboole_0(u1_struct_0(X0)) != iProver_top
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_87,plain,
    ( v2_struct_0(sK2) = iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) != iProver_top
    | l1_struct_0(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_85])).

cnf(c_7,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_95,plain,
    ( l1_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_97,plain,
    ( l1_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_95])).

cnf(c_1827,plain,
    ( r2_hidden(sK3,u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_1828,plain,
    ( r2_hidden(sK3,u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1827])).

cnf(c_3822,plain,
    ( r2_hidden(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3506,c_36,c_39,c_40,c_87,c_97,c_1828])).

cnf(c_22,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1453,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_9,plain,
    ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1466,plain,
    ( v4_pre_topc(k2_pre_topc(X0,X1),X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_5725,plain,
    ( v4_pre_topc(k2_pre_topc(X0,X1),X0) = iProver_top
    | r1_tarski(X1,u1_struct_0(X0)) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1453,c_1466])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1469,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1452,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_4634,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(k2_pre_topc(X1,X0),u1_struct_0(X1)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1469,c_1452])).

cnf(c_19,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | r1_tarski(k2_pre_topc(X1,X2),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1456,plain,
    ( v4_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(k2_pre_topc(X1,X2),X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_5478,plain,
    ( v4_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(X0,u1_struct_0(X1)) != iProver_top
    | r1_tarski(k2_pre_topc(X1,X2),X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1453,c_1456])).

cnf(c_27743,plain,
    ( v4_pre_topc(X0,X1) != iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(X2,u1_struct_0(X1)) != iProver_top
    | r1_tarski(X0,u1_struct_0(X1)) != iProver_top
    | r1_tarski(k2_pre_topc(X1,X2),X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1453,c_5478])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1450,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(X1,X0)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3376,plain,
    ( r1_tarski(X0,k2_pre_topc(X1,X0)) = iProver_top
    | r1_tarski(X0,u1_struct_0(X1)) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1453,c_1450])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1473,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_7549,plain,
    ( k2_pre_topc(X0,X1) = X1
    | r1_tarski(X1,u1_struct_0(X0)) != iProver_top
    | r1_tarski(k2_pre_topc(X0,X1),X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3376,c_1473])).

cnf(c_46466,plain,
    ( k2_pre_topc(X0,X1) = X1
    | v4_pre_topc(X1,X0) != iProver_top
    | r1_tarski(X1,X1) != iProver_top
    | r1_tarski(X1,u1_struct_0(X0)) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_27743,c_7549])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1472,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_46809,plain,
    ( k2_pre_topc(X0,X1) = X1
    | v4_pre_topc(X1,X0) != iProver_top
    | r1_tarski(X1,u1_struct_0(X0)) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_46466,c_1472])).

cnf(c_46816,plain,
    ( k2_pre_topc(X0,k2_pre_topc(X0,X1)) = k2_pre_topc(X0,X1)
    | v4_pre_topc(k2_pre_topc(X0,X1),X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4634,c_46809])).

cnf(c_47998,plain,
    ( k2_pre_topc(X0,k2_pre_topc(X0,X1)) = k2_pre_topc(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | r1_tarski(X1,u1_struct_0(X0)) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5725,c_46816])).

cnf(c_89,plain,
    ( v4_pre_topc(k2_pre_topc(X0,X1),X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_48057,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | k2_pre_topc(X0,k2_pre_topc(X0,X1)) = k2_pre_topc(X0,X1)
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_47998,c_89,c_46816])).

cnf(c_48058,plain,
    ( k2_pre_topc(X0,k2_pre_topc(X0,X1)) = k2_pre_topc(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_48057])).

cnf(c_48070,plain,
    ( k2_pre_topc(X0,k2_pre_topc(X0,X1)) = k2_pre_topc(X0,X1)
    | r1_tarski(X1,u1_struct_0(X0)) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1453,c_48058])).

cnf(c_50234,plain,
    ( k2_pre_topc(X0,k2_pre_topc(X0,k1_tarski(X1))) = k2_pre_topc(X0,k1_tarski(X1))
    | r2_hidden(X1,u1_struct_0(X0)) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1455,c_48070])).

cnf(c_50464,plain,
    ( k2_pre_topc(sK2,k2_pre_topc(sK2,k1_tarski(sK3))) = k2_pre_topc(sK2,k1_tarski(sK3))
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3822,c_50234])).

cnf(c_34,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_86,plain,
    ( v2_struct_0(sK2)
    | ~ v1_xboole_0(u1_struct_0(sK2))
    | ~ l1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_96,plain,
    ( l1_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1970,plain,
    ( ~ r2_hidden(sK3,u1_struct_0(sK2))
    | r1_tarski(k1_tarski(sK3),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_1848,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,u1_struct_0(X1)) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_2545,plain,
    ( m1_subset_1(k1_tarski(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(k1_tarski(sK3),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1848])).

cnf(c_3026,plain,
    ( v4_pre_topc(k2_pre_topc(sK2,k1_tarski(sK3)),sK2)
    | ~ m1_subset_1(k1_tarski(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_3030,plain,
    ( m1_subset_1(k2_pre_topc(sK2,k1_tarski(sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(k1_tarski(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_5922,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK2,k1_tarski(sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(k2_pre_topc(sK2,k1_tarski(sK3)),k2_pre_topc(sK2,k2_pre_topc(sK2,k1_tarski(sK3))))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_3649,plain,
    ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_7131,plain,
    ( r1_tarski(k2_pre_topc(X0,k1_tarski(sK3)),k2_pre_topc(X0,k1_tarski(sK3))) ),
    inference(instantiation,[status(thm)],[c_3649])).

cnf(c_7134,plain,
    ( r1_tarski(k2_pre_topc(sK2,k1_tarski(sK3)),k2_pre_topc(sK2,k1_tarski(sK3))) ),
    inference(instantiation,[status(thm)],[c_7131])).

cnf(c_3595,plain,
    ( ~ r1_tarski(X0,k2_pre_topc(X1,k1_tarski(sK3)))
    | ~ r1_tarski(k2_pre_topc(X1,k1_tarski(sK3)),X0)
    | X0 = k2_pre_topc(X1,k1_tarski(sK3)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_13344,plain,
    ( ~ r1_tarski(k2_pre_topc(sK2,k2_pre_topc(sK2,k1_tarski(sK3))),k2_pre_topc(sK2,k1_tarski(sK3)))
    | ~ r1_tarski(k2_pre_topc(sK2,k1_tarski(sK3)),k2_pre_topc(sK2,k2_pre_topc(sK2,k1_tarski(sK3))))
    | k2_pre_topc(sK2,k2_pre_topc(sK2,k1_tarski(sK3))) = k2_pre_topc(sK2,k1_tarski(sK3)) ),
    inference(instantiation,[status(thm)],[c_3595])).

cnf(c_5888,plain,
    ( ~ v4_pre_topc(k2_pre_topc(sK2,k1_tarski(sK3)),sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(k2_pre_topc(sK2,k1_tarski(sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X0,k2_pre_topc(sK2,k1_tarski(sK3)))
    | r1_tarski(k2_pre_topc(sK2,X0),k2_pre_topc(sK2,k1_tarski(sK3)))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_14945,plain,
    ( ~ v4_pre_topc(k2_pre_topc(sK2,k1_tarski(sK3)),sK2)
    | ~ m1_subset_1(k2_pre_topc(sK2,k1_tarski(sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(k2_pre_topc(sK2,k2_pre_topc(sK2,k1_tarski(sK3))),k2_pre_topc(sK2,k1_tarski(sK3)))
    | ~ r1_tarski(k2_pre_topc(sK2,k1_tarski(sK3)),k2_pre_topc(sK2,k1_tarski(sK3)))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_5888])).

cnf(c_51095,plain,
    ( k2_pre_topc(sK2,k2_pre_topc(sK2,k1_tarski(sK3))) = k2_pre_topc(sK2,k1_tarski(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_50464,c_35,c_34,c_32,c_31,c_86,c_96,c_1827,c_1970,c_2545,c_3026,c_3030,c_5922,c_7134,c_13344,c_14945])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1446,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_3505,plain,
    ( r2_hidden(sK4,u1_struct_0(sK2)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1446,c_1457])).

cnf(c_41,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_1824,plain,
    ( r2_hidden(sK4,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_1825,plain,
    ( r2_hidden(sK4,u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1824])).

cnf(c_3814,plain,
    ( r2_hidden(sK4,u1_struct_0(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3505,c_36,c_39,c_41,c_87,c_97,c_1825])).

cnf(c_17,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1458,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_46450,plain,
    ( k3_xboole_0(k2_pre_topc(X0,X1),X2) = k2_pre_topc(X0,X1)
    | v4_pre_topc(X2,X0) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X2,u1_struct_0(X0)) != iProver_top
    | r1_tarski(X1,u1_struct_0(X0)) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_27743,c_1458])).

cnf(c_58200,plain,
    ( k3_xboole_0(k2_pre_topc(X0,k1_tarski(X1)),X2) = k2_pre_topc(X0,k1_tarski(X1))
    | r2_hidden(X1,u1_struct_0(X0)) != iProver_top
    | v4_pre_topc(X2,X0) != iProver_top
    | r1_tarski(X2,u1_struct_0(X0)) != iProver_top
    | r1_tarski(k1_tarski(X1),X2) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1455,c_46450])).

cnf(c_75986,plain,
    ( k3_xboole_0(k2_pre_topc(sK2,k1_tarski(sK4)),X0) = k2_pre_topc(sK2,k1_tarski(sK4))
    | v4_pre_topc(X0,sK2) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK2)) != iProver_top
    | r1_tarski(k1_tarski(sK4),X0) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3814,c_58200])).

cnf(c_76045,plain,
    ( r1_tarski(k1_tarski(sK4),X0) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK2)) != iProver_top
    | v4_pre_topc(X0,sK2) != iProver_top
    | k3_xboole_0(k2_pre_topc(sK2,k1_tarski(sK4)),X0) = k2_pre_topc(sK2,k1_tarski(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_75986,c_39])).

cnf(c_76046,plain,
    ( k3_xboole_0(k2_pre_topc(sK2,k1_tarski(sK4)),X0) = k2_pre_topc(sK2,k1_tarski(sK4))
    | v4_pre_topc(X0,sK2) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK2)) != iProver_top
    | r1_tarski(k1_tarski(sK4),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_76045])).

cnf(c_76058,plain,
    ( k3_xboole_0(k2_pre_topc(sK2,k1_tarski(sK4)),k2_pre_topc(sK2,X0)) = k2_pre_topc(sK2,k1_tarski(sK4))
    | v4_pre_topc(k2_pre_topc(sK2,X0),sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(k1_tarski(sK4),k2_pre_topc(sK2,X0)) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4634,c_76046])).

cnf(c_77569,plain,
    ( r1_tarski(k1_tarski(sK4),k2_pre_topc(sK2,X0)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v4_pre_topc(k2_pre_topc(sK2,X0),sK2) != iProver_top
    | k3_xboole_0(k2_pre_topc(sK2,k1_tarski(sK4)),k2_pre_topc(sK2,X0)) = k2_pre_topc(sK2,k1_tarski(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_76058,c_39])).

cnf(c_77570,plain,
    ( k3_xboole_0(k2_pre_topc(sK2,k1_tarski(sK4)),k2_pre_topc(sK2,X0)) = k2_pre_topc(sK2,k1_tarski(sK4))
    | v4_pre_topc(k2_pre_topc(sK2,X0),sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(k1_tarski(sK4),k2_pre_topc(sK2,X0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_77569])).

cnf(c_77584,plain,
    ( k3_xboole_0(k2_pre_topc(sK2,k1_tarski(sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k1_tarski(sK3)))) = k2_pre_topc(sK2,k1_tarski(sK4))
    | v4_pre_topc(k2_pre_topc(sK2,k2_pre_topc(sK2,k1_tarski(sK3))),sK2) != iProver_top
    | m1_subset_1(k2_pre_topc(sK2,k1_tarski(sK3)),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(k1_tarski(sK4),k2_pre_topc(sK2,k1_tarski(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_51095,c_77570])).

cnf(c_77589,plain,
    ( k3_xboole_0(k2_pre_topc(sK2,k1_tarski(sK4)),k2_pre_topc(sK2,k1_tarski(sK3))) = k2_pre_topc(sK2,k1_tarski(sK4))
    | v4_pre_topc(k2_pre_topc(sK2,k1_tarski(sK3)),sK2) != iProver_top
    | m1_subset_1(k2_pre_topc(sK2,k1_tarski(sK3)),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(k1_tarski(sK4),k2_pre_topc(sK2,k1_tarski(sK3))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_77584,c_51095])).

cnf(c_37,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_1971,plain,
    ( r2_hidden(sK3,u1_struct_0(sK2)) != iProver_top
    | r1_tarski(k1_tarski(sK3),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1970])).

cnf(c_2546,plain,
    ( m1_subset_1(k1_tarski(sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | r1_tarski(k1_tarski(sK3),u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2545])).

cnf(c_3027,plain,
    ( v4_pre_topc(k2_pre_topc(sK2,k1_tarski(sK3)),sK2) = iProver_top
    | m1_subset_1(k1_tarski(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3026])).

cnf(c_3031,plain,
    ( m1_subset_1(k2_pre_topc(sK2,k1_tarski(sK3)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | m1_subset_1(k1_tarski(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3030])).

cnf(c_79205,plain,
    ( k3_xboole_0(k2_pre_topc(sK2,k1_tarski(sK4)),k2_pre_topc(sK2,k1_tarski(sK3))) = k2_pre_topc(sK2,k1_tarski(sK4))
    | r1_tarski(k1_tarski(sK4),k2_pre_topc(sK2,k1_tarski(sK3))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_77589,c_36,c_37,c_39,c_40,c_87,c_97,c_1828,c_1971,c_2546,c_3027,c_3031])).

cnf(c_79211,plain,
    ( k3_xboole_0(k2_pre_topc(sK2,k1_tarski(sK4)),k2_pre_topc(sK2,k1_tarski(sK3))) = k2_pre_topc(sK2,k1_tarski(sK4))
    | r2_hidden(sK4,k2_pre_topc(sK2,k1_tarski(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1455,c_79205])).

cnf(c_83178,plain,
    ( k3_xboole_0(k2_pre_topc(sK2,k1_tarski(sK4)),k2_pre_topc(sK2,k1_tarski(sK3))) = k2_pre_topc(sK2,k1_tarski(sK4))
    | k3_xboole_0(k1_tarski(sK4),k2_pre_topc(sK2,k1_tarski(sK3))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2598,c_79211])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_109434,plain,
    ( k3_xboole_0(k2_pre_topc(sK2,k1_tarski(sK3)),k2_pre_topc(sK2,k1_tarski(sK4))) = k2_pre_topc(sK2,k1_tarski(sK4))
    | k3_xboole_0(k1_tarski(sK4),k2_pre_topc(sK2,k1_tarski(sK3))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_83178,c_0])).

cnf(c_50463,plain,
    ( k2_pre_topc(sK2,k2_pre_topc(sK2,k1_tarski(sK4))) = k2_pre_topc(sK2,k1_tarski(sK4))
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3814,c_50234])).

cnf(c_1962,plain,
    ( ~ r2_hidden(sK4,u1_struct_0(sK2))
    | r1_tarski(k1_tarski(sK4),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_2542,plain,
    ( m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(k1_tarski(sK4),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1848])).

cnf(c_3011,plain,
    ( v4_pre_topc(k2_pre_topc(sK2,k1_tarski(sK4)),sK2)
    | ~ m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_3015,plain,
    ( m1_subset_1(k2_pre_topc(sK2,k1_tarski(sK4)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_5872,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK2,k1_tarski(sK4)),k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(k2_pre_topc(sK2,k1_tarski(sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k1_tarski(sK4))))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_10335,plain,
    ( r1_tarski(k2_pre_topc(X0,k1_tarski(sK4)),k2_pre_topc(X0,k1_tarski(sK4))) ),
    inference(instantiation,[status(thm)],[c_3649])).

cnf(c_10337,plain,
    ( r1_tarski(k2_pre_topc(sK2,k1_tarski(sK4)),k2_pre_topc(sK2,k1_tarski(sK4))) ),
    inference(instantiation,[status(thm)],[c_10335])).

cnf(c_5670,plain,
    ( ~ r1_tarski(X0,k2_pre_topc(X1,k1_tarski(sK4)))
    | ~ r1_tarski(k2_pre_topc(X1,k1_tarski(sK4)),X0)
    | X0 = k2_pre_topc(X1,k1_tarski(sK4)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_13016,plain,
    ( ~ r1_tarski(k2_pre_topc(sK2,k2_pre_topc(sK2,k1_tarski(sK4))),k2_pre_topc(sK2,k1_tarski(sK4)))
    | ~ r1_tarski(k2_pre_topc(sK2,k1_tarski(sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k1_tarski(sK4))))
    | k2_pre_topc(sK2,k2_pre_topc(sK2,k1_tarski(sK4))) = k2_pre_topc(sK2,k1_tarski(sK4)) ),
    inference(instantiation,[status(thm)],[c_5670])).

cnf(c_5838,plain,
    ( ~ v4_pre_topc(k2_pre_topc(sK2,k1_tarski(sK4)),sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(k2_pre_topc(sK2,k1_tarski(sK4)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X0,k2_pre_topc(sK2,k1_tarski(sK4)))
    | r1_tarski(k2_pre_topc(sK2,X0),k2_pre_topc(sK2,k1_tarski(sK4)))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_26371,plain,
    ( ~ v4_pre_topc(k2_pre_topc(sK2,k1_tarski(sK4)),sK2)
    | ~ m1_subset_1(k2_pre_topc(sK2,k1_tarski(sK4)),k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(k2_pre_topc(sK2,k2_pre_topc(sK2,k1_tarski(sK4))),k2_pre_topc(sK2,k1_tarski(sK4)))
    | ~ r1_tarski(k2_pre_topc(sK2,k1_tarski(sK4)),k2_pre_topc(sK2,k1_tarski(sK4)))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_5838])).

cnf(c_50502,plain,
    ( k2_pre_topc(sK2,k2_pre_topc(sK2,k1_tarski(sK4))) = k2_pre_topc(sK2,k1_tarski(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_50463,c_35,c_34,c_32,c_30,c_86,c_96,c_1824,c_1962,c_2542,c_3011,c_3015,c_5872,c_10337,c_13016,c_26371])).

cnf(c_75987,plain,
    ( k3_xboole_0(k2_pre_topc(sK2,k1_tarski(sK3)),X0) = k2_pre_topc(sK2,k1_tarski(sK3))
    | v4_pre_topc(X0,sK2) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK2)) != iProver_top
    | r1_tarski(k1_tarski(sK3),X0) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3822,c_58200])).

cnf(c_76334,plain,
    ( r1_tarski(k1_tarski(sK3),X0) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK2)) != iProver_top
    | v4_pre_topc(X0,sK2) != iProver_top
    | k3_xboole_0(k2_pre_topc(sK2,k1_tarski(sK3)),X0) = k2_pre_topc(sK2,k1_tarski(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_75987,c_39])).

cnf(c_76335,plain,
    ( k3_xboole_0(k2_pre_topc(sK2,k1_tarski(sK3)),X0) = k2_pre_topc(sK2,k1_tarski(sK3))
    | v4_pre_topc(X0,sK2) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK2)) != iProver_top
    | r1_tarski(k1_tarski(sK3),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_76334])).

cnf(c_76347,plain,
    ( k3_xboole_0(k2_pre_topc(sK2,k1_tarski(sK3)),k2_pre_topc(sK2,X0)) = k2_pre_topc(sK2,k1_tarski(sK3))
    | v4_pre_topc(k2_pre_topc(sK2,X0),sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(k1_tarski(sK3),k2_pre_topc(sK2,X0)) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4634,c_76335])).

cnf(c_78091,plain,
    ( r1_tarski(k1_tarski(sK3),k2_pre_topc(sK2,X0)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v4_pre_topc(k2_pre_topc(sK2,X0),sK2) != iProver_top
    | k3_xboole_0(k2_pre_topc(sK2,k1_tarski(sK3)),k2_pre_topc(sK2,X0)) = k2_pre_topc(sK2,k1_tarski(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_76347,c_39])).

cnf(c_78092,plain,
    ( k3_xboole_0(k2_pre_topc(sK2,k1_tarski(sK3)),k2_pre_topc(sK2,X0)) = k2_pre_topc(sK2,k1_tarski(sK3))
    | v4_pre_topc(k2_pre_topc(sK2,X0),sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(k1_tarski(sK3),k2_pre_topc(sK2,X0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_78091])).

cnf(c_78105,plain,
    ( k3_xboole_0(k2_pre_topc(sK2,k1_tarski(sK3)),k2_pre_topc(sK2,k2_pre_topc(sK2,k1_tarski(sK4)))) = k2_pre_topc(sK2,k1_tarski(sK3))
    | v4_pre_topc(k2_pre_topc(sK2,k2_pre_topc(sK2,k1_tarski(sK4))),sK2) != iProver_top
    | m1_subset_1(k2_pre_topc(sK2,k1_tarski(sK4)),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(k1_tarski(sK3),k2_pre_topc(sK2,k1_tarski(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_50502,c_78092])).

cnf(c_78117,plain,
    ( k3_xboole_0(k2_pre_topc(sK2,k1_tarski(sK3)),k2_pre_topc(sK2,k1_tarski(sK4))) = k2_pre_topc(sK2,k1_tarski(sK3))
    | v4_pre_topc(k2_pre_topc(sK2,k1_tarski(sK4)),sK2) != iProver_top
    | m1_subset_1(k2_pre_topc(sK2,k1_tarski(sK4)),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(k1_tarski(sK3),k2_pre_topc(sK2,k1_tarski(sK4))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_78105,c_50502])).

cnf(c_29,negated_conjecture,
    ( r2_hidden(sK3,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_108,plain,
    ( r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_112,plain,
    ( ~ r1_tarski(sK2,sK2)
    | sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1748,plain,
    ( ~ r2_hidden(sK3,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)))
    | r1_tarski(k1_tarski(sK3),k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1863,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2))
    | k6_domain_1(u1_struct_0(sK2),sK4) = k1_tarski(sK4) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_627,plain,
    ( X0 != X1
    | X2 != X3
    | k2_pre_topc(X0,X2) = k2_pre_topc(X1,X3) ),
    theory(equality)).

cnf(c_2333,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK4) != X0
    | k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)) = k2_pre_topc(X1,X0)
    | sK2 != X1 ),
    inference(instantiation,[status(thm)],[c_627])).

cnf(c_3454,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK4) != k1_tarski(sK4)
    | k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)) = k2_pre_topc(X0,k1_tarski(sK4))
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_2333])).

cnf(c_3455,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK4) != k1_tarski(sK4)
    | k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)) = k2_pre_topc(sK2,k1_tarski(sK4))
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_3454])).

cnf(c_623,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2654,plain,
    ( k1_tarski(X0) = k1_tarski(X0) ),
    inference(instantiation,[status(thm)],[c_623])).

cnf(c_4615,plain,
    ( k1_tarski(sK3) = k1_tarski(sK3) ),
    inference(instantiation,[status(thm)],[c_2654])).

cnf(c_624,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2767,plain,
    ( X0 != X1
    | X0 = k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))
    | k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)) != X1 ),
    inference(instantiation,[status(thm)],[c_624])).

cnf(c_4583,plain,
    ( X0 != k2_pre_topc(X1,k1_tarski(sK4))
    | X0 = k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))
    | k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)) != k2_pre_topc(X1,k1_tarski(sK4)) ),
    inference(instantiation,[status(thm)],[c_2767])).

cnf(c_5682,plain,
    ( k2_pre_topc(X0,k1_tarski(sK4)) != k2_pre_topc(X0,k1_tarski(sK4))
    | k2_pre_topc(X0,k1_tarski(sK4)) = k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))
    | k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)) != k2_pre_topc(X0,k1_tarski(sK4)) ),
    inference(instantiation,[status(thm)],[c_4583])).

cnf(c_5684,plain,
    ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)) != k2_pre_topc(sK2,k1_tarski(sK4))
    | k2_pre_topc(sK2,k1_tarski(sK4)) = k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))
    | k2_pre_topc(sK2,k1_tarski(sK4)) != k2_pre_topc(sK2,k1_tarski(sK4)) ),
    inference(instantiation,[status(thm)],[c_5682])).

cnf(c_5683,plain,
    ( k2_pre_topc(X0,k1_tarski(sK4)) = k2_pre_topc(X0,k1_tarski(sK4)) ),
    inference(instantiation,[status(thm)],[c_623])).

cnf(c_5685,plain,
    ( k2_pre_topc(sK2,k1_tarski(sK4)) = k2_pre_topc(sK2,k1_tarski(sK4)) ),
    inference(instantiation,[status(thm)],[c_5683])).

cnf(c_625,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1897,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_tarski(X2),X3)
    | X3 != X1
    | k1_tarski(X2) != X0 ),
    inference(instantiation,[status(thm)],[c_625])).

cnf(c_2653,plain,
    ( ~ r1_tarski(k1_tarski(X0),X1)
    | r1_tarski(k1_tarski(X0),X2)
    | X2 != X1
    | k1_tarski(X0) != k1_tarski(X0) ),
    inference(instantiation,[status(thm)],[c_1897])).

cnf(c_4217,plain,
    ( r1_tarski(k1_tarski(sK3),X0)
    | ~ r1_tarski(k1_tarski(sK3),k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)))
    | X0 != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))
    | k1_tarski(sK3) != k1_tarski(sK3) ),
    inference(instantiation,[status(thm)],[c_2653])).

cnf(c_11918,plain,
    ( r1_tarski(k1_tarski(sK3),k2_pre_topc(X0,k1_tarski(sK4)))
    | ~ r1_tarski(k1_tarski(sK3),k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)))
    | k2_pre_topc(X0,k1_tarski(sK4)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))
    | k1_tarski(sK3) != k1_tarski(sK3) ),
    inference(instantiation,[status(thm)],[c_4217])).

cnf(c_11926,plain,
    ( ~ r1_tarski(k1_tarski(sK3),k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)))
    | r1_tarski(k1_tarski(sK3),k2_pre_topc(sK2,k1_tarski(sK4)))
    | k2_pre_topc(sK2,k1_tarski(sK4)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))
    | k1_tarski(sK3) != k1_tarski(sK3) ),
    inference(instantiation,[status(thm)],[c_11918])).

cnf(c_21066,plain,
    ( ~ v4_pre_topc(k2_pre_topc(sK2,k1_tarski(sK4)),sK2)
    | ~ m1_subset_1(k2_pre_topc(sK2,k1_tarski(sK4)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(k1_tarski(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(k2_pre_topc(sK2,k1_tarski(sK3)),k2_pre_topc(sK2,k1_tarski(sK4)))
    | ~ r1_tarski(k1_tarski(sK3),k2_pre_topc(sK2,k1_tarski(sK4)))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_5838])).

cnf(c_3601,plain,
    ( ~ r1_tarski(k2_pre_topc(X0,k1_tarski(sK3)),X1)
    | k3_xboole_0(k2_pre_topc(X0,k1_tarski(sK3)),X1) = k2_pre_topc(X0,k1_tarski(sK3)) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_51824,plain,
    ( ~ r1_tarski(k2_pre_topc(sK2,k1_tarski(sK3)),k2_pre_topc(sK2,k1_tarski(sK4)))
    | k3_xboole_0(k2_pre_topc(sK2,k1_tarski(sK3)),k2_pre_topc(sK2,k1_tarski(sK4))) = k2_pre_topc(sK2,k1_tarski(sK3)) ),
    inference(instantiation,[status(thm)],[c_3601])).

cnf(c_79214,plain,
    ( k3_xboole_0(k2_pre_topc(sK2,k1_tarski(sK3)),k2_pre_topc(sK2,k1_tarski(sK4))) = k2_pre_topc(sK2,k1_tarski(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_78117,c_35,c_34,c_32,c_31,c_30,c_29,c_86,c_96,c_108,c_112,c_1748,c_1824,c_1827,c_1863,c_1962,c_1970,c_2542,c_2545,c_3011,c_3015,c_3455,c_4615,c_5684,c_5685,c_11926,c_21066,c_51824])).

cnf(c_109438,plain,
    ( k2_pre_topc(sK2,k1_tarski(sK4)) = k2_pre_topc(sK2,k1_tarski(sK3))
    | k3_xboole_0(k1_tarski(sK4),k2_pre_topc(sK2,k1_tarski(sK3))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_109434,c_79214])).

cnf(c_1463,plain,
    ( k6_domain_1(X0,X1) = k1_tarski(X1)
    | m1_subset_1(X1,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3712,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK3) = k1_tarski(sK3)
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1445,c_1463])).

cnf(c_1866,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2))
    | k6_domain_1(u1_struct_0(sK2),sK3) = k1_tarski(sK3) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_4096,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK3) = k1_tarski(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3712,c_35,c_32,c_31,c_86,c_96,c_1866])).

cnf(c_3711,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK4) = k1_tarski(sK4)
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1446,c_1463])).

cnf(c_3991,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK4) = k1_tarski(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3711,c_35,c_32,c_30,c_86,c_96,c_1863])).

cnf(c_28,negated_conjecture,
    ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_3996,plain,
    ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)) != k2_pre_topc(sK2,k1_tarski(sK4)) ),
    inference(demodulation,[status(thm)],[c_3991,c_28])).

cnf(c_4099,plain,
    ( k2_pre_topc(sK2,k1_tarski(sK4)) != k2_pre_topc(sK2,k1_tarski(sK3)) ),
    inference(demodulation,[status(thm)],[c_4096,c_3996])).

cnf(c_109455,plain,
    ( k3_xboole_0(k1_tarski(sK4),k2_pre_topc(sK2,k1_tarski(sK3))) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_109438,c_4099])).

cnf(c_4,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1471,plain,
    ( k3_xboole_0(X0,X1) != k1_xboole_0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2467,plain,
    ( k3_xboole_0(X0,X1) != k1_xboole_0
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_1471])).

cnf(c_109458,plain,
    ( r1_xboole_0(k2_pre_topc(sK2,k1_tarski(sK3)),k1_tarski(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_109455,c_2467])).

cnf(c_24,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_xboole_0(X0,X2)
    | r1_xboole_0(X0,k2_pre_topc(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1451,plain,
    ( v3_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_xboole_0(X0,X2) != iProver_top
    | r1_xboole_0(X0,k2_pre_topc(X1,X2)) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_4467,plain,
    ( v3_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_xboole_0(X0,X2) != iProver_top
    | r1_xboole_0(X0,k2_pre_topc(X1,X2)) = iProver_top
    | r1_tarski(X0,u1_struct_0(X1)) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1453,c_1451])).

cnf(c_11501,plain,
    ( v3_pre_topc(X0,X1) != iProver_top
    | r1_xboole_0(X0,X2) != iProver_top
    | r1_xboole_0(X0,k2_pre_topc(X1,X2)) = iProver_top
    | r1_tarski(X2,u1_struct_0(X1)) != iProver_top
    | r1_tarski(X0,u1_struct_0(X1)) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1453,c_4467])).

cnf(c_4630,plain,
    ( v3_pre_topc(k2_pre_topc(X0,X1),X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | r1_xboole_0(k2_pre_topc(X0,X1),X2) != iProver_top
    | r1_xboole_0(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1469,c_1451])).

cnf(c_12927,plain,
    ( k3_xboole_0(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) = k1_xboole_0
    | v3_pre_topc(k2_pre_topc(X0,X1),X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | r1_xboole_0(k2_pre_topc(X0,X1),X2) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4630,c_1470])).

cnf(c_82838,plain,
    ( k3_xboole_0(k2_pre_topc(sK2,k2_pre_topc(sK2,k1_tarski(sK3))),k2_pre_topc(sK2,X0)) = k1_xboole_0
    | v3_pre_topc(k2_pre_topc(sK2,k1_tarski(sK3)),sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK2,k1_tarski(sK3)),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_xboole_0(k2_pre_topc(sK2,k2_pre_topc(sK2,k1_tarski(sK3))),X0) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_51095,c_12927])).

cnf(c_82846,plain,
    ( k3_xboole_0(k2_pre_topc(sK2,k1_tarski(sK3)),k2_pre_topc(sK2,X0)) = k1_xboole_0
    | v3_pre_topc(k2_pre_topc(sK2,k1_tarski(sK3)),sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK2,k1_tarski(sK3)),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_xboole_0(k2_pre_topc(sK2,k1_tarski(sK3)),X0) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_82838,c_51095])).

cnf(c_16,plain,
    ( v3_pre_topc(X0,X1)
    | ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1459,plain,
    ( v3_pre_topc(X0,X1) = iProver_top
    | v4_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v3_tdlat_3(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_5940,plain,
    ( v3_pre_topc(k2_pre_topc(X0,X1),X0) = iProver_top
    | v4_pre_topc(k2_pre_topc(X0,X1),X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v3_tdlat_3(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1469,c_1459])).

cnf(c_29419,plain,
    ( v3_pre_topc(k2_pre_topc(X0,X1),X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v3_tdlat_3(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5940,c_89])).

cnf(c_29433,plain,
    ( v3_pre_topc(k2_pre_topc(X0,X1),X0) = iProver_top
    | r1_tarski(X1,u1_struct_0(X0)) != iProver_top
    | v3_tdlat_3(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1453,c_29419])).

cnf(c_51139,plain,
    ( v3_pre_topc(k2_pre_topc(sK2,k1_tarski(sK3)),sK2) = iProver_top
    | r1_tarski(k2_pre_topc(sK2,k1_tarski(sK3)),u1_struct_0(sK2)) != iProver_top
    | v3_tdlat_3(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_51095,c_29433])).

cnf(c_33,negated_conjecture,
    ( v3_tdlat_3(sK2) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_38,plain,
    ( v3_tdlat_3(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_5889,plain,
    ( v3_pre_topc(k2_pre_topc(sK2,k1_tarski(sK3)),sK2)
    | ~ v4_pre_topc(k2_pre_topc(sK2,k1_tarski(sK3)),sK2)
    | ~ m1_subset_1(k2_pre_topc(sK2,k1_tarski(sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v3_tdlat_3(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_5895,plain,
    ( v3_pre_topc(k2_pre_topc(sK2,k1_tarski(sK3)),sK2) = iProver_top
    | v4_pre_topc(k2_pre_topc(sK2,k1_tarski(sK3)),sK2) != iProver_top
    | m1_subset_1(k2_pre_topc(sK2,k1_tarski(sK3)),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v3_tdlat_3(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5889])).

cnf(c_53827,plain,
    ( v3_pre_topc(k2_pre_topc(sK2,k1_tarski(sK3)),sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_51139,c_36,c_37,c_38,c_39,c_40,c_87,c_97,c_1828,c_1971,c_2546,c_3027,c_3031,c_5895])).

cnf(c_82833,plain,
    ( k3_xboole_0(k2_pre_topc(sK2,k1_tarski(sK3)),k2_pre_topc(sK2,X0)) = k1_xboole_0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(k1_tarski(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_xboole_0(k2_pre_topc(sK2,k1_tarski(sK3)),X0) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_53827,c_12927])).

cnf(c_83853,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | k3_xboole_0(k2_pre_topc(sK2,k1_tarski(sK3)),k2_pre_topc(sK2,X0)) = k1_xboole_0
    | r1_xboole_0(k2_pre_topc(sK2,k1_tarski(sK3)),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_82846,c_36,c_37,c_39,c_40,c_87,c_97,c_1828,c_1971,c_2546,c_82833])).

cnf(c_83854,plain,
    ( k3_xboole_0(k2_pre_topc(sK2,k1_tarski(sK3)),k2_pre_topc(sK2,X0)) = k1_xboole_0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_xboole_0(k2_pre_topc(sK2,k1_tarski(sK3)),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_83853])).

cnf(c_83862,plain,
    ( k3_xboole_0(k2_pre_topc(sK2,k1_tarski(sK3)),k2_pre_topc(sK2,k2_pre_topc(X0,X1))) = k1_xboole_0
    | v3_pre_topc(k2_pre_topc(sK2,k1_tarski(sK3)),X0) != iProver_top
    | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_xboole_0(k2_pre_topc(sK2,k1_tarski(sK3)),X1) != iProver_top
    | r1_tarski(X1,u1_struct_0(X0)) != iProver_top
    | r1_tarski(k2_pre_topc(sK2,k1_tarski(sK3)),u1_struct_0(X0)) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_11501,c_83854])).

cnf(c_91119,plain,
    ( k3_xboole_0(k2_pre_topc(sK2,k1_tarski(sK3)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k1_tarski(sK4))))) = k1_xboole_0
    | v3_pre_topc(k2_pre_topc(sK2,k1_tarski(sK3)),sK2) != iProver_top
    | m1_subset_1(k2_pre_topc(sK2,k1_tarski(sK4)),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_xboole_0(k2_pre_topc(sK2,k1_tarski(sK3)),k2_pre_topc(sK2,k1_tarski(sK4))) != iProver_top
    | r1_tarski(k2_pre_topc(sK2,k1_tarski(sK4)),u1_struct_0(sK2)) != iProver_top
    | r1_tarski(k2_pre_topc(sK2,k1_tarski(sK3)),u1_struct_0(sK2)) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_50502,c_83862])).

cnf(c_91145,plain,
    ( k2_pre_topc(sK2,k1_tarski(sK3)) = k1_xboole_0
    | v3_pre_topc(k2_pre_topc(sK2,k1_tarski(sK3)),sK2) != iProver_top
    | m1_subset_1(k2_pre_topc(sK2,k1_tarski(sK4)),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_xboole_0(k2_pre_topc(sK2,k1_tarski(sK3)),k2_pre_topc(sK2,k1_tarski(sK4))) != iProver_top
    | r1_tarski(k2_pre_topc(sK2,k1_tarski(sK4)),u1_struct_0(sK2)) != iProver_top
    | r1_tarski(k2_pre_topc(sK2,k1_tarski(sK3)),u1_struct_0(sK2)) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_91119,c_50502,c_79214])).

cnf(c_1963,plain,
    ( r2_hidden(sK4,u1_struct_0(sK2)) != iProver_top
    | r1_tarski(k1_tarski(sK4),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1962])).

cnf(c_2543,plain,
    ( m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | r1_tarski(k1_tarski(sK4),u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2542])).

cnf(c_3016,plain,
    ( m1_subset_1(k2_pre_topc(sK2,k1_tarski(sK4)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3015])).

cnf(c_2522,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,u1_struct_0(X1)) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_5871,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK2,k1_tarski(sK4)),k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(k2_pre_topc(sK2,k1_tarski(sK4)),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2522])).

cnf(c_5878,plain,
    ( m1_subset_1(k2_pre_topc(sK2,k1_tarski(sK4)),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(k2_pre_topc(sK2,k1_tarski(sK4)),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5871])).

cnf(c_5921,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK2,k1_tarski(sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(k2_pre_topc(sK2,k1_tarski(sK3)),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2522])).

cnf(c_5928,plain,
    ( m1_subset_1(k2_pre_topc(sK2,k1_tarski(sK3)),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(k2_pre_topc(sK2,k1_tarski(sK3)),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5921])).

cnf(c_92219,plain,
    ( k2_pre_topc(sK2,k1_tarski(sK3)) = k1_xboole_0
    | r1_xboole_0(k2_pre_topc(sK2,k1_tarski(sK3)),k2_pre_topc(sK2,k1_tarski(sK4))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_91145,c_36,c_37,c_38,c_39,c_40,c_41,c_87,c_97,c_1825,c_1828,c_1963,c_1971,c_2543,c_2546,c_3016,c_3027,c_3031,c_5878,c_5895,c_5928])).

cnf(c_92225,plain,
    ( k2_pre_topc(sK2,k1_tarski(sK3)) = k1_xboole_0
    | v3_pre_topc(k2_pre_topc(sK2,k1_tarski(sK3)),sK2) != iProver_top
    | r1_xboole_0(k2_pre_topc(sK2,k1_tarski(sK3)),k1_tarski(sK4)) != iProver_top
    | r1_tarski(k2_pre_topc(sK2,k1_tarski(sK3)),u1_struct_0(sK2)) != iProver_top
    | r1_tarski(k1_tarski(sK4),u1_struct_0(sK2)) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_11501,c_92219])).

cnf(c_92226,plain,
    ( k2_pre_topc(sK2,k1_tarski(sK3)) = k1_xboole_0
    | v3_pre_topc(k2_pre_topc(sK2,k1_tarski(sK3)),sK2) != iProver_top
    | m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(k1_tarski(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_xboole_0(k2_pre_topc(sK2,k1_tarski(sK3)),k1_tarski(sK4)) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4630,c_92219])).

cnf(c_92258,plain,
    ( k2_pre_topc(sK2,k1_tarski(sK3)) = k1_xboole_0
    | r1_xboole_0(k2_pre_topc(sK2,k1_tarski(sK3)),k1_tarski(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_92225,c_36,c_37,c_38,c_39,c_40,c_41,c_87,c_97,c_1825,c_1828,c_1963,c_1971,c_2546,c_3027,c_3031,c_5895,c_5928])).

cnf(c_109610,plain,
    ( k2_pre_topc(sK2,k1_tarski(sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_109458,c_92258])).

cnf(c_7550,plain,
    ( k3_xboole_0(X0,k2_pre_topc(X1,X0)) = X0
    | r1_tarski(X0,u1_struct_0(X1)) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3376,c_1458])).

cnf(c_7839,plain,
    ( k3_xboole_0(k1_tarski(X0),k2_pre_topc(X1,k1_tarski(X0))) = k1_tarski(X0)
    | r2_hidden(X0,u1_struct_0(X1)) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1455,c_7550])).

cnf(c_10030,plain,
    ( k3_xboole_0(k1_tarski(sK3),k2_pre_topc(sK2,k1_tarski(sK3))) = k1_tarski(sK3)
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3822,c_7839])).

cnf(c_3029,plain,
    ( ~ m1_subset_1(k1_tarski(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(k1_tarski(sK3),k2_pre_topc(sK2,k1_tarski(sK3)))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_2665,plain,
    ( ~ r1_tarski(k1_tarski(X0),X1)
    | k3_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_5902,plain,
    ( ~ r1_tarski(k1_tarski(sK3),k2_pre_topc(sK2,k1_tarski(sK3)))
    | k3_xboole_0(k1_tarski(sK3),k2_pre_topc(sK2,k1_tarski(sK3))) = k1_tarski(sK3) ),
    inference(instantiation,[status(thm)],[c_2665])).

cnf(c_10216,plain,
    ( k3_xboole_0(k1_tarski(sK3),k2_pre_topc(sK2,k1_tarski(sK3))) = k1_tarski(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10030,c_35,c_32,c_31,c_86,c_96,c_1827,c_1970,c_2545,c_3029,c_5902])).

cnf(c_126111,plain,
    ( k3_xboole_0(k1_tarski(sK3),k1_xboole_0) = k1_tarski(sK3) ),
    inference(demodulation,[status(thm)],[c_109610,c_10216])).

cnf(c_10,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1465,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_27,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1448,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_6855,plain,
    ( k3_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2598,c_1448])).

cnf(c_6878,plain,
    ( k3_xboole_0(k1_tarski(X0),k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1465,c_6855])).

cnf(c_126116,plain,
    ( k1_tarski(sK3) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_126111,c_6878])).

cnf(c_1770,plain,
    ( ~ r1_xboole_0(k1_tarski(X0),X1)
    | k3_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_5635,plain,
    ( ~ r1_xboole_0(k1_tarski(sK3),X0)
    | k3_xboole_0(k1_tarski(sK3),X0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1770])).

cnf(c_53090,plain,
    ( ~ r1_xboole_0(k1_tarski(sK3),u1_struct_0(sK2))
    | k3_xboole_0(k1_tarski(sK3),u1_struct_0(sK2)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5635])).

cnf(c_634,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_9592,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k6_domain_1(u1_struct_0(sK2),sK3))
    | k6_domain_1(u1_struct_0(sK2),sK3) != X0 ),
    inference(instantiation,[status(thm)],[c_634])).

cnf(c_25115,plain,
    ( v1_xboole_0(k6_domain_1(u1_struct_0(sK2),sK3))
    | ~ v1_xboole_0(k1_xboole_0)
    | k6_domain_1(u1_struct_0(sK2),sK3) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_9592])).

cnf(c_2165,plain,
    ( X0 != X1
    | k6_domain_1(u1_struct_0(sK2),sK3) != X1
    | k6_domain_1(u1_struct_0(sK2),sK3) = X0 ),
    inference(instantiation,[status(thm)],[c_624])).

cnf(c_5324,plain,
    ( X0 != k3_xboole_0(k1_tarski(sK3),u1_struct_0(sK2))
    | k6_domain_1(u1_struct_0(sK2),sK3) = X0
    | k6_domain_1(u1_struct_0(sK2),sK3) != k3_xboole_0(k1_tarski(sK3),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2165])).

cnf(c_17732,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK3) != k3_xboole_0(k1_tarski(sK3),u1_struct_0(sK2))
    | k6_domain_1(u1_struct_0(sK2),sK3) = k1_xboole_0
    | k1_xboole_0 != k3_xboole_0(k1_tarski(sK3),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_5324])).

cnf(c_2589,plain,
    ( X0 != X1
    | k1_xboole_0 != X1
    | k1_xboole_0 = X0 ),
    inference(instantiation,[status(thm)],[c_624])).

cnf(c_3913,plain,
    ( X0 != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2589])).

cnf(c_7937,plain,
    ( k3_xboole_0(k1_tarski(X0),X1) != k1_xboole_0
    | k1_xboole_0 = k3_xboole_0(k1_tarski(X0),X1)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3913])).

cnf(c_17731,plain,
    ( k3_xboole_0(k1_tarski(sK3),u1_struct_0(sK2)) != k1_xboole_0
    | k1_xboole_0 = k3_xboole_0(k1_tarski(sK3),u1_struct_0(sK2))
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7937])).

cnf(c_3140,plain,
    ( ~ r2_hidden(sK3,X0)
    | ~ v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_11398,plain,
    ( ~ r2_hidden(sK3,k1_tarski(sK3))
    | ~ v1_xboole_0(k1_tarski(sK3)) ),
    inference(instantiation,[status(thm)],[c_3140])).

cnf(c_5147,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k1_tarski(X1))
    | k1_tarski(X1) != X0 ),
    inference(instantiation,[status(thm)],[c_634])).

cnf(c_9226,plain,
    ( ~ v1_xboole_0(k6_domain_1(u1_struct_0(sK2),sK3))
    | v1_xboole_0(k1_tarski(sK3))
    | k1_tarski(sK3) != k6_domain_1(u1_struct_0(sK2),sK3) ),
    inference(instantiation,[status(thm)],[c_5147])).

cnf(c_2658,plain,
    ( X0 != X1
    | k1_tarski(X2) != X1
    | k1_tarski(X2) = X0 ),
    inference(instantiation,[status(thm)],[c_624])).

cnf(c_4051,plain,
    ( X0 != k1_tarski(X1)
    | k1_tarski(X1) = X0
    | k1_tarski(X1) != k1_tarski(X1) ),
    inference(instantiation,[status(thm)],[c_2658])).

cnf(c_8329,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK3) != k1_tarski(sK3)
    | k1_tarski(sK3) = k6_domain_1(u1_struct_0(sK2),sK3)
    | k1_tarski(sK3) != k1_tarski(sK3) ),
    inference(instantiation,[status(thm)],[c_4051])).

cnf(c_3362,plain,
    ( k3_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
    | r2_hidden(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1455,c_1458])).

cnf(c_5235,plain,
    ( k3_xboole_0(k1_tarski(sK3),u1_struct_0(sK2)) = k1_tarski(sK3) ),
    inference(superposition,[status(thm)],[c_3822,c_3362])).

cnf(c_5353,plain,
    ( k1_tarski(sK3) != k1_xboole_0
    | r1_xboole_0(k1_tarski(sK3),u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5235,c_1471])).

cnf(c_5367,plain,
    ( r1_xboole_0(k1_tarski(sK3),u1_struct_0(sK2))
    | k1_tarski(sK3) != k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5353])).

cnf(c_1780,plain,
    ( r1_tarski(k1_tarski(X0),k1_tarski(X0)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_5304,plain,
    ( r1_tarski(k1_tarski(sK3),k1_tarski(sK3)) ),
    inference(instantiation,[status(thm)],[c_1780])).

cnf(c_3355,plain,
    ( X0 != k1_tarski(sK3)
    | k6_domain_1(u1_struct_0(sK2),sK3) = X0
    | k6_domain_1(u1_struct_0(sK2),sK3) != k1_tarski(sK3) ),
    inference(instantiation,[status(thm)],[c_2165])).

cnf(c_4778,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK3) = k3_xboole_0(k1_tarski(sK3),u1_struct_0(sK2))
    | k6_domain_1(u1_struct_0(sK2),sK3) != k1_tarski(sK3)
    | k3_xboole_0(k1_tarski(sK3),u1_struct_0(sK2)) != k1_tarski(sK3) ),
    inference(instantiation,[status(thm)],[c_3355])).

cnf(c_21,plain,
    ( r2_hidden(X0,X1)
    | ~ r1_tarski(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1781,plain,
    ( r2_hidden(X0,k1_tarski(X0))
    | ~ r1_tarski(k1_tarski(X0),k1_tarski(X0)) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_4592,plain,
    ( r2_hidden(sK3,k1_tarski(sK3))
    | ~ r1_tarski(k1_tarski(sK3),k1_tarski(sK3)) ),
    inference(instantiation,[status(thm)],[c_1781])).

cnf(c_3937,plain,
    ( ~ r1_tarski(k1_tarski(sK3),u1_struct_0(sK2))
    | k3_xboole_0(k1_tarski(sK3),u1_struct_0(sK2)) = k1_tarski(sK3) ),
    inference(instantiation,[status(thm)],[c_2665])).

cnf(c_2583,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,X0)
    | k1_xboole_0 = X0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3810,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2583])).

cnf(c_2429,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_126116,c_53090,c_25115,c_17732,c_17731,c_11398,c_9226,c_8329,c_5367,c_5304,c_4778,c_4615,c_4592,c_3937,c_3810,c_2429,c_1970,c_1866,c_1827,c_96,c_10,c_86,c_31,c_32,c_35])).


%------------------------------------------------------------------------------
