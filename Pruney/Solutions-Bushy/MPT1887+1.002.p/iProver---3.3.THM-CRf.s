%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1887+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:48 EST 2020

% Result     : Theorem 19.44s
% Output     : CNFRefutation 19.44s
% Verified   : 
% Statistics : Number of formulae       :  278 (6086 expanded)
%              Number of clauses        :  188 (2310 expanded)
%              Number of leaves         :   24 (1317 expanded)
%              Depth                    :   36
%              Number of atoms          :  952 (26144 expanded)
%              Number of equality atoms :  484 (6655 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20,conjecture,(
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

fof(f21,negated_conjecture,(
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
    inference(negated_conjecture,[],[f20])).

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
    inference(ennf_transformation,[],[f21])).

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

fof(f57,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))
          & r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
        & r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK3)))
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))
              & r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK2)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))
            & r2_hidden(sK2,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,
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
              ( k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X1)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X2))
              & r2_hidden(X1,k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X2)))
              & m1_subset_1(X2,u1_struct_0(sK1)) )
          & m1_subset_1(X1,u1_struct_0(sK1)) )
      & l1_pre_topc(sK1)
      & v3_tdlat_3(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,
    ( k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3))
    & r2_hidden(sK2,k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3)))
    & m1_subset_1(sK3,u1_struct_0(sK1))
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l1_pre_topc(sK1)
    & v3_tdlat_3(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f45,f57,f56,f55])).

fof(f90,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f58])).

fof(f12,axiom,(
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
    inference(ennf_transformation,[],[f12])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f35])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f86,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f58])).

fof(f89,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f58])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f68,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f65,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f81,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f13,axiom,(
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
    inference(ennf_transformation,[],[f13])).

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

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_pre_topc(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f17,axiom,(
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
    inference(ennf_transformation,[],[f17])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f1,axiom,(
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
    inference(nnf_transformation,[],[f1])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f46])).

fof(f61,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f94,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f60])).

fof(f87,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f58])).

fof(f16,axiom,(
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
    inference(ennf_transformation,[],[f16])).

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

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X1,k2_pre_topc(X0,X2))
      | ~ v3_pre_topc(X1,X0)
      | ~ r1_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f88,plain,(
    v3_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f58])).

fof(f10,axiom,(
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
    inference(ennf_transformation,[],[f10])).

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

fof(f49,plain,(
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

fof(f50,plain,(
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
    inference(rectify,[],[f49])).

fof(f51,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_pre_topc(X1,X0)
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK0(X0),X0)
        & v4_pre_topc(sK0(X0),X0)
        & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0] :
      ( ( ( v3_tdlat_3(X0)
          | ( ~ v3_pre_topc(sK0(X0),X0)
            & v4_pre_topc(sK0(X0),X0)
            & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v3_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f50,f51])).

fof(f71,plain,(
    ! [X2,X0] :
      ( v3_pre_topc(X2,X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f91,plain,(
    m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f58])).

fof(f2,axiom,(
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
    inference(nnf_transformation,[],[f2])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f92,plain,(
    r2_hidden(sK2,k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3))) ),
    inference(cnf_transformation,[],[f58])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f93,plain,(
    k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3)) ),
    inference(cnf_transformation,[],[f58])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f19,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f6,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1441,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_17,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1453,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | m1_subset_1(X0,X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3382,plain,
    ( r2_hidden(sK2,u1_struct_0(sK1)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1441,c_1453])).

cnf(c_34,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_35,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_31,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_38,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_39,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_9,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_85,plain,
    ( v2_struct_0(X0) = iProver_top
    | v1_xboole_0(u1_struct_0(X0)) != iProver_top
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_87,plain,
    ( v2_struct_0(sK1) = iProver_top
    | v1_xboole_0(u1_struct_0(sK1)) != iProver_top
    | l1_struct_0(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_85])).

cnf(c_6,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_92,plain,
    ( l1_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_94,plain,
    ( l1_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_92])).

cnf(c_1820,plain,
    ( r2_hidden(sK2,u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1821,plain,
    ( r2_hidden(sK2,u1_struct_0(sK1)) = iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1820])).

cnf(c_3852,plain,
    ( r2_hidden(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3382,c_35,c_38,c_39,c_87,c_94,c_1821])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1451,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(k1_tarski(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_21,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1449,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_7,plain,
    ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1463,plain,
    ( v4_pre_topc(k2_pre_topc(X0,X1),X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4868,plain,
    ( v4_pre_topc(k2_pre_topc(X0,X1),X0) = iProver_top
    | r1_tarski(X1,u1_struct_0(X0)) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1449,c_1463])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1465,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1448,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_4526,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(k2_pre_topc(X1,X0),u1_struct_0(X1)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1465,c_1448])).

cnf(c_18,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | r1_tarski(k2_pre_topc(X1,X2),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1452,plain,
    ( v4_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(k2_pre_topc(X1,X2),X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_4331,plain,
    ( v4_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(X0,u1_struct_0(X1)) != iProver_top
    | r1_tarski(k2_pre_topc(X1,X2),X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1449,c_1452])).

cnf(c_8005,plain,
    ( v4_pre_topc(X0,X1) != iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(X2,u1_struct_0(X1)) != iProver_top
    | r1_tarski(X0,u1_struct_0(X1)) != iProver_top
    | r1_tarski(k2_pre_topc(X1,X2),X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1449,c_4331])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1446,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(X1,X0)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_2624,plain,
    ( r1_tarski(X0,k2_pre_topc(X1,X0)) = iProver_top
    | r1_tarski(X0,u1_struct_0(X1)) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1449,c_1446])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1469,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_6495,plain,
    ( k2_pre_topc(X0,X1) = X1
    | r1_tarski(X1,u1_struct_0(X0)) != iProver_top
    | r1_tarski(k2_pre_topc(X0,X1),X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2624,c_1469])).

cnf(c_28411,plain,
    ( k2_pre_topc(X0,X1) = X1
    | v4_pre_topc(X1,X0) != iProver_top
    | r1_tarski(X1,X1) != iProver_top
    | r1_tarski(X1,u1_struct_0(X0)) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8005,c_6495])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1468,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_29003,plain,
    ( k2_pre_topc(X0,X1) = X1
    | v4_pre_topc(X1,X0) != iProver_top
    | r1_tarski(X1,u1_struct_0(X0)) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_28411,c_1468])).

cnf(c_29010,plain,
    ( k2_pre_topc(X0,k2_pre_topc(X0,X1)) = k2_pre_topc(X0,X1)
    | v4_pre_topc(k2_pre_topc(X0,X1),X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4526,c_29003])).

cnf(c_31936,plain,
    ( k2_pre_topc(X0,k2_pre_topc(X0,X1)) = k2_pre_topc(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | r1_tarski(X1,u1_struct_0(X0)) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4868,c_29010])).

cnf(c_89,plain,
    ( v4_pre_topc(k2_pre_topc(X0,X1),X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_32299,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | k2_pre_topc(X0,k2_pre_topc(X0,X1)) = k2_pre_topc(X0,X1)
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_31936,c_89,c_29010])).

cnf(c_32300,plain,
    ( k2_pre_topc(X0,k2_pre_topc(X0,X1)) = k2_pre_topc(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_32299])).

cnf(c_32311,plain,
    ( k2_pre_topc(X0,k2_pre_topc(X0,X1)) = k2_pre_topc(X0,X1)
    | r1_tarski(X1,u1_struct_0(X0)) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1449,c_32300])).

cnf(c_32350,plain,
    ( k2_pre_topc(X0,k2_pre_topc(X0,k1_tarski(X1))) = k2_pre_topc(X0,k1_tarski(X1))
    | r2_hidden(X1,u1_struct_0(X0)) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1451,c_32311])).

cnf(c_32586,plain,
    ( k2_pre_topc(sK1,k2_pre_topc(sK1,k1_tarski(sK2))) = k2_pre_topc(sK1,k1_tarski(sK2))
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3852,c_32350])).

cnf(c_33,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_36,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_33006,plain,
    ( k2_pre_topc(sK1,k2_pre_topc(sK1,k1_tarski(sK2))) = k2_pre_topc(sK1,k1_tarski(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_32586,c_36,c_38])).

cnf(c_23,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_xboole_0(X0,X2)
    | r1_xboole_0(X0,k2_pre_topc(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1447,plain,
    ( v3_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_xboole_0(X0,X2) != iProver_top
    | r1_xboole_0(X0,k2_pre_topc(X1,X2)) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_4522,plain,
    ( v3_pre_topc(k2_pre_topc(X0,X1),X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | r1_xboole_0(k2_pre_topc(X0,X1),X2) != iProver_top
    | r1_xboole_0(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1465,c_1447])).

cnf(c_11,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1459,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_11253,plain,
    ( v3_pre_topc(k2_pre_topc(X0,X1),X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | r1_xboole_0(k2_pre_topc(X0,X1),X2) != iProver_top
    | r1_xboole_0(k2_pre_topc(X0,X2),k2_pre_topc(X0,X1)) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4522,c_1459])).

cnf(c_69776,plain,
    ( v3_pre_topc(k2_pre_topc(sK1,k2_pre_topc(sK1,k1_tarski(sK2))),sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK1,k1_tarski(sK2)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_xboole_0(k2_pre_topc(sK1,X0),k2_pre_topc(sK1,k1_tarski(sK2))) = iProver_top
    | r1_xboole_0(k2_pre_topc(sK1,k2_pre_topc(sK1,k1_tarski(sK2))),X0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_33006,c_11253])).

cnf(c_69800,plain,
    ( v3_pre_topc(k2_pre_topc(sK1,k1_tarski(sK2)),sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK1,k1_tarski(sK2)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_xboole_0(k2_pre_topc(sK1,X0),k2_pre_topc(sK1,k1_tarski(sK2))) = iProver_top
    | r1_xboole_0(k2_pre_topc(sK1,k1_tarski(sK2)),X0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_69776,c_33006])).

cnf(c_32,negated_conjecture,
    ( v3_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_37,plain,
    ( v3_tdlat_3(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_2466,plain,
    ( ~ r2_hidden(X0,u1_struct_0(X1))
    | r1_tarski(k1_tarski(X0),u1_struct_0(X1)) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_4047,plain,
    ( ~ r2_hidden(sK2,u1_struct_0(sK1))
    | r1_tarski(k1_tarski(sK2),u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_2466])).

cnf(c_4048,plain,
    ( r2_hidden(sK2,u1_struct_0(sK1)) != iProver_top
    | r1_tarski(k1_tarski(sK2),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4047])).

cnf(c_1831,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,u1_struct_0(X1)) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_2464,plain,
    ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k1_tarski(X0),u1_struct_0(X1)) ),
    inference(instantiation,[status(thm)],[c_1831])).

cnf(c_4362,plain,
    ( m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(k1_tarski(sK2),u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_2464])).

cnf(c_4363,plain,
    ( m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | r1_tarski(k1_tarski(sK2),u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4362])).

cnf(c_5273,plain,
    ( v4_pre_topc(k2_pre_topc(sK1,k1_tarski(sK2)),sK1)
    | ~ m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_5274,plain,
    ( v4_pre_topc(k2_pre_topc(sK1,k1_tarski(sK2)),sK1) = iProver_top
    | m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5273])).

cnf(c_5278,plain,
    ( m1_subset_1(k2_pre_topc(sK1,k1_tarski(sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_5279,plain,
    ( m1_subset_1(k2_pre_topc(sK1,k1_tarski(sK2)),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5278])).

cnf(c_15,plain,
    ( v3_pre_topc(X0,X1)
    | ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_12477,plain,
    ( v3_pre_topc(k2_pre_topc(sK1,k1_tarski(sK2)),sK1)
    | ~ v4_pre_topc(k2_pre_topc(sK1,k1_tarski(sK2)),sK1)
    | ~ m1_subset_1(k2_pre_topc(sK1,k1_tarski(sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v3_tdlat_3(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_12483,plain,
    ( v3_pre_topc(k2_pre_topc(sK1,k1_tarski(sK2)),sK1) = iProver_top
    | v4_pre_topc(k2_pre_topc(sK1,k1_tarski(sK2)),sK1) != iProver_top
    | m1_subset_1(k2_pre_topc(sK1,k1_tarski(sK2)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v3_tdlat_3(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12477])).

cnf(c_71328,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_xboole_0(k2_pre_topc(sK1,X0),k2_pre_topc(sK1,k1_tarski(sK2))) = iProver_top
    | r1_xboole_0(k2_pre_topc(sK1,k1_tarski(sK2)),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_69800,c_35,c_36,c_37,c_38,c_39,c_87,c_94,c_1821,c_4048,c_4363,c_5274,c_5279,c_12483])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1442,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_3381,plain,
    ( r2_hidden(sK3,u1_struct_0(sK1)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1442,c_1453])).

cnf(c_40,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_1817,plain,
    ( r2_hidden(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1818,plain,
    ( r2_hidden(sK3,u1_struct_0(sK1)) = iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1817])).

cnf(c_3671,plain,
    ( r2_hidden(sK3,u1_struct_0(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3381,c_35,c_38,c_40,c_87,c_94,c_1818])).

cnf(c_32585,plain,
    ( k2_pre_topc(sK1,k2_pre_topc(sK1,k1_tarski(sK3))) = k2_pre_topc(sK1,k1_tarski(sK3))
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3671,c_32350])).

cnf(c_32835,plain,
    ( k2_pre_topc(sK1,k2_pre_topc(sK1,k1_tarski(sK3))) = k2_pre_topc(sK1,k1_tarski(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_32585,c_36,c_38])).

cnf(c_69775,plain,
    ( v3_pre_topc(k2_pre_topc(sK1,k2_pre_topc(sK1,k1_tarski(sK3))),sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK1,k1_tarski(sK3)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_xboole_0(k2_pre_topc(sK1,X0),k2_pre_topc(sK1,k1_tarski(sK3))) = iProver_top
    | r1_xboole_0(k2_pre_topc(sK1,k2_pre_topc(sK1,k1_tarski(sK3))),X0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_32835,c_11253])).

cnf(c_69815,plain,
    ( v3_pre_topc(k2_pre_topc(sK1,k1_tarski(sK3)),sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK1,k1_tarski(sK3)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_xboole_0(k2_pre_topc(sK1,X0),k2_pre_topc(sK1,k1_tarski(sK3))) = iProver_top
    | r1_xboole_0(k2_pre_topc(sK1,k1_tarski(sK3)),X0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_69775,c_32835])).

cnf(c_4044,plain,
    ( ~ r2_hidden(sK3,u1_struct_0(sK1))
    | r1_tarski(k1_tarski(sK3),u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_2466])).

cnf(c_4045,plain,
    ( r2_hidden(sK3,u1_struct_0(sK1)) != iProver_top
    | r1_tarski(k1_tarski(sK3),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4044])).

cnf(c_4358,plain,
    ( m1_subset_1(k1_tarski(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(k1_tarski(sK3),u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_2464])).

cnf(c_4359,plain,
    ( m1_subset_1(k1_tarski(sK3),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | r1_tarski(k1_tarski(sK3),u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4358])).

cnf(c_5206,plain,
    ( v4_pre_topc(k2_pre_topc(sK1,k1_tarski(sK3)),sK1)
    | ~ m1_subset_1(k1_tarski(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_5207,plain,
    ( v4_pre_topc(k2_pre_topc(sK1,k1_tarski(sK3)),sK1) = iProver_top
    | m1_subset_1(k1_tarski(sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5206])).

cnf(c_5211,plain,
    ( m1_subset_1(k2_pre_topc(sK1,k1_tarski(sK3)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(k1_tarski(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_5212,plain,
    ( m1_subset_1(k2_pre_topc(sK1,k1_tarski(sK3)),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m1_subset_1(k1_tarski(sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5211])).

cnf(c_12430,plain,
    ( v3_pre_topc(k2_pre_topc(sK1,k1_tarski(sK3)),sK1)
    | ~ v4_pre_topc(k2_pre_topc(sK1,k1_tarski(sK3)),sK1)
    | ~ m1_subset_1(k2_pre_topc(sK1,k1_tarski(sK3)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v3_tdlat_3(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_12436,plain,
    ( v3_pre_topc(k2_pre_topc(sK1,k1_tarski(sK3)),sK1) = iProver_top
    | v4_pre_topc(k2_pre_topc(sK1,k1_tarski(sK3)),sK1) != iProver_top
    | m1_subset_1(k2_pre_topc(sK1,k1_tarski(sK3)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v3_tdlat_3(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12430])).

cnf(c_71367,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_xboole_0(k2_pre_topc(sK1,X0),k2_pre_topc(sK1,k1_tarski(sK3))) = iProver_top
    | r1_xboole_0(k2_pre_topc(sK1,k1_tarski(sK3)),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_69815,c_35,c_36,c_37,c_38,c_40,c_87,c_94,c_1818,c_4045,c_4359,c_5207,c_5212,c_12436])).

cnf(c_4,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1466,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_71379,plain,
    ( k3_xboole_0(k2_pre_topc(sK1,X0),k2_pre_topc(sK1,k1_tarski(sK3))) = k1_xboole_0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_xboole_0(k2_pre_topc(sK1,k1_tarski(sK3)),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_71367,c_1466])).

cnf(c_73686,plain,
    ( k3_xboole_0(k2_pre_topc(sK1,k2_pre_topc(sK1,k1_tarski(sK2))),k2_pre_topc(sK1,k1_tarski(sK3))) = k1_xboole_0
    | m1_subset_1(k2_pre_topc(sK1,k1_tarski(sK2)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k1_tarski(sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_xboole_0(k2_pre_topc(sK1,k1_tarski(sK2)),k1_tarski(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_71328,c_71379])).

cnf(c_16,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1454,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_28396,plain,
    ( k3_xboole_0(k2_pre_topc(X0,X1),X2) = k2_pre_topc(X0,X1)
    | v4_pre_topc(X2,X0) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X2,u1_struct_0(X0)) != iProver_top
    | r1_tarski(X1,u1_struct_0(X0)) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8005,c_1454])).

cnf(c_38976,plain,
    ( k3_xboole_0(k2_pre_topc(X0,k1_tarski(X1)),X2) = k2_pre_topc(X0,k1_tarski(X1))
    | r2_hidden(X1,u1_struct_0(X0)) != iProver_top
    | v4_pre_topc(X2,X0) != iProver_top
    | r1_tarski(X2,u1_struct_0(X0)) != iProver_top
    | r1_tarski(k1_tarski(X1),X2) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1451,c_28396])).

cnf(c_44789,plain,
    ( k3_xboole_0(k2_pre_topc(sK1,k1_tarski(sK2)),X0) = k2_pre_topc(sK1,k1_tarski(sK2))
    | v4_pre_topc(X0,sK1) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK1)) != iProver_top
    | r1_tarski(k1_tarski(sK2),X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3852,c_38976])).

cnf(c_45175,plain,
    ( r1_tarski(k1_tarski(sK2),X0) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK1)) != iProver_top
    | v4_pre_topc(X0,sK1) != iProver_top
    | k3_xboole_0(k2_pre_topc(sK1,k1_tarski(sK2)),X0) = k2_pre_topc(sK1,k1_tarski(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_44789,c_38])).

cnf(c_45176,plain,
    ( k3_xboole_0(k2_pre_topc(sK1,k1_tarski(sK2)),X0) = k2_pre_topc(sK1,k1_tarski(sK2))
    | v4_pre_topc(X0,sK1) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK1)) != iProver_top
    | r1_tarski(k1_tarski(sK2),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_45175])).

cnf(c_45188,plain,
    ( k3_xboole_0(k2_pre_topc(sK1,k1_tarski(sK2)),k2_pre_topc(sK1,X0)) = k2_pre_topc(sK1,k1_tarski(sK2))
    | v4_pre_topc(k2_pre_topc(sK1,X0),sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(k1_tarski(sK2),k2_pre_topc(sK1,X0)) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4526,c_45176])).

cnf(c_47157,plain,
    ( r1_tarski(k1_tarski(sK2),k2_pre_topc(sK1,X0)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v4_pre_topc(k2_pre_topc(sK1,X0),sK1) != iProver_top
    | k3_xboole_0(k2_pre_topc(sK1,k1_tarski(sK2)),k2_pre_topc(sK1,X0)) = k2_pre_topc(sK1,k1_tarski(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_45188,c_38])).

cnf(c_47158,plain,
    ( k3_xboole_0(k2_pre_topc(sK1,k1_tarski(sK2)),k2_pre_topc(sK1,X0)) = k2_pre_topc(sK1,k1_tarski(sK2))
    | v4_pre_topc(k2_pre_topc(sK1,X0),sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(k1_tarski(sK2),k2_pre_topc(sK1,X0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_47157])).

cnf(c_47170,plain,
    ( k3_xboole_0(k2_pre_topc(sK1,k1_tarski(sK2)),k2_pre_topc(sK1,k2_pre_topc(sK1,k1_tarski(sK3)))) = k2_pre_topc(sK1,k1_tarski(sK2))
    | v4_pre_topc(k2_pre_topc(sK1,k2_pre_topc(sK1,k1_tarski(sK3))),sK1) != iProver_top
    | m1_subset_1(k2_pre_topc(sK1,k1_tarski(sK3)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(k1_tarski(sK2),k2_pre_topc(sK1,k1_tarski(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_32835,c_47158])).

cnf(c_47182,plain,
    ( k3_xboole_0(k2_pre_topc(sK1,k1_tarski(sK2)),k2_pre_topc(sK1,k1_tarski(sK3))) = k2_pre_topc(sK1,k1_tarski(sK2))
    | v4_pre_topc(k2_pre_topc(sK1,k1_tarski(sK3)),sK1) != iProver_top
    | m1_subset_1(k2_pre_topc(sK1,k1_tarski(sK3)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(k1_tarski(sK2),k2_pre_topc(sK1,k1_tarski(sK3))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_47170,c_32835])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1460,plain,
    ( k6_domain_1(X0,X1) = k1_tarski(X1)
    | m1_subset_1(X1,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3501,plain,
    ( k6_domain_1(u1_struct_0(sK1),sK3) = k1_tarski(sK3)
    | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1442,c_1460])).

cnf(c_86,plain,
    ( v2_struct_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ l1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_93,plain,
    ( l1_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1841,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK1))
    | k6_domain_1(u1_struct_0(sK1),sK3) = k1_tarski(sK3) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_3862,plain,
    ( k6_domain_1(u1_struct_0(sK1),sK3) = k1_tarski(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3501,c_34,c_31,c_29,c_86,c_93,c_1841])).

cnf(c_28,negated_conjecture,
    ( r2_hidden(sK2,k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3))) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1443,plain,
    ( r2_hidden(sK2,k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_3868,plain,
    ( r2_hidden(sK2,k2_pre_topc(sK1,k1_tarski(sK3))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3862,c_1443])).

cnf(c_4781,plain,
    ( ~ r2_hidden(sK2,X0)
    | r1_tarski(k1_tarski(sK2),X0) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_15669,plain,
    ( ~ r2_hidden(sK2,k2_pre_topc(X0,k1_tarski(sK3)))
    | r1_tarski(k1_tarski(sK2),k2_pre_topc(X0,k1_tarski(sK3))) ),
    inference(instantiation,[status(thm)],[c_4781])).

cnf(c_15674,plain,
    ( r2_hidden(sK2,k2_pre_topc(X0,k1_tarski(sK3))) != iProver_top
    | r1_tarski(k1_tarski(sK2),k2_pre_topc(X0,k1_tarski(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15669])).

cnf(c_15676,plain,
    ( r2_hidden(sK2,k2_pre_topc(sK1,k1_tarski(sK3))) != iProver_top
    | r1_tarski(k1_tarski(sK2),k2_pre_topc(sK1,k1_tarski(sK3))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_15674])).

cnf(c_47528,plain,
    ( k3_xboole_0(k2_pre_topc(sK1,k1_tarski(sK2)),k2_pre_topc(sK1,k1_tarski(sK3))) = k2_pre_topc(sK1,k1_tarski(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_47182,c_35,c_36,c_38,c_40,c_87,c_94,c_1818,c_3868,c_4045,c_4359,c_5207,c_5212,c_15676])).

cnf(c_73691,plain,
    ( k2_pre_topc(sK1,k1_tarski(sK2)) = k1_xboole_0
    | m1_subset_1(k2_pre_topc(sK1,k1_tarski(sK2)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k1_tarski(sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_xboole_0(k2_pre_topc(sK1,k1_tarski(sK2)),k1_tarski(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_73686,c_33006,c_47528])).

cnf(c_25,plain,
    ( r2_hidden(X0,X1)
    | r1_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1445,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r1_xboole_0(k1_tarski(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2316,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r1_xboole_0(X1,k1_tarski(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1445,c_1459])).

cnf(c_5789,plain,
    ( k3_xboole_0(X0,k1_tarski(X1)) = k1_xboole_0
    | r2_hidden(X1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2316,c_1466])).

cnf(c_4521,plain,
    ( v4_pre_topc(k2_pre_topc(X0,X1),X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | r1_tarski(X2,k2_pre_topc(X0,X1)) != iProver_top
    | r1_tarski(k2_pre_topc(X0,X2),k2_pre_topc(X0,X1)) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1465,c_1452])).

cnf(c_9539,plain,
    ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,X2)
    | v4_pre_topc(k2_pre_topc(X0,X2),X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | r1_tarski(X1,k2_pre_topc(X0,X2)) != iProver_top
    | r1_tarski(k2_pre_topc(X0,X2),k2_pre_topc(X0,X1)) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4521,c_1469])).

cnf(c_62179,plain,
    ( k2_pre_topc(sK1,k2_pre_topc(sK1,k1_tarski(sK2))) = k2_pre_topc(sK1,X0)
    | v4_pre_topc(k2_pre_topc(sK1,k2_pre_topc(sK1,k1_tarski(sK2))),sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK1,k1_tarski(sK2)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK1,k2_pre_topc(sK1,k1_tarski(sK2)))) != iProver_top
    | r1_tarski(k2_pre_topc(sK1,k1_tarski(sK2)),k2_pre_topc(sK1,X0)) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_33006,c_9539])).

cnf(c_62214,plain,
    ( k2_pre_topc(sK1,k2_pre_topc(sK1,k1_tarski(sK2))) = k2_pre_topc(sK1,X0)
    | v4_pre_topc(k2_pre_topc(sK1,k1_tarski(sK2)),sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK1,k1_tarski(sK2)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK1,k1_tarski(sK2))) != iProver_top
    | r1_tarski(k2_pre_topc(sK1,k1_tarski(sK2)),k2_pre_topc(sK1,X0)) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_62179,c_33006])).

cnf(c_62215,plain,
    ( k2_pre_topc(sK1,k1_tarski(sK2)) = k2_pre_topc(sK1,X0)
    | v4_pre_topc(k2_pre_topc(sK1,k1_tarski(sK2)),sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK1,k1_tarski(sK2)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK1,k1_tarski(sK2))) != iProver_top
    | r1_tarski(k2_pre_topc(sK1,k1_tarski(sK2)),k2_pre_topc(sK1,X0)) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_62214,c_33006])).

cnf(c_63271,plain,
    ( r1_tarski(k2_pre_topc(sK1,k1_tarski(sK2)),k2_pre_topc(sK1,X0)) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK1,k1_tarski(sK2))) != iProver_top
    | k2_pre_topc(sK1,k1_tarski(sK2)) = k2_pre_topc(sK1,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_62215,c_35,c_36,c_38,c_39,c_87,c_94,c_1821,c_4048,c_4363,c_5274,c_5279])).

cnf(c_63272,plain,
    ( k2_pre_topc(sK1,k1_tarski(sK2)) = k2_pre_topc(sK1,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK1,k1_tarski(sK2))) != iProver_top
    | r1_tarski(k2_pre_topc(sK1,k1_tarski(sK2)),k2_pre_topc(sK1,X0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_63271])).

cnf(c_63285,plain,
    ( k2_pre_topc(sK1,k1_tarski(sK2)) = k2_pre_topc(sK1,X0)
    | v4_pre_topc(k2_pre_topc(sK1,X0),sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK1,k1_tarski(sK2))) != iProver_top
    | r1_tarski(k1_tarski(sK2),k2_pre_topc(sK1,X0)) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4521,c_63272])).

cnf(c_63847,plain,
    ( r1_tarski(k1_tarski(sK2),k2_pre_topc(sK1,X0)) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK1,k1_tarski(sK2))) != iProver_top
    | k2_pre_topc(sK1,k1_tarski(sK2)) = k2_pre_topc(sK1,X0)
    | v4_pre_topc(k2_pre_topc(sK1,X0),sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_63285,c_35,c_38,c_39,c_87,c_94,c_1821,c_4048,c_4363])).

cnf(c_63848,plain,
    ( k2_pre_topc(sK1,k1_tarski(sK2)) = k2_pre_topc(sK1,X0)
    | v4_pre_topc(k2_pre_topc(sK1,X0),sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK1,k1_tarski(sK2))) != iProver_top
    | r1_tarski(k1_tarski(sK2),k2_pre_topc(sK1,X0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_63847])).

cnf(c_63859,plain,
    ( k2_pre_topc(sK1,k2_pre_topc(X0,X1)) = k2_pre_topc(sK1,k1_tarski(sK2))
    | v4_pre_topc(k2_pre_topc(sK1,k2_pre_topc(X0,X1)),sK1) != iProver_top
    | v4_pre_topc(k2_pre_topc(sK1,k1_tarski(sK2)),X0) != iProver_top
    | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(X1,k2_pre_topc(sK1,k1_tarski(sK2))) != iProver_top
    | r1_tarski(X1,u1_struct_0(X0)) != iProver_top
    | r1_tarski(k2_pre_topc(sK1,k1_tarski(sK2)),u1_struct_0(X0)) != iProver_top
    | r1_tarski(k1_tarski(sK2),k2_pre_topc(sK1,k2_pre_topc(X0,X1))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8005,c_63848])).

cnf(c_68239,plain,
    ( k2_pre_topc(sK1,k2_pre_topc(sK1,k1_tarski(sK3))) = k2_pre_topc(sK1,k1_tarski(sK2))
    | v4_pre_topc(k2_pre_topc(sK1,k2_pre_topc(sK1,k1_tarski(sK3))),sK1) != iProver_top
    | v4_pre_topc(k2_pre_topc(sK1,k1_tarski(sK2)),sK1) != iProver_top
    | m1_subset_1(k2_pre_topc(sK1,k1_tarski(sK3)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(k2_pre_topc(sK1,k1_tarski(sK2)),u1_struct_0(sK1)) != iProver_top
    | r1_tarski(k1_tarski(sK3),k2_pre_topc(sK1,k1_tarski(sK2))) != iProver_top
    | r1_tarski(k1_tarski(sK3),u1_struct_0(sK1)) != iProver_top
    | r1_tarski(k1_tarski(sK2),k2_pre_topc(sK1,k1_tarski(sK3))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_32835,c_63859])).

cnf(c_68291,plain,
    ( k2_pre_topc(sK1,k2_pre_topc(sK1,k1_tarski(sK3))) = k2_pre_topc(sK1,k1_tarski(sK2))
    | v4_pre_topc(k2_pre_topc(sK1,k1_tarski(sK3)),sK1) != iProver_top
    | v4_pre_topc(k2_pre_topc(sK1,k1_tarski(sK2)),sK1) != iProver_top
    | m1_subset_1(k2_pre_topc(sK1,k1_tarski(sK3)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(k2_pre_topc(sK1,k1_tarski(sK2)),u1_struct_0(sK1)) != iProver_top
    | r1_tarski(k1_tarski(sK3),k2_pre_topc(sK1,k1_tarski(sK2))) != iProver_top
    | r1_tarski(k1_tarski(sK3),u1_struct_0(sK1)) != iProver_top
    | r1_tarski(k1_tarski(sK2),k2_pre_topc(sK1,k1_tarski(sK3))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_68239,c_32835])).

cnf(c_68292,plain,
    ( k2_pre_topc(sK1,k1_tarski(sK3)) = k2_pre_topc(sK1,k1_tarski(sK2))
    | v4_pre_topc(k2_pre_topc(sK1,k1_tarski(sK3)),sK1) != iProver_top
    | v4_pre_topc(k2_pre_topc(sK1,k1_tarski(sK2)),sK1) != iProver_top
    | m1_subset_1(k2_pre_topc(sK1,k1_tarski(sK3)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(k2_pre_topc(sK1,k1_tarski(sK2)),u1_struct_0(sK1)) != iProver_top
    | r1_tarski(k1_tarski(sK3),k2_pre_topc(sK1,k1_tarski(sK2))) != iProver_top
    | r1_tarski(k1_tarski(sK3),u1_struct_0(sK1)) != iProver_top
    | r1_tarski(k1_tarski(sK2),k2_pre_topc(sK1,k1_tarski(sK3))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_68291,c_32835])).

cnf(c_3502,plain,
    ( k6_domain_1(u1_struct_0(sK1),sK2) = k1_tarski(sK2)
    | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1441,c_1460])).

cnf(c_1844,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK1))
    | k6_domain_1(u1_struct_0(sK1),sK2) = k1_tarski(sK2) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_4108,plain,
    ( k6_domain_1(u1_struct_0(sK1),sK2) = k1_tarski(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3502,c_34,c_31,c_30,c_86,c_93,c_1844])).

cnf(c_27,negated_conjecture,
    ( k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_3869,plain,
    ( k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)) != k2_pre_topc(sK1,k1_tarski(sK3)) ),
    inference(demodulation,[status(thm)],[c_3862,c_27])).

cnf(c_4111,plain,
    ( k2_pre_topc(sK1,k1_tarski(sK3)) != k2_pre_topc(sK1,k1_tarski(sK2)) ),
    inference(demodulation,[status(thm)],[c_4108,c_3869])).

cnf(c_2449,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,u1_struct_0(X1)) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_12456,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK1,k1_tarski(sK3)),k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(k2_pre_topc(sK1,k1_tarski(sK3)),u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_2449])).

cnf(c_12463,plain,
    ( m1_subset_1(k2_pre_topc(sK1,k1_tarski(sK3)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(k2_pre_topc(sK1,k1_tarski(sK3)),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12456])).

cnf(c_12621,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK1,k1_tarski(sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(k2_pre_topc(sK1,k1_tarski(sK2)),u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_2449])).

cnf(c_12628,plain,
    ( m1_subset_1(k2_pre_topc(sK1,k1_tarski(sK2)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(k2_pre_topc(sK1,k1_tarski(sK2)),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12621])).

cnf(c_12476,plain,
    ( ~ v4_pre_topc(k2_pre_topc(sK1,k1_tarski(sK2)),sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(k2_pre_topc(sK1,k1_tarski(sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X0,k2_pre_topc(sK1,k1_tarski(sK2)))
    | r1_tarski(k2_pre_topc(sK1,X0),k2_pre_topc(sK1,k1_tarski(sK2)))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_46492,plain,
    ( ~ v4_pre_topc(k2_pre_topc(sK1,k1_tarski(sK2)),sK1)
    | ~ m1_subset_1(k2_pre_topc(sK1,k1_tarski(sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(k1_tarski(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(k2_pre_topc(sK1,k1_tarski(sK3)),k2_pre_topc(sK1,k1_tarski(sK2)))
    | ~ r1_tarski(k1_tarski(sK3),k2_pre_topc(sK1,k1_tarski(sK2)))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_12476])).

cnf(c_46495,plain,
    ( v4_pre_topc(k2_pre_topc(sK1,k1_tarski(sK2)),sK1) != iProver_top
    | m1_subset_1(k2_pre_topc(sK1,k1_tarski(sK2)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k1_tarski(sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(k2_pre_topc(sK1,k1_tarski(sK3)),k2_pre_topc(sK1,k1_tarski(sK2))) = iProver_top
    | r1_tarski(k1_tarski(sK3),k2_pre_topc(sK1,k1_tarski(sK2))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46492])).

cnf(c_68242,plain,
    ( k2_pre_topc(sK1,k2_pre_topc(sK1,k2_pre_topc(sK1,k1_tarski(sK3)))) = k2_pre_topc(sK1,k1_tarski(sK2))
    | v4_pre_topc(k2_pre_topc(sK1,k2_pre_topc(sK1,k2_pre_topc(sK1,k1_tarski(sK3)))),sK1) != iProver_top
    | v4_pre_topc(k2_pre_topc(sK1,k1_tarski(sK2)),sK1) != iProver_top
    | m1_subset_1(k2_pre_topc(sK1,k2_pre_topc(sK1,k1_tarski(sK3))),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(k2_pre_topc(sK1,k1_tarski(sK3)),k2_pre_topc(sK1,k1_tarski(sK2))) != iProver_top
    | r1_tarski(k2_pre_topc(sK1,k1_tarski(sK3)),u1_struct_0(sK1)) != iProver_top
    | r1_tarski(k2_pre_topc(sK1,k1_tarski(sK2)),u1_struct_0(sK1)) != iProver_top
    | r1_tarski(k1_tarski(sK2),k2_pre_topc(sK1,k2_pre_topc(sK1,k1_tarski(sK3)))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_32835,c_63859])).

cnf(c_68262,plain,
    ( k2_pre_topc(sK1,k1_tarski(sK3)) = k2_pre_topc(sK1,k1_tarski(sK2))
    | v4_pre_topc(k2_pre_topc(sK1,k1_tarski(sK3)),sK1) != iProver_top
    | v4_pre_topc(k2_pre_topc(sK1,k1_tarski(sK2)),sK1) != iProver_top
    | m1_subset_1(k2_pre_topc(sK1,k1_tarski(sK3)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(k2_pre_topc(sK1,k1_tarski(sK3)),k2_pre_topc(sK1,k1_tarski(sK2))) != iProver_top
    | r1_tarski(k2_pre_topc(sK1,k1_tarski(sK3)),u1_struct_0(sK1)) != iProver_top
    | r1_tarski(k2_pre_topc(sK1,k1_tarski(sK2)),u1_struct_0(sK1)) != iProver_top
    | r1_tarski(k1_tarski(sK2),k2_pre_topc(sK1,k1_tarski(sK3))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_68242,c_32835])).

cnf(c_68326,plain,
    ( r1_tarski(k1_tarski(sK3),k2_pre_topc(sK1,k1_tarski(sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_68292,c_35,c_36,c_38,c_39,c_40,c_87,c_94,c_1818,c_1821,c_3868,c_4045,c_4048,c_4111,c_4359,c_4363,c_5207,c_5212,c_5274,c_5279,c_12463,c_12628,c_15676,c_46495,c_68262])).

cnf(c_68331,plain,
    ( r2_hidden(sK3,k2_pre_topc(sK1,k1_tarski(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1451,c_68326])).

cnf(c_68866,plain,
    ( k3_xboole_0(k2_pre_topc(sK1,k1_tarski(sK2)),k1_tarski(sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5789,c_68331])).

cnf(c_3,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1467,plain,
    ( k3_xboole_0(X0,X1) != k1_xboole_0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_69378,plain,
    ( r1_xboole_0(k2_pre_topc(sK1,k1_tarski(sK2)),k1_tarski(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_68866,c_1467])).

cnf(c_74344,plain,
    ( k2_pre_topc(sK1,k1_tarski(sK2)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_73691,c_35,c_38,c_39,c_40,c_87,c_94,c_1818,c_1821,c_4045,c_4048,c_4359,c_4363,c_5279,c_69378])).

cnf(c_74834,plain,
    ( r1_tarski(k1_tarski(sK2),u1_struct_0(sK1)) != iProver_top
    | r1_tarski(k1_tarski(sK2),k1_xboole_0) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_74344,c_2624])).

cnf(c_26,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1769,plain,
    ( ~ r2_hidden(X0,k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_31234,plain,
    ( ~ r2_hidden(sK2,k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1769])).

cnf(c_31235,plain,
    ( r2_hidden(sK2,k1_xboole_0) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31234])).

cnf(c_20,plain,
    ( r2_hidden(X0,X1)
    | ~ r1_tarski(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_2251,plain,
    ( r2_hidden(X0,k1_xboole_0)
    | ~ r1_tarski(k1_tarski(X0),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_9709,plain,
    ( r2_hidden(sK2,k1_xboole_0)
    | ~ r1_tarski(k1_tarski(sK2),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2251])).

cnf(c_9712,plain,
    ( r2_hidden(sK2,k1_xboole_0) = iProver_top
    | r1_tarski(k1_tarski(sK2),k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9709])).

cnf(c_8,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_88,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_74834,c_31235,c_9712,c_4048,c_1821,c_94,c_88,c_87,c_39,c_38,c_35])).


%------------------------------------------------------------------------------
