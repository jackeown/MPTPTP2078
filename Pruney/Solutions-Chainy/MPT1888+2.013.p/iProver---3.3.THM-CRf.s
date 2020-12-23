%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:27:32 EST 2020

% Result     : Theorem 1.33s
% Output     : CNFRefutation 1.33s
% Verified   : 
% Statistics : Number of formulae       :  150 ( 927 expanded)
%              Number of clauses        :   85 ( 263 expanded)
%              Number of leaves         :   17 ( 259 expanded)
%              Depth                    :   21
%              Number of atoms          :  545 (4733 expanded)
%              Number of equality atoms :  105 ( 743 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
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

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X1,k2_pre_topc(X0,X2))
      | ~ v3_pre_topc(X1,X0)
      | ~ r1_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f13,conjecture,(
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

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))
          & ~ r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
        & ~ r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK3)))
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))
              & ~ r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK2)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))
            & ~ r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK2)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
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
              ( k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X1)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X2))
              & ~ r1_xboole_0(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X1)),k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X2)))
              & m1_subset_1(X2,u1_struct_0(sK1)) )
          & m1_subset_1(X1,u1_struct_0(sK1)) )
      & l1_pre_topc(sK1)
      & v3_tdlat_3(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3))
    & ~ r1_xboole_0(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)),k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3)))
    & m1_subset_1(sK3,u1_struct_0(sK1))
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l1_pre_topc(sK1)
    & v3_tdlat_3(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f35,f42,f41,f40])).

fof(f60,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f62,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f9,axiom,(
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
    inference(ennf_transformation,[],[f9])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

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

fof(f28,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f29,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_pre_topc(X1,X0)
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK0(X0),X0)
        & v4_pre_topc(sK0(X0),X0)
        & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f38])).

fof(f53,plain,(
    ! [X2,X0] :
      ( v3_pre_topc(X2,X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f61,plain,(
    v3_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f64,plain,(
    m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f43])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k2_tarski(X1,X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f51,f45])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f48,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f59,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f65,plain,(
    ~ r1_xboole_0(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)),k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3))) ),
    inference(cnf_transformation,[],[f43])).

fof(f63,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f43])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_tarski(X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f46,f45])).

fof(f12,axiom,(
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

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))
      | ~ r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f66,plain,(
    k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_12,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_xboole_0(X0,X2)
    | r1_xboole_0(X0,k2_pre_topc(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_20,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_459,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_xboole_0(X0,X2)
    | r1_xboole_0(X0,k2_pre_topc(X1,X2))
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_20])).

cnf(c_460,plain,
    ( ~ v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X0,k2_pre_topc(sK1,X1))
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_459])).

cnf(c_18,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_464,plain,
    ( r1_xboole_0(X0,k2_pre_topc(sK1,X1))
    | ~ r1_xboole_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v3_pre_topc(X0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_460,c_18])).

cnf(c_465,plain,
    ( ~ v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X0,k2_pre_topc(sK1,X1)) ),
    inference(renaming,[status(thm)],[c_464])).

cnf(c_7,plain,
    ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_11,plain,
    ( v3_pre_topc(X0,X1)
    | ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_425,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_tdlat_3(X1)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | X1 != X3
    | k2_pre_topc(X3,X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_11])).

cnf(c_426,plain,
    ( v3_pre_topc(k2_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v3_tdlat_3(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(unflattening,[status(thm)],[c_425])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_442,plain,
    ( v3_pre_topc(k2_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v3_tdlat_3(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_426,c_2])).

cnf(c_486,plain,
    ( v3_pre_topc(k2_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v3_tdlat_3(X0)
    | ~ l1_pre_topc(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_442,c_20])).

cnf(c_487,plain,
    ( v3_pre_topc(k2_pre_topc(sK1,X0),sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v3_tdlat_3(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_486])).

cnf(c_19,negated_conjecture,
    ( v3_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_491,plain,
    ( v3_pre_topc(k2_pre_topc(sK1,X0),sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_487,c_19,c_18])).

cnf(c_532,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_xboole_0(X1,X2)
    | r1_xboole_0(X1,k2_pre_topc(sK1,X2))
    | k2_pre_topc(sK1,X0) != X1
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_465,c_491])).

cnf(c_533,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(k2_pre_topc(sK1,X1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_xboole_0(k2_pre_topc(sK1,X1),X0)
    | r1_xboole_0(k2_pre_topc(sK1,X1),k2_pre_topc(sK1,X0)) ),
    inference(unflattening,[status(thm)],[c_532])).

cnf(c_517,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_18])).

cnf(c_518,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(k2_pre_topc(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_517])).

cnf(c_547,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_xboole_0(k2_pre_topc(sK1,X1),X0)
    | r1_xboole_0(k2_pre_topc(sK1,X1),k2_pre_topc(sK1,X0)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_533,c_518])).

cnf(c_627,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1_48,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_xboole_0(k2_pre_topc(sK1,X1_48),X0_48)
    | r1_xboole_0(k2_pre_topc(sK1,X1_48),k2_pre_topc(sK1,X0_48)) ),
    inference(subtyping,[status(esa)],[c_547])).

cnf(c_828,plain,
    ( m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X1_48,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_xboole_0(k2_pre_topc(sK1,X0_48),X1_48) != iProver_top
    | r1_xboole_0(k2_pre_topc(sK1,X0_48),k2_pre_topc(sK1,X1_48)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_627])).

cnf(c_0,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_636,plain,
    ( ~ r1_xboole_0(X0_48,X1_48)
    | r1_xboole_0(X1_48,X0_48) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_820,plain,
    ( r1_xboole_0(X0_48,X1_48) != iProver_top
    | r1_xboole_0(X1_48,X0_48) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_636])).

cnf(c_1432,plain,
    ( m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X1_48,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_xboole_0(k2_pre_topc(sK1,X1_48),X0_48) != iProver_top
    | r1_xboole_0(k2_pre_topc(sK1,X0_48),k2_pre_topc(sK1,X1_48)) = iProver_top ),
    inference(superposition,[status(thm)],[c_828,c_820])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_633,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_822,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_633])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_3,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_4,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_230,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_3,c_4])).

cnf(c_21,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_354,plain,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_pre_topc(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_230,c_21])).

cnf(c_355,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_354])).

cnf(c_51,plain,
    ( v2_struct_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ l1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_54,plain,
    ( l1_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_357,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_355,c_21,c_18,c_51,c_54])).

cnf(c_395,plain,
    ( ~ m1_subset_1(X0,X1)
    | k6_domain_1(X1,X0) = k2_tarski(X0,X0)
    | u1_struct_0(sK1) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_357])).

cnf(c_396,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | k6_domain_1(u1_struct_0(sK1),X0) = k2_tarski(X0,X0) ),
    inference(unflattening,[status(thm)],[c_395])).

cnf(c_630,plain,
    ( ~ m1_subset_1(X0_48,u1_struct_0(sK1))
    | k6_domain_1(u1_struct_0(sK1),X0_48) = k2_tarski(X0_48,X0_48) ),
    inference(subtyping,[status(esa)],[c_396])).

cnf(c_825,plain,
    ( k6_domain_1(u1_struct_0(sK1),X0_48) = k2_tarski(X0_48,X0_48)
    | m1_subset_1(X0_48,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_630])).

cnf(c_1011,plain,
    ( k6_domain_1(u1_struct_0(sK1),sK3) = k2_tarski(sK3,sK3) ),
    inference(superposition,[status(thm)],[c_822,c_825])).

cnf(c_15,negated_conjecture,
    ( ~ r1_xboole_0(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)),k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_634,negated_conjecture,
    ( ~ r1_xboole_0(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)),k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3))) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_821,plain,
    ( r1_xboole_0(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)),k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_634])).

cnf(c_1089,plain,
    ( r1_xboole_0(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)),k2_pre_topc(sK1,k2_tarski(sK3,sK3))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1011,c_821])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_632,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_823,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_632])).

cnf(c_1012,plain,
    ( k6_domain_1(u1_struct_0(sK1),sK2) = k2_tarski(sK2,sK2) ),
    inference(superposition,[status(thm)],[c_823,c_825])).

cnf(c_1222,plain,
    ( r1_xboole_0(k2_pre_topc(sK1,k2_tarski(sK2,sK2)),k2_pre_topc(sK1,k2_tarski(sK3,sK3))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1089,c_1012])).

cnf(c_1736,plain,
    ( m1_subset_1(k2_tarski(sK3,sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_xboole_0(k2_pre_topc(sK1,k2_tarski(sK3,sK3)),k2_tarski(sK2,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1432,c_1222])).

cnf(c_1,plain,
    ( r2_hidden(X0,X1)
    | r1_xboole_0(k2_tarski(X0,X0),X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X0)))
    | ~ v3_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X0)) = k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_330,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X0,k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2)))
    | ~ v3_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X0)) = k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_21])).

cnf(c_331,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ r2_hidden(X1,k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X0)))
    | ~ v3_tdlat_3(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X1)) = k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X0)) ),
    inference(unflattening,[status(thm)],[c_330])).

cnf(c_335,plain,
    ( ~ r2_hidden(X1,k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X0)))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X1)) = k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_331,c_20,c_19,c_18])).

cnf(c_336,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ r2_hidden(X1,k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X0)))
    | k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X1)) = k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X0)) ),
    inference(renaming,[status(thm)],[c_335])).

cnf(c_372,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | r1_xboole_0(k2_tarski(X2,X2),X3)
    | X0 != X2
    | k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X1)) != X3
    | k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X1)) = k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X0)) ),
    inference(resolution_lifted,[status(thm)],[c_1,c_336])).

cnf(c_373,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | r1_xboole_0(k2_tarski(X0,X0),k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X1)))
    | k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X1)) = k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X0)) ),
    inference(unflattening,[status(thm)],[c_372])).

cnf(c_631,plain,
    ( ~ m1_subset_1(X0_48,u1_struct_0(sK1))
    | ~ m1_subset_1(X1_48,u1_struct_0(sK1))
    | r1_xboole_0(k2_tarski(X0_48,X0_48),k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X1_48)))
    | k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X1_48)) = k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X0_48)) ),
    inference(subtyping,[status(esa)],[c_373])).

cnf(c_824,plain,
    ( k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X0_48)) = k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X1_48))
    | m1_subset_1(X0_48,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1_48,u1_struct_0(sK1)) != iProver_top
    | r1_xboole_0(k2_tarski(X1_48,X1_48),k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X0_48))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_631])).

cnf(c_1521,plain,
    ( k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X0_48)) = k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3))
    | m1_subset_1(X0_48,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top
    | r1_xboole_0(k2_tarski(X0_48,X0_48),k2_pre_topc(sK1,k2_tarski(sK3,sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1011,c_824])).

cnf(c_1535,plain,
    ( k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X0_48)) = k2_pre_topc(sK1,k2_tarski(sK3,sK3))
    | m1_subset_1(X0_48,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top
    | r1_xboole_0(k2_tarski(X0_48,X0_48),k2_pre_topc(sK1,k2_tarski(sK3,sK3))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1521,c_1011])).

cnf(c_27,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1557,plain,
    ( m1_subset_1(X0_48,u1_struct_0(sK1)) != iProver_top
    | k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X0_48)) = k2_pre_topc(sK1,k2_tarski(sK3,sK3))
    | r1_xboole_0(k2_tarski(X0_48,X0_48),k2_pre_topc(sK1,k2_tarski(sK3,sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1535,c_27])).

cnf(c_1558,plain,
    ( k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X0_48)) = k2_pre_topc(sK1,k2_tarski(sK3,sK3))
    | m1_subset_1(X0_48,u1_struct_0(sK1)) != iProver_top
    | r1_xboole_0(k2_tarski(X0_48,X0_48),k2_pre_topc(sK1,k2_tarski(sK3,sK3))) = iProver_top ),
    inference(renaming,[status(thm)],[c_1557])).

cnf(c_1566,plain,
    ( k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X0_48)) = k2_pre_topc(sK1,k2_tarski(sK3,sK3))
    | m1_subset_1(X0_48,u1_struct_0(sK1)) != iProver_top
    | r1_xboole_0(k2_pre_topc(sK1,k2_tarski(sK3,sK3)),k2_tarski(X0_48,X0_48)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1558,c_820])).

cnf(c_1568,plain,
    ( k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)) = k2_pre_topc(sK1,k2_tarski(sK3,sK3))
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | r1_xboole_0(k2_pre_topc(sK1,k2_tarski(sK3,sK3)),k2_tarski(sK2,sK2)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1566])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_407,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
    | u1_struct_0(sK1) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_357])).

cnf(c_408,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | m1_subset_1(k6_domain_1(u1_struct_0(sK1),X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_407])).

cnf(c_629,plain,
    ( ~ m1_subset_1(X0_48,u1_struct_0(sK1))
    | m1_subset_1(k6_domain_1(u1_struct_0(sK1),X0_48),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subtyping,[status(esa)],[c_408])).

cnf(c_826,plain,
    ( m1_subset_1(X0_48,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k6_domain_1(u1_struct_0(sK1),X0_48),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_629])).

cnf(c_1311,plain,
    ( m1_subset_1(k2_tarski(sK3,sK3),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1011,c_826])).

cnf(c_1310,plain,
    ( m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1012,c_826])).

cnf(c_14,negated_conjecture,
    ( k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_635,negated_conjecture,
    ( k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3)) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1090,plain,
    ( k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)) != k2_pre_topc(sK1,k2_tarski(sK3,sK3)) ),
    inference(demodulation,[status(thm)],[c_1011,c_635])).

cnf(c_26,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1736,c_1568,c_1311,c_1310,c_1090,c_27,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:51:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 1.33/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.33/1.00  
% 1.33/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.33/1.00  
% 1.33/1.00  ------  iProver source info
% 1.33/1.00  
% 1.33/1.00  git: date: 2020-06-30 10:37:57 +0100
% 1.33/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.33/1.00  git: non_committed_changes: false
% 1.33/1.00  git: last_make_outside_of_git: false
% 1.33/1.00  
% 1.33/1.00  ------ 
% 1.33/1.00  
% 1.33/1.00  ------ Input Options
% 1.33/1.00  
% 1.33/1.00  --out_options                           all
% 1.33/1.00  --tptp_safe_out                         true
% 1.33/1.00  --problem_path                          ""
% 1.33/1.00  --include_path                          ""
% 1.33/1.00  --clausifier                            res/vclausify_rel
% 1.33/1.00  --clausifier_options                    --mode clausify
% 1.33/1.00  --stdin                                 false
% 1.33/1.00  --stats_out                             all
% 1.33/1.00  
% 1.33/1.00  ------ General Options
% 1.33/1.00  
% 1.33/1.00  --fof                                   false
% 1.33/1.00  --time_out_real                         305.
% 1.33/1.00  --time_out_virtual                      -1.
% 1.33/1.00  --symbol_type_check                     false
% 1.33/1.00  --clausify_out                          false
% 1.33/1.00  --sig_cnt_out                           false
% 1.33/1.00  --trig_cnt_out                          false
% 1.33/1.00  --trig_cnt_out_tolerance                1.
% 1.33/1.00  --trig_cnt_out_sk_spl                   false
% 1.33/1.00  --abstr_cl_out                          false
% 1.33/1.00  
% 1.33/1.00  ------ Global Options
% 1.33/1.00  
% 1.33/1.00  --schedule                              default
% 1.33/1.00  --add_important_lit                     false
% 1.33/1.00  --prop_solver_per_cl                    1000
% 1.33/1.00  --min_unsat_core                        false
% 1.33/1.00  --soft_assumptions                      false
% 1.33/1.00  --soft_lemma_size                       3
% 1.33/1.00  --prop_impl_unit_size                   0
% 1.33/1.00  --prop_impl_unit                        []
% 1.33/1.00  --share_sel_clauses                     true
% 1.33/1.00  --reset_solvers                         false
% 1.33/1.00  --bc_imp_inh                            [conj_cone]
% 1.33/1.00  --conj_cone_tolerance                   3.
% 1.33/1.00  --extra_neg_conj                        none
% 1.33/1.00  --large_theory_mode                     true
% 1.33/1.00  --prolific_symb_bound                   200
% 1.33/1.00  --lt_threshold                          2000
% 1.33/1.00  --clause_weak_htbl                      true
% 1.33/1.00  --gc_record_bc_elim                     false
% 1.33/1.00  
% 1.33/1.00  ------ Preprocessing Options
% 1.33/1.00  
% 1.33/1.00  --preprocessing_flag                    true
% 1.33/1.00  --time_out_prep_mult                    0.1
% 1.33/1.00  --splitting_mode                        input
% 1.33/1.00  --splitting_grd                         true
% 1.33/1.00  --splitting_cvd                         false
% 1.33/1.00  --splitting_cvd_svl                     false
% 1.33/1.00  --splitting_nvd                         32
% 1.33/1.00  --sub_typing                            true
% 1.33/1.00  --prep_gs_sim                           true
% 1.33/1.00  --prep_unflatten                        true
% 1.33/1.00  --prep_res_sim                          true
% 1.33/1.00  --prep_upred                            true
% 1.33/1.00  --prep_sem_filter                       exhaustive
% 1.33/1.00  --prep_sem_filter_out                   false
% 1.33/1.00  --pred_elim                             true
% 1.33/1.00  --res_sim_input                         true
% 1.33/1.00  --eq_ax_congr_red                       true
% 1.33/1.00  --pure_diseq_elim                       true
% 1.33/1.00  --brand_transform                       false
% 1.33/1.00  --non_eq_to_eq                          false
% 1.33/1.00  --prep_def_merge                        true
% 1.33/1.00  --prep_def_merge_prop_impl              false
% 1.33/1.00  --prep_def_merge_mbd                    true
% 1.33/1.00  --prep_def_merge_tr_red                 false
% 1.33/1.00  --prep_def_merge_tr_cl                  false
% 1.33/1.00  --smt_preprocessing                     true
% 1.33/1.00  --smt_ac_axioms                         fast
% 1.33/1.00  --preprocessed_out                      false
% 1.33/1.00  --preprocessed_stats                    false
% 1.33/1.00  
% 1.33/1.00  ------ Abstraction refinement Options
% 1.33/1.00  
% 1.33/1.00  --abstr_ref                             []
% 1.33/1.00  --abstr_ref_prep                        false
% 1.33/1.00  --abstr_ref_until_sat                   false
% 1.33/1.00  --abstr_ref_sig_restrict                funpre
% 1.33/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.33/1.00  --abstr_ref_under                       []
% 1.33/1.00  
% 1.33/1.00  ------ SAT Options
% 1.33/1.00  
% 1.33/1.00  --sat_mode                              false
% 1.33/1.00  --sat_fm_restart_options                ""
% 1.33/1.00  --sat_gr_def                            false
% 1.33/1.00  --sat_epr_types                         true
% 1.33/1.00  --sat_non_cyclic_types                  false
% 1.33/1.00  --sat_finite_models                     false
% 1.33/1.00  --sat_fm_lemmas                         false
% 1.33/1.00  --sat_fm_prep                           false
% 1.33/1.00  --sat_fm_uc_incr                        true
% 1.33/1.00  --sat_out_model                         small
% 1.33/1.00  --sat_out_clauses                       false
% 1.33/1.00  
% 1.33/1.00  ------ QBF Options
% 1.33/1.00  
% 1.33/1.00  --qbf_mode                              false
% 1.33/1.00  --qbf_elim_univ                         false
% 1.33/1.00  --qbf_dom_inst                          none
% 1.33/1.00  --qbf_dom_pre_inst                      false
% 1.33/1.00  --qbf_sk_in                             false
% 1.33/1.00  --qbf_pred_elim                         true
% 1.33/1.00  --qbf_split                             512
% 1.33/1.00  
% 1.33/1.00  ------ BMC1 Options
% 1.33/1.00  
% 1.33/1.00  --bmc1_incremental                      false
% 1.33/1.00  --bmc1_axioms                           reachable_all
% 1.33/1.00  --bmc1_min_bound                        0
% 1.33/1.00  --bmc1_max_bound                        -1
% 1.33/1.00  --bmc1_max_bound_default                -1
% 1.33/1.00  --bmc1_symbol_reachability              true
% 1.33/1.00  --bmc1_property_lemmas                  false
% 1.33/1.00  --bmc1_k_induction                      false
% 1.33/1.00  --bmc1_non_equiv_states                 false
% 1.33/1.00  --bmc1_deadlock                         false
% 1.33/1.00  --bmc1_ucm                              false
% 1.33/1.00  --bmc1_add_unsat_core                   none
% 1.33/1.00  --bmc1_unsat_core_children              false
% 1.33/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.33/1.00  --bmc1_out_stat                         full
% 1.33/1.00  --bmc1_ground_init                      false
% 1.33/1.00  --bmc1_pre_inst_next_state              false
% 1.33/1.00  --bmc1_pre_inst_state                   false
% 1.33/1.00  --bmc1_pre_inst_reach_state             false
% 1.33/1.00  --bmc1_out_unsat_core                   false
% 1.33/1.00  --bmc1_aig_witness_out                  false
% 1.33/1.00  --bmc1_verbose                          false
% 1.33/1.00  --bmc1_dump_clauses_tptp                false
% 1.33/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.33/1.00  --bmc1_dump_file                        -
% 1.33/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.33/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.33/1.00  --bmc1_ucm_extend_mode                  1
% 1.33/1.00  --bmc1_ucm_init_mode                    2
% 1.33/1.00  --bmc1_ucm_cone_mode                    none
% 1.33/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.33/1.00  --bmc1_ucm_relax_model                  4
% 1.33/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.33/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.33/1.00  --bmc1_ucm_layered_model                none
% 1.33/1.00  --bmc1_ucm_max_lemma_size               10
% 1.33/1.00  
% 1.33/1.00  ------ AIG Options
% 1.33/1.00  
% 1.33/1.00  --aig_mode                              false
% 1.33/1.00  
% 1.33/1.00  ------ Instantiation Options
% 1.33/1.00  
% 1.33/1.00  --instantiation_flag                    true
% 1.33/1.00  --inst_sos_flag                         false
% 1.33/1.00  --inst_sos_phase                        true
% 1.33/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.33/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.33/1.00  --inst_lit_sel_side                     num_symb
% 1.33/1.00  --inst_solver_per_active                1400
% 1.33/1.00  --inst_solver_calls_frac                1.
% 1.33/1.00  --inst_passive_queue_type               priority_queues
% 1.33/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.33/1.00  --inst_passive_queues_freq              [25;2]
% 1.33/1.00  --inst_dismatching                      true
% 1.33/1.00  --inst_eager_unprocessed_to_passive     true
% 1.33/1.00  --inst_prop_sim_given                   true
% 1.33/1.00  --inst_prop_sim_new                     false
% 1.33/1.00  --inst_subs_new                         false
% 1.33/1.00  --inst_eq_res_simp                      false
% 1.33/1.00  --inst_subs_given                       false
% 1.33/1.00  --inst_orphan_elimination               true
% 1.33/1.00  --inst_learning_loop_flag               true
% 1.33/1.00  --inst_learning_start                   3000
% 1.33/1.00  --inst_learning_factor                  2
% 1.33/1.00  --inst_start_prop_sim_after_learn       3
% 1.33/1.00  --inst_sel_renew                        solver
% 1.33/1.00  --inst_lit_activity_flag                true
% 1.33/1.00  --inst_restr_to_given                   false
% 1.33/1.00  --inst_activity_threshold               500
% 1.33/1.00  --inst_out_proof                        true
% 1.33/1.00  
% 1.33/1.00  ------ Resolution Options
% 1.33/1.00  
% 1.33/1.00  --resolution_flag                       true
% 1.33/1.00  --res_lit_sel                           adaptive
% 1.33/1.00  --res_lit_sel_side                      none
% 1.33/1.00  --res_ordering                          kbo
% 1.33/1.00  --res_to_prop_solver                    active
% 1.33/1.00  --res_prop_simpl_new                    false
% 1.33/1.00  --res_prop_simpl_given                  true
% 1.33/1.00  --res_passive_queue_type                priority_queues
% 1.33/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.33/1.00  --res_passive_queues_freq               [15;5]
% 1.33/1.00  --res_forward_subs                      full
% 1.33/1.00  --res_backward_subs                     full
% 1.33/1.00  --res_forward_subs_resolution           true
% 1.33/1.00  --res_backward_subs_resolution          true
% 1.33/1.00  --res_orphan_elimination                true
% 1.33/1.00  --res_time_limit                        2.
% 1.33/1.00  --res_out_proof                         true
% 1.33/1.00  
% 1.33/1.00  ------ Superposition Options
% 1.33/1.00  
% 1.33/1.00  --superposition_flag                    true
% 1.33/1.00  --sup_passive_queue_type                priority_queues
% 1.33/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.33/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.33/1.00  --demod_completeness_check              fast
% 1.33/1.00  --demod_use_ground                      true
% 1.33/1.00  --sup_to_prop_solver                    passive
% 1.33/1.00  --sup_prop_simpl_new                    true
% 1.33/1.00  --sup_prop_simpl_given                  true
% 1.33/1.00  --sup_fun_splitting                     false
% 1.33/1.00  --sup_smt_interval                      50000
% 1.33/1.00  
% 1.33/1.00  ------ Superposition Simplification Setup
% 1.33/1.00  
% 1.33/1.00  --sup_indices_passive                   []
% 1.33/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.33/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.33/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.33/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.33/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.33/1.00  --sup_full_bw                           [BwDemod]
% 1.33/1.00  --sup_immed_triv                        [TrivRules]
% 1.33/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.33/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.33/1.00  --sup_immed_bw_main                     []
% 1.33/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.33/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.33/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.33/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.33/1.00  
% 1.33/1.00  ------ Combination Options
% 1.33/1.00  
% 1.33/1.00  --comb_res_mult                         3
% 1.33/1.00  --comb_sup_mult                         2
% 1.33/1.00  --comb_inst_mult                        10
% 1.33/1.00  
% 1.33/1.00  ------ Debug Options
% 1.33/1.00  
% 1.33/1.00  --dbg_backtrace                         false
% 1.33/1.00  --dbg_dump_prop_clauses                 false
% 1.33/1.00  --dbg_dump_prop_clauses_file            -
% 1.33/1.00  --dbg_out_stat                          false
% 1.33/1.00  ------ Parsing...
% 1.33/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.33/1.00  
% 1.33/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 9 0s  sf_e  pe_s  pe_e 
% 1.33/1.00  
% 1.33/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.33/1.00  
% 1.33/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.33/1.00  ------ Proving...
% 1.33/1.00  ------ Problem Properties 
% 1.33/1.00  
% 1.33/1.00  
% 1.33/1.00  clauses                                 10
% 1.33/1.00  conjectures                             4
% 1.33/1.00  EPR                                     1
% 1.33/1.00  Horn                                    9
% 1.33/1.00  unary                                   4
% 1.33/1.00  binary                                  4
% 1.33/1.00  lits                                    20
% 1.33/1.00  lits eq                                 3
% 1.33/1.00  fd_pure                                 0
% 1.33/1.00  fd_pseudo                               0
% 1.33/1.00  fd_cond                                 0
% 1.33/1.00  fd_pseudo_cond                          0
% 1.33/1.00  AC symbols                              0
% 1.33/1.00  
% 1.33/1.00  ------ Schedule dynamic 5 is on 
% 1.33/1.00  
% 1.33/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.33/1.00  
% 1.33/1.00  
% 1.33/1.00  ------ 
% 1.33/1.00  Current options:
% 1.33/1.00  ------ 
% 1.33/1.00  
% 1.33/1.00  ------ Input Options
% 1.33/1.00  
% 1.33/1.00  --out_options                           all
% 1.33/1.00  --tptp_safe_out                         true
% 1.33/1.00  --problem_path                          ""
% 1.33/1.00  --include_path                          ""
% 1.33/1.00  --clausifier                            res/vclausify_rel
% 1.33/1.00  --clausifier_options                    --mode clausify
% 1.33/1.00  --stdin                                 false
% 1.33/1.00  --stats_out                             all
% 1.33/1.00  
% 1.33/1.00  ------ General Options
% 1.33/1.00  
% 1.33/1.00  --fof                                   false
% 1.33/1.00  --time_out_real                         305.
% 1.33/1.00  --time_out_virtual                      -1.
% 1.33/1.00  --symbol_type_check                     false
% 1.33/1.00  --clausify_out                          false
% 1.33/1.00  --sig_cnt_out                           false
% 1.33/1.00  --trig_cnt_out                          false
% 1.33/1.00  --trig_cnt_out_tolerance                1.
% 1.33/1.00  --trig_cnt_out_sk_spl                   false
% 1.33/1.00  --abstr_cl_out                          false
% 1.33/1.00  
% 1.33/1.00  ------ Global Options
% 1.33/1.00  
% 1.33/1.00  --schedule                              default
% 1.33/1.00  --add_important_lit                     false
% 1.33/1.00  --prop_solver_per_cl                    1000
% 1.33/1.00  --min_unsat_core                        false
% 1.33/1.00  --soft_assumptions                      false
% 1.33/1.00  --soft_lemma_size                       3
% 1.33/1.00  --prop_impl_unit_size                   0
% 1.33/1.00  --prop_impl_unit                        []
% 1.33/1.00  --share_sel_clauses                     true
% 1.33/1.00  --reset_solvers                         false
% 1.33/1.00  --bc_imp_inh                            [conj_cone]
% 1.33/1.00  --conj_cone_tolerance                   3.
% 1.33/1.00  --extra_neg_conj                        none
% 1.33/1.00  --large_theory_mode                     true
% 1.33/1.00  --prolific_symb_bound                   200
% 1.33/1.00  --lt_threshold                          2000
% 1.33/1.00  --clause_weak_htbl                      true
% 1.33/1.00  --gc_record_bc_elim                     false
% 1.33/1.00  
% 1.33/1.00  ------ Preprocessing Options
% 1.33/1.00  
% 1.33/1.00  --preprocessing_flag                    true
% 1.33/1.00  --time_out_prep_mult                    0.1
% 1.33/1.00  --splitting_mode                        input
% 1.33/1.00  --splitting_grd                         true
% 1.33/1.00  --splitting_cvd                         false
% 1.33/1.00  --splitting_cvd_svl                     false
% 1.33/1.00  --splitting_nvd                         32
% 1.33/1.00  --sub_typing                            true
% 1.33/1.00  --prep_gs_sim                           true
% 1.33/1.00  --prep_unflatten                        true
% 1.33/1.00  --prep_res_sim                          true
% 1.33/1.00  --prep_upred                            true
% 1.33/1.00  --prep_sem_filter                       exhaustive
% 1.33/1.00  --prep_sem_filter_out                   false
% 1.33/1.00  --pred_elim                             true
% 1.33/1.00  --res_sim_input                         true
% 1.33/1.00  --eq_ax_congr_red                       true
% 1.33/1.00  --pure_diseq_elim                       true
% 1.33/1.00  --brand_transform                       false
% 1.33/1.00  --non_eq_to_eq                          false
% 1.33/1.00  --prep_def_merge                        true
% 1.33/1.00  --prep_def_merge_prop_impl              false
% 1.33/1.00  --prep_def_merge_mbd                    true
% 1.33/1.00  --prep_def_merge_tr_red                 false
% 1.33/1.00  --prep_def_merge_tr_cl                  false
% 1.33/1.00  --smt_preprocessing                     true
% 1.33/1.00  --smt_ac_axioms                         fast
% 1.33/1.00  --preprocessed_out                      false
% 1.33/1.00  --preprocessed_stats                    false
% 1.33/1.00  
% 1.33/1.00  ------ Abstraction refinement Options
% 1.33/1.00  
% 1.33/1.00  --abstr_ref                             []
% 1.33/1.00  --abstr_ref_prep                        false
% 1.33/1.00  --abstr_ref_until_sat                   false
% 1.33/1.00  --abstr_ref_sig_restrict                funpre
% 1.33/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.33/1.00  --abstr_ref_under                       []
% 1.33/1.00  
% 1.33/1.00  ------ SAT Options
% 1.33/1.00  
% 1.33/1.00  --sat_mode                              false
% 1.33/1.00  --sat_fm_restart_options                ""
% 1.33/1.00  --sat_gr_def                            false
% 1.33/1.00  --sat_epr_types                         true
% 1.33/1.00  --sat_non_cyclic_types                  false
% 1.33/1.00  --sat_finite_models                     false
% 1.33/1.00  --sat_fm_lemmas                         false
% 1.33/1.00  --sat_fm_prep                           false
% 1.33/1.00  --sat_fm_uc_incr                        true
% 1.33/1.00  --sat_out_model                         small
% 1.33/1.00  --sat_out_clauses                       false
% 1.33/1.00  
% 1.33/1.00  ------ QBF Options
% 1.33/1.00  
% 1.33/1.00  --qbf_mode                              false
% 1.33/1.00  --qbf_elim_univ                         false
% 1.33/1.00  --qbf_dom_inst                          none
% 1.33/1.00  --qbf_dom_pre_inst                      false
% 1.33/1.00  --qbf_sk_in                             false
% 1.33/1.00  --qbf_pred_elim                         true
% 1.33/1.00  --qbf_split                             512
% 1.33/1.00  
% 1.33/1.00  ------ BMC1 Options
% 1.33/1.00  
% 1.33/1.00  --bmc1_incremental                      false
% 1.33/1.00  --bmc1_axioms                           reachable_all
% 1.33/1.00  --bmc1_min_bound                        0
% 1.33/1.00  --bmc1_max_bound                        -1
% 1.33/1.00  --bmc1_max_bound_default                -1
% 1.33/1.00  --bmc1_symbol_reachability              true
% 1.33/1.00  --bmc1_property_lemmas                  false
% 1.33/1.00  --bmc1_k_induction                      false
% 1.33/1.00  --bmc1_non_equiv_states                 false
% 1.33/1.00  --bmc1_deadlock                         false
% 1.33/1.00  --bmc1_ucm                              false
% 1.33/1.00  --bmc1_add_unsat_core                   none
% 1.33/1.00  --bmc1_unsat_core_children              false
% 1.33/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.33/1.00  --bmc1_out_stat                         full
% 1.33/1.00  --bmc1_ground_init                      false
% 1.33/1.00  --bmc1_pre_inst_next_state              false
% 1.33/1.00  --bmc1_pre_inst_state                   false
% 1.33/1.00  --bmc1_pre_inst_reach_state             false
% 1.33/1.00  --bmc1_out_unsat_core                   false
% 1.33/1.00  --bmc1_aig_witness_out                  false
% 1.33/1.00  --bmc1_verbose                          false
% 1.33/1.00  --bmc1_dump_clauses_tptp                false
% 1.33/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.33/1.00  --bmc1_dump_file                        -
% 1.33/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.33/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.33/1.00  --bmc1_ucm_extend_mode                  1
% 1.33/1.00  --bmc1_ucm_init_mode                    2
% 1.33/1.00  --bmc1_ucm_cone_mode                    none
% 1.33/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.33/1.00  --bmc1_ucm_relax_model                  4
% 1.33/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.33/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.33/1.00  --bmc1_ucm_layered_model                none
% 1.33/1.00  --bmc1_ucm_max_lemma_size               10
% 1.33/1.00  
% 1.33/1.00  ------ AIG Options
% 1.33/1.00  
% 1.33/1.00  --aig_mode                              false
% 1.33/1.00  
% 1.33/1.00  ------ Instantiation Options
% 1.33/1.00  
% 1.33/1.00  --instantiation_flag                    true
% 1.33/1.00  --inst_sos_flag                         false
% 1.33/1.00  --inst_sos_phase                        true
% 1.33/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.33/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.33/1.00  --inst_lit_sel_side                     none
% 1.33/1.00  --inst_solver_per_active                1400
% 1.33/1.00  --inst_solver_calls_frac                1.
% 1.33/1.00  --inst_passive_queue_type               priority_queues
% 1.33/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.33/1.00  --inst_passive_queues_freq              [25;2]
% 1.33/1.00  --inst_dismatching                      true
% 1.33/1.00  --inst_eager_unprocessed_to_passive     true
% 1.33/1.00  --inst_prop_sim_given                   true
% 1.33/1.00  --inst_prop_sim_new                     false
% 1.33/1.00  --inst_subs_new                         false
% 1.33/1.00  --inst_eq_res_simp                      false
% 1.33/1.00  --inst_subs_given                       false
% 1.33/1.00  --inst_orphan_elimination               true
% 1.33/1.00  --inst_learning_loop_flag               true
% 1.33/1.00  --inst_learning_start                   3000
% 1.33/1.00  --inst_learning_factor                  2
% 1.33/1.00  --inst_start_prop_sim_after_learn       3
% 1.33/1.00  --inst_sel_renew                        solver
% 1.33/1.00  --inst_lit_activity_flag                true
% 1.33/1.00  --inst_restr_to_given                   false
% 1.33/1.00  --inst_activity_threshold               500
% 1.33/1.00  --inst_out_proof                        true
% 1.33/1.00  
% 1.33/1.00  ------ Resolution Options
% 1.33/1.00  
% 1.33/1.00  --resolution_flag                       false
% 1.33/1.00  --res_lit_sel                           adaptive
% 1.33/1.00  --res_lit_sel_side                      none
% 1.33/1.00  --res_ordering                          kbo
% 1.33/1.00  --res_to_prop_solver                    active
% 1.33/1.00  --res_prop_simpl_new                    false
% 1.33/1.00  --res_prop_simpl_given                  true
% 1.33/1.00  --res_passive_queue_type                priority_queues
% 1.33/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.33/1.00  --res_passive_queues_freq               [15;5]
% 1.33/1.00  --res_forward_subs                      full
% 1.33/1.00  --res_backward_subs                     full
% 1.33/1.00  --res_forward_subs_resolution           true
% 1.33/1.00  --res_backward_subs_resolution          true
% 1.33/1.00  --res_orphan_elimination                true
% 1.33/1.00  --res_time_limit                        2.
% 1.33/1.00  --res_out_proof                         true
% 1.33/1.00  
% 1.33/1.00  ------ Superposition Options
% 1.33/1.00  
% 1.33/1.00  --superposition_flag                    true
% 1.33/1.00  --sup_passive_queue_type                priority_queues
% 1.33/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.33/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.33/1.00  --demod_completeness_check              fast
% 1.33/1.00  --demod_use_ground                      true
% 1.33/1.00  --sup_to_prop_solver                    passive
% 1.33/1.00  --sup_prop_simpl_new                    true
% 1.33/1.00  --sup_prop_simpl_given                  true
% 1.33/1.00  --sup_fun_splitting                     false
% 1.33/1.00  --sup_smt_interval                      50000
% 1.33/1.00  
% 1.33/1.00  ------ Superposition Simplification Setup
% 1.33/1.00  
% 1.33/1.00  --sup_indices_passive                   []
% 1.33/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.33/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.33/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.33/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.33/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.33/1.00  --sup_full_bw                           [BwDemod]
% 1.33/1.00  --sup_immed_triv                        [TrivRules]
% 1.33/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.33/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.33/1.00  --sup_immed_bw_main                     []
% 1.33/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.33/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.33/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.33/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.33/1.00  
% 1.33/1.00  ------ Combination Options
% 1.33/1.00  
% 1.33/1.00  --comb_res_mult                         3
% 1.33/1.00  --comb_sup_mult                         2
% 1.33/1.00  --comb_inst_mult                        10
% 1.33/1.00  
% 1.33/1.00  ------ Debug Options
% 1.33/1.00  
% 1.33/1.00  --dbg_backtrace                         false
% 1.33/1.00  --dbg_dump_prop_clauses                 false
% 1.33/1.00  --dbg_dump_prop_clauses_file            -
% 1.33/1.00  --dbg_out_stat                          false
% 1.33/1.00  
% 1.33/1.00  
% 1.33/1.00  
% 1.33/1.00  
% 1.33/1.00  ------ Proving...
% 1.33/1.00  
% 1.33/1.00  
% 1.33/1.00  % SZS status Theorem for theBenchmark.p
% 1.33/1.00  
% 1.33/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 1.33/1.00  
% 1.33/1.00  fof(f11,axiom,(
% 1.33/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X1,X0) & r1_xboole_0(X1,X2)) => r1_xboole_0(X1,k2_pre_topc(X0,X2))))))),
% 1.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.33/1.00  
% 1.33/1.00  fof(f30,plain,(
% 1.33/1.00    ! [X0] : (! [X1] : (! [X2] : ((r1_xboole_0(X1,k2_pre_topc(X0,X2)) | (~v3_pre_topc(X1,X0) | ~r1_xboole_0(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.33/1.00    inference(ennf_transformation,[],[f11])).
% 1.33/1.00  
% 1.33/1.00  fof(f31,plain,(
% 1.33/1.00    ! [X0] : (! [X1] : (! [X2] : (r1_xboole_0(X1,k2_pre_topc(X0,X2)) | ~v3_pre_topc(X1,X0) | ~r1_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.33/1.00    inference(flattening,[],[f30])).
% 1.33/1.00  
% 1.33/1.00  fof(f57,plain,(
% 1.33/1.00    ( ! [X2,X0,X1] : (r1_xboole_0(X1,k2_pre_topc(X0,X2)) | ~v3_pre_topc(X1,X0) | ~r1_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.33/1.00    inference(cnf_transformation,[],[f31])).
% 1.33/1.00  
% 1.33/1.00  fof(f13,conjecture,(
% 1.33/1.00    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) | r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))))))),
% 1.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.33/1.00  
% 1.33/1.00  fof(f14,negated_conjecture,(
% 1.33/1.00    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) | r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))))))),
% 1.33/1.00    inference(negated_conjecture,[],[f13])).
% 1.33/1.00  
% 1.33/1.00  fof(f34,plain,(
% 1.33/1.00    ? [X0] : (? [X1] : (? [X2] : ((k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.33/1.00    inference(ennf_transformation,[],[f14])).
% 1.33/1.00  
% 1.33/1.00  fof(f35,plain,(
% 1.33/1.00    ? [X0] : (? [X1] : (? [X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.33/1.00    inference(flattening,[],[f34])).
% 1.33/1.00  
% 1.33/1.00  fof(f42,plain,(
% 1.33/1.00    ( ! [X0,X1] : (? [X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & m1_subset_1(X2,u1_struct_0(X0))) => (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK3))) & m1_subset_1(sK3,u1_struct_0(X0)))) )),
% 1.33/1.00    introduced(choice_axiom,[])).
% 1.33/1.00  
% 1.33/1.00  fof(f41,plain,(
% 1.33/1.00    ( ! [X0] : (? [X1] : (? [X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK2)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK2)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK2,u1_struct_0(X0)))) )),
% 1.33/1.00    introduced(choice_axiom,[])).
% 1.33/1.00  
% 1.33/1.00  fof(f40,plain,(
% 1.33/1.00    ? [X0] : (? [X1] : (? [X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X1)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X2)) & ~r1_xboole_0(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X1)),k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X2))) & m1_subset_1(X2,u1_struct_0(sK1))) & m1_subset_1(X1,u1_struct_0(sK1))) & l1_pre_topc(sK1) & v3_tdlat_3(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 1.33/1.00    introduced(choice_axiom,[])).
% 1.33/1.00  
% 1.33/1.00  fof(f43,plain,(
% 1.33/1.00    ((k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3)) & ~r1_xboole_0(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)),k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3))) & m1_subset_1(sK3,u1_struct_0(sK1))) & m1_subset_1(sK2,u1_struct_0(sK1))) & l1_pre_topc(sK1) & v3_tdlat_3(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 1.33/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f35,f42,f41,f40])).
% 1.33/1.00  
% 1.33/1.00  fof(f60,plain,(
% 1.33/1.00    v2_pre_topc(sK1)),
% 1.33/1.00    inference(cnf_transformation,[],[f43])).
% 1.33/1.00  
% 1.33/1.00  fof(f62,plain,(
% 1.33/1.00    l1_pre_topc(sK1)),
% 1.33/1.00    inference(cnf_transformation,[],[f43])).
% 1.33/1.00  
% 1.33/1.00  fof(f9,axiom,(
% 1.33/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_pre_topc(X0,X1),X0))),
% 1.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.33/1.00  
% 1.33/1.00  fof(f26,plain,(
% 1.33/1.00    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.33/1.00    inference(ennf_transformation,[],[f9])).
% 1.33/1.00  
% 1.33/1.00  fof(f27,plain,(
% 1.33/1.00    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.33/1.00    inference(flattening,[],[f26])).
% 1.33/1.00  
% 1.33/1.00  fof(f52,plain,(
% 1.33/1.00    ( ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.33/1.00    inference(cnf_transformation,[],[f27])).
% 1.33/1.00  
% 1.33/1.00  fof(f10,axiom,(
% 1.33/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v3_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => v3_pre_topc(X1,X0)))))),
% 1.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.33/1.00  
% 1.33/1.00  fof(f28,plain,(
% 1.33/1.00    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : ((v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.33/1.00    inference(ennf_transformation,[],[f10])).
% 1.33/1.00  
% 1.33/1.00  fof(f29,plain,(
% 1.33/1.00    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.33/1.00    inference(flattening,[],[f28])).
% 1.33/1.00  
% 1.33/1.00  fof(f36,plain,(
% 1.33/1.00    ! [X0] : (((v3_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X1] : (v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.33/1.00    inference(nnf_transformation,[],[f29])).
% 1.33/1.00  
% 1.33/1.00  fof(f37,plain,(
% 1.33/1.00    ! [X0] : (((v3_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.33/1.00    inference(rectify,[],[f36])).
% 1.33/1.00  
% 1.33/1.00  fof(f38,plain,(
% 1.33/1.00    ! [X0] : (? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK0(X0),X0) & v4_pre_topc(sK0(X0),X0) & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.33/1.00    introduced(choice_axiom,[])).
% 1.33/1.00  
% 1.33/1.00  fof(f39,plain,(
% 1.33/1.00    ! [X0] : (((v3_tdlat_3(X0) | (~v3_pre_topc(sK0(X0),X0) & v4_pre_topc(sK0(X0),X0) & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.33/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f38])).
% 1.33/1.00  
% 1.33/1.00  fof(f53,plain,(
% 1.33/1.00    ( ! [X2,X0] : (v3_pre_topc(X2,X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tdlat_3(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.33/1.00    inference(cnf_transformation,[],[f39])).
% 1.33/1.00  
% 1.33/1.00  fof(f4,axiom,(
% 1.33/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.33/1.00  
% 1.33/1.00  fof(f17,plain,(
% 1.33/1.00    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.33/1.00    inference(ennf_transformation,[],[f4])).
% 1.33/1.00  
% 1.33/1.00  fof(f18,plain,(
% 1.33/1.00    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.33/1.00    inference(flattening,[],[f17])).
% 1.33/1.00  
% 1.33/1.00  fof(f47,plain,(
% 1.33/1.00    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.33/1.00    inference(cnf_transformation,[],[f18])).
% 1.33/1.00  
% 1.33/1.00  fof(f61,plain,(
% 1.33/1.00    v3_tdlat_3(sK1)),
% 1.33/1.00    inference(cnf_transformation,[],[f43])).
% 1.33/1.00  
% 1.33/1.00  fof(f1,axiom,(
% 1.33/1.00    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.33/1.00  
% 1.33/1.00  fof(f15,plain,(
% 1.33/1.00    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.33/1.00    inference(ennf_transformation,[],[f1])).
% 1.33/1.00  
% 1.33/1.00  fof(f44,plain,(
% 1.33/1.00    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 1.33/1.00    inference(cnf_transformation,[],[f15])).
% 1.33/1.00  
% 1.33/1.00  fof(f64,plain,(
% 1.33/1.00    m1_subset_1(sK3,u1_struct_0(sK1))),
% 1.33/1.00    inference(cnf_transformation,[],[f43])).
% 1.33/1.00  
% 1.33/1.00  fof(f8,axiom,(
% 1.33/1.00    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 1.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.33/1.00  
% 1.33/1.00  fof(f24,plain,(
% 1.33/1.00    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.33/1.00    inference(ennf_transformation,[],[f8])).
% 1.33/1.00  
% 1.33/1.00  fof(f25,plain,(
% 1.33/1.00    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.33/1.00    inference(flattening,[],[f24])).
% 1.33/1.00  
% 1.33/1.00  fof(f51,plain,(
% 1.33/1.00    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.33/1.00    inference(cnf_transformation,[],[f25])).
% 1.33/1.00  
% 1.33/1.00  fof(f2,axiom,(
% 1.33/1.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.33/1.00  
% 1.33/1.00  fof(f45,plain,(
% 1.33/1.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.33/1.00    inference(cnf_transformation,[],[f2])).
% 1.33/1.00  
% 1.33/1.00  fof(f68,plain,(
% 1.33/1.00    ( ! [X0,X1] : (k2_tarski(X1,X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.33/1.00    inference(definition_unfolding,[],[f51,f45])).
% 1.33/1.00  
% 1.33/1.00  fof(f5,axiom,(
% 1.33/1.00    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.33/1.00  
% 1.33/1.00  fof(f19,plain,(
% 1.33/1.00    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.33/1.00    inference(ennf_transformation,[],[f5])).
% 1.33/1.00  
% 1.33/1.00  fof(f48,plain,(
% 1.33/1.00    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.33/1.00    inference(cnf_transformation,[],[f19])).
% 1.33/1.00  
% 1.33/1.00  fof(f6,axiom,(
% 1.33/1.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.33/1.00  
% 1.33/1.00  fof(f20,plain,(
% 1.33/1.00    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.33/1.00    inference(ennf_transformation,[],[f6])).
% 1.33/1.00  
% 1.33/1.00  fof(f21,plain,(
% 1.33/1.00    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.33/1.00    inference(flattening,[],[f20])).
% 1.33/1.00  
% 1.33/1.00  fof(f49,plain,(
% 1.33/1.00    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.33/1.00    inference(cnf_transformation,[],[f21])).
% 1.33/1.00  
% 1.33/1.00  fof(f59,plain,(
% 1.33/1.00    ~v2_struct_0(sK1)),
% 1.33/1.00    inference(cnf_transformation,[],[f43])).
% 1.33/1.00  
% 1.33/1.00  fof(f65,plain,(
% 1.33/1.00    ~r1_xboole_0(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)),k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3)))),
% 1.33/1.00    inference(cnf_transformation,[],[f43])).
% 1.33/1.00  
% 1.33/1.00  fof(f63,plain,(
% 1.33/1.00    m1_subset_1(sK2,u1_struct_0(sK1))),
% 1.33/1.00    inference(cnf_transformation,[],[f43])).
% 1.33/1.00  
% 1.33/1.00  fof(f3,axiom,(
% 1.33/1.00    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 1.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.33/1.00  
% 1.33/1.00  fof(f16,plain,(
% 1.33/1.00    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 1.33/1.00    inference(ennf_transformation,[],[f3])).
% 1.33/1.00  
% 1.33/1.00  fof(f46,plain,(
% 1.33/1.00    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 1.33/1.00    inference(cnf_transformation,[],[f16])).
% 1.33/1.00  
% 1.33/1.00  fof(f67,plain,(
% 1.33/1.00    ( ! [X0,X1] : (r1_xboole_0(k2_tarski(X0,X0),X1) | r2_hidden(X0,X1)) )),
% 1.33/1.00    inference(definition_unfolding,[],[f46,f45])).
% 1.33/1.00  
% 1.33/1.00  fof(f12,axiom,(
% 1.33/1.00    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) => k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))))))),
% 1.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.33/1.00  
% 1.33/1.00  fof(f32,plain,(
% 1.33/1.00    ! [X0] : (! [X1] : (! [X2] : ((k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) | ~r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.33/1.00    inference(ennf_transformation,[],[f12])).
% 1.33/1.00  
% 1.33/1.00  fof(f33,plain,(
% 1.33/1.00    ! [X0] : (! [X1] : (! [X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) | ~r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.33/1.00    inference(flattening,[],[f32])).
% 1.33/1.00  
% 1.33/1.00  fof(f58,plain,(
% 1.33/1.00    ( ! [X2,X0,X1] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) | ~r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.33/1.00    inference(cnf_transformation,[],[f33])).
% 1.33/1.00  
% 1.33/1.00  fof(f7,axiom,(
% 1.33/1.00    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.33/1.00  
% 1.33/1.00  fof(f22,plain,(
% 1.33/1.00    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.33/1.00    inference(ennf_transformation,[],[f7])).
% 1.33/1.00  
% 1.33/1.00  fof(f23,plain,(
% 1.33/1.00    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.33/1.00    inference(flattening,[],[f22])).
% 1.33/1.00  
% 1.33/1.00  fof(f50,plain,(
% 1.33/1.00    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.33/1.00    inference(cnf_transformation,[],[f23])).
% 1.33/1.00  
% 1.33/1.00  fof(f66,plain,(
% 1.33/1.00    k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3))),
% 1.33/1.00    inference(cnf_transformation,[],[f43])).
% 1.33/1.00  
% 1.33/1.00  cnf(c_12,plain,
% 1.33/1.00      ( ~ v3_pre_topc(X0,X1)
% 1.33/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.33/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.33/1.00      | ~ r1_xboole_0(X0,X2)
% 1.33/1.00      | r1_xboole_0(X0,k2_pre_topc(X1,X2))
% 1.33/1.00      | ~ v2_pre_topc(X1)
% 1.33/1.00      | ~ l1_pre_topc(X1) ),
% 1.33/1.00      inference(cnf_transformation,[],[f57]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_20,negated_conjecture,
% 1.33/1.00      ( v2_pre_topc(sK1) ),
% 1.33/1.00      inference(cnf_transformation,[],[f60]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_459,plain,
% 1.33/1.00      ( ~ v3_pre_topc(X0,X1)
% 1.33/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.33/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.33/1.00      | ~ r1_xboole_0(X0,X2)
% 1.33/1.00      | r1_xboole_0(X0,k2_pre_topc(X1,X2))
% 1.33/1.00      | ~ l1_pre_topc(X1)
% 1.33/1.00      | sK1 != X1 ),
% 1.33/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_20]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_460,plain,
% 1.33/1.00      ( ~ v3_pre_topc(X0,sK1)
% 1.33/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.33/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.33/1.00      | ~ r1_xboole_0(X0,X1)
% 1.33/1.00      | r1_xboole_0(X0,k2_pre_topc(sK1,X1))
% 1.33/1.00      | ~ l1_pre_topc(sK1) ),
% 1.33/1.00      inference(unflattening,[status(thm)],[c_459]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_18,negated_conjecture,
% 1.33/1.00      ( l1_pre_topc(sK1) ),
% 1.33/1.00      inference(cnf_transformation,[],[f62]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_464,plain,
% 1.33/1.00      ( r1_xboole_0(X0,k2_pre_topc(sK1,X1))
% 1.33/1.00      | ~ r1_xboole_0(X0,X1)
% 1.33/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.33/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.33/1.00      | ~ v3_pre_topc(X0,sK1) ),
% 1.33/1.00      inference(global_propositional_subsumption,
% 1.33/1.00                [status(thm)],
% 1.33/1.00                [c_460,c_18]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_465,plain,
% 1.33/1.00      ( ~ v3_pre_topc(X0,sK1)
% 1.33/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.33/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.33/1.00      | ~ r1_xboole_0(X0,X1)
% 1.33/1.00      | r1_xboole_0(X0,k2_pre_topc(sK1,X1)) ),
% 1.33/1.00      inference(renaming,[status(thm)],[c_464]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_7,plain,
% 1.33/1.00      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
% 1.33/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 1.33/1.00      | ~ v2_pre_topc(X0)
% 1.33/1.00      | ~ l1_pre_topc(X0) ),
% 1.33/1.00      inference(cnf_transformation,[],[f52]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_11,plain,
% 1.33/1.00      ( v3_pre_topc(X0,X1)
% 1.33/1.00      | ~ v4_pre_topc(X0,X1)
% 1.33/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.33/1.00      | ~ v3_tdlat_3(X1)
% 1.33/1.00      | ~ v2_pre_topc(X1)
% 1.33/1.00      | ~ l1_pre_topc(X1) ),
% 1.33/1.00      inference(cnf_transformation,[],[f53]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_425,plain,
% 1.33/1.00      ( v3_pre_topc(X0,X1)
% 1.33/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 1.33/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.33/1.00      | ~ v3_tdlat_3(X1)
% 1.33/1.00      | ~ v2_pre_topc(X3)
% 1.33/1.00      | ~ v2_pre_topc(X1)
% 1.33/1.00      | ~ l1_pre_topc(X3)
% 1.33/1.00      | ~ l1_pre_topc(X1)
% 1.33/1.00      | X1 != X3
% 1.33/1.00      | k2_pre_topc(X3,X2) != X0 ),
% 1.33/1.00      inference(resolution_lifted,[status(thm)],[c_7,c_11]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_426,plain,
% 1.33/1.00      ( v3_pre_topc(k2_pre_topc(X0,X1),X0)
% 1.33/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 1.33/1.00      | ~ m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
% 1.33/1.00      | ~ v3_tdlat_3(X0)
% 1.33/1.00      | ~ v2_pre_topc(X0)
% 1.33/1.00      | ~ l1_pre_topc(X0) ),
% 1.33/1.00      inference(unflattening,[status(thm)],[c_425]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_2,plain,
% 1.33/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.33/1.00      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.33/1.00      | ~ l1_pre_topc(X1) ),
% 1.33/1.00      inference(cnf_transformation,[],[f47]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_442,plain,
% 1.33/1.00      ( v3_pre_topc(k2_pre_topc(X0,X1),X0)
% 1.33/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 1.33/1.00      | ~ v3_tdlat_3(X0)
% 1.33/1.00      | ~ v2_pre_topc(X0)
% 1.33/1.00      | ~ l1_pre_topc(X0) ),
% 1.33/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_426,c_2]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_486,plain,
% 1.33/1.00      ( v3_pre_topc(k2_pre_topc(X0,X1),X0)
% 1.33/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 1.33/1.00      | ~ v3_tdlat_3(X0)
% 1.33/1.00      | ~ l1_pre_topc(X0)
% 1.33/1.00      | sK1 != X0 ),
% 1.33/1.00      inference(resolution_lifted,[status(thm)],[c_442,c_20]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_487,plain,
% 1.33/1.00      ( v3_pre_topc(k2_pre_topc(sK1,X0),sK1)
% 1.33/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.33/1.00      | ~ v3_tdlat_3(sK1)
% 1.33/1.00      | ~ l1_pre_topc(sK1) ),
% 1.33/1.00      inference(unflattening,[status(thm)],[c_486]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_19,negated_conjecture,
% 1.33/1.00      ( v3_tdlat_3(sK1) ),
% 1.33/1.00      inference(cnf_transformation,[],[f61]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_491,plain,
% 1.33/1.00      ( v3_pre_topc(k2_pre_topc(sK1,X0),sK1)
% 1.33/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.33/1.00      inference(global_propositional_subsumption,
% 1.33/1.00                [status(thm)],
% 1.33/1.00                [c_487,c_19,c_18]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_532,plain,
% 1.33/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.33/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.33/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.33/1.00      | ~ r1_xboole_0(X1,X2)
% 1.33/1.00      | r1_xboole_0(X1,k2_pre_topc(sK1,X2))
% 1.33/1.00      | k2_pre_topc(sK1,X0) != X1
% 1.33/1.00      | sK1 != sK1 ),
% 1.33/1.00      inference(resolution_lifted,[status(thm)],[c_465,c_491]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_533,plain,
% 1.33/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.33/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.33/1.00      | ~ m1_subset_1(k2_pre_topc(sK1,X1),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.33/1.00      | ~ r1_xboole_0(k2_pre_topc(sK1,X1),X0)
% 1.33/1.00      | r1_xboole_0(k2_pre_topc(sK1,X1),k2_pre_topc(sK1,X0)) ),
% 1.33/1.00      inference(unflattening,[status(thm)],[c_532]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_517,plain,
% 1.33/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.33/1.00      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.33/1.00      | sK1 != X1 ),
% 1.33/1.00      inference(resolution_lifted,[status(thm)],[c_2,c_18]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_518,plain,
% 1.33/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.33/1.00      | m1_subset_1(k2_pre_topc(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.33/1.00      inference(unflattening,[status(thm)],[c_517]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_547,plain,
% 1.33/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.33/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.33/1.00      | ~ r1_xboole_0(k2_pre_topc(sK1,X1),X0)
% 1.33/1.00      | r1_xboole_0(k2_pre_topc(sK1,X1),k2_pre_topc(sK1,X0)) ),
% 1.33/1.00      inference(forward_subsumption_resolution,
% 1.33/1.00                [status(thm)],
% 1.33/1.00                [c_533,c_518]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_627,plain,
% 1.33/1.00      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.33/1.00      | ~ m1_subset_1(X1_48,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.33/1.00      | ~ r1_xboole_0(k2_pre_topc(sK1,X1_48),X0_48)
% 1.33/1.00      | r1_xboole_0(k2_pre_topc(sK1,X1_48),k2_pre_topc(sK1,X0_48)) ),
% 1.33/1.00      inference(subtyping,[status(esa)],[c_547]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_828,plain,
% 1.33/1.00      ( m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.33/1.00      | m1_subset_1(X1_48,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.33/1.00      | r1_xboole_0(k2_pre_topc(sK1,X0_48),X1_48) != iProver_top
% 1.33/1.00      | r1_xboole_0(k2_pre_topc(sK1,X0_48),k2_pre_topc(sK1,X1_48)) = iProver_top ),
% 1.33/1.00      inference(predicate_to_equality,[status(thm)],[c_627]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_0,plain,
% 1.33/1.00      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 1.33/1.00      inference(cnf_transformation,[],[f44]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_636,plain,
% 1.33/1.00      ( ~ r1_xboole_0(X0_48,X1_48) | r1_xboole_0(X1_48,X0_48) ),
% 1.33/1.00      inference(subtyping,[status(esa)],[c_0]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_820,plain,
% 1.33/1.00      ( r1_xboole_0(X0_48,X1_48) != iProver_top
% 1.33/1.00      | r1_xboole_0(X1_48,X0_48) = iProver_top ),
% 1.33/1.00      inference(predicate_to_equality,[status(thm)],[c_636]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_1432,plain,
% 1.33/1.00      ( m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.33/1.00      | m1_subset_1(X1_48,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.33/1.00      | r1_xboole_0(k2_pre_topc(sK1,X1_48),X0_48) != iProver_top
% 1.33/1.00      | r1_xboole_0(k2_pre_topc(sK1,X0_48),k2_pre_topc(sK1,X1_48)) = iProver_top ),
% 1.33/1.00      inference(superposition,[status(thm)],[c_828,c_820]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_16,negated_conjecture,
% 1.33/1.00      ( m1_subset_1(sK3,u1_struct_0(sK1)) ),
% 1.33/1.00      inference(cnf_transformation,[],[f64]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_633,negated_conjecture,
% 1.33/1.00      ( m1_subset_1(sK3,u1_struct_0(sK1)) ),
% 1.33/1.00      inference(subtyping,[status(esa)],[c_16]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_822,plain,
% 1.33/1.00      ( m1_subset_1(sK3,u1_struct_0(sK1)) = iProver_top ),
% 1.33/1.00      inference(predicate_to_equality,[status(thm)],[c_633]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_6,plain,
% 1.33/1.00      ( ~ m1_subset_1(X0,X1)
% 1.33/1.00      | v1_xboole_0(X1)
% 1.33/1.00      | k6_domain_1(X1,X0) = k2_tarski(X0,X0) ),
% 1.33/1.00      inference(cnf_transformation,[],[f68]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_3,plain,
% 1.33/1.00      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 1.33/1.00      inference(cnf_transformation,[],[f48]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_4,plain,
% 1.33/1.00      ( v2_struct_0(X0)
% 1.33/1.00      | ~ v1_xboole_0(u1_struct_0(X0))
% 1.33/1.00      | ~ l1_struct_0(X0) ),
% 1.33/1.00      inference(cnf_transformation,[],[f49]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_230,plain,
% 1.33/1.00      ( v2_struct_0(X0)
% 1.33/1.00      | ~ v1_xboole_0(u1_struct_0(X0))
% 1.33/1.00      | ~ l1_pre_topc(X0) ),
% 1.33/1.00      inference(resolution,[status(thm)],[c_3,c_4]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_21,negated_conjecture,
% 1.33/1.00      ( ~ v2_struct_0(sK1) ),
% 1.33/1.00      inference(cnf_transformation,[],[f59]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_354,plain,
% 1.33/1.00      ( ~ v1_xboole_0(u1_struct_0(X0)) | ~ l1_pre_topc(X0) | sK1 != X0 ),
% 1.33/1.00      inference(resolution_lifted,[status(thm)],[c_230,c_21]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_355,plain,
% 1.33/1.00      ( ~ v1_xboole_0(u1_struct_0(sK1)) | ~ l1_pre_topc(sK1) ),
% 1.33/1.00      inference(unflattening,[status(thm)],[c_354]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_51,plain,
% 1.33/1.00      ( v2_struct_0(sK1)
% 1.33/1.00      | ~ v1_xboole_0(u1_struct_0(sK1))
% 1.33/1.00      | ~ l1_struct_0(sK1) ),
% 1.33/1.00      inference(instantiation,[status(thm)],[c_4]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_54,plain,
% 1.33/1.00      ( l1_struct_0(sK1) | ~ l1_pre_topc(sK1) ),
% 1.33/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_357,plain,
% 1.33/1.00      ( ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 1.33/1.00      inference(global_propositional_subsumption,
% 1.33/1.00                [status(thm)],
% 1.33/1.00                [c_355,c_21,c_18,c_51,c_54]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_395,plain,
% 1.33/1.00      ( ~ m1_subset_1(X0,X1)
% 1.33/1.00      | k6_domain_1(X1,X0) = k2_tarski(X0,X0)
% 1.33/1.00      | u1_struct_0(sK1) != X1 ),
% 1.33/1.00      inference(resolution_lifted,[status(thm)],[c_6,c_357]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_396,plain,
% 1.33/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.33/1.00      | k6_domain_1(u1_struct_0(sK1),X0) = k2_tarski(X0,X0) ),
% 1.33/1.00      inference(unflattening,[status(thm)],[c_395]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_630,plain,
% 1.33/1.00      ( ~ m1_subset_1(X0_48,u1_struct_0(sK1))
% 1.33/1.00      | k6_domain_1(u1_struct_0(sK1),X0_48) = k2_tarski(X0_48,X0_48) ),
% 1.33/1.00      inference(subtyping,[status(esa)],[c_396]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_825,plain,
% 1.33/1.00      ( k6_domain_1(u1_struct_0(sK1),X0_48) = k2_tarski(X0_48,X0_48)
% 1.33/1.00      | m1_subset_1(X0_48,u1_struct_0(sK1)) != iProver_top ),
% 1.33/1.00      inference(predicate_to_equality,[status(thm)],[c_630]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_1011,plain,
% 1.33/1.00      ( k6_domain_1(u1_struct_0(sK1),sK3) = k2_tarski(sK3,sK3) ),
% 1.33/1.00      inference(superposition,[status(thm)],[c_822,c_825]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_15,negated_conjecture,
% 1.33/1.00      ( ~ r1_xboole_0(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)),k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3))) ),
% 1.33/1.00      inference(cnf_transformation,[],[f65]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_634,negated_conjecture,
% 1.33/1.00      ( ~ r1_xboole_0(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)),k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3))) ),
% 1.33/1.00      inference(subtyping,[status(esa)],[c_15]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_821,plain,
% 1.33/1.00      ( r1_xboole_0(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)),k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3))) != iProver_top ),
% 1.33/1.00      inference(predicate_to_equality,[status(thm)],[c_634]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_1089,plain,
% 1.33/1.00      ( r1_xboole_0(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)),k2_pre_topc(sK1,k2_tarski(sK3,sK3))) != iProver_top ),
% 1.33/1.00      inference(demodulation,[status(thm)],[c_1011,c_821]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_17,negated_conjecture,
% 1.33/1.00      ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 1.33/1.00      inference(cnf_transformation,[],[f63]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_632,negated_conjecture,
% 1.33/1.00      ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 1.33/1.00      inference(subtyping,[status(esa)],[c_17]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_823,plain,
% 1.33/1.00      ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
% 1.33/1.00      inference(predicate_to_equality,[status(thm)],[c_632]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_1012,plain,
% 1.33/1.00      ( k6_domain_1(u1_struct_0(sK1),sK2) = k2_tarski(sK2,sK2) ),
% 1.33/1.00      inference(superposition,[status(thm)],[c_823,c_825]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_1222,plain,
% 1.33/1.00      ( r1_xboole_0(k2_pre_topc(sK1,k2_tarski(sK2,sK2)),k2_pre_topc(sK1,k2_tarski(sK3,sK3))) != iProver_top ),
% 1.33/1.00      inference(light_normalisation,[status(thm)],[c_1089,c_1012]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_1736,plain,
% 1.33/1.00      ( m1_subset_1(k2_tarski(sK3,sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.33/1.00      | m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.33/1.00      | r1_xboole_0(k2_pre_topc(sK1,k2_tarski(sK3,sK3)),k2_tarski(sK2,sK2)) != iProver_top ),
% 1.33/1.00      inference(superposition,[status(thm)],[c_1432,c_1222]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_1,plain,
% 1.33/1.00      ( r2_hidden(X0,X1) | r1_xboole_0(k2_tarski(X0,X0),X1) ),
% 1.33/1.00      inference(cnf_transformation,[],[f67]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_13,plain,
% 1.33/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.33/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.33/1.00      | ~ r2_hidden(X2,k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X0)))
% 1.33/1.00      | ~ v3_tdlat_3(X1)
% 1.33/1.00      | ~ v2_pre_topc(X1)
% 1.33/1.00      | v2_struct_0(X1)
% 1.33/1.00      | ~ l1_pre_topc(X1)
% 1.33/1.00      | k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X0)) = k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2)) ),
% 1.33/1.00      inference(cnf_transformation,[],[f58]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_330,plain,
% 1.33/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.33/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.33/1.00      | ~ r2_hidden(X0,k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2)))
% 1.33/1.00      | ~ v3_tdlat_3(X1)
% 1.33/1.00      | ~ v2_pre_topc(X1)
% 1.33/1.00      | ~ l1_pre_topc(X1)
% 1.33/1.00      | k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X0)) = k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2))
% 1.33/1.00      | sK1 != X1 ),
% 1.33/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_21]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_331,plain,
% 1.33/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.33/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.33/1.00      | ~ r2_hidden(X1,k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X0)))
% 1.33/1.00      | ~ v3_tdlat_3(sK1)
% 1.33/1.00      | ~ v2_pre_topc(sK1)
% 1.33/1.00      | ~ l1_pre_topc(sK1)
% 1.33/1.00      | k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X1)) = k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X0)) ),
% 1.33/1.00      inference(unflattening,[status(thm)],[c_330]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_335,plain,
% 1.33/1.00      ( ~ r2_hidden(X1,k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X0)))
% 1.33/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.33/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.33/1.00      | k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X1)) = k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X0)) ),
% 1.33/1.00      inference(global_propositional_subsumption,
% 1.33/1.00                [status(thm)],
% 1.33/1.00                [c_331,c_20,c_19,c_18]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_336,plain,
% 1.33/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.33/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.33/1.00      | ~ r2_hidden(X1,k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X0)))
% 1.33/1.00      | k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X1)) = k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X0)) ),
% 1.33/1.00      inference(renaming,[status(thm)],[c_335]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_372,plain,
% 1.33/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.33/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.33/1.00      | r1_xboole_0(k2_tarski(X2,X2),X3)
% 1.33/1.00      | X0 != X2
% 1.33/1.00      | k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X1)) != X3
% 1.33/1.00      | k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X1)) = k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X0)) ),
% 1.33/1.00      inference(resolution_lifted,[status(thm)],[c_1,c_336]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_373,plain,
% 1.33/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.33/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.33/1.00      | r1_xboole_0(k2_tarski(X0,X0),k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X1)))
% 1.33/1.00      | k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X1)) = k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X0)) ),
% 1.33/1.00      inference(unflattening,[status(thm)],[c_372]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_631,plain,
% 1.33/1.00      ( ~ m1_subset_1(X0_48,u1_struct_0(sK1))
% 1.33/1.00      | ~ m1_subset_1(X1_48,u1_struct_0(sK1))
% 1.33/1.00      | r1_xboole_0(k2_tarski(X0_48,X0_48),k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X1_48)))
% 1.33/1.00      | k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X1_48)) = k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X0_48)) ),
% 1.33/1.00      inference(subtyping,[status(esa)],[c_373]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_824,plain,
% 1.33/1.00      ( k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X0_48)) = k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X1_48))
% 1.33/1.00      | m1_subset_1(X0_48,u1_struct_0(sK1)) != iProver_top
% 1.33/1.00      | m1_subset_1(X1_48,u1_struct_0(sK1)) != iProver_top
% 1.33/1.00      | r1_xboole_0(k2_tarski(X1_48,X1_48),k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X0_48))) = iProver_top ),
% 1.33/1.00      inference(predicate_to_equality,[status(thm)],[c_631]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_1521,plain,
% 1.33/1.00      ( k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X0_48)) = k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3))
% 1.33/1.00      | m1_subset_1(X0_48,u1_struct_0(sK1)) != iProver_top
% 1.33/1.00      | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top
% 1.33/1.00      | r1_xboole_0(k2_tarski(X0_48,X0_48),k2_pre_topc(sK1,k2_tarski(sK3,sK3))) = iProver_top ),
% 1.33/1.00      inference(superposition,[status(thm)],[c_1011,c_824]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_1535,plain,
% 1.33/1.00      ( k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X0_48)) = k2_pre_topc(sK1,k2_tarski(sK3,sK3))
% 1.33/1.00      | m1_subset_1(X0_48,u1_struct_0(sK1)) != iProver_top
% 1.33/1.00      | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top
% 1.33/1.00      | r1_xboole_0(k2_tarski(X0_48,X0_48),k2_pre_topc(sK1,k2_tarski(sK3,sK3))) = iProver_top ),
% 1.33/1.00      inference(light_normalisation,[status(thm)],[c_1521,c_1011]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_27,plain,
% 1.33/1.00      ( m1_subset_1(sK3,u1_struct_0(sK1)) = iProver_top ),
% 1.33/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_1557,plain,
% 1.33/1.00      ( m1_subset_1(X0_48,u1_struct_0(sK1)) != iProver_top
% 1.33/1.00      | k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X0_48)) = k2_pre_topc(sK1,k2_tarski(sK3,sK3))
% 1.33/1.00      | r1_xboole_0(k2_tarski(X0_48,X0_48),k2_pre_topc(sK1,k2_tarski(sK3,sK3))) = iProver_top ),
% 1.33/1.00      inference(global_propositional_subsumption,
% 1.33/1.00                [status(thm)],
% 1.33/1.00                [c_1535,c_27]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_1558,plain,
% 1.33/1.00      ( k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X0_48)) = k2_pre_topc(sK1,k2_tarski(sK3,sK3))
% 1.33/1.00      | m1_subset_1(X0_48,u1_struct_0(sK1)) != iProver_top
% 1.33/1.00      | r1_xboole_0(k2_tarski(X0_48,X0_48),k2_pre_topc(sK1,k2_tarski(sK3,sK3))) = iProver_top ),
% 1.33/1.00      inference(renaming,[status(thm)],[c_1557]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_1566,plain,
% 1.33/1.00      ( k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X0_48)) = k2_pre_topc(sK1,k2_tarski(sK3,sK3))
% 1.33/1.00      | m1_subset_1(X0_48,u1_struct_0(sK1)) != iProver_top
% 1.33/1.00      | r1_xboole_0(k2_pre_topc(sK1,k2_tarski(sK3,sK3)),k2_tarski(X0_48,X0_48)) = iProver_top ),
% 1.33/1.00      inference(superposition,[status(thm)],[c_1558,c_820]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_1568,plain,
% 1.33/1.00      ( k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)) = k2_pre_topc(sK1,k2_tarski(sK3,sK3))
% 1.33/1.00      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 1.33/1.00      | r1_xboole_0(k2_pre_topc(sK1,k2_tarski(sK3,sK3)),k2_tarski(sK2,sK2)) = iProver_top ),
% 1.33/1.00      inference(instantiation,[status(thm)],[c_1566]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_5,plain,
% 1.33/1.00      ( ~ m1_subset_1(X0,X1)
% 1.33/1.00      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
% 1.33/1.00      | v1_xboole_0(X1) ),
% 1.33/1.00      inference(cnf_transformation,[],[f50]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_407,plain,
% 1.33/1.00      ( ~ m1_subset_1(X0,X1)
% 1.33/1.00      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
% 1.33/1.00      | u1_struct_0(sK1) != X1 ),
% 1.33/1.00      inference(resolution_lifted,[status(thm)],[c_5,c_357]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_408,plain,
% 1.33/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.33/1.00      | m1_subset_1(k6_domain_1(u1_struct_0(sK1),X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.33/1.00      inference(unflattening,[status(thm)],[c_407]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_629,plain,
% 1.33/1.00      ( ~ m1_subset_1(X0_48,u1_struct_0(sK1))
% 1.33/1.00      | m1_subset_1(k6_domain_1(u1_struct_0(sK1),X0_48),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.33/1.00      inference(subtyping,[status(esa)],[c_408]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_826,plain,
% 1.33/1.00      ( m1_subset_1(X0_48,u1_struct_0(sK1)) != iProver_top
% 1.33/1.00      | m1_subset_1(k6_domain_1(u1_struct_0(sK1),X0_48),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 1.33/1.00      inference(predicate_to_equality,[status(thm)],[c_629]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_1311,plain,
% 1.33/1.00      ( m1_subset_1(k2_tarski(sK3,sK3),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 1.33/1.00      | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top ),
% 1.33/1.00      inference(superposition,[status(thm)],[c_1011,c_826]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_1310,plain,
% 1.33/1.00      ( m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 1.33/1.00      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top ),
% 1.33/1.00      inference(superposition,[status(thm)],[c_1012,c_826]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_14,negated_conjecture,
% 1.33/1.00      ( k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3)) ),
% 1.33/1.00      inference(cnf_transformation,[],[f66]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_635,negated_conjecture,
% 1.33/1.00      ( k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3)) ),
% 1.33/1.00      inference(subtyping,[status(esa)],[c_14]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_1090,plain,
% 1.33/1.00      ( k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)) != k2_pre_topc(sK1,k2_tarski(sK3,sK3)) ),
% 1.33/1.00      inference(demodulation,[status(thm)],[c_1011,c_635]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_26,plain,
% 1.33/1.00      ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
% 1.33/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(contradiction,plain,
% 1.33/1.00      ( $false ),
% 1.33/1.00      inference(minisat,
% 1.33/1.00                [status(thm)],
% 1.33/1.00                [c_1736,c_1568,c_1311,c_1310,c_1090,c_27,c_26]) ).
% 1.33/1.00  
% 1.33/1.00  
% 1.33/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 1.33/1.00  
% 1.33/1.00  ------                               Statistics
% 1.33/1.00  
% 1.33/1.00  ------ General
% 1.33/1.00  
% 1.33/1.00  abstr_ref_over_cycles:                  0
% 1.33/1.00  abstr_ref_under_cycles:                 0
% 1.33/1.00  gc_basic_clause_elim:                   0
% 1.33/1.00  forced_gc_time:                         0
% 1.33/1.00  parsing_time:                           0.038
% 1.33/1.00  unif_index_cands_time:                  0.
% 1.33/1.00  unif_index_add_time:                    0.
% 1.33/1.00  orderings_time:                         0.
% 1.33/1.00  out_proof_time:                         0.014
% 1.33/1.00  total_time:                             0.124
% 1.33/1.00  num_of_symbols:                         54
% 1.33/1.00  num_of_terms:                           1988
% 1.33/1.00  
% 1.33/1.00  ------ Preprocessing
% 1.33/1.00  
% 1.33/1.00  num_of_splits:                          0
% 1.33/1.00  num_of_split_atoms:                     0
% 1.33/1.00  num_of_reused_defs:                     0
% 1.33/1.00  num_eq_ax_congr_red:                    16
% 1.33/1.00  num_of_sem_filtered_clauses:            1
% 1.33/1.00  num_of_subtypes:                        3
% 1.33/1.00  monotx_restored_types:                  0
% 1.33/1.00  sat_num_of_epr_types:                   0
% 1.33/1.00  sat_num_of_non_cyclic_types:            0
% 1.33/1.00  sat_guarded_non_collapsed_types:        0
% 1.33/1.00  num_pure_diseq_elim:                    0
% 1.33/1.00  simp_replaced_by:                       0
% 1.33/1.00  res_preprocessed:                       65
% 1.33/1.00  prep_upred:                             0
% 1.33/1.00  prep_unflattend:                        20
% 1.33/1.00  smt_new_axioms:                         0
% 1.33/1.00  pred_elim_cands:                        2
% 1.33/1.00  pred_elim:                              9
% 1.33/1.00  pred_elim_cl:                           12
% 1.33/1.00  pred_elim_cycles:                       13
% 1.33/1.00  merged_defs:                            0
% 1.33/1.00  merged_defs_ncl:                        0
% 1.33/1.00  bin_hyper_res:                          0
% 1.33/1.00  prep_cycles:                            4
% 1.33/1.00  pred_elim_time:                         0.006
% 1.33/1.00  splitting_time:                         0.
% 1.33/1.00  sem_filter_time:                        0.
% 1.33/1.00  monotx_time:                            0.
% 1.33/1.00  subtype_inf_time:                       0.
% 1.33/1.00  
% 1.33/1.00  ------ Problem properties
% 1.33/1.00  
% 1.33/1.00  clauses:                                10
% 1.33/1.00  conjectures:                            4
% 1.33/1.00  epr:                                    1
% 1.33/1.00  horn:                                   9
% 1.33/1.00  ground:                                 4
% 1.33/1.00  unary:                                  4
% 1.33/1.00  binary:                                 4
% 1.33/1.00  lits:                                   20
% 1.33/1.00  lits_eq:                                3
% 1.45/1.00  fd_pure:                                0
% 1.45/1.00  fd_pseudo:                              0
% 1.45/1.00  fd_cond:                                0
% 1.45/1.00  fd_pseudo_cond:                         0
% 1.45/1.00  ac_symbols:                             0
% 1.45/1.00  
% 1.45/1.00  ------ Propositional Solver
% 1.45/1.00  
% 1.45/1.00  prop_solver_calls:                      28
% 1.45/1.00  prop_fast_solver_calls:                 433
% 1.45/1.00  smt_solver_calls:                       0
% 1.45/1.00  smt_fast_solver_calls:                  0
% 1.45/1.00  prop_num_of_clauses:                    615
% 1.45/1.00  prop_preprocess_simplified:             2252
% 1.45/1.00  prop_fo_subsumed:                       13
% 1.45/1.00  prop_solver_time:                       0.
% 1.45/1.00  smt_solver_time:                        0.
% 1.45/1.00  smt_fast_solver_time:                   0.
% 1.45/1.00  prop_fast_solver_time:                  0.
% 1.45/1.00  prop_unsat_core_time:                   0.
% 1.45/1.00  
% 1.45/1.00  ------ QBF
% 1.45/1.00  
% 1.45/1.00  qbf_q_res:                              0
% 1.45/1.00  qbf_num_tautologies:                    0
% 1.45/1.00  qbf_prep_cycles:                        0
% 1.45/1.00  
% 1.45/1.00  ------ BMC1
% 1.45/1.00  
% 1.45/1.00  bmc1_current_bound:                     -1
% 1.45/1.00  bmc1_last_solved_bound:                 -1
% 1.45/1.00  bmc1_unsat_core_size:                   -1
% 1.45/1.00  bmc1_unsat_core_parents_size:           -1
% 1.45/1.00  bmc1_merge_next_fun:                    0
% 1.45/1.00  bmc1_unsat_core_clauses_time:           0.
% 1.45/1.00  
% 1.45/1.00  ------ Instantiation
% 1.45/1.00  
% 1.45/1.00  inst_num_of_clauses:                    161
% 1.45/1.00  inst_num_in_passive:                    42
% 1.45/1.00  inst_num_in_active:                     103
% 1.45/1.00  inst_num_in_unprocessed:                16
% 1.45/1.00  inst_num_of_loops:                      110
% 1.45/1.00  inst_num_of_learning_restarts:          0
% 1.45/1.00  inst_num_moves_active_passive:          4
% 1.45/1.00  inst_lit_activity:                      0
% 1.45/1.00  inst_lit_activity_moves:                0
% 1.45/1.00  inst_num_tautologies:                   0
% 1.45/1.00  inst_num_prop_implied:                  0
% 1.45/1.00  inst_num_existing_simplified:           0
% 1.45/1.00  inst_num_eq_res_simplified:             0
% 1.45/1.00  inst_num_child_elim:                    0
% 1.45/1.00  inst_num_of_dismatching_blockings:      30
% 1.45/1.00  inst_num_of_non_proper_insts:           140
% 1.45/1.00  inst_num_of_duplicates:                 0
% 1.45/1.00  inst_inst_num_from_inst_to_res:         0
% 1.45/1.00  inst_dismatching_checking_time:         0.
% 1.45/1.00  
% 1.45/1.00  ------ Resolution
% 1.45/1.00  
% 1.45/1.00  res_num_of_clauses:                     0
% 1.45/1.00  res_num_in_passive:                     0
% 1.45/1.00  res_num_in_active:                      0
% 1.45/1.00  res_num_of_loops:                       69
% 1.45/1.00  res_forward_subset_subsumed:            27
% 1.45/1.00  res_backward_subset_subsumed:           0
% 1.45/1.00  res_forward_subsumed:                   0
% 1.45/1.00  res_backward_subsumed:                  0
% 1.45/1.00  res_forward_subsumption_resolution:     2
% 1.45/1.00  res_backward_subsumption_resolution:    0
% 1.45/1.00  res_clause_to_clause_subsumption:       60
% 1.45/1.00  res_orphan_elimination:                 0
% 1.45/1.00  res_tautology_del:                      26
% 1.45/1.00  res_num_eq_res_simplified:              0
% 1.45/1.00  res_num_sel_changes:                    0
% 1.45/1.00  res_moves_from_active_to_pass:          0
% 1.45/1.00  
% 1.45/1.00  ------ Superposition
% 1.45/1.00  
% 1.45/1.00  sup_time_total:                         0.
% 1.45/1.00  sup_time_generating:                    0.
% 1.45/1.00  sup_time_sim_full:                      0.
% 1.45/1.00  sup_time_sim_immed:                     0.
% 1.45/1.00  
% 1.45/1.00  sup_num_of_clauses:                     22
% 1.45/1.00  sup_num_in_active:                      18
% 1.45/1.00  sup_num_in_passive:                     4
% 1.45/1.00  sup_num_of_loops:                       20
% 1.45/1.00  sup_fw_superposition:                   6
% 1.45/1.00  sup_bw_superposition:                   7
% 1.45/1.00  sup_immediate_simplified:               2
% 1.45/1.00  sup_given_eliminated:                   0
% 1.45/1.00  comparisons_done:                       0
% 1.45/1.00  comparisons_avoided:                    0
% 1.45/1.00  
% 1.45/1.00  ------ Simplifications
% 1.45/1.00  
% 1.45/1.00  
% 1.45/1.00  sim_fw_subset_subsumed:                 0
% 1.45/1.00  sim_bw_subset_subsumed:                 0
% 1.45/1.00  sim_fw_subsumed:                        0
% 1.45/1.00  sim_bw_subsumed:                        0
% 1.45/1.00  sim_fw_subsumption_res:                 0
% 1.45/1.00  sim_bw_subsumption_res:                 0
% 1.45/1.00  sim_tautology_del:                      0
% 1.45/1.00  sim_eq_tautology_del:                   0
% 1.45/1.00  sim_eq_res_simp:                        0
% 1.45/1.00  sim_fw_demodulated:                     0
% 1.45/1.00  sim_bw_demodulated:                     3
% 1.45/1.00  sim_light_normalised:                   3
% 1.45/1.00  sim_joinable_taut:                      0
% 1.45/1.00  sim_joinable_simp:                      0
% 1.45/1.00  sim_ac_normalised:                      0
% 1.45/1.00  sim_smt_subsumption:                    0
% 1.45/1.00  
%------------------------------------------------------------------------------
