%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:27:32 EST 2020

% Result     : Theorem 2.44s
% Output     : CNFRefutation 2.44s
% Verified   : 
% Statistics : Number of formulae       :  160 (1148 expanded)
%              Number of clauses        :   91 ( 278 expanded)
%              Number of leaves         :   18 ( 339 expanded)
%              Depth                    :   26
%              Number of atoms          :  558 (6097 expanded)
%              Number of equality atoms :  127 (1055 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_tarski(X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f52,f51])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f17,conjecture,(
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

fof(f18,negated_conjecture,(
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
    inference(negated_conjecture,[],[f17])).

fof(f40,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))
          & ~ r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
        & ~ r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK3)))
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
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

fof(f46,plain,
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

fof(f49,plain,
    ( k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3))
    & ~ r1_xboole_0(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)),k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3)))
    & m1_subset_1(sK3,u1_struct_0(sK1))
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l1_pre_topc(sK1)
    & v3_tdlat_3(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f41,f48,f47,f46])).

fof(f74,plain,(
    m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f49])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k2_tarski(X1,X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f61,f51])).

fof(f69,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f72,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f11,axiom,(
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
    inference(ennf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f60,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f59,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f15,axiom,(
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

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X1,k2_pre_topc(X0,X2))
      | ~ v3_pre_topc(X1,X0)
      | ~ r1_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f70,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
             => v3_pre_topc(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f35,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f35])).

fof(f43,plain,(
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
    inference(rectify,[],[f42])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_pre_topc(X1,X0)
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK0(X0),X0)
        & v4_pre_topc(sK0(X0),X0)
        & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f43,f44])).

fof(f63,plain,(
    ! [X2,X0] :
      ( v3_pre_topc(X2,X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f71,plain,(
    v3_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f75,plain,(
    ~ r1_xboole_0(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)),k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3))) ),
    inference(cnf_transformation,[],[f49])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f78,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f55,f51])).

fof(f73,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f49])).

fof(f16,axiom,(
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

fof(f38,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))
      | ~ r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f76,plain,(
    k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1,plain,
    ( r2_hidden(X0,X1)
    | r1_xboole_0(k2_tarski(X0,X0),X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1201,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r1_xboole_0(k2_tarski(X0,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1202,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1685,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r1_xboole_0(X1,k2_tarski(X0,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1201,c_1202])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1194,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1196,plain,
    ( k6_domain_1(X0,X1) = k2_tarski(X1,X1)
    | m1_subset_1(X1,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1516,plain,
    ( k6_domain_1(u1_struct_0(sK1),sK3) = k2_tarski(sK3,sK3)
    | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1194,c_1196])).

cnf(c_25,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_22,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_9,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_52,plain,
    ( v2_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_8,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_55,plain,
    ( l1_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1357,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK1))
    | k6_domain_1(u1_struct_0(sK1),sK3) = k2_tarski(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1813,plain,
    ( k6_domain_1(u1_struct_0(sK1),sK3) = k2_tarski(sK3,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1516,c_25,c_22,c_20,c_52,c_55,c_1357])).

cnf(c_16,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_xboole_0(X0,X2)
    | r1_xboole_0(X0,k2_pre_topc(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_24,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_428,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_xboole_0(X0,X2)
    | r1_xboole_0(X0,k2_pre_topc(X1,X2))
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_24])).

cnf(c_429,plain,
    ( ~ v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X0,k2_pre_topc(sK1,X1))
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_428])).

cnf(c_433,plain,
    ( r1_xboole_0(X0,k2_pre_topc(sK1,X1))
    | ~ r1_xboole_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v3_pre_topc(X0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_429,c_22])).

cnf(c_434,plain,
    ( ~ v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X0,k2_pre_topc(sK1,X1)) ),
    inference(renaming,[status(thm)],[c_433])).

cnf(c_11,plain,
    ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_15,plain,
    ( v3_pre_topc(X0,X1)
    | ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_394,plain,
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
    inference(resolution_lifted,[status(thm)],[c_11,c_15])).

cnf(c_395,plain,
    ( v3_pre_topc(k2_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v3_tdlat_3(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(unflattening,[status(thm)],[c_394])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_411,plain,
    ( v3_pre_topc(k2_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v3_tdlat_3(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_395,c_7])).

cnf(c_455,plain,
    ( v3_pre_topc(k2_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v3_tdlat_3(X0)
    | ~ l1_pre_topc(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_411,c_24])).

cnf(c_456,plain,
    ( v3_pre_topc(k2_pre_topc(sK1,X0),sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v3_tdlat_3(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_455])).

cnf(c_23,negated_conjecture,
    ( v3_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_460,plain,
    ( v3_pre_topc(k2_pre_topc(sK1,X0),sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_456,c_23,c_22])).

cnf(c_501,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_xboole_0(X1,X2)
    | r1_xboole_0(X1,k2_pre_topc(sK1,X2))
    | k2_pre_topc(sK1,X0) != X1
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_434,c_460])).

cnf(c_502,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(k2_pre_topc(sK1,X1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_xboole_0(k2_pre_topc(sK1,X1),X0)
    | r1_xboole_0(k2_pre_topc(sK1,X1),k2_pre_topc(sK1,X0)) ),
    inference(unflattening,[status(thm)],[c_501])).

cnf(c_486,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_22])).

cnf(c_487,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(k2_pre_topc(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_486])).

cnf(c_516,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_xboole_0(k2_pre_topc(sK1,X1),X0)
    | r1_xboole_0(k2_pre_topc(sK1,X1),k2_pre_topc(sK1,X0)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_502,c_487])).

cnf(c_1189,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_xboole_0(k2_pre_topc(sK1,X0),X1) != iProver_top
    | r1_xboole_0(k2_pre_topc(sK1,X0),k2_pre_topc(sK1,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_516])).

cnf(c_19,negated_conjecture,
    ( ~ r1_xboole_0(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)),k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1195,plain,
    ( r1_xboole_0(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)),k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1458,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_xboole_0(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)),k6_domain_1(u1_struct_0(sK1),sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1189,c_1195])).

cnf(c_1816,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k2_tarski(sK3,sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_xboole_0(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)),k2_tarski(sK3,sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1813,c_1458])).

cnf(c_26,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_29,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_31,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_51,plain,
    ( v2_struct_0(X0) = iProver_top
    | l1_struct_0(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_53,plain,
    ( v2_struct_0(sK1) = iProver_top
    | l1_struct_0(sK1) != iProver_top
    | v1_xboole_0(u1_struct_0(sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_51])).

cnf(c_54,plain,
    ( l1_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_56,plain,
    ( l1_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_54])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1567,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | r2_hidden(sK3,u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1568,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top
    | r2_hidden(sK3,u1_struct_0(sK1)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1567])).

cnf(c_4,plain,
    ( m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1326,plain,
    ( m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X0,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1639,plain,
    ( m1_subset_1(k2_tarski(sK3,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK3,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_1326])).

cnf(c_1640,plain,
    ( m1_subset_1(k2_tarski(sK3,sK3),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | r2_hidden(sK3,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1639])).

cnf(c_2106,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_xboole_0(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)),k2_tarski(sK3,sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1816,c_26,c_29,c_31,c_53,c_56,c_1568,c_1640])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1193,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1517,plain,
    ( k6_domain_1(u1_struct_0(sK1),sK2) = k2_tarski(sK2,sK2)
    | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1193,c_1196])).

cnf(c_1360,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK1))
    | k6_domain_1(u1_struct_0(sK1),sK2) = k2_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1922,plain,
    ( k6_domain_1(u1_struct_0(sK1),sK2) = k2_tarski(sK2,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1517,c_25,c_22,c_21,c_52,c_55,c_1360])).

cnf(c_2110,plain,
    ( m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_xboole_0(k2_pre_topc(sK1,k2_tarski(sK2,sK2)),k2_tarski(sK3,sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2106,c_1922])).

cnf(c_30,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1570,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | r2_hidden(sK2,u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1571,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | r2_hidden(sK2,u1_struct_0(sK1)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1570])).

cnf(c_1648,plain,
    ( m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK2,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_1326])).

cnf(c_1649,plain,
    ( m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | r2_hidden(sK2,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1648])).

cnf(c_1817,plain,
    ( r1_xboole_0(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)),k2_pre_topc(sK1,k2_tarski(sK3,sK3))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1813,c_1195])).

cnf(c_1925,plain,
    ( r1_xboole_0(k2_pre_topc(sK1,k2_tarski(sK2,sK2)),k2_pre_topc(sK1,k2_tarski(sK3,sK3))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1922,c_1817])).

cnf(c_1990,plain,
    ( m1_subset_1(k2_tarski(sK3,sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_xboole_0(k2_pre_topc(sK1,k2_tarski(sK2,sK2)),k2_tarski(sK3,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1189,c_1925])).

cnf(c_2114,plain,
    ( r1_xboole_0(k2_pre_topc(sK1,k2_tarski(sK2,sK2)),k2_tarski(sK3,sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2110,c_26,c_29,c_30,c_31,c_53,c_56,c_1568,c_1571,c_1640,c_1649,c_1990])).

cnf(c_2996,plain,
    ( r2_hidden(sK3,k2_pre_topc(sK1,k2_tarski(sK2,sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1685,c_2114])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X0)))
    | ~ v3_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X0)) = k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_284,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X0,k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2)))
    | ~ v3_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X0)) = k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_25])).

cnf(c_285,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ r2_hidden(X1,k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X0)))
    | ~ v3_tdlat_3(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X1)) = k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X0)) ),
    inference(unflattening,[status(thm)],[c_284])).

cnf(c_289,plain,
    ( ~ r2_hidden(X1,k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X0)))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X1)) = k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_285,c_24,c_23,c_22])).

cnf(c_290,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ r2_hidden(X1,k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X0)))
    | k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X1)) = k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X0)) ),
    inference(renaming,[status(thm)],[c_289])).

cnf(c_1192,plain,
    ( k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X0)) = k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X1))
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
    | r2_hidden(X0,k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_290])).

cnf(c_1932,plain,
    ( k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X0)) = k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2))
    | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | r2_hidden(X0,k2_pre_topc(sK1,k2_tarski(sK2,sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1922,c_1192])).

cnf(c_1933,plain,
    ( k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X0)) = k2_pre_topc(sK1,k2_tarski(sK2,sK2))
    | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | r2_hidden(X0,k2_pre_topc(sK1,k2_tarski(sK2,sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1932,c_1922])).

cnf(c_2601,plain,
    ( m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
    | k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X0)) = k2_pre_topc(sK1,k2_tarski(sK2,sK2))
    | r2_hidden(X0,k2_pre_topc(sK1,k2_tarski(sK2,sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1933,c_30])).

cnf(c_2602,plain,
    ( k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X0)) = k2_pre_topc(sK1,k2_tarski(sK2,sK2))
    | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
    | r2_hidden(X0,k2_pre_topc(sK1,k2_tarski(sK2,sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2601])).

cnf(c_5866,plain,
    ( k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3)) = k2_pre_topc(sK1,k2_tarski(sK2,sK2))
    | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2996,c_2602])).

cnf(c_5869,plain,
    ( k2_pre_topc(sK1,k2_tarski(sK2,sK2)) = k2_pre_topc(sK1,k2_tarski(sK3,sK3))
    | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5866,c_1813])).

cnf(c_18,negated_conjecture,
    ( k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1818,plain,
    ( k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)) != k2_pre_topc(sK1,k2_tarski(sK3,sK3)) ),
    inference(demodulation,[status(thm)],[c_1813,c_18])).

cnf(c_1926,plain,
    ( k2_pre_topc(sK1,k2_tarski(sK2,sK2)) != k2_pre_topc(sK1,k2_tarski(sK3,sK3)) ),
    inference(demodulation,[status(thm)],[c_1922,c_1818])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5869,c_1926,c_31])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:35:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.44/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.44/0.99  
% 2.44/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.44/0.99  
% 2.44/0.99  ------  iProver source info
% 2.44/0.99  
% 2.44/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.44/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.44/0.99  git: non_committed_changes: false
% 2.44/0.99  git: last_make_outside_of_git: false
% 2.44/0.99  
% 2.44/0.99  ------ 
% 2.44/0.99  
% 2.44/0.99  ------ Input Options
% 2.44/0.99  
% 2.44/0.99  --out_options                           all
% 2.44/0.99  --tptp_safe_out                         true
% 2.44/0.99  --problem_path                          ""
% 2.44/0.99  --include_path                          ""
% 2.44/0.99  --clausifier                            res/vclausify_rel
% 2.44/0.99  --clausifier_options                    --mode clausify
% 2.44/0.99  --stdin                                 false
% 2.44/0.99  --stats_out                             all
% 2.44/0.99  
% 2.44/0.99  ------ General Options
% 2.44/0.99  
% 2.44/0.99  --fof                                   false
% 2.44/0.99  --time_out_real                         305.
% 2.44/0.99  --time_out_virtual                      -1.
% 2.44/0.99  --symbol_type_check                     false
% 2.44/0.99  --clausify_out                          false
% 2.44/0.99  --sig_cnt_out                           false
% 2.44/0.99  --trig_cnt_out                          false
% 2.44/0.99  --trig_cnt_out_tolerance                1.
% 2.44/0.99  --trig_cnt_out_sk_spl                   false
% 2.44/0.99  --abstr_cl_out                          false
% 2.44/0.99  
% 2.44/0.99  ------ Global Options
% 2.44/0.99  
% 2.44/0.99  --schedule                              default
% 2.44/0.99  --add_important_lit                     false
% 2.44/0.99  --prop_solver_per_cl                    1000
% 2.44/0.99  --min_unsat_core                        false
% 2.44/0.99  --soft_assumptions                      false
% 2.44/0.99  --soft_lemma_size                       3
% 2.44/0.99  --prop_impl_unit_size                   0
% 2.44/0.99  --prop_impl_unit                        []
% 2.44/0.99  --share_sel_clauses                     true
% 2.44/0.99  --reset_solvers                         false
% 2.44/0.99  --bc_imp_inh                            [conj_cone]
% 2.44/0.99  --conj_cone_tolerance                   3.
% 2.44/0.99  --extra_neg_conj                        none
% 2.44/0.99  --large_theory_mode                     true
% 2.44/0.99  --prolific_symb_bound                   200
% 2.44/0.99  --lt_threshold                          2000
% 2.44/0.99  --clause_weak_htbl                      true
% 2.44/0.99  --gc_record_bc_elim                     false
% 2.44/0.99  
% 2.44/0.99  ------ Preprocessing Options
% 2.44/0.99  
% 2.44/0.99  --preprocessing_flag                    true
% 2.44/0.99  --time_out_prep_mult                    0.1
% 2.44/0.99  --splitting_mode                        input
% 2.44/0.99  --splitting_grd                         true
% 2.44/0.99  --splitting_cvd                         false
% 2.44/0.99  --splitting_cvd_svl                     false
% 2.44/0.99  --splitting_nvd                         32
% 2.44/0.99  --sub_typing                            true
% 2.44/0.99  --prep_gs_sim                           true
% 2.44/0.99  --prep_unflatten                        true
% 2.44/0.99  --prep_res_sim                          true
% 2.44/0.99  --prep_upred                            true
% 2.44/0.99  --prep_sem_filter                       exhaustive
% 2.44/0.99  --prep_sem_filter_out                   false
% 2.44/0.99  --pred_elim                             true
% 2.44/0.99  --res_sim_input                         true
% 2.44/0.99  --eq_ax_congr_red                       true
% 2.44/0.99  --pure_diseq_elim                       true
% 2.44/0.99  --brand_transform                       false
% 2.44/0.99  --non_eq_to_eq                          false
% 2.44/0.99  --prep_def_merge                        true
% 2.44/0.99  --prep_def_merge_prop_impl              false
% 2.44/0.99  --prep_def_merge_mbd                    true
% 2.44/0.99  --prep_def_merge_tr_red                 false
% 2.44/0.99  --prep_def_merge_tr_cl                  false
% 2.44/0.99  --smt_preprocessing                     true
% 2.44/0.99  --smt_ac_axioms                         fast
% 2.44/0.99  --preprocessed_out                      false
% 2.44/0.99  --preprocessed_stats                    false
% 2.44/0.99  
% 2.44/0.99  ------ Abstraction refinement Options
% 2.44/0.99  
% 2.44/0.99  --abstr_ref                             []
% 2.44/0.99  --abstr_ref_prep                        false
% 2.44/0.99  --abstr_ref_until_sat                   false
% 2.44/0.99  --abstr_ref_sig_restrict                funpre
% 2.44/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.44/0.99  --abstr_ref_under                       []
% 2.44/0.99  
% 2.44/0.99  ------ SAT Options
% 2.44/0.99  
% 2.44/0.99  --sat_mode                              false
% 2.44/0.99  --sat_fm_restart_options                ""
% 2.44/0.99  --sat_gr_def                            false
% 2.44/0.99  --sat_epr_types                         true
% 2.44/0.99  --sat_non_cyclic_types                  false
% 2.44/0.99  --sat_finite_models                     false
% 2.44/0.99  --sat_fm_lemmas                         false
% 2.44/0.99  --sat_fm_prep                           false
% 2.44/0.99  --sat_fm_uc_incr                        true
% 2.44/0.99  --sat_out_model                         small
% 2.44/0.99  --sat_out_clauses                       false
% 2.44/0.99  
% 2.44/0.99  ------ QBF Options
% 2.44/0.99  
% 2.44/0.99  --qbf_mode                              false
% 2.44/0.99  --qbf_elim_univ                         false
% 2.44/0.99  --qbf_dom_inst                          none
% 2.44/0.99  --qbf_dom_pre_inst                      false
% 2.44/0.99  --qbf_sk_in                             false
% 2.44/0.99  --qbf_pred_elim                         true
% 2.44/0.99  --qbf_split                             512
% 2.44/0.99  
% 2.44/0.99  ------ BMC1 Options
% 2.44/0.99  
% 2.44/0.99  --bmc1_incremental                      false
% 2.44/0.99  --bmc1_axioms                           reachable_all
% 2.44/0.99  --bmc1_min_bound                        0
% 2.44/0.99  --bmc1_max_bound                        -1
% 2.44/0.99  --bmc1_max_bound_default                -1
% 2.44/0.99  --bmc1_symbol_reachability              true
% 2.44/0.99  --bmc1_property_lemmas                  false
% 2.44/0.99  --bmc1_k_induction                      false
% 2.44/0.99  --bmc1_non_equiv_states                 false
% 2.44/0.99  --bmc1_deadlock                         false
% 2.44/0.99  --bmc1_ucm                              false
% 2.44/0.99  --bmc1_add_unsat_core                   none
% 2.44/0.99  --bmc1_unsat_core_children              false
% 2.44/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.44/0.99  --bmc1_out_stat                         full
% 2.44/0.99  --bmc1_ground_init                      false
% 2.44/0.99  --bmc1_pre_inst_next_state              false
% 2.44/0.99  --bmc1_pre_inst_state                   false
% 2.44/0.99  --bmc1_pre_inst_reach_state             false
% 2.44/0.99  --bmc1_out_unsat_core                   false
% 2.44/0.99  --bmc1_aig_witness_out                  false
% 2.44/0.99  --bmc1_verbose                          false
% 2.44/0.99  --bmc1_dump_clauses_tptp                false
% 2.44/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.44/0.99  --bmc1_dump_file                        -
% 2.44/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.44/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.44/0.99  --bmc1_ucm_extend_mode                  1
% 2.44/0.99  --bmc1_ucm_init_mode                    2
% 2.44/0.99  --bmc1_ucm_cone_mode                    none
% 2.44/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.44/0.99  --bmc1_ucm_relax_model                  4
% 2.44/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.44/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.44/0.99  --bmc1_ucm_layered_model                none
% 2.44/0.99  --bmc1_ucm_max_lemma_size               10
% 2.44/0.99  
% 2.44/0.99  ------ AIG Options
% 2.44/0.99  
% 2.44/0.99  --aig_mode                              false
% 2.44/0.99  
% 2.44/0.99  ------ Instantiation Options
% 2.44/0.99  
% 2.44/0.99  --instantiation_flag                    true
% 2.44/0.99  --inst_sos_flag                         false
% 2.44/0.99  --inst_sos_phase                        true
% 2.44/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.44/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.44/0.99  --inst_lit_sel_side                     num_symb
% 2.44/0.99  --inst_solver_per_active                1400
% 2.44/0.99  --inst_solver_calls_frac                1.
% 2.44/0.99  --inst_passive_queue_type               priority_queues
% 2.44/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.44/0.99  --inst_passive_queues_freq              [25;2]
% 2.44/0.99  --inst_dismatching                      true
% 2.44/0.99  --inst_eager_unprocessed_to_passive     true
% 2.44/0.99  --inst_prop_sim_given                   true
% 2.44/0.99  --inst_prop_sim_new                     false
% 2.44/0.99  --inst_subs_new                         false
% 2.44/0.99  --inst_eq_res_simp                      false
% 2.44/0.99  --inst_subs_given                       false
% 2.44/0.99  --inst_orphan_elimination               true
% 2.44/0.99  --inst_learning_loop_flag               true
% 2.44/0.99  --inst_learning_start                   3000
% 2.44/0.99  --inst_learning_factor                  2
% 2.44/0.99  --inst_start_prop_sim_after_learn       3
% 2.44/0.99  --inst_sel_renew                        solver
% 2.44/0.99  --inst_lit_activity_flag                true
% 2.44/0.99  --inst_restr_to_given                   false
% 2.44/0.99  --inst_activity_threshold               500
% 2.44/0.99  --inst_out_proof                        true
% 2.44/0.99  
% 2.44/0.99  ------ Resolution Options
% 2.44/0.99  
% 2.44/0.99  --resolution_flag                       true
% 2.44/0.99  --res_lit_sel                           adaptive
% 2.44/0.99  --res_lit_sel_side                      none
% 2.44/0.99  --res_ordering                          kbo
% 2.44/0.99  --res_to_prop_solver                    active
% 2.44/0.99  --res_prop_simpl_new                    false
% 2.44/0.99  --res_prop_simpl_given                  true
% 2.44/0.99  --res_passive_queue_type                priority_queues
% 2.44/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.44/0.99  --res_passive_queues_freq               [15;5]
% 2.44/0.99  --res_forward_subs                      full
% 2.44/0.99  --res_backward_subs                     full
% 2.44/0.99  --res_forward_subs_resolution           true
% 2.44/0.99  --res_backward_subs_resolution          true
% 2.44/0.99  --res_orphan_elimination                true
% 2.44/0.99  --res_time_limit                        2.
% 2.44/0.99  --res_out_proof                         true
% 2.44/0.99  
% 2.44/0.99  ------ Superposition Options
% 2.44/0.99  
% 2.44/0.99  --superposition_flag                    true
% 2.44/0.99  --sup_passive_queue_type                priority_queues
% 2.44/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.44/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.44/0.99  --demod_completeness_check              fast
% 2.44/0.99  --demod_use_ground                      true
% 2.44/0.99  --sup_to_prop_solver                    passive
% 2.44/0.99  --sup_prop_simpl_new                    true
% 2.44/0.99  --sup_prop_simpl_given                  true
% 2.44/0.99  --sup_fun_splitting                     false
% 2.44/0.99  --sup_smt_interval                      50000
% 2.44/0.99  
% 2.44/0.99  ------ Superposition Simplification Setup
% 2.44/0.99  
% 2.44/0.99  --sup_indices_passive                   []
% 2.44/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.44/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.44/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.44/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.44/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.44/0.99  --sup_full_bw                           [BwDemod]
% 2.44/0.99  --sup_immed_triv                        [TrivRules]
% 2.44/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.44/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.44/0.99  --sup_immed_bw_main                     []
% 2.44/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.44/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.44/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.44/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.44/0.99  
% 2.44/0.99  ------ Combination Options
% 2.44/0.99  
% 2.44/0.99  --comb_res_mult                         3
% 2.44/0.99  --comb_sup_mult                         2
% 2.44/0.99  --comb_inst_mult                        10
% 2.44/0.99  
% 2.44/0.99  ------ Debug Options
% 2.44/0.99  
% 2.44/0.99  --dbg_backtrace                         false
% 2.44/0.99  --dbg_dump_prop_clauses                 false
% 2.44/0.99  --dbg_dump_prop_clauses_file            -
% 2.44/0.99  --dbg_out_stat                          false
% 2.44/0.99  ------ Parsing...
% 2.44/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.44/0.99  
% 2.44/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 2.44/0.99  
% 2.44/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.44/0.99  
% 2.44/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.44/0.99  ------ Proving...
% 2.44/0.99  ------ Problem Properties 
% 2.44/0.99  
% 2.44/0.99  
% 2.44/0.99  clauses                                 16
% 2.44/0.99  conjectures                             4
% 2.44/0.99  EPR                                     2
% 2.44/0.99  Horn                                    13
% 2.44/0.99  unary                                   7
% 2.44/0.99  binary                                  4
% 2.44/0.99  lits                                    32
% 2.44/0.99  lits eq                                 4
% 2.44/0.99  fd_pure                                 0
% 2.44/0.99  fd_pseudo                               0
% 2.44/0.99  fd_cond                                 0
% 2.44/0.99  fd_pseudo_cond                          0
% 2.44/0.99  AC symbols                              0
% 2.44/0.99  
% 2.44/0.99  ------ Schedule dynamic 5 is on 
% 2.44/0.99  
% 2.44/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.44/0.99  
% 2.44/0.99  
% 2.44/0.99  ------ 
% 2.44/0.99  Current options:
% 2.44/0.99  ------ 
% 2.44/0.99  
% 2.44/0.99  ------ Input Options
% 2.44/0.99  
% 2.44/0.99  --out_options                           all
% 2.44/0.99  --tptp_safe_out                         true
% 2.44/0.99  --problem_path                          ""
% 2.44/0.99  --include_path                          ""
% 2.44/0.99  --clausifier                            res/vclausify_rel
% 2.44/0.99  --clausifier_options                    --mode clausify
% 2.44/0.99  --stdin                                 false
% 2.44/0.99  --stats_out                             all
% 2.44/0.99  
% 2.44/0.99  ------ General Options
% 2.44/0.99  
% 2.44/0.99  --fof                                   false
% 2.44/0.99  --time_out_real                         305.
% 2.44/0.99  --time_out_virtual                      -1.
% 2.44/0.99  --symbol_type_check                     false
% 2.44/0.99  --clausify_out                          false
% 2.44/0.99  --sig_cnt_out                           false
% 2.44/0.99  --trig_cnt_out                          false
% 2.44/0.99  --trig_cnt_out_tolerance                1.
% 2.44/0.99  --trig_cnt_out_sk_spl                   false
% 2.44/0.99  --abstr_cl_out                          false
% 2.44/0.99  
% 2.44/0.99  ------ Global Options
% 2.44/0.99  
% 2.44/0.99  --schedule                              default
% 2.44/0.99  --add_important_lit                     false
% 2.44/0.99  --prop_solver_per_cl                    1000
% 2.44/0.99  --min_unsat_core                        false
% 2.44/0.99  --soft_assumptions                      false
% 2.44/0.99  --soft_lemma_size                       3
% 2.44/0.99  --prop_impl_unit_size                   0
% 2.44/0.99  --prop_impl_unit                        []
% 2.44/0.99  --share_sel_clauses                     true
% 2.44/0.99  --reset_solvers                         false
% 2.44/0.99  --bc_imp_inh                            [conj_cone]
% 2.44/0.99  --conj_cone_tolerance                   3.
% 2.44/0.99  --extra_neg_conj                        none
% 2.44/0.99  --large_theory_mode                     true
% 2.44/0.99  --prolific_symb_bound                   200
% 2.44/0.99  --lt_threshold                          2000
% 2.44/0.99  --clause_weak_htbl                      true
% 2.44/0.99  --gc_record_bc_elim                     false
% 2.44/0.99  
% 2.44/0.99  ------ Preprocessing Options
% 2.44/0.99  
% 2.44/0.99  --preprocessing_flag                    true
% 2.44/0.99  --time_out_prep_mult                    0.1
% 2.44/0.99  --splitting_mode                        input
% 2.44/0.99  --splitting_grd                         true
% 2.44/0.99  --splitting_cvd                         false
% 2.44/0.99  --splitting_cvd_svl                     false
% 2.44/0.99  --splitting_nvd                         32
% 2.44/0.99  --sub_typing                            true
% 2.44/0.99  --prep_gs_sim                           true
% 2.44/0.99  --prep_unflatten                        true
% 2.44/0.99  --prep_res_sim                          true
% 2.44/0.99  --prep_upred                            true
% 2.44/0.99  --prep_sem_filter                       exhaustive
% 2.44/0.99  --prep_sem_filter_out                   false
% 2.44/0.99  --pred_elim                             true
% 2.44/0.99  --res_sim_input                         true
% 2.44/0.99  --eq_ax_congr_red                       true
% 2.44/0.99  --pure_diseq_elim                       true
% 2.44/0.99  --brand_transform                       false
% 2.44/0.99  --non_eq_to_eq                          false
% 2.44/0.99  --prep_def_merge                        true
% 2.44/0.99  --prep_def_merge_prop_impl              false
% 2.44/0.99  --prep_def_merge_mbd                    true
% 2.44/0.99  --prep_def_merge_tr_red                 false
% 2.44/0.99  --prep_def_merge_tr_cl                  false
% 2.44/0.99  --smt_preprocessing                     true
% 2.44/0.99  --smt_ac_axioms                         fast
% 2.44/0.99  --preprocessed_out                      false
% 2.44/0.99  --preprocessed_stats                    false
% 2.44/0.99  
% 2.44/0.99  ------ Abstraction refinement Options
% 2.44/0.99  
% 2.44/0.99  --abstr_ref                             []
% 2.44/0.99  --abstr_ref_prep                        false
% 2.44/0.99  --abstr_ref_until_sat                   false
% 2.44/0.99  --abstr_ref_sig_restrict                funpre
% 2.44/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.44/0.99  --abstr_ref_under                       []
% 2.44/0.99  
% 2.44/0.99  ------ SAT Options
% 2.44/0.99  
% 2.44/0.99  --sat_mode                              false
% 2.44/0.99  --sat_fm_restart_options                ""
% 2.44/0.99  --sat_gr_def                            false
% 2.44/0.99  --sat_epr_types                         true
% 2.44/0.99  --sat_non_cyclic_types                  false
% 2.44/0.99  --sat_finite_models                     false
% 2.44/0.99  --sat_fm_lemmas                         false
% 2.44/0.99  --sat_fm_prep                           false
% 2.44/0.99  --sat_fm_uc_incr                        true
% 2.44/0.99  --sat_out_model                         small
% 2.44/0.99  --sat_out_clauses                       false
% 2.44/0.99  
% 2.44/0.99  ------ QBF Options
% 2.44/0.99  
% 2.44/0.99  --qbf_mode                              false
% 2.44/0.99  --qbf_elim_univ                         false
% 2.44/0.99  --qbf_dom_inst                          none
% 2.44/0.99  --qbf_dom_pre_inst                      false
% 2.44/0.99  --qbf_sk_in                             false
% 2.44/0.99  --qbf_pred_elim                         true
% 2.44/0.99  --qbf_split                             512
% 2.44/0.99  
% 2.44/0.99  ------ BMC1 Options
% 2.44/0.99  
% 2.44/0.99  --bmc1_incremental                      false
% 2.44/0.99  --bmc1_axioms                           reachable_all
% 2.44/0.99  --bmc1_min_bound                        0
% 2.44/0.99  --bmc1_max_bound                        -1
% 2.44/0.99  --bmc1_max_bound_default                -1
% 2.44/0.99  --bmc1_symbol_reachability              true
% 2.44/0.99  --bmc1_property_lemmas                  false
% 2.44/0.99  --bmc1_k_induction                      false
% 2.44/0.99  --bmc1_non_equiv_states                 false
% 2.44/0.99  --bmc1_deadlock                         false
% 2.44/0.99  --bmc1_ucm                              false
% 2.44/0.99  --bmc1_add_unsat_core                   none
% 2.44/0.99  --bmc1_unsat_core_children              false
% 2.44/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.44/0.99  --bmc1_out_stat                         full
% 2.44/0.99  --bmc1_ground_init                      false
% 2.44/0.99  --bmc1_pre_inst_next_state              false
% 2.44/0.99  --bmc1_pre_inst_state                   false
% 2.44/0.99  --bmc1_pre_inst_reach_state             false
% 2.44/0.99  --bmc1_out_unsat_core                   false
% 2.44/0.99  --bmc1_aig_witness_out                  false
% 2.44/0.99  --bmc1_verbose                          false
% 2.44/0.99  --bmc1_dump_clauses_tptp                false
% 2.44/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.44/0.99  --bmc1_dump_file                        -
% 2.44/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.44/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.44/0.99  --bmc1_ucm_extend_mode                  1
% 2.44/0.99  --bmc1_ucm_init_mode                    2
% 2.44/0.99  --bmc1_ucm_cone_mode                    none
% 2.44/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.44/0.99  --bmc1_ucm_relax_model                  4
% 2.44/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.44/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.44/0.99  --bmc1_ucm_layered_model                none
% 2.44/0.99  --bmc1_ucm_max_lemma_size               10
% 2.44/0.99  
% 2.44/0.99  ------ AIG Options
% 2.44/0.99  
% 2.44/0.99  --aig_mode                              false
% 2.44/0.99  
% 2.44/0.99  ------ Instantiation Options
% 2.44/0.99  
% 2.44/0.99  --instantiation_flag                    true
% 2.44/0.99  --inst_sos_flag                         false
% 2.44/0.99  --inst_sos_phase                        true
% 2.44/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.44/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.44/0.99  --inst_lit_sel_side                     none
% 2.44/0.99  --inst_solver_per_active                1400
% 2.44/0.99  --inst_solver_calls_frac                1.
% 2.44/0.99  --inst_passive_queue_type               priority_queues
% 2.44/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.44/0.99  --inst_passive_queues_freq              [25;2]
% 2.44/0.99  --inst_dismatching                      true
% 2.44/0.99  --inst_eager_unprocessed_to_passive     true
% 2.44/0.99  --inst_prop_sim_given                   true
% 2.44/0.99  --inst_prop_sim_new                     false
% 2.44/0.99  --inst_subs_new                         false
% 2.44/0.99  --inst_eq_res_simp                      false
% 2.44/0.99  --inst_subs_given                       false
% 2.44/0.99  --inst_orphan_elimination               true
% 2.44/0.99  --inst_learning_loop_flag               true
% 2.44/0.99  --inst_learning_start                   3000
% 2.44/0.99  --inst_learning_factor                  2
% 2.44/0.99  --inst_start_prop_sim_after_learn       3
% 2.44/0.99  --inst_sel_renew                        solver
% 2.44/0.99  --inst_lit_activity_flag                true
% 2.44/0.99  --inst_restr_to_given                   false
% 2.44/0.99  --inst_activity_threshold               500
% 2.44/0.99  --inst_out_proof                        true
% 2.44/0.99  
% 2.44/0.99  ------ Resolution Options
% 2.44/0.99  
% 2.44/0.99  --resolution_flag                       false
% 2.44/0.99  --res_lit_sel                           adaptive
% 2.44/0.99  --res_lit_sel_side                      none
% 2.44/0.99  --res_ordering                          kbo
% 2.44/0.99  --res_to_prop_solver                    active
% 2.44/0.99  --res_prop_simpl_new                    false
% 2.44/0.99  --res_prop_simpl_given                  true
% 2.44/0.99  --res_passive_queue_type                priority_queues
% 2.44/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.44/0.99  --res_passive_queues_freq               [15;5]
% 2.44/0.99  --res_forward_subs                      full
% 2.44/0.99  --res_backward_subs                     full
% 2.44/0.99  --res_forward_subs_resolution           true
% 2.44/0.99  --res_backward_subs_resolution          true
% 2.44/0.99  --res_orphan_elimination                true
% 2.44/0.99  --res_time_limit                        2.
% 2.44/0.99  --res_out_proof                         true
% 2.44/0.99  
% 2.44/0.99  ------ Superposition Options
% 2.44/0.99  
% 2.44/0.99  --superposition_flag                    true
% 2.44/0.99  --sup_passive_queue_type                priority_queues
% 2.44/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.44/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.44/0.99  --demod_completeness_check              fast
% 2.44/1.00  --demod_use_ground                      true
% 2.44/1.00  --sup_to_prop_solver                    passive
% 2.44/1.00  --sup_prop_simpl_new                    true
% 2.44/1.00  --sup_prop_simpl_given                  true
% 2.44/1.00  --sup_fun_splitting                     false
% 2.44/1.00  --sup_smt_interval                      50000
% 2.44/1.00  
% 2.44/1.00  ------ Superposition Simplification Setup
% 2.44/1.00  
% 2.44/1.00  --sup_indices_passive                   []
% 2.44/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.44/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.44/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.44/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.44/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.44/1.00  --sup_full_bw                           [BwDemod]
% 2.44/1.00  --sup_immed_triv                        [TrivRules]
% 2.44/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.44/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.44/1.00  --sup_immed_bw_main                     []
% 2.44/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.44/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.44/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.44/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.44/1.00  
% 2.44/1.00  ------ Combination Options
% 2.44/1.00  
% 2.44/1.00  --comb_res_mult                         3
% 2.44/1.00  --comb_sup_mult                         2
% 2.44/1.00  --comb_inst_mult                        10
% 2.44/1.00  
% 2.44/1.00  ------ Debug Options
% 2.44/1.00  
% 2.44/1.00  --dbg_backtrace                         false
% 2.44/1.00  --dbg_dump_prop_clauses                 false
% 2.44/1.00  --dbg_dump_prop_clauses_file            -
% 2.44/1.00  --dbg_out_stat                          false
% 2.44/1.00  
% 2.44/1.00  
% 2.44/1.00  
% 2.44/1.00  
% 2.44/1.00  ------ Proving...
% 2.44/1.00  
% 2.44/1.00  
% 2.44/1.00  % SZS status Theorem for theBenchmark.p
% 2.44/1.00  
% 2.44/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.44/1.00  
% 2.44/1.00  fof(f3,axiom,(
% 2.44/1.00    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 2.44/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.44/1.00  
% 2.44/1.00  fof(f20,plain,(
% 2.44/1.00    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 2.44/1.00    inference(ennf_transformation,[],[f3])).
% 2.44/1.00  
% 2.44/1.00  fof(f52,plain,(
% 2.44/1.00    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 2.44/1.00    inference(cnf_transformation,[],[f20])).
% 2.44/1.00  
% 2.44/1.00  fof(f2,axiom,(
% 2.44/1.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.44/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.44/1.00  
% 2.44/1.00  fof(f51,plain,(
% 2.44/1.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.44/1.00    inference(cnf_transformation,[],[f2])).
% 2.44/1.00  
% 2.44/1.00  fof(f77,plain,(
% 2.44/1.00    ( ! [X0,X1] : (r1_xboole_0(k2_tarski(X0,X0),X1) | r2_hidden(X0,X1)) )),
% 2.44/1.00    inference(definition_unfolding,[],[f52,f51])).
% 2.44/1.00  
% 2.44/1.00  fof(f1,axiom,(
% 2.44/1.00    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 2.44/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.44/1.00  
% 2.44/1.00  fof(f19,plain,(
% 2.44/1.00    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 2.44/1.00    inference(ennf_transformation,[],[f1])).
% 2.44/1.00  
% 2.44/1.00  fof(f50,plain,(
% 2.44/1.00    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 2.44/1.00    inference(cnf_transformation,[],[f19])).
% 2.44/1.00  
% 2.44/1.00  fof(f17,conjecture,(
% 2.44/1.00    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) | r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))))))),
% 2.44/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.44/1.00  
% 2.44/1.00  fof(f18,negated_conjecture,(
% 2.44/1.00    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) | r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))))))),
% 2.44/1.00    inference(negated_conjecture,[],[f17])).
% 2.44/1.00  
% 2.44/1.00  fof(f40,plain,(
% 2.44/1.00    ? [X0] : (? [X1] : (? [X2] : ((k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.44/1.00    inference(ennf_transformation,[],[f18])).
% 2.44/1.00  
% 2.44/1.00  fof(f41,plain,(
% 2.44/1.00    ? [X0] : (? [X1] : (? [X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.44/1.00    inference(flattening,[],[f40])).
% 2.44/1.00  
% 2.44/1.00  fof(f48,plain,(
% 2.44/1.00    ( ! [X0,X1] : (? [X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & m1_subset_1(X2,u1_struct_0(X0))) => (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK3))) & m1_subset_1(sK3,u1_struct_0(X0)))) )),
% 2.44/1.00    introduced(choice_axiom,[])).
% 2.44/1.00  
% 2.44/1.00  fof(f47,plain,(
% 2.44/1.00    ( ! [X0] : (? [X1] : (? [X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK2)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK2)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK2,u1_struct_0(X0)))) )),
% 2.44/1.00    introduced(choice_axiom,[])).
% 2.44/1.00  
% 2.44/1.00  fof(f46,plain,(
% 2.44/1.00    ? [X0] : (? [X1] : (? [X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X1)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X2)) & ~r1_xboole_0(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X1)),k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X2))) & m1_subset_1(X2,u1_struct_0(sK1))) & m1_subset_1(X1,u1_struct_0(sK1))) & l1_pre_topc(sK1) & v3_tdlat_3(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 2.44/1.00    introduced(choice_axiom,[])).
% 2.44/1.00  
% 2.44/1.00  fof(f49,plain,(
% 2.44/1.00    ((k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3)) & ~r1_xboole_0(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)),k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3))) & m1_subset_1(sK3,u1_struct_0(sK1))) & m1_subset_1(sK2,u1_struct_0(sK1))) & l1_pre_topc(sK1) & v3_tdlat_3(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 2.44/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f41,f48,f47,f46])).
% 2.44/1.00  
% 2.44/1.00  fof(f74,plain,(
% 2.44/1.00    m1_subset_1(sK3,u1_struct_0(sK1))),
% 2.44/1.00    inference(cnf_transformation,[],[f49])).
% 2.44/1.00  
% 2.44/1.00  fof(f12,axiom,(
% 2.44/1.00    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 2.44/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.44/1.00  
% 2.44/1.00  fof(f30,plain,(
% 2.44/1.00    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 2.44/1.00    inference(ennf_transformation,[],[f12])).
% 2.44/1.00  
% 2.44/1.00  fof(f31,plain,(
% 2.44/1.00    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 2.44/1.00    inference(flattening,[],[f30])).
% 2.44/1.00  
% 2.44/1.00  fof(f61,plain,(
% 2.44/1.00    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.44/1.00    inference(cnf_transformation,[],[f31])).
% 2.44/1.00  
% 2.44/1.00  fof(f79,plain,(
% 2.44/1.00    ( ! [X0,X1] : (k2_tarski(X1,X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.44/1.00    inference(definition_unfolding,[],[f61,f51])).
% 2.44/1.00  
% 2.44/1.00  fof(f69,plain,(
% 2.44/1.00    ~v2_struct_0(sK1)),
% 2.44/1.00    inference(cnf_transformation,[],[f49])).
% 2.44/1.00  
% 2.44/1.00  fof(f72,plain,(
% 2.44/1.00    l1_pre_topc(sK1)),
% 2.44/1.00    inference(cnf_transformation,[],[f49])).
% 2.44/1.00  
% 2.44/1.00  fof(f11,axiom,(
% 2.44/1.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.44/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.44/1.00  
% 2.44/1.00  fof(f28,plain,(
% 2.44/1.00    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.44/1.00    inference(ennf_transformation,[],[f11])).
% 2.44/1.00  
% 2.44/1.00  fof(f29,plain,(
% 2.44/1.00    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.44/1.00    inference(flattening,[],[f28])).
% 2.44/1.00  
% 2.44/1.00  fof(f60,plain,(
% 2.44/1.00    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.44/1.00    inference(cnf_transformation,[],[f29])).
% 2.44/1.00  
% 2.44/1.00  fof(f10,axiom,(
% 2.44/1.00    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.44/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.44/1.00  
% 2.44/1.00  fof(f27,plain,(
% 2.44/1.00    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.44/1.00    inference(ennf_transformation,[],[f10])).
% 2.44/1.00  
% 2.44/1.00  fof(f59,plain,(
% 2.44/1.00    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.44/1.00    inference(cnf_transformation,[],[f27])).
% 2.44/1.00  
% 2.44/1.00  fof(f15,axiom,(
% 2.44/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X1,X0) & r1_xboole_0(X1,X2)) => r1_xboole_0(X1,k2_pre_topc(X0,X2))))))),
% 2.44/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.44/1.00  
% 2.44/1.00  fof(f36,plain,(
% 2.44/1.00    ! [X0] : (! [X1] : (! [X2] : ((r1_xboole_0(X1,k2_pre_topc(X0,X2)) | (~v3_pre_topc(X1,X0) | ~r1_xboole_0(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.44/1.00    inference(ennf_transformation,[],[f15])).
% 2.44/1.00  
% 2.44/1.00  fof(f37,plain,(
% 2.44/1.00    ! [X0] : (! [X1] : (! [X2] : (r1_xboole_0(X1,k2_pre_topc(X0,X2)) | ~v3_pre_topc(X1,X0) | ~r1_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.44/1.00    inference(flattening,[],[f36])).
% 2.44/1.00  
% 2.44/1.00  fof(f67,plain,(
% 2.44/1.00    ( ! [X2,X0,X1] : (r1_xboole_0(X1,k2_pre_topc(X0,X2)) | ~v3_pre_topc(X1,X0) | ~r1_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.44/1.00    inference(cnf_transformation,[],[f37])).
% 2.44/1.00  
% 2.44/1.00  fof(f70,plain,(
% 2.44/1.00    v2_pre_topc(sK1)),
% 2.44/1.00    inference(cnf_transformation,[],[f49])).
% 2.44/1.00  
% 2.44/1.00  fof(f13,axiom,(
% 2.44/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_pre_topc(X0,X1),X0))),
% 2.44/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.44/1.00  
% 2.44/1.00  fof(f32,plain,(
% 2.44/1.00    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.44/1.00    inference(ennf_transformation,[],[f13])).
% 2.44/1.00  
% 2.44/1.00  fof(f33,plain,(
% 2.44/1.00    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.44/1.00    inference(flattening,[],[f32])).
% 2.44/1.00  
% 2.44/1.00  fof(f62,plain,(
% 2.44/1.00    ( ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.44/1.00    inference(cnf_transformation,[],[f33])).
% 2.44/1.00  
% 2.44/1.00  fof(f14,axiom,(
% 2.44/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v3_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => v3_pre_topc(X1,X0)))))),
% 2.44/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.44/1.00  
% 2.44/1.00  fof(f34,plain,(
% 2.44/1.00    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : ((v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.44/1.00    inference(ennf_transformation,[],[f14])).
% 2.44/1.00  
% 2.44/1.00  fof(f35,plain,(
% 2.44/1.00    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.44/1.00    inference(flattening,[],[f34])).
% 2.44/1.00  
% 2.44/1.00  fof(f42,plain,(
% 2.44/1.00    ! [X0] : (((v3_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X1] : (v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.44/1.00    inference(nnf_transformation,[],[f35])).
% 2.44/1.00  
% 2.44/1.00  fof(f43,plain,(
% 2.44/1.00    ! [X0] : (((v3_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.44/1.00    inference(rectify,[],[f42])).
% 2.44/1.00  
% 2.44/1.00  fof(f44,plain,(
% 2.44/1.00    ! [X0] : (? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK0(X0),X0) & v4_pre_topc(sK0(X0),X0) & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.44/1.00    introduced(choice_axiom,[])).
% 2.44/1.00  
% 2.44/1.00  fof(f45,plain,(
% 2.44/1.00    ! [X0] : (((v3_tdlat_3(X0) | (~v3_pre_topc(sK0(X0),X0) & v4_pre_topc(sK0(X0),X0) & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.44/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f43,f44])).
% 2.44/1.00  
% 2.44/1.00  fof(f63,plain,(
% 2.44/1.00    ( ! [X2,X0] : (v3_pre_topc(X2,X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tdlat_3(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.44/1.00    inference(cnf_transformation,[],[f45])).
% 2.44/1.00  
% 2.44/1.00  fof(f9,axiom,(
% 2.44/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.44/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.44/1.00  
% 2.44/1.00  fof(f25,plain,(
% 2.44/1.00    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.44/1.00    inference(ennf_transformation,[],[f9])).
% 2.44/1.00  
% 2.44/1.00  fof(f26,plain,(
% 2.44/1.00    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.44/1.00    inference(flattening,[],[f25])).
% 2.44/1.00  
% 2.44/1.00  fof(f58,plain,(
% 2.44/1.00    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.44/1.00    inference(cnf_transformation,[],[f26])).
% 2.44/1.00  
% 2.44/1.00  fof(f71,plain,(
% 2.44/1.00    v3_tdlat_3(sK1)),
% 2.44/1.00    inference(cnf_transformation,[],[f49])).
% 2.44/1.00  
% 2.44/1.00  fof(f75,plain,(
% 2.44/1.00    ~r1_xboole_0(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)),k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3)))),
% 2.44/1.00    inference(cnf_transformation,[],[f49])).
% 2.44/1.00  
% 2.44/1.00  fof(f7,axiom,(
% 2.44/1.00    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.44/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.44/1.00  
% 2.44/1.00  fof(f22,plain,(
% 2.44/1.00    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.44/1.00    inference(ennf_transformation,[],[f7])).
% 2.44/1.00  
% 2.44/1.00  fof(f23,plain,(
% 2.44/1.00    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.44/1.00    inference(flattening,[],[f22])).
% 2.44/1.00  
% 2.44/1.00  fof(f56,plain,(
% 2.44/1.00    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 2.44/1.00    inference(cnf_transformation,[],[f23])).
% 2.44/1.00  
% 2.44/1.00  fof(f6,axiom,(
% 2.44/1.00    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 2.44/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.44/1.00  
% 2.44/1.00  fof(f21,plain,(
% 2.44/1.00    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 2.44/1.00    inference(ennf_transformation,[],[f6])).
% 2.44/1.00  
% 2.44/1.00  fof(f55,plain,(
% 2.44/1.00    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 2.44/1.00    inference(cnf_transformation,[],[f21])).
% 2.44/1.00  
% 2.44/1.00  fof(f78,plain,(
% 2.44/1.00    ( ! [X0,X1] : (m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 2.44/1.00    inference(definition_unfolding,[],[f55,f51])).
% 2.44/1.00  
% 2.44/1.00  fof(f73,plain,(
% 2.44/1.00    m1_subset_1(sK2,u1_struct_0(sK1))),
% 2.44/1.00    inference(cnf_transformation,[],[f49])).
% 2.44/1.00  
% 2.44/1.00  fof(f16,axiom,(
% 2.44/1.00    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) => k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))))))),
% 2.44/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.44/1.00  
% 2.44/1.00  fof(f38,plain,(
% 2.44/1.00    ! [X0] : (! [X1] : (! [X2] : ((k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) | ~r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.44/1.00    inference(ennf_transformation,[],[f16])).
% 2.44/1.00  
% 2.44/1.00  fof(f39,plain,(
% 2.44/1.00    ! [X0] : (! [X1] : (! [X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) | ~r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.44/1.00    inference(flattening,[],[f38])).
% 2.44/1.00  
% 2.44/1.00  fof(f68,plain,(
% 2.44/1.00    ( ! [X2,X0,X1] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) | ~r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.44/1.00    inference(cnf_transformation,[],[f39])).
% 2.44/1.00  
% 2.44/1.00  fof(f76,plain,(
% 2.44/1.00    k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3))),
% 2.44/1.00    inference(cnf_transformation,[],[f49])).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1,plain,
% 2.44/1.00      ( r2_hidden(X0,X1) | r1_xboole_0(k2_tarski(X0,X0),X1) ),
% 2.44/1.00      inference(cnf_transformation,[],[f77]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1201,plain,
% 2.44/1.00      ( r2_hidden(X0,X1) = iProver_top
% 2.44/1.00      | r1_xboole_0(k2_tarski(X0,X0),X1) = iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_0,plain,
% 2.44/1.00      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 2.44/1.00      inference(cnf_transformation,[],[f50]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1202,plain,
% 2.44/1.00      ( r1_xboole_0(X0,X1) != iProver_top
% 2.44/1.00      | r1_xboole_0(X1,X0) = iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1685,plain,
% 2.44/1.00      ( r2_hidden(X0,X1) = iProver_top
% 2.44/1.00      | r1_xboole_0(X1,k2_tarski(X0,X0)) = iProver_top ),
% 2.44/1.00      inference(superposition,[status(thm)],[c_1201,c_1202]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_20,negated_conjecture,
% 2.44/1.00      ( m1_subset_1(sK3,u1_struct_0(sK1)) ),
% 2.44/1.00      inference(cnf_transformation,[],[f74]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1194,plain,
% 2.44/1.00      ( m1_subset_1(sK3,u1_struct_0(sK1)) = iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_10,plain,
% 2.44/1.00      ( ~ m1_subset_1(X0,X1)
% 2.44/1.00      | v1_xboole_0(X1)
% 2.44/1.00      | k6_domain_1(X1,X0) = k2_tarski(X0,X0) ),
% 2.44/1.00      inference(cnf_transformation,[],[f79]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1196,plain,
% 2.44/1.00      ( k6_domain_1(X0,X1) = k2_tarski(X1,X1)
% 2.44/1.00      | m1_subset_1(X1,X0) != iProver_top
% 2.44/1.00      | v1_xboole_0(X0) = iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1516,plain,
% 2.44/1.00      ( k6_domain_1(u1_struct_0(sK1),sK3) = k2_tarski(sK3,sK3)
% 2.44/1.00      | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
% 2.44/1.00      inference(superposition,[status(thm)],[c_1194,c_1196]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_25,negated_conjecture,
% 2.44/1.00      ( ~ v2_struct_0(sK1) ),
% 2.44/1.00      inference(cnf_transformation,[],[f69]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_22,negated_conjecture,
% 2.44/1.00      ( l1_pre_topc(sK1) ),
% 2.44/1.00      inference(cnf_transformation,[],[f72]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_9,plain,
% 2.44/1.00      ( v2_struct_0(X0)
% 2.44/1.00      | ~ l1_struct_0(X0)
% 2.44/1.00      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.44/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_52,plain,
% 2.44/1.00      ( v2_struct_0(sK1)
% 2.44/1.00      | ~ l1_struct_0(sK1)
% 2.44/1.00      | ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 2.44/1.00      inference(instantiation,[status(thm)],[c_9]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_8,plain,
% 2.44/1.00      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 2.44/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_55,plain,
% 2.44/1.00      ( l1_struct_0(sK1) | ~ l1_pre_topc(sK1) ),
% 2.44/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1357,plain,
% 2.44/1.00      ( ~ m1_subset_1(sK3,u1_struct_0(sK1))
% 2.44/1.00      | v1_xboole_0(u1_struct_0(sK1))
% 2.44/1.00      | k6_domain_1(u1_struct_0(sK1),sK3) = k2_tarski(sK3,sK3) ),
% 2.44/1.00      inference(instantiation,[status(thm)],[c_10]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1813,plain,
% 2.44/1.00      ( k6_domain_1(u1_struct_0(sK1),sK3) = k2_tarski(sK3,sK3) ),
% 2.44/1.00      inference(global_propositional_subsumption,
% 2.44/1.00                [status(thm)],
% 2.44/1.00                [c_1516,c_25,c_22,c_20,c_52,c_55,c_1357]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_16,plain,
% 2.44/1.00      ( ~ v3_pre_topc(X0,X1)
% 2.44/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.44/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.44/1.00      | ~ r1_xboole_0(X0,X2)
% 2.44/1.00      | r1_xboole_0(X0,k2_pre_topc(X1,X2))
% 2.44/1.00      | ~ v2_pre_topc(X1)
% 2.44/1.00      | ~ l1_pre_topc(X1) ),
% 2.44/1.00      inference(cnf_transformation,[],[f67]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_24,negated_conjecture,
% 2.44/1.00      ( v2_pre_topc(sK1) ),
% 2.44/1.00      inference(cnf_transformation,[],[f70]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_428,plain,
% 2.44/1.00      ( ~ v3_pre_topc(X0,X1)
% 2.44/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.44/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.44/1.00      | ~ r1_xboole_0(X0,X2)
% 2.44/1.00      | r1_xboole_0(X0,k2_pre_topc(X1,X2))
% 2.44/1.00      | ~ l1_pre_topc(X1)
% 2.44/1.00      | sK1 != X1 ),
% 2.44/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_24]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_429,plain,
% 2.44/1.00      ( ~ v3_pre_topc(X0,sK1)
% 2.44/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.44/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.44/1.00      | ~ r1_xboole_0(X0,X1)
% 2.44/1.00      | r1_xboole_0(X0,k2_pre_topc(sK1,X1))
% 2.44/1.00      | ~ l1_pre_topc(sK1) ),
% 2.44/1.00      inference(unflattening,[status(thm)],[c_428]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_433,plain,
% 2.44/1.00      ( r1_xboole_0(X0,k2_pre_topc(sK1,X1))
% 2.44/1.00      | ~ r1_xboole_0(X0,X1)
% 2.44/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.44/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.44/1.00      | ~ v3_pre_topc(X0,sK1) ),
% 2.44/1.00      inference(global_propositional_subsumption,
% 2.44/1.00                [status(thm)],
% 2.44/1.00                [c_429,c_22]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_434,plain,
% 2.44/1.00      ( ~ v3_pre_topc(X0,sK1)
% 2.44/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.44/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.44/1.00      | ~ r1_xboole_0(X0,X1)
% 2.44/1.00      | r1_xboole_0(X0,k2_pre_topc(sK1,X1)) ),
% 2.44/1.00      inference(renaming,[status(thm)],[c_433]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_11,plain,
% 2.44/1.00      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
% 2.44/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.44/1.00      | ~ v2_pre_topc(X0)
% 2.44/1.00      | ~ l1_pre_topc(X0) ),
% 2.44/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_15,plain,
% 2.44/1.00      ( v3_pre_topc(X0,X1)
% 2.44/1.00      | ~ v4_pre_topc(X0,X1)
% 2.44/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.44/1.00      | ~ v3_tdlat_3(X1)
% 2.44/1.00      | ~ v2_pre_topc(X1)
% 2.44/1.00      | ~ l1_pre_topc(X1) ),
% 2.44/1.00      inference(cnf_transformation,[],[f63]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_394,plain,
% 2.44/1.00      ( v3_pre_topc(X0,X1)
% 2.44/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 2.44/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.44/1.00      | ~ v3_tdlat_3(X1)
% 2.44/1.00      | ~ v2_pre_topc(X3)
% 2.44/1.00      | ~ v2_pre_topc(X1)
% 2.44/1.00      | ~ l1_pre_topc(X3)
% 2.44/1.00      | ~ l1_pre_topc(X1)
% 2.44/1.00      | X1 != X3
% 2.44/1.00      | k2_pre_topc(X3,X2) != X0 ),
% 2.44/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_15]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_395,plain,
% 2.44/1.00      ( v3_pre_topc(k2_pre_topc(X0,X1),X0)
% 2.44/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.44/1.00      | ~ m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
% 2.44/1.00      | ~ v3_tdlat_3(X0)
% 2.44/1.00      | ~ v2_pre_topc(X0)
% 2.44/1.00      | ~ l1_pre_topc(X0) ),
% 2.44/1.00      inference(unflattening,[status(thm)],[c_394]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_7,plain,
% 2.44/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.44/1.00      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.44/1.00      | ~ l1_pre_topc(X1) ),
% 2.44/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_411,plain,
% 2.44/1.00      ( v3_pre_topc(k2_pre_topc(X0,X1),X0)
% 2.44/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.44/1.00      | ~ v3_tdlat_3(X0)
% 2.44/1.00      | ~ v2_pre_topc(X0)
% 2.44/1.00      | ~ l1_pre_topc(X0) ),
% 2.44/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_395,c_7]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_455,plain,
% 2.44/1.00      ( v3_pre_topc(k2_pre_topc(X0,X1),X0)
% 2.44/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.44/1.00      | ~ v3_tdlat_3(X0)
% 2.44/1.00      | ~ l1_pre_topc(X0)
% 2.44/1.00      | sK1 != X0 ),
% 2.44/1.00      inference(resolution_lifted,[status(thm)],[c_411,c_24]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_456,plain,
% 2.44/1.00      ( v3_pre_topc(k2_pre_topc(sK1,X0),sK1)
% 2.44/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.44/1.00      | ~ v3_tdlat_3(sK1)
% 2.44/1.00      | ~ l1_pre_topc(sK1) ),
% 2.44/1.00      inference(unflattening,[status(thm)],[c_455]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_23,negated_conjecture,
% 2.44/1.00      ( v3_tdlat_3(sK1) ),
% 2.44/1.00      inference(cnf_transformation,[],[f71]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_460,plain,
% 2.44/1.00      ( v3_pre_topc(k2_pre_topc(sK1,X0),sK1)
% 2.44/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.44/1.00      inference(global_propositional_subsumption,
% 2.44/1.00                [status(thm)],
% 2.44/1.00                [c_456,c_23,c_22]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_501,plain,
% 2.44/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.44/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.44/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.44/1.00      | ~ r1_xboole_0(X1,X2)
% 2.44/1.00      | r1_xboole_0(X1,k2_pre_topc(sK1,X2))
% 2.44/1.00      | k2_pre_topc(sK1,X0) != X1
% 2.44/1.00      | sK1 != sK1 ),
% 2.44/1.00      inference(resolution_lifted,[status(thm)],[c_434,c_460]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_502,plain,
% 2.44/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.44/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.44/1.00      | ~ m1_subset_1(k2_pre_topc(sK1,X1),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.44/1.00      | ~ r1_xboole_0(k2_pre_topc(sK1,X1),X0)
% 2.44/1.00      | r1_xboole_0(k2_pre_topc(sK1,X1),k2_pre_topc(sK1,X0)) ),
% 2.44/1.00      inference(unflattening,[status(thm)],[c_501]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_486,plain,
% 2.44/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.44/1.00      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.44/1.00      | sK1 != X1 ),
% 2.44/1.00      inference(resolution_lifted,[status(thm)],[c_7,c_22]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_487,plain,
% 2.44/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.44/1.00      | m1_subset_1(k2_pre_topc(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.44/1.00      inference(unflattening,[status(thm)],[c_486]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_516,plain,
% 2.44/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.44/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.44/1.00      | ~ r1_xboole_0(k2_pre_topc(sK1,X1),X0)
% 2.44/1.00      | r1_xboole_0(k2_pre_topc(sK1,X1),k2_pre_topc(sK1,X0)) ),
% 2.44/1.00      inference(forward_subsumption_resolution,
% 2.44/1.00                [status(thm)],
% 2.44/1.00                [c_502,c_487]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1189,plain,
% 2.44/1.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.44/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.44/1.00      | r1_xboole_0(k2_pre_topc(sK1,X0),X1) != iProver_top
% 2.44/1.00      | r1_xboole_0(k2_pre_topc(sK1,X0),k2_pre_topc(sK1,X1)) = iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_516]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_19,negated_conjecture,
% 2.44/1.00      ( ~ r1_xboole_0(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)),k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3))) ),
% 2.44/1.00      inference(cnf_transformation,[],[f75]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1195,plain,
% 2.44/1.00      ( r1_xboole_0(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)),k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3))) != iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1458,plain,
% 2.44/1.00      ( m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.44/1.00      | m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.44/1.00      | r1_xboole_0(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)),k6_domain_1(u1_struct_0(sK1),sK3)) != iProver_top ),
% 2.44/1.00      inference(superposition,[status(thm)],[c_1189,c_1195]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1816,plain,
% 2.44/1.00      ( m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.44/1.00      | m1_subset_1(k2_tarski(sK3,sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.44/1.00      | r1_xboole_0(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)),k2_tarski(sK3,sK3)) != iProver_top ),
% 2.44/1.00      inference(demodulation,[status(thm)],[c_1813,c_1458]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_26,plain,
% 2.44/1.00      ( v2_struct_0(sK1) != iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_29,plain,
% 2.44/1.00      ( l1_pre_topc(sK1) = iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_31,plain,
% 2.44/1.00      ( m1_subset_1(sK3,u1_struct_0(sK1)) = iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_51,plain,
% 2.44/1.00      ( v2_struct_0(X0) = iProver_top
% 2.44/1.00      | l1_struct_0(X0) != iProver_top
% 2.44/1.00      | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_53,plain,
% 2.44/1.00      ( v2_struct_0(sK1) = iProver_top
% 2.44/1.00      | l1_struct_0(sK1) != iProver_top
% 2.44/1.00      | v1_xboole_0(u1_struct_0(sK1)) != iProver_top ),
% 2.44/1.00      inference(instantiation,[status(thm)],[c_51]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_54,plain,
% 2.44/1.00      ( l1_struct_0(X0) = iProver_top | l1_pre_topc(X0) != iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_56,plain,
% 2.44/1.00      ( l1_struct_0(sK1) = iProver_top
% 2.44/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.44/1.00      inference(instantiation,[status(thm)],[c_54]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_5,plain,
% 2.44/1.00      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.44/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1567,plain,
% 2.44/1.00      ( ~ m1_subset_1(sK3,u1_struct_0(sK1))
% 2.44/1.00      | r2_hidden(sK3,u1_struct_0(sK1))
% 2.44/1.00      | v1_xboole_0(u1_struct_0(sK1)) ),
% 2.44/1.00      inference(instantiation,[status(thm)],[c_5]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1568,plain,
% 2.44/1.00      ( m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top
% 2.44/1.00      | r2_hidden(sK3,u1_struct_0(sK1)) = iProver_top
% 2.44/1.00      | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_1567]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_4,plain,
% 2.44/1.00      ( m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1))
% 2.44/1.00      | ~ r2_hidden(X0,X1) ),
% 2.44/1.00      inference(cnf_transformation,[],[f78]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1326,plain,
% 2.44/1.00      ( m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.44/1.00      | ~ r2_hidden(X0,u1_struct_0(sK1)) ),
% 2.44/1.00      inference(instantiation,[status(thm)],[c_4]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1639,plain,
% 2.44/1.00      ( m1_subset_1(k2_tarski(sK3,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.44/1.00      | ~ r2_hidden(sK3,u1_struct_0(sK1)) ),
% 2.44/1.00      inference(instantiation,[status(thm)],[c_1326]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1640,plain,
% 2.44/1.00      ( m1_subset_1(k2_tarski(sK3,sK3),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 2.44/1.00      | r2_hidden(sK3,u1_struct_0(sK1)) != iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_1639]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_2106,plain,
% 2.44/1.00      ( m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.44/1.00      | r1_xboole_0(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)),k2_tarski(sK3,sK3)) != iProver_top ),
% 2.44/1.00      inference(global_propositional_subsumption,
% 2.44/1.00                [status(thm)],
% 2.44/1.00                [c_1816,c_26,c_29,c_31,c_53,c_56,c_1568,c_1640]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_21,negated_conjecture,
% 2.44/1.00      ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 2.44/1.00      inference(cnf_transformation,[],[f73]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1193,plain,
% 2.44/1.00      ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1517,plain,
% 2.44/1.00      ( k6_domain_1(u1_struct_0(sK1),sK2) = k2_tarski(sK2,sK2)
% 2.44/1.00      | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
% 2.44/1.00      inference(superposition,[status(thm)],[c_1193,c_1196]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1360,plain,
% 2.44/1.00      ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 2.44/1.00      | v1_xboole_0(u1_struct_0(sK1))
% 2.44/1.00      | k6_domain_1(u1_struct_0(sK1),sK2) = k2_tarski(sK2,sK2) ),
% 2.44/1.00      inference(instantiation,[status(thm)],[c_10]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1922,plain,
% 2.44/1.00      ( k6_domain_1(u1_struct_0(sK1),sK2) = k2_tarski(sK2,sK2) ),
% 2.44/1.00      inference(global_propositional_subsumption,
% 2.44/1.00                [status(thm)],
% 2.44/1.00                [c_1517,c_25,c_22,c_21,c_52,c_55,c_1360]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_2110,plain,
% 2.44/1.00      ( m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.44/1.00      | r1_xboole_0(k2_pre_topc(sK1,k2_tarski(sK2,sK2)),k2_tarski(sK3,sK3)) != iProver_top ),
% 2.44/1.00      inference(light_normalisation,[status(thm)],[c_2106,c_1922]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_30,plain,
% 2.44/1.00      ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1570,plain,
% 2.44/1.00      ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 2.44/1.00      | r2_hidden(sK2,u1_struct_0(sK1))
% 2.44/1.00      | v1_xboole_0(u1_struct_0(sK1)) ),
% 2.44/1.00      inference(instantiation,[status(thm)],[c_5]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1571,plain,
% 2.44/1.00      ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 2.44/1.00      | r2_hidden(sK2,u1_struct_0(sK1)) = iProver_top
% 2.44/1.00      | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_1570]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1648,plain,
% 2.44/1.00      ( m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.44/1.00      | ~ r2_hidden(sK2,u1_struct_0(sK1)) ),
% 2.44/1.00      inference(instantiation,[status(thm)],[c_1326]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1649,plain,
% 2.44/1.00      ( m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 2.44/1.00      | r2_hidden(sK2,u1_struct_0(sK1)) != iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_1648]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1817,plain,
% 2.44/1.00      ( r1_xboole_0(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)),k2_pre_topc(sK1,k2_tarski(sK3,sK3))) != iProver_top ),
% 2.44/1.00      inference(demodulation,[status(thm)],[c_1813,c_1195]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1925,plain,
% 2.44/1.00      ( r1_xboole_0(k2_pre_topc(sK1,k2_tarski(sK2,sK2)),k2_pre_topc(sK1,k2_tarski(sK3,sK3))) != iProver_top ),
% 2.44/1.00      inference(demodulation,[status(thm)],[c_1922,c_1817]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1990,plain,
% 2.44/1.00      ( m1_subset_1(k2_tarski(sK3,sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.44/1.00      | m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.44/1.00      | r1_xboole_0(k2_pre_topc(sK1,k2_tarski(sK2,sK2)),k2_tarski(sK3,sK3)) != iProver_top ),
% 2.44/1.00      inference(superposition,[status(thm)],[c_1189,c_1925]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_2114,plain,
% 2.44/1.00      ( r1_xboole_0(k2_pre_topc(sK1,k2_tarski(sK2,sK2)),k2_tarski(sK3,sK3)) != iProver_top ),
% 2.44/1.00      inference(global_propositional_subsumption,
% 2.44/1.00                [status(thm)],
% 2.44/1.00                [c_2110,c_26,c_29,c_30,c_31,c_53,c_56,c_1568,c_1571,
% 2.44/1.00                 c_1640,c_1649,c_1990]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_2996,plain,
% 2.44/1.00      ( r2_hidden(sK3,k2_pre_topc(sK1,k2_tarski(sK2,sK2))) = iProver_top ),
% 2.44/1.00      inference(superposition,[status(thm)],[c_1685,c_2114]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_17,plain,
% 2.44/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.44/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.44/1.00      | ~ r2_hidden(X2,k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X0)))
% 2.44/1.00      | ~ v3_tdlat_3(X1)
% 2.44/1.00      | ~ v2_pre_topc(X1)
% 2.44/1.00      | v2_struct_0(X1)
% 2.44/1.00      | ~ l1_pre_topc(X1)
% 2.44/1.00      | k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X0)) = k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2)) ),
% 2.44/1.00      inference(cnf_transformation,[],[f68]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_284,plain,
% 2.44/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.44/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.44/1.00      | ~ r2_hidden(X0,k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2)))
% 2.44/1.00      | ~ v3_tdlat_3(X1)
% 2.44/1.00      | ~ v2_pre_topc(X1)
% 2.44/1.00      | ~ l1_pre_topc(X1)
% 2.44/1.00      | k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X0)) = k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2))
% 2.44/1.00      | sK1 != X1 ),
% 2.44/1.00      inference(resolution_lifted,[status(thm)],[c_17,c_25]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_285,plain,
% 2.44/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.44/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.44/1.00      | ~ r2_hidden(X1,k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X0)))
% 2.44/1.00      | ~ v3_tdlat_3(sK1)
% 2.44/1.00      | ~ v2_pre_topc(sK1)
% 2.44/1.00      | ~ l1_pre_topc(sK1)
% 2.44/1.00      | k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X1)) = k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X0)) ),
% 2.44/1.00      inference(unflattening,[status(thm)],[c_284]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_289,plain,
% 2.44/1.00      ( ~ r2_hidden(X1,k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X0)))
% 2.44/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.44/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.44/1.00      | k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X1)) = k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X0)) ),
% 2.44/1.00      inference(global_propositional_subsumption,
% 2.44/1.00                [status(thm)],
% 2.44/1.00                [c_285,c_24,c_23,c_22]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_290,plain,
% 2.44/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.44/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.44/1.00      | ~ r2_hidden(X1,k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X0)))
% 2.44/1.00      | k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X1)) = k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X0)) ),
% 2.44/1.00      inference(renaming,[status(thm)],[c_289]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1192,plain,
% 2.44/1.00      ( k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X0)) = k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X1))
% 2.44/1.00      | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
% 2.44/1.00      | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
% 2.44/1.00      | r2_hidden(X0,k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X1))) != iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_290]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1932,plain,
% 2.44/1.00      ( k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X0)) = k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2))
% 2.44/1.00      | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
% 2.44/1.00      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 2.44/1.00      | r2_hidden(X0,k2_pre_topc(sK1,k2_tarski(sK2,sK2))) != iProver_top ),
% 2.44/1.00      inference(superposition,[status(thm)],[c_1922,c_1192]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1933,plain,
% 2.44/1.00      ( k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X0)) = k2_pre_topc(sK1,k2_tarski(sK2,sK2))
% 2.44/1.00      | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
% 2.44/1.00      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 2.44/1.00      | r2_hidden(X0,k2_pre_topc(sK1,k2_tarski(sK2,sK2))) != iProver_top ),
% 2.44/1.00      inference(light_normalisation,[status(thm)],[c_1932,c_1922]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_2601,plain,
% 2.44/1.00      ( m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
% 2.44/1.00      | k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X0)) = k2_pre_topc(sK1,k2_tarski(sK2,sK2))
% 2.44/1.00      | r2_hidden(X0,k2_pre_topc(sK1,k2_tarski(sK2,sK2))) != iProver_top ),
% 2.44/1.00      inference(global_propositional_subsumption,
% 2.44/1.00                [status(thm)],
% 2.44/1.00                [c_1933,c_30]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_2602,plain,
% 2.44/1.00      ( k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X0)) = k2_pre_topc(sK1,k2_tarski(sK2,sK2))
% 2.44/1.00      | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
% 2.44/1.00      | r2_hidden(X0,k2_pre_topc(sK1,k2_tarski(sK2,sK2))) != iProver_top ),
% 2.44/1.00      inference(renaming,[status(thm)],[c_2601]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_5866,plain,
% 2.44/1.00      ( k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3)) = k2_pre_topc(sK1,k2_tarski(sK2,sK2))
% 2.44/1.00      | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top ),
% 2.44/1.00      inference(superposition,[status(thm)],[c_2996,c_2602]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_5869,plain,
% 2.44/1.00      ( k2_pre_topc(sK1,k2_tarski(sK2,sK2)) = k2_pre_topc(sK1,k2_tarski(sK3,sK3))
% 2.44/1.00      | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top ),
% 2.44/1.00      inference(light_normalisation,[status(thm)],[c_5866,c_1813]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_18,negated_conjecture,
% 2.44/1.00      ( k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3)) ),
% 2.44/1.00      inference(cnf_transformation,[],[f76]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1818,plain,
% 2.44/1.00      ( k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)) != k2_pre_topc(sK1,k2_tarski(sK3,sK3)) ),
% 2.44/1.00      inference(demodulation,[status(thm)],[c_1813,c_18]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1926,plain,
% 2.44/1.00      ( k2_pre_topc(sK1,k2_tarski(sK2,sK2)) != k2_pre_topc(sK1,k2_tarski(sK3,sK3)) ),
% 2.44/1.00      inference(demodulation,[status(thm)],[c_1922,c_1818]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(contradiction,plain,
% 2.44/1.00      ( $false ),
% 2.44/1.00      inference(minisat,[status(thm)],[c_5869,c_1926,c_31]) ).
% 2.44/1.00  
% 2.44/1.00  
% 2.44/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.44/1.00  
% 2.44/1.00  ------                               Statistics
% 2.44/1.00  
% 2.44/1.00  ------ General
% 2.44/1.00  
% 2.44/1.00  abstr_ref_over_cycles:                  0
% 2.44/1.00  abstr_ref_under_cycles:                 0
% 2.44/1.00  gc_basic_clause_elim:                   0
% 2.44/1.00  forced_gc_time:                         0
% 2.44/1.00  parsing_time:                           0.01
% 2.44/1.00  unif_index_cands_time:                  0.
% 2.44/1.00  unif_index_add_time:                    0.
% 2.44/1.00  orderings_time:                         0.
% 2.44/1.00  out_proof_time:                         0.012
% 2.44/1.00  total_time:                             0.22
% 2.44/1.00  num_of_symbols:                         52
% 2.44/1.00  num_of_terms:                           5619
% 2.44/1.00  
% 2.44/1.00  ------ Preprocessing
% 2.44/1.00  
% 2.44/1.00  num_of_splits:                          0
% 2.44/1.00  num_of_split_atoms:                     0
% 2.44/1.00  num_of_reused_defs:                     0
% 2.44/1.00  num_eq_ax_congr_red:                    16
% 2.44/1.00  num_of_sem_filtered_clauses:            1
% 2.44/1.00  num_of_subtypes:                        0
% 2.44/1.00  monotx_restored_types:                  0
% 2.44/1.00  sat_num_of_epr_types:                   0
% 2.44/1.00  sat_num_of_non_cyclic_types:            0
% 2.44/1.00  sat_guarded_non_collapsed_types:        0
% 2.44/1.00  num_pure_diseq_elim:                    0
% 2.44/1.00  simp_replaced_by:                       0
% 2.44/1.00  res_preprocessed:                       95
% 2.44/1.00  prep_upred:                             0
% 2.44/1.00  prep_unflattend:                        32
% 2.44/1.00  smt_new_axioms:                         0
% 2.44/1.00  pred_elim_cands:                        4
% 2.44/1.00  pred_elim:                              7
% 2.44/1.00  pred_elim_cl:                           10
% 2.44/1.00  pred_elim_cycles:                       11
% 2.44/1.00  merged_defs:                            0
% 2.44/1.00  merged_defs_ncl:                        0
% 2.44/1.00  bin_hyper_res:                          0
% 2.44/1.00  prep_cycles:                            4
% 2.44/1.00  pred_elim_time:                         0.009
% 2.44/1.00  splitting_time:                         0.
% 2.44/1.00  sem_filter_time:                        0.
% 2.44/1.00  monotx_time:                            0.001
% 2.44/1.00  subtype_inf_time:                       0.
% 2.44/1.00  
% 2.44/1.00  ------ Problem properties
% 2.44/1.00  
% 2.44/1.00  clauses:                                16
% 2.44/1.00  conjectures:                            4
% 2.44/1.00  epr:                                    2
% 2.44/1.00  horn:                                   13
% 2.44/1.00  ground:                                 5
% 2.44/1.00  unary:                                  7
% 2.44/1.00  binary:                                 4
% 2.44/1.00  lits:                                   32
% 2.44/1.00  lits_eq:                                4
% 2.44/1.00  fd_pure:                                0
% 2.44/1.00  fd_pseudo:                              0
% 2.44/1.00  fd_cond:                                0
% 2.44/1.00  fd_pseudo_cond:                         0
% 2.44/1.00  ac_symbols:                             0
% 2.44/1.00  
% 2.44/1.00  ------ Propositional Solver
% 2.44/1.00  
% 2.44/1.00  prop_solver_calls:                      29
% 2.44/1.00  prop_fast_solver_calls:                 786
% 2.44/1.00  smt_solver_calls:                       0
% 2.44/1.00  smt_fast_solver_calls:                  0
% 2.44/1.00  prop_num_of_clauses:                    2336
% 2.44/1.00  prop_preprocess_simplified:             5229
% 2.44/1.00  prop_fo_subsumed:                       18
% 2.44/1.00  prop_solver_time:                       0.
% 2.44/1.00  smt_solver_time:                        0.
% 2.44/1.00  smt_fast_solver_time:                   0.
% 2.44/1.00  prop_fast_solver_time:                  0.
% 2.44/1.00  prop_unsat_core_time:                   0.
% 2.44/1.00  
% 2.44/1.00  ------ QBF
% 2.44/1.00  
% 2.44/1.00  qbf_q_res:                              0
% 2.44/1.00  qbf_num_tautologies:                    0
% 2.44/1.00  qbf_prep_cycles:                        0
% 2.44/1.00  
% 2.44/1.00  ------ BMC1
% 2.44/1.00  
% 2.44/1.00  bmc1_current_bound:                     -1
% 2.44/1.00  bmc1_last_solved_bound:                 -1
% 2.44/1.00  bmc1_unsat_core_size:                   -1
% 2.44/1.00  bmc1_unsat_core_parents_size:           -1
% 2.44/1.00  bmc1_merge_next_fun:                    0
% 2.44/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.44/1.00  
% 2.44/1.00  ------ Instantiation
% 2.44/1.00  
% 2.44/1.00  inst_num_of_clauses:                    762
% 2.44/1.00  inst_num_in_passive:                    98
% 2.44/1.00  inst_num_in_active:                     384
% 2.44/1.00  inst_num_in_unprocessed:                280
% 2.44/1.00  inst_num_of_loops:                      420
% 2.44/1.00  inst_num_of_learning_restarts:          0
% 2.44/1.00  inst_num_moves_active_passive:          33
% 2.44/1.00  inst_lit_activity:                      0
% 2.44/1.00  inst_lit_activity_moves:                0
% 2.44/1.00  inst_num_tautologies:                   0
% 2.44/1.00  inst_num_prop_implied:                  0
% 2.44/1.00  inst_num_existing_simplified:           0
% 2.44/1.00  inst_num_eq_res_simplified:             0
% 2.44/1.00  inst_num_child_elim:                    0
% 2.44/1.00  inst_num_of_dismatching_blockings:      260
% 2.44/1.00  inst_num_of_non_proper_insts:           735
% 2.44/1.00  inst_num_of_duplicates:                 0
% 2.44/1.00  inst_inst_num_from_inst_to_res:         0
% 2.44/1.00  inst_dismatching_checking_time:         0.
% 2.44/1.00  
% 2.44/1.00  ------ Resolution
% 2.44/1.00  
% 2.44/1.00  res_num_of_clauses:                     0
% 2.44/1.00  res_num_in_passive:                     0
% 2.44/1.00  res_num_in_active:                      0
% 2.44/1.00  res_num_of_loops:                       99
% 2.44/1.00  res_forward_subset_subsumed:            62
% 2.44/1.00  res_backward_subset_subsumed:           0
% 2.44/1.00  res_forward_subsumed:                   0
% 2.44/1.00  res_backward_subsumed:                  0
% 2.44/1.00  res_forward_subsumption_resolution:     2
% 2.44/1.00  res_backward_subsumption_resolution:    0
% 2.44/1.00  res_clause_to_clause_subsumption:       1034
% 2.44/1.00  res_orphan_elimination:                 0
% 2.44/1.00  res_tautology_del:                      52
% 2.44/1.00  res_num_eq_res_simplified:              0
% 2.44/1.00  res_num_sel_changes:                    0
% 2.44/1.00  res_moves_from_active_to_pass:          0
% 2.44/1.00  
% 2.44/1.00  ------ Superposition
% 2.44/1.00  
% 2.44/1.00  sup_time_total:                         0.
% 2.44/1.00  sup_time_generating:                    0.
% 2.44/1.00  sup_time_sim_full:                      0.
% 2.44/1.00  sup_time_sim_immed:                     0.
% 2.44/1.00  
% 2.44/1.00  sup_num_of_clauses:                     127
% 2.44/1.00  sup_num_in_active:                      79
% 2.44/1.00  sup_num_in_passive:                     48
% 2.44/1.00  sup_num_of_loops:                       83
% 2.44/1.00  sup_fw_superposition:                   100
% 2.44/1.00  sup_bw_superposition:                   19
% 2.44/1.00  sup_immediate_simplified:               4
% 2.44/1.00  sup_given_eliminated:                   0
% 2.44/1.00  comparisons_done:                       0
% 2.44/1.00  comparisons_avoided:                    0
% 2.44/1.00  
% 2.44/1.00  ------ Simplifications
% 2.44/1.00  
% 2.44/1.00  
% 2.44/1.00  sim_fw_subset_subsumed:                 1
% 2.44/1.00  sim_bw_subset_subsumed:                 0
% 2.44/1.00  sim_fw_subsumed:                        0
% 2.44/1.00  sim_bw_subsumed:                        0
% 2.44/1.00  sim_fw_subsumption_res:                 0
% 2.44/1.00  sim_bw_subsumption_res:                 0
% 2.44/1.00  sim_tautology_del:                      1
% 2.44/1.00  sim_eq_tautology_del:                   0
% 2.44/1.00  sim_eq_res_simp:                        0
% 2.44/1.00  sim_fw_demodulated:                     0
% 2.44/1.00  sim_bw_demodulated:                     5
% 2.44/1.00  sim_light_normalised:                   5
% 2.44/1.00  sim_joinable_taut:                      0
% 2.44/1.00  sim_joinable_simp:                      0
% 2.44/1.00  sim_ac_normalised:                      0
% 2.44/1.00  sim_smt_subsumption:                    0
% 2.44/1.00  
%------------------------------------------------------------------------------
