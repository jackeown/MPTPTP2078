%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:27:33 EST 2020

% Result     : Theorem 3.58s
% Output     : CNFRefutation 3.58s
% Verified   : 
% Statistics : Number of formulae       :  184 ( 984 expanded)
%              Number of clauses        :  110 ( 278 expanded)
%              Number of leaves         :   23 ( 276 expanded)
%              Depth                    :   19
%              Number of atoms          :  651 (4991 expanded)
%              Number of equality atoms :  209 ( 944 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_tarski(X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f54,f53])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(rectify,[],[f1])).

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

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f40])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f41])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f38,plain,(
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

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))
          & ~ r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK4)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
        & ~ r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK4)))
        & m1_subset_1(sK4,u1_struct_0(X0)) ) ) ),
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
            ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))
            & ~ r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK3)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
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
              ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X1)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X2))
              & ~ r1_xboole_0(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X1)),k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X2)))
              & m1_subset_1(X2,u1_struct_0(sK2)) )
          & m1_subset_1(X1,u1_struct_0(sK2)) )
      & l1_pre_topc(sK2)
      & v3_tdlat_3(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))
    & ~ r1_xboole_0(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)),k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)))
    & m1_subset_1(sK4,u1_struct_0(sK2))
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & l1_pre_topc(sK2)
    & v3_tdlat_3(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f39,f48,f47,f46])).

fof(f73,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f49])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k2_tarski(X1,X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f62,f53])).

fof(f69,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f72,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f57,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f56,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
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

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X1,k2_pre_topc(X0,X2))
      | ~ v3_pre_topc(X1,X0)
      | ~ r1_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f70,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f74,plain,(
    m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f49])).

fof(f75,plain,(
    ~ r1_xboole_0(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)),k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))) ),
    inference(cnf_transformation,[],[f49])).

fof(f71,plain,(
    v3_tdlat_3(sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
             => v3_pre_topc(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(nnf_transformation,[],[f33])).

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
     => ( ~ v3_pre_topc(sK1(X0),X0)
        & v4_pre_topc(sK1(X0),X0)
        & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f43,f44])).

fof(f63,plain,(
    ! [X2,X0] :
      ( v3_pre_topc(X2,X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
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

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

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
    inference(cnf_transformation,[],[f37])).

fof(f76,plain,(
    k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_3,plain,
    ( r2_hidden(X0,X1)
    | r1_xboole_0(k2_tarski(X0,X0),X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_247,plain,
    ( r2_hidden(X0_50,X1_50)
    | r1_xboole_0(k2_tarski(X0_50,X0_50),X1_50) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_690,plain,
    ( r2_hidden(X0_50,X1_50) = iProver_top
    | r1_xboole_0(k2_tarski(X0_50,X0_50),X1_50) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_247])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_249,plain,
    ( r2_hidden(sK0(X0_50,X1_50),X1_50)
    | r1_xboole_0(X0_50,X1_50) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_688,plain,
    ( r2_hidden(sK0(X0_50,X1_50),X1_50) = iProver_top
    | r1_xboole_0(X0_50,X1_50) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_249])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_248,plain,
    ( r2_hidden(sK0(X0_50,X1_50),X0_50)
    | r1_xboole_0(X0_50,X1_50) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_689,plain,
    ( r2_hidden(sK0(X0_50,X1_50),X0_50) = iProver_top
    | r1_xboole_0(X0_50,X1_50) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_248])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_250,plain,
    ( ~ r2_hidden(X0_50,X1_50)
    | ~ r2_hidden(X0_50,X2_50)
    | ~ r1_xboole_0(X2_50,X1_50) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_687,plain,
    ( r2_hidden(X0_50,X1_50) != iProver_top
    | r2_hidden(X0_50,X2_50) != iProver_top
    | r1_xboole_0(X2_50,X1_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_250])).

cnf(c_1265,plain,
    ( r2_hidden(sK0(X0_50,X1_50),X2_50) != iProver_top
    | r1_xboole_0(X2_50,X0_50) != iProver_top
    | r1_xboole_0(X0_50,X1_50) = iProver_top ),
    inference(superposition,[status(thm)],[c_689,c_687])).

cnf(c_1508,plain,
    ( r1_xboole_0(X0_50,X1_50) != iProver_top
    | r1_xboole_0(X1_50,X0_50) = iProver_top ),
    inference(superposition,[status(thm)],[c_688,c_1265])).

cnf(c_1652,plain,
    ( r2_hidden(X0_50,X1_50) = iProver_top
    | r1_xboole_0(X1_50,k2_tarski(X0_50,X0_50)) = iProver_top ),
    inference(superposition,[status(thm)],[c_690,c_1508])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_229,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_707,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_229])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_239,plain,
    ( ~ m1_subset_1(X0_50,X0_51)
    | v1_xboole_0(X0_51)
    | k6_domain_1(X0_51,X0_50) = k2_tarski(X0_50,X0_50) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_698,plain,
    ( k6_domain_1(X0_51,X0_50) = k2_tarski(X0_50,X0_50)
    | m1_subset_1(X0_50,X0_51) != iProver_top
    | v1_xboole_0(X0_51) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_239])).

cnf(c_1868,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK3) = k2_tarski(sK3,sK3)
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_707,c_698])).

cnf(c_25,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_22,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_6,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_61,plain,
    ( v2_struct_0(sK2)
    | ~ v1_xboole_0(u1_struct_0(sK2))
    | ~ l1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_5,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_64,plain,
    ( l1_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_976,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2))
    | k6_domain_1(u1_struct_0(sK2),sK3) = k2_tarski(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_239])).

cnf(c_2300,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK3) = k2_tarski(sK3,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1868,c_25,c_22,c_21,c_61,c_64,c_976])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_240,plain,
    ( ~ m1_subset_1(X0_50,X0_51)
    | m1_subset_1(k6_domain_1(X0_51,X0_50),k1_zfmisc_1(X0_51))
    | v1_xboole_0(X0_51) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_697,plain,
    ( m1_subset_1(X0_50,X0_51) != iProver_top
    | m1_subset_1(k6_domain_1(X0_51,X0_50),k1_zfmisc_1(X0_51)) = iProver_top
    | v1_xboole_0(X0_51) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_240])).

cnf(c_2310,plain,
    ( m1_subset_1(k2_tarski(sK3,sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2300,c_697])).

cnf(c_26,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_29,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_30,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_60,plain,
    ( v2_struct_0(X0) = iProver_top
    | v1_xboole_0(u1_struct_0(X0)) != iProver_top
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_62,plain,
    ( v2_struct_0(sK2) = iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) != iProver_top
    | l1_struct_0(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_60])).

cnf(c_63,plain,
    ( l1_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_65,plain,
    ( l1_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_63])).

cnf(c_2507,plain,
    ( m1_subset_1(k2_tarski(sK3,sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2310,c_26,c_29,c_30,c_62,c_65])).

cnf(c_16,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_xboole_0(X0,X2)
    | r1_xboole_0(X0,k2_pre_topc(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_234,plain,
    ( ~ v3_pre_topc(X0_50,X0_49)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(X0_49)))
    | ~ m1_subset_1(X1_50,k1_zfmisc_1(u1_struct_0(X0_49)))
    | ~ r1_xboole_0(X0_50,X1_50)
    | r1_xboole_0(X0_50,k2_pre_topc(X0_49,X1_50))
    | ~ v2_pre_topc(X0_49)
    | ~ l1_pre_topc(X0_49) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_703,plain,
    ( v3_pre_topc(X0_50,X0_49) != iProver_top
    | m1_subset_1(X1_50,k1_zfmisc_1(u1_struct_0(X0_49))) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(X0_49))) != iProver_top
    | r1_xboole_0(X0_50,X1_50) != iProver_top
    | r1_xboole_0(X0_50,k2_pre_topc(X0_49,X1_50)) = iProver_top
    | v2_pre_topc(X0_49) != iProver_top
    | l1_pre_topc(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_234])).

cnf(c_3078,plain,
    ( v3_pre_topc(X0_50,sK2) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_xboole_0(X0_50,k2_pre_topc(sK2,k2_tarski(sK3,sK3))) = iProver_top
    | r1_xboole_0(X0_50,k2_tarski(sK3,sK3)) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2507,c_703])).

cnf(c_24,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_27,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_4466,plain,
    ( v3_pre_topc(X0_50,sK2) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_xboole_0(X0_50,k2_pre_topc(sK2,k2_tarski(sK3,sK3))) = iProver_top
    | r1_xboole_0(X0_50,k2_tarski(sK3,sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3078,c_27,c_29])).

cnf(c_4476,plain,
    ( v3_pre_topc(X0_50,sK2) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_xboole_0(X0_50,k2_tarski(sK3,sK3)) != iProver_top
    | r1_xboole_0(k2_pre_topc(sK2,k2_tarski(sK3,sK3)),X0_50) = iProver_top ),
    inference(superposition,[status(thm)],[c_4466,c_1508])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_230,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_706,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_230])).

cnf(c_1867,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK4) = k2_tarski(sK4,sK4)
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_706,c_698])).

cnf(c_973,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2))
    | k6_domain_1(u1_struct_0(sK2),sK4) = k2_tarski(sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_239])).

cnf(c_2208,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK4) = k2_tarski(sK4,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1867,c_25,c_22,c_20,c_61,c_64,c_973])).

cnf(c_19,negated_conjecture,
    ( ~ r1_xboole_0(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)),k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_231,negated_conjecture,
    ( ~ r1_xboole_0(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)),k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_705,plain,
    ( r1_xboole_0(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)),k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_231])).

cnf(c_2211,plain,
    ( r1_xboole_0(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)),k2_pre_topc(sK2,k2_tarski(sK4,sK4))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2208,c_705])).

cnf(c_2303,plain,
    ( r1_xboole_0(k2_pre_topc(sK2,k2_tarski(sK3,sK3)),k2_pre_topc(sK2,k2_tarski(sK4,sK4))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2300,c_2211])).

cnf(c_5963,plain,
    ( v3_pre_topc(k2_pre_topc(sK2,k2_tarski(sK4,sK4)),sK2) != iProver_top
    | m1_subset_1(k2_pre_topc(sK2,k2_tarski(sK4,sK4)),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_xboole_0(k2_pre_topc(sK2,k2_tarski(sK4,sK4)),k2_tarski(sK3,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4476,c_2303])).

cnf(c_23,negated_conjecture,
    ( v3_tdlat_3(sK2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_28,plain,
    ( v3_tdlat_3(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_31,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_946,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_240])).

cnf(c_947,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_946])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_246,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(X0_49)))
    | m1_subset_1(k2_pre_topc(X0_49,X0_50),k1_zfmisc_1(u1_struct_0(X0_49)))
    | ~ l1_pre_topc(X0_49) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1031,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_246])).

cnf(c_1032,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK4),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1031])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k2_pre_topc(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_243,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(X0_49)))
    | ~ l1_pre_topc(X0_49)
    | k2_pre_topc(X0_49,k2_pre_topc(X0_49,X0_50)) = k2_pre_topc(X0_49,X0_50) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1029,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | k2_pre_topc(sK2,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))) = k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)) ),
    inference(instantiation,[status(thm)],[c_243])).

cnf(c_15,plain,
    ( v3_pre_topc(X0,X1)
    | ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_235,plain,
    ( v3_pre_topc(X0_50,X0_49)
    | ~ v4_pre_topc(X0_50,X0_49)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(X0_49)))
    | ~ v3_tdlat_3(X0_49)
    | ~ v2_pre_topc(X0_49)
    | ~ l1_pre_topc(X0_49) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1156,plain,
    ( v3_pre_topc(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)),sK2)
    | ~ v4_pre_topc(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)),sK2)
    | ~ m1_subset_1(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v3_tdlat_3(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_235])).

cnf(c_1166,plain,
    ( v3_pre_topc(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)),sK2) = iProver_top
    | v4_pre_topc(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)),sK2) != iProver_top
    | m1_subset_1(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v3_tdlat_3(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1156])).

cnf(c_8,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_242,plain,
    ( v4_pre_topc(X0_50,X0_49)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(X0_49)))
    | ~ v2_pre_topc(X0_49)
    | ~ l1_pre_topc(X0_49)
    | k2_pre_topc(X0_49,X0_50) != X0_50 ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1155,plain,
    ( v4_pre_topc(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)),sK2)
    | ~ m1_subset_1(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | k2_pre_topc(sK2,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)) ),
    inference(instantiation,[status(thm)],[c_242])).

cnf(c_1168,plain,
    ( k2_pre_topc(sK2,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))
    | v4_pre_topc(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)),sK2) = iProver_top
    | m1_subset_1(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1155])).

cnf(c_2218,plain,
    ( m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2208,c_697])).

cnf(c_253,plain,
    ( X0_50 != X1_50
    | X2_50 != X1_50
    | X2_50 = X0_50 ),
    theory(equality)).

cnf(c_1292,plain,
    ( X0_50 != X1_50
    | X0_50 = k6_domain_1(u1_struct_0(sK2),sK4)
    | k6_domain_1(u1_struct_0(sK2),sK4) != X1_50 ),
    inference(instantiation,[status(thm)],[c_253])).

cnf(c_2143,plain,
    ( X0_50 = k6_domain_1(u1_struct_0(sK2),sK4)
    | X0_50 != k2_tarski(sK4,sK4)
    | k6_domain_1(u1_struct_0(sK2),sK4) != k2_tarski(sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_1292])).

cnf(c_2378,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK4) != k2_tarski(sK4,sK4)
    | k2_tarski(sK4,sK4) = k6_domain_1(u1_struct_0(sK2),sK4)
    | k2_tarski(sK4,sK4) != k2_tarski(sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_2143])).

cnf(c_252,plain,
    ( X0_50 = X0_50 ),
    theory(equality)).

cnf(c_2379,plain,
    ( k2_tarski(sK4,sK4) = k2_tarski(sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_252])).

cnf(c_256,plain,
    ( X0_50 != X1_50
    | k2_pre_topc(X0_49,X0_50) = k2_pre_topc(X0_49,X1_50) ),
    theory(equality)).

cnf(c_1801,plain,
    ( X0_50 != k6_domain_1(u1_struct_0(sK2),sK4)
    | k2_pre_topc(sK2,X0_50) = k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)) ),
    inference(instantiation,[status(thm)],[c_256])).

cnf(c_3289,plain,
    ( k2_pre_topc(sK2,k2_tarski(sK4,sK4)) = k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))
    | k2_tarski(sK4,sK4) != k6_domain_1(u1_struct_0(sK2),sK4) ),
    inference(instantiation,[status(thm)],[c_1801])).

cnf(c_5465,plain,
    ( m1_subset_1(k2_pre_topc(sK2,k2_tarski(sK4,sK4)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_246])).

cnf(c_5466,plain,
    ( m1_subset_1(k2_pre_topc(sK2,k2_tarski(sK4,sK4)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5465])).

cnf(c_260,plain,
    ( ~ v3_pre_topc(X0_50,X0_49)
    | v3_pre_topc(X1_50,X0_49)
    | X1_50 != X0_50 ),
    theory(equality)).

cnf(c_1491,plain,
    ( v3_pre_topc(X0_50,sK2)
    | ~ v3_pre_topc(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)),sK2)
    | X0_50 != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)) ),
    inference(instantiation,[status(thm)],[c_260])).

cnf(c_5890,plain,
    ( ~ v3_pre_topc(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)),sK2)
    | v3_pre_topc(k2_pre_topc(sK2,k2_tarski(sK4,sK4)),sK2)
    | k2_pre_topc(sK2,k2_tarski(sK4,sK4)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)) ),
    inference(instantiation,[status(thm)],[c_1491])).

cnf(c_5895,plain,
    ( k2_pre_topc(sK2,k2_tarski(sK4,sK4)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))
    | v3_pre_topc(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)),sK2) != iProver_top
    | v3_pre_topc(k2_pre_topc(sK2,k2_tarski(sK4,sK4)),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5890])).

cnf(c_5998,plain,
    ( r1_xboole_0(k2_pre_topc(sK2,k2_tarski(sK4,sK4)),k2_tarski(sK3,sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5963,c_25,c_26,c_27,c_28,c_22,c_29,c_20,c_31,c_61,c_62,c_64,c_65,c_946,c_947,c_973,c_1032,c_1029,c_1166,c_1168,c_2218,c_2378,c_2379,c_3289,c_5466,c_5895])).

cnf(c_6004,plain,
    ( r2_hidden(sK3,k2_pre_topc(sK2,k2_tarski(sK4,sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1652,c_5998])).

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

cnf(c_233,plain,
    ( ~ m1_subset_1(X0_50,u1_struct_0(X0_49))
    | ~ m1_subset_1(X1_50,u1_struct_0(X0_49))
    | ~ r2_hidden(X1_50,k2_pre_topc(X0_49,k6_domain_1(u1_struct_0(X0_49),X0_50)))
    | ~ v3_tdlat_3(X0_49)
    | ~ v2_pre_topc(X0_49)
    | v2_struct_0(X0_49)
    | ~ l1_pre_topc(X0_49)
    | k2_pre_topc(X0_49,k6_domain_1(u1_struct_0(X0_49),X0_50)) = k2_pre_topc(X0_49,k6_domain_1(u1_struct_0(X0_49),X1_50)) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_704,plain,
    ( k2_pre_topc(X0_49,k6_domain_1(u1_struct_0(X0_49),X0_50)) = k2_pre_topc(X0_49,k6_domain_1(u1_struct_0(X0_49),X1_50))
    | m1_subset_1(X1_50,u1_struct_0(X0_49)) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(X0_49)) != iProver_top
    | r2_hidden(X1_50,k2_pre_topc(X0_49,k6_domain_1(u1_struct_0(X0_49),X0_50))) != iProver_top
    | v3_tdlat_3(X0_49) != iProver_top
    | v2_pre_topc(X0_49) != iProver_top
    | v2_struct_0(X0_49) = iProver_top
    | l1_pre_topc(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_233])).

cnf(c_3684,plain,
    ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0_50)) = k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))
    | m1_subset_1(X0_50,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X0_50,k2_pre_topc(sK2,k2_tarski(sK4,sK4))) != iProver_top
    | v3_tdlat_3(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2208,c_704])).

cnf(c_3693,plain,
    ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0_50)) = k2_pre_topc(sK2,k2_tarski(sK4,sK4))
    | m1_subset_1(X0_50,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X0_50,k2_pre_topc(sK2,k2_tarski(sK4,sK4))) != iProver_top
    | v3_tdlat_3(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3684,c_2208])).

cnf(c_3758,plain,
    ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)) = k2_pre_topc(sK2,k2_tarski(sK4,sK4))
    | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK3,k2_pre_topc(sK2,k2_tarski(sK4,sK4))) != iProver_top
    | v3_tdlat_3(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3693])).

cnf(c_18,negated_conjecture,
    ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_232,negated_conjecture,
    ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_2212,plain,
    ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)) != k2_pre_topc(sK2,k2_tarski(sK4,sK4)) ),
    inference(demodulation,[status(thm)],[c_2208,c_232])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6004,c_3758,c_2212,c_31,c_30,c_29,c_28,c_27,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 20:12:49 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.34  % Running in FOF mode
% 3.58/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.58/0.99  
% 3.58/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.58/0.99  
% 3.58/0.99  ------  iProver source info
% 3.58/0.99  
% 3.58/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.58/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.58/0.99  git: non_committed_changes: false
% 3.58/0.99  git: last_make_outside_of_git: false
% 3.58/0.99  
% 3.58/0.99  ------ 
% 3.58/0.99  ------ Parsing...
% 3.58/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.58/0.99  
% 3.58/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.58/0.99  
% 3.58/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.58/0.99  
% 3.58/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.58/0.99  ------ Proving...
% 3.58/0.99  ------ Problem Properties 
% 3.58/0.99  
% 3.58/0.99  
% 3.58/0.99  clauses                                 26
% 3.58/0.99  conjectures                             8
% 3.58/0.99  EPR                                     6
% 3.58/0.99  Horn                                    18
% 3.58/0.99  unary                                   8
% 3.58/0.99  binary                                  4
% 3.58/0.99  lits                                    76
% 3.58/0.99  lits eq                                 6
% 3.58/0.99  fd_pure                                 0
% 3.58/0.99  fd_pseudo                               0
% 3.58/0.99  fd_cond                                 0
% 3.58/0.99  fd_pseudo_cond                          0
% 3.58/0.99  AC symbols                              0
% 3.58/0.99  
% 3.58/0.99  ------ Input Options Time Limit: Unbounded
% 3.58/0.99  
% 3.58/0.99  
% 3.58/0.99  ------ 
% 3.58/0.99  Current options:
% 3.58/0.99  ------ 
% 3.58/0.99  
% 3.58/0.99  
% 3.58/0.99  
% 3.58/0.99  
% 3.58/0.99  ------ Proving...
% 3.58/0.99  
% 3.58/0.99  
% 3.58/0.99  % SZS status Theorem for theBenchmark.p
% 3.58/0.99  
% 3.58/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.58/0.99  
% 3.58/0.99  fof(f3,axiom,(
% 3.58/0.99    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 3.58/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.58/0.99  
% 3.58/0.99  fof(f18,plain,(
% 3.58/0.99    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 3.58/0.99    inference(ennf_transformation,[],[f3])).
% 3.58/0.99  
% 3.58/0.99  fof(f54,plain,(
% 3.58/0.99    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 3.58/0.99    inference(cnf_transformation,[],[f18])).
% 3.58/0.99  
% 3.58/0.99  fof(f2,axiom,(
% 3.58/0.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.58/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.58/0.99  
% 3.58/0.99  fof(f53,plain,(
% 3.58/0.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.58/0.99    inference(cnf_transformation,[],[f2])).
% 3.58/0.99  
% 3.58/0.99  fof(f77,plain,(
% 3.58/0.99    ( ! [X0,X1] : (r1_xboole_0(k2_tarski(X0,X0),X1) | r2_hidden(X0,X1)) )),
% 3.58/0.99    inference(definition_unfolding,[],[f54,f53])).
% 3.58/0.99  
% 3.58/0.99  fof(f1,axiom,(
% 3.58/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.58/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.58/0.99  
% 3.58/0.99  fof(f16,plain,(
% 3.58/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.58/0.99    inference(rectify,[],[f1])).
% 3.58/0.99  
% 3.58/0.99  fof(f17,plain,(
% 3.58/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 3.58/0.99    inference(ennf_transformation,[],[f16])).
% 3.58/0.99  
% 3.58/0.99  fof(f40,plain,(
% 3.58/0.99    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.58/0.99    introduced(choice_axiom,[])).
% 3.58/0.99  
% 3.58/0.99  fof(f41,plain,(
% 3.58/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 3.58/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f40])).
% 3.58/0.99  
% 3.58/0.99  fof(f51,plain,(
% 3.58/0.99    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 3.58/0.99    inference(cnf_transformation,[],[f41])).
% 3.58/0.99  
% 3.58/0.99  fof(f50,plain,(
% 3.58/0.99    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 3.58/0.99    inference(cnf_transformation,[],[f41])).
% 3.58/0.99  
% 3.58/0.99  fof(f52,plain,(
% 3.58/0.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 3.58/0.99    inference(cnf_transformation,[],[f41])).
% 3.58/0.99  
% 3.58/0.99  fof(f14,conjecture,(
% 3.58/0.99    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) | r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))))))),
% 3.58/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.58/0.99  
% 3.58/0.99  fof(f15,negated_conjecture,(
% 3.58/0.99    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) | r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))))))),
% 3.58/0.99    inference(negated_conjecture,[],[f14])).
% 3.58/0.99  
% 3.58/0.99  fof(f38,plain,(
% 3.58/0.99    ? [X0] : (? [X1] : (? [X2] : ((k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.58/0.99    inference(ennf_transformation,[],[f15])).
% 3.58/0.99  
% 3.58/0.99  fof(f39,plain,(
% 3.58/0.99    ? [X0] : (? [X1] : (? [X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.58/0.99    inference(flattening,[],[f38])).
% 3.58/0.99  
% 3.58/0.99  fof(f48,plain,(
% 3.58/0.99    ( ! [X0,X1] : (? [X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & m1_subset_1(X2,u1_struct_0(X0))) => (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK4)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK4))) & m1_subset_1(sK4,u1_struct_0(X0)))) )),
% 3.58/0.99    introduced(choice_axiom,[])).
% 3.58/0.99  
% 3.58/0.99  fof(f47,plain,(
% 3.58/0.99    ( ! [X0] : (? [X1] : (? [X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK3)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK3,u1_struct_0(X0)))) )),
% 3.58/0.99    introduced(choice_axiom,[])).
% 3.58/0.99  
% 3.58/0.99  fof(f46,plain,(
% 3.58/0.99    ? [X0] : (? [X1] : (? [X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X1)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X2)) & ~r1_xboole_0(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X1)),k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X2))) & m1_subset_1(X2,u1_struct_0(sK2))) & m1_subset_1(X1,u1_struct_0(sK2))) & l1_pre_topc(sK2) & v3_tdlat_3(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 3.58/0.99    introduced(choice_axiom,[])).
% 3.58/0.99  
% 3.58/0.99  fof(f49,plain,(
% 3.58/0.99    ((k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)) & ~r1_xboole_0(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)),k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))) & m1_subset_1(sK4,u1_struct_0(sK2))) & m1_subset_1(sK3,u1_struct_0(sK2))) & l1_pre_topc(sK2) & v3_tdlat_3(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 3.58/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f39,f48,f47,f46])).
% 3.58/0.99  
% 3.58/0.99  fof(f73,plain,(
% 3.58/0.99    m1_subset_1(sK3,u1_struct_0(sK2))),
% 3.58/0.99    inference(cnf_transformation,[],[f49])).
% 3.58/0.99  
% 3.58/0.99  fof(f10,axiom,(
% 3.58/0.99    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 3.58/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.58/0.99  
% 3.58/0.99  fof(f30,plain,(
% 3.58/0.99    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 3.58/0.99    inference(ennf_transformation,[],[f10])).
% 3.58/0.99  
% 3.58/0.99  fof(f31,plain,(
% 3.58/0.99    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 3.58/0.99    inference(flattening,[],[f30])).
% 3.58/0.99  
% 3.58/0.99  fof(f62,plain,(
% 3.58/0.99    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.58/0.99    inference(cnf_transformation,[],[f31])).
% 3.58/0.99  
% 3.58/0.99  fof(f78,plain,(
% 3.58/0.99    ( ! [X0,X1] : (k2_tarski(X1,X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.58/0.99    inference(definition_unfolding,[],[f62,f53])).
% 3.58/0.99  
% 3.58/0.99  fof(f69,plain,(
% 3.58/0.99    ~v2_struct_0(sK2)),
% 3.58/0.99    inference(cnf_transformation,[],[f49])).
% 3.58/0.99  
% 3.58/0.99  fof(f72,plain,(
% 3.58/0.99    l1_pre_topc(sK2)),
% 3.58/0.99    inference(cnf_transformation,[],[f49])).
% 3.58/0.99  
% 3.58/0.99  fof(f6,axiom,(
% 3.58/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 3.58/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.58/0.99  
% 3.58/0.99  fof(f22,plain,(
% 3.58/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.58/0.99    inference(ennf_transformation,[],[f6])).
% 3.58/0.99  
% 3.58/0.99  fof(f23,plain,(
% 3.58/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.58/0.99    inference(flattening,[],[f22])).
% 3.58/0.99  
% 3.58/0.99  fof(f57,plain,(
% 3.58/0.99    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.58/0.99    inference(cnf_transformation,[],[f23])).
% 3.58/0.99  
% 3.58/0.99  fof(f5,axiom,(
% 3.58/0.99    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.58/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.58/0.99  
% 3.58/0.99  fof(f21,plain,(
% 3.58/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.58/0.99    inference(ennf_transformation,[],[f5])).
% 3.58/0.99  
% 3.58/0.99  fof(f56,plain,(
% 3.58/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.58/0.99    inference(cnf_transformation,[],[f21])).
% 3.58/0.99  
% 3.58/0.99  fof(f9,axiom,(
% 3.58/0.99    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 3.58/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.58/0.99  
% 3.58/0.99  fof(f28,plain,(
% 3.58/0.99    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 3.58/0.99    inference(ennf_transformation,[],[f9])).
% 3.58/0.99  
% 3.58/0.99  fof(f29,plain,(
% 3.58/0.99    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 3.58/0.99    inference(flattening,[],[f28])).
% 3.58/0.99  
% 3.58/0.99  fof(f61,plain,(
% 3.58/0.99    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.58/0.99    inference(cnf_transformation,[],[f29])).
% 3.58/0.99  
% 3.58/0.99  fof(f12,axiom,(
% 3.58/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X1,X0) & r1_xboole_0(X1,X2)) => r1_xboole_0(X1,k2_pre_topc(X0,X2))))))),
% 3.58/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.58/0.99  
% 3.58/0.99  fof(f34,plain,(
% 3.58/0.99    ! [X0] : (! [X1] : (! [X2] : ((r1_xboole_0(X1,k2_pre_topc(X0,X2)) | (~v3_pre_topc(X1,X0) | ~r1_xboole_0(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.58/0.99    inference(ennf_transformation,[],[f12])).
% 3.58/0.99  
% 3.58/0.99  fof(f35,plain,(
% 3.58/0.99    ! [X0] : (! [X1] : (! [X2] : (r1_xboole_0(X1,k2_pre_topc(X0,X2)) | ~v3_pre_topc(X1,X0) | ~r1_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.58/0.99    inference(flattening,[],[f34])).
% 3.58/0.99  
% 3.58/0.99  fof(f67,plain,(
% 3.58/0.99    ( ! [X2,X0,X1] : (r1_xboole_0(X1,k2_pre_topc(X0,X2)) | ~v3_pre_topc(X1,X0) | ~r1_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.58/0.99    inference(cnf_transformation,[],[f35])).
% 3.58/0.99  
% 3.58/0.99  fof(f70,plain,(
% 3.58/0.99    v2_pre_topc(sK2)),
% 3.58/0.99    inference(cnf_transformation,[],[f49])).
% 3.58/0.99  
% 3.58/0.99  fof(f74,plain,(
% 3.58/0.99    m1_subset_1(sK4,u1_struct_0(sK2))),
% 3.58/0.99    inference(cnf_transformation,[],[f49])).
% 3.58/0.99  
% 3.58/0.99  fof(f75,plain,(
% 3.58/0.99    ~r1_xboole_0(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)),k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)))),
% 3.58/0.99    inference(cnf_transformation,[],[f49])).
% 3.58/0.99  
% 3.58/0.99  fof(f71,plain,(
% 3.58/0.99    v3_tdlat_3(sK2)),
% 3.58/0.99    inference(cnf_transformation,[],[f49])).
% 3.58/0.99  
% 3.58/0.99  fof(f4,axiom,(
% 3.58/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.58/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.58/0.99  
% 3.58/0.99  fof(f19,plain,(
% 3.58/0.99    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.58/0.99    inference(ennf_transformation,[],[f4])).
% 3.58/0.99  
% 3.58/0.99  fof(f20,plain,(
% 3.58/0.99    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.58/0.99    inference(flattening,[],[f19])).
% 3.58/0.99  
% 3.58/0.99  fof(f55,plain,(
% 3.58/0.99    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.58/0.99    inference(cnf_transformation,[],[f20])).
% 3.58/0.99  
% 3.58/0.99  fof(f7,axiom,(
% 3.58/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)))),
% 3.58/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.58/0.99  
% 3.58/0.99  fof(f24,plain,(
% 3.58/0.99    ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.58/0.99    inference(ennf_transformation,[],[f7])).
% 3.58/0.99  
% 3.58/0.99  fof(f25,plain,(
% 3.58/0.99    ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.58/0.99    inference(flattening,[],[f24])).
% 3.58/0.99  
% 3.58/0.99  fof(f58,plain,(
% 3.58/0.99    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.58/0.99    inference(cnf_transformation,[],[f25])).
% 3.58/0.99  
% 3.58/0.99  fof(f11,axiom,(
% 3.58/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v3_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => v3_pre_topc(X1,X0)))))),
% 3.58/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.58/0.99  
% 3.58/0.99  fof(f32,plain,(
% 3.58/0.99    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : ((v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.58/0.99    inference(ennf_transformation,[],[f11])).
% 3.58/0.99  
% 3.58/0.99  fof(f33,plain,(
% 3.58/0.99    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.58/0.99    inference(flattening,[],[f32])).
% 3.58/0.99  
% 3.58/0.99  fof(f42,plain,(
% 3.58/0.99    ! [X0] : (((v3_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X1] : (v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.58/0.99    inference(nnf_transformation,[],[f33])).
% 3.58/0.99  
% 3.58/0.99  fof(f43,plain,(
% 3.58/0.99    ! [X0] : (((v3_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.58/0.99    inference(rectify,[],[f42])).
% 3.58/0.99  
% 3.58/0.99  fof(f44,plain,(
% 3.58/0.99    ! [X0] : (? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK1(X0),X0) & v4_pre_topc(sK1(X0),X0) & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.58/0.99    introduced(choice_axiom,[])).
% 3.58/0.99  
% 3.58/0.99  fof(f45,plain,(
% 3.58/0.99    ! [X0] : (((v3_tdlat_3(X0) | (~v3_pre_topc(sK1(X0),X0) & v4_pre_topc(sK1(X0),X0) & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.58/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f43,f44])).
% 3.58/0.99  
% 3.58/0.99  fof(f63,plain,(
% 3.58/0.99    ( ! [X2,X0] : (v3_pre_topc(X2,X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tdlat_3(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.58/0.99    inference(cnf_transformation,[],[f45])).
% 3.58/0.99  
% 3.58/0.99  fof(f8,axiom,(
% 3.58/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 3.58/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.58/0.99  
% 3.58/0.99  fof(f26,plain,(
% 3.58/0.99    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.58/0.99    inference(ennf_transformation,[],[f8])).
% 3.58/0.99  
% 3.58/0.99  fof(f27,plain,(
% 3.58/0.99    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.58/0.99    inference(flattening,[],[f26])).
% 3.58/0.99  
% 3.58/0.99  fof(f60,plain,(
% 3.58/0.99    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.58/0.99    inference(cnf_transformation,[],[f27])).
% 3.58/0.99  
% 3.58/0.99  fof(f13,axiom,(
% 3.58/0.99    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) => k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))))))),
% 3.58/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.58/0.99  
% 3.58/0.99  fof(f36,plain,(
% 3.58/0.99    ! [X0] : (! [X1] : (! [X2] : ((k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) | ~r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.58/0.99    inference(ennf_transformation,[],[f13])).
% 3.58/0.99  
% 3.58/0.99  fof(f37,plain,(
% 3.58/0.99    ! [X0] : (! [X1] : (! [X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) | ~r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.58/0.99    inference(flattening,[],[f36])).
% 3.58/0.99  
% 3.58/0.99  fof(f68,plain,(
% 3.58/0.99    ( ! [X2,X0,X1] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) | ~r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.58/0.99    inference(cnf_transformation,[],[f37])).
% 3.58/0.99  
% 3.58/0.99  fof(f76,plain,(
% 3.58/0.99    k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))),
% 3.58/0.99    inference(cnf_transformation,[],[f49])).
% 3.58/0.99  
% 3.58/0.99  cnf(c_3,plain,
% 3.58/0.99      ( r2_hidden(X0,X1) | r1_xboole_0(k2_tarski(X0,X0),X1) ),
% 3.58/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_247,plain,
% 3.58/0.99      ( r2_hidden(X0_50,X1_50)
% 3.58/0.99      | r1_xboole_0(k2_tarski(X0_50,X0_50),X1_50) ),
% 3.58/0.99      inference(subtyping,[status(esa)],[c_3]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_690,plain,
% 3.58/0.99      ( r2_hidden(X0_50,X1_50) = iProver_top
% 3.58/0.99      | r1_xboole_0(k2_tarski(X0_50,X0_50),X1_50) = iProver_top ),
% 3.58/0.99      inference(predicate_to_equality,[status(thm)],[c_247]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_1,plain,
% 3.58/0.99      ( r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1) ),
% 3.58/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_249,plain,
% 3.58/0.99      ( r2_hidden(sK0(X0_50,X1_50),X1_50) | r1_xboole_0(X0_50,X1_50) ),
% 3.58/0.99      inference(subtyping,[status(esa)],[c_1]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_688,plain,
% 3.58/0.99      ( r2_hidden(sK0(X0_50,X1_50),X1_50) = iProver_top
% 3.58/0.99      | r1_xboole_0(X0_50,X1_50) = iProver_top ),
% 3.58/0.99      inference(predicate_to_equality,[status(thm)],[c_249]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_2,plain,
% 3.58/0.99      ( r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1) ),
% 3.58/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_248,plain,
% 3.58/0.99      ( r2_hidden(sK0(X0_50,X1_50),X0_50) | r1_xboole_0(X0_50,X1_50) ),
% 3.58/0.99      inference(subtyping,[status(esa)],[c_2]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_689,plain,
% 3.58/0.99      ( r2_hidden(sK0(X0_50,X1_50),X0_50) = iProver_top
% 3.58/0.99      | r1_xboole_0(X0_50,X1_50) = iProver_top ),
% 3.58/0.99      inference(predicate_to_equality,[status(thm)],[c_248]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_0,plain,
% 3.58/0.99      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_xboole_0(X2,X1) ),
% 3.58/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_250,plain,
% 3.58/0.99      ( ~ r2_hidden(X0_50,X1_50)
% 3.58/0.99      | ~ r2_hidden(X0_50,X2_50)
% 3.58/0.99      | ~ r1_xboole_0(X2_50,X1_50) ),
% 3.58/0.99      inference(subtyping,[status(esa)],[c_0]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_687,plain,
% 3.58/0.99      ( r2_hidden(X0_50,X1_50) != iProver_top
% 3.58/0.99      | r2_hidden(X0_50,X2_50) != iProver_top
% 3.58/0.99      | r1_xboole_0(X2_50,X1_50) != iProver_top ),
% 3.58/0.99      inference(predicate_to_equality,[status(thm)],[c_250]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_1265,plain,
% 3.58/0.99      ( r2_hidden(sK0(X0_50,X1_50),X2_50) != iProver_top
% 3.58/0.99      | r1_xboole_0(X2_50,X0_50) != iProver_top
% 3.58/0.99      | r1_xboole_0(X0_50,X1_50) = iProver_top ),
% 3.58/0.99      inference(superposition,[status(thm)],[c_689,c_687]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_1508,plain,
% 3.58/0.99      ( r1_xboole_0(X0_50,X1_50) != iProver_top
% 3.58/0.99      | r1_xboole_0(X1_50,X0_50) = iProver_top ),
% 3.58/0.99      inference(superposition,[status(thm)],[c_688,c_1265]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_1652,plain,
% 3.58/0.99      ( r2_hidden(X0_50,X1_50) = iProver_top
% 3.58/0.99      | r1_xboole_0(X1_50,k2_tarski(X0_50,X0_50)) = iProver_top ),
% 3.58/0.99      inference(superposition,[status(thm)],[c_690,c_1508]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_21,negated_conjecture,
% 3.58/0.99      ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 3.58/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_229,negated_conjecture,
% 3.58/0.99      ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 3.58/0.99      inference(subtyping,[status(esa)],[c_21]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_707,plain,
% 3.58/0.99      ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
% 3.58/0.99      inference(predicate_to_equality,[status(thm)],[c_229]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_11,plain,
% 3.58/0.99      ( ~ m1_subset_1(X0,X1)
% 3.58/0.99      | v1_xboole_0(X1)
% 3.58/0.99      | k6_domain_1(X1,X0) = k2_tarski(X0,X0) ),
% 3.58/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_239,plain,
% 3.58/0.99      ( ~ m1_subset_1(X0_50,X0_51)
% 3.58/0.99      | v1_xboole_0(X0_51)
% 3.58/0.99      | k6_domain_1(X0_51,X0_50) = k2_tarski(X0_50,X0_50) ),
% 3.58/0.99      inference(subtyping,[status(esa)],[c_11]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_698,plain,
% 3.58/0.99      ( k6_domain_1(X0_51,X0_50) = k2_tarski(X0_50,X0_50)
% 3.58/0.99      | m1_subset_1(X0_50,X0_51) != iProver_top
% 3.58/0.99      | v1_xboole_0(X0_51) = iProver_top ),
% 3.58/0.99      inference(predicate_to_equality,[status(thm)],[c_239]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_1868,plain,
% 3.58/0.99      ( k6_domain_1(u1_struct_0(sK2),sK3) = k2_tarski(sK3,sK3)
% 3.58/0.99      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 3.58/0.99      inference(superposition,[status(thm)],[c_707,c_698]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_25,negated_conjecture,
% 3.58/0.99      ( ~ v2_struct_0(sK2) ),
% 3.58/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_22,negated_conjecture,
% 3.58/0.99      ( l1_pre_topc(sK2) ),
% 3.58/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_6,plain,
% 3.58/0.99      ( v2_struct_0(X0)
% 3.58/0.99      | ~ v1_xboole_0(u1_struct_0(X0))
% 3.58/0.99      | ~ l1_struct_0(X0) ),
% 3.58/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_61,plain,
% 3.58/0.99      ( v2_struct_0(sK2)
% 3.58/0.99      | ~ v1_xboole_0(u1_struct_0(sK2))
% 3.58/0.99      | ~ l1_struct_0(sK2) ),
% 3.58/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_5,plain,
% 3.58/0.99      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 3.58/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_64,plain,
% 3.58/0.99      ( l1_struct_0(sK2) | ~ l1_pre_topc(sK2) ),
% 3.58/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_976,plain,
% 3.58/0.99      ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 3.58/0.99      | v1_xboole_0(u1_struct_0(sK2))
% 3.58/0.99      | k6_domain_1(u1_struct_0(sK2),sK3) = k2_tarski(sK3,sK3) ),
% 3.58/0.99      inference(instantiation,[status(thm)],[c_239]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_2300,plain,
% 3.58/0.99      ( k6_domain_1(u1_struct_0(sK2),sK3) = k2_tarski(sK3,sK3) ),
% 3.58/0.99      inference(global_propositional_subsumption,
% 3.58/0.99                [status(thm)],
% 3.58/0.99                [c_1868,c_25,c_22,c_21,c_61,c_64,c_976]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_10,plain,
% 3.58/0.99      ( ~ m1_subset_1(X0,X1)
% 3.58/0.99      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
% 3.58/0.99      | v1_xboole_0(X1) ),
% 3.58/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_240,plain,
% 3.58/0.99      ( ~ m1_subset_1(X0_50,X0_51)
% 3.58/0.99      | m1_subset_1(k6_domain_1(X0_51,X0_50),k1_zfmisc_1(X0_51))
% 3.58/0.99      | v1_xboole_0(X0_51) ),
% 3.58/0.99      inference(subtyping,[status(esa)],[c_10]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_697,plain,
% 3.58/0.99      ( m1_subset_1(X0_50,X0_51) != iProver_top
% 3.58/0.99      | m1_subset_1(k6_domain_1(X0_51,X0_50),k1_zfmisc_1(X0_51)) = iProver_top
% 3.58/0.99      | v1_xboole_0(X0_51) = iProver_top ),
% 3.58/0.99      inference(predicate_to_equality,[status(thm)],[c_240]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_2310,plain,
% 3.58/0.99      ( m1_subset_1(k2_tarski(sK3,sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 3.58/0.99      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 3.58/0.99      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 3.58/0.99      inference(superposition,[status(thm)],[c_2300,c_697]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_26,plain,
% 3.58/0.99      ( v2_struct_0(sK2) != iProver_top ),
% 3.58/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_29,plain,
% 3.58/0.99      ( l1_pre_topc(sK2) = iProver_top ),
% 3.58/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_30,plain,
% 3.58/0.99      ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
% 3.58/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_60,plain,
% 3.58/0.99      ( v2_struct_0(X0) = iProver_top
% 3.58/0.99      | v1_xboole_0(u1_struct_0(X0)) != iProver_top
% 3.58/0.99      | l1_struct_0(X0) != iProver_top ),
% 3.58/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_62,plain,
% 3.58/0.99      ( v2_struct_0(sK2) = iProver_top
% 3.58/0.99      | v1_xboole_0(u1_struct_0(sK2)) != iProver_top
% 3.58/0.99      | l1_struct_0(sK2) != iProver_top ),
% 3.58/0.99      inference(instantiation,[status(thm)],[c_60]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_63,plain,
% 3.58/0.99      ( l1_struct_0(X0) = iProver_top | l1_pre_topc(X0) != iProver_top ),
% 3.58/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_65,plain,
% 3.58/0.99      ( l1_struct_0(sK2) = iProver_top
% 3.58/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.58/0.99      inference(instantiation,[status(thm)],[c_63]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_2507,plain,
% 3.58/0.99      ( m1_subset_1(k2_tarski(sK3,sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.58/0.99      inference(global_propositional_subsumption,
% 3.58/0.99                [status(thm)],
% 3.58/0.99                [c_2310,c_26,c_29,c_30,c_62,c_65]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_16,plain,
% 3.58/0.99      ( ~ v3_pre_topc(X0,X1)
% 3.58/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.58/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.58/0.99      | ~ r1_xboole_0(X0,X2)
% 3.58/0.99      | r1_xboole_0(X0,k2_pre_topc(X1,X2))
% 3.58/0.99      | ~ v2_pre_topc(X1)
% 3.58/0.99      | ~ l1_pre_topc(X1) ),
% 3.58/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_234,plain,
% 3.58/0.99      ( ~ v3_pre_topc(X0_50,X0_49)
% 3.58/0.99      | ~ m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(X0_49)))
% 3.58/0.99      | ~ m1_subset_1(X1_50,k1_zfmisc_1(u1_struct_0(X0_49)))
% 3.58/0.99      | ~ r1_xboole_0(X0_50,X1_50)
% 3.58/0.99      | r1_xboole_0(X0_50,k2_pre_topc(X0_49,X1_50))
% 3.58/0.99      | ~ v2_pre_topc(X0_49)
% 3.58/0.99      | ~ l1_pre_topc(X0_49) ),
% 3.58/0.99      inference(subtyping,[status(esa)],[c_16]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_703,plain,
% 3.58/0.99      ( v3_pre_topc(X0_50,X0_49) != iProver_top
% 3.58/0.99      | m1_subset_1(X1_50,k1_zfmisc_1(u1_struct_0(X0_49))) != iProver_top
% 3.58/0.99      | m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(X0_49))) != iProver_top
% 3.58/0.99      | r1_xboole_0(X0_50,X1_50) != iProver_top
% 3.58/0.99      | r1_xboole_0(X0_50,k2_pre_topc(X0_49,X1_50)) = iProver_top
% 3.58/0.99      | v2_pre_topc(X0_49) != iProver_top
% 3.58/0.99      | l1_pre_topc(X0_49) != iProver_top ),
% 3.58/0.99      inference(predicate_to_equality,[status(thm)],[c_234]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_3078,plain,
% 3.58/0.99      ( v3_pre_topc(X0_50,sK2) != iProver_top
% 3.58/0.99      | m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.58/0.99      | r1_xboole_0(X0_50,k2_pre_topc(sK2,k2_tarski(sK3,sK3))) = iProver_top
% 3.58/0.99      | r1_xboole_0(X0_50,k2_tarski(sK3,sK3)) != iProver_top
% 3.58/0.99      | v2_pre_topc(sK2) != iProver_top
% 3.58/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.58/0.99      inference(superposition,[status(thm)],[c_2507,c_703]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_24,negated_conjecture,
% 3.58/0.99      ( v2_pre_topc(sK2) ),
% 3.58/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_27,plain,
% 3.58/0.99      ( v2_pre_topc(sK2) = iProver_top ),
% 3.58/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_4466,plain,
% 3.58/0.99      ( v3_pre_topc(X0_50,sK2) != iProver_top
% 3.58/0.99      | m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.58/0.99      | r1_xboole_0(X0_50,k2_pre_topc(sK2,k2_tarski(sK3,sK3))) = iProver_top
% 3.58/0.99      | r1_xboole_0(X0_50,k2_tarski(sK3,sK3)) != iProver_top ),
% 3.58/0.99      inference(global_propositional_subsumption,
% 3.58/0.99                [status(thm)],
% 3.58/0.99                [c_3078,c_27,c_29]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_4476,plain,
% 3.58/0.99      ( v3_pre_topc(X0_50,sK2) != iProver_top
% 3.58/0.99      | m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.58/0.99      | r1_xboole_0(X0_50,k2_tarski(sK3,sK3)) != iProver_top
% 3.58/0.99      | r1_xboole_0(k2_pre_topc(sK2,k2_tarski(sK3,sK3)),X0_50) = iProver_top ),
% 3.58/0.99      inference(superposition,[status(thm)],[c_4466,c_1508]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_20,negated_conjecture,
% 3.58/0.99      ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
% 3.58/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_230,negated_conjecture,
% 3.58/0.99      ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
% 3.58/0.99      inference(subtyping,[status(esa)],[c_20]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_706,plain,
% 3.58/0.99      ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
% 3.58/0.99      inference(predicate_to_equality,[status(thm)],[c_230]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_1867,plain,
% 3.58/0.99      ( k6_domain_1(u1_struct_0(sK2),sK4) = k2_tarski(sK4,sK4)
% 3.58/0.99      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 3.58/0.99      inference(superposition,[status(thm)],[c_706,c_698]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_973,plain,
% 3.58/0.99      ( ~ m1_subset_1(sK4,u1_struct_0(sK2))
% 3.58/0.99      | v1_xboole_0(u1_struct_0(sK2))
% 3.58/0.99      | k6_domain_1(u1_struct_0(sK2),sK4) = k2_tarski(sK4,sK4) ),
% 3.58/0.99      inference(instantiation,[status(thm)],[c_239]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_2208,plain,
% 3.58/0.99      ( k6_domain_1(u1_struct_0(sK2),sK4) = k2_tarski(sK4,sK4) ),
% 3.58/0.99      inference(global_propositional_subsumption,
% 3.58/0.99                [status(thm)],
% 3.58/0.99                [c_1867,c_25,c_22,c_20,c_61,c_64,c_973]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_19,negated_conjecture,
% 3.58/0.99      ( ~ r1_xboole_0(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)),k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))) ),
% 3.58/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_231,negated_conjecture,
% 3.58/0.99      ( ~ r1_xboole_0(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)),k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))) ),
% 3.58/0.99      inference(subtyping,[status(esa)],[c_19]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_705,plain,
% 3.58/0.99      ( r1_xboole_0(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)),k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))) != iProver_top ),
% 3.58/0.99      inference(predicate_to_equality,[status(thm)],[c_231]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_2211,plain,
% 3.58/0.99      ( r1_xboole_0(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)),k2_pre_topc(sK2,k2_tarski(sK4,sK4))) != iProver_top ),
% 3.58/0.99      inference(demodulation,[status(thm)],[c_2208,c_705]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_2303,plain,
% 3.58/0.99      ( r1_xboole_0(k2_pre_topc(sK2,k2_tarski(sK3,sK3)),k2_pre_topc(sK2,k2_tarski(sK4,sK4))) != iProver_top ),
% 3.58/0.99      inference(demodulation,[status(thm)],[c_2300,c_2211]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_5963,plain,
% 3.58/0.99      ( v3_pre_topc(k2_pre_topc(sK2,k2_tarski(sK4,sK4)),sK2) != iProver_top
% 3.58/0.99      | m1_subset_1(k2_pre_topc(sK2,k2_tarski(sK4,sK4)),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.58/0.99      | r1_xboole_0(k2_pre_topc(sK2,k2_tarski(sK4,sK4)),k2_tarski(sK3,sK3)) != iProver_top ),
% 3.58/0.99      inference(superposition,[status(thm)],[c_4476,c_2303]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_23,negated_conjecture,
% 3.58/0.99      ( v3_tdlat_3(sK2) ),
% 3.58/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_28,plain,
% 3.58/0.99      ( v3_tdlat_3(sK2) = iProver_top ),
% 3.58/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_31,plain,
% 3.58/0.99      ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
% 3.58/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_946,plain,
% 3.58/0.99      ( m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK4),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.58/0.99      | ~ m1_subset_1(sK4,u1_struct_0(sK2))
% 3.58/0.99      | v1_xboole_0(u1_struct_0(sK2)) ),
% 3.58/0.99      inference(instantiation,[status(thm)],[c_240]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_947,plain,
% 3.58/0.99      ( m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 3.58/0.99      | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
% 3.58/0.99      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 3.58/0.99      inference(predicate_to_equality,[status(thm)],[c_946]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_4,plain,
% 3.58/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.58/0.99      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.58/0.99      | ~ l1_pre_topc(X1) ),
% 3.58/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_246,plain,
% 3.58/0.99      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(X0_49)))
% 3.58/0.99      | m1_subset_1(k2_pre_topc(X0_49,X0_50),k1_zfmisc_1(u1_struct_0(X0_49)))
% 3.58/0.99      | ~ l1_pre_topc(X0_49) ),
% 3.58/0.99      inference(subtyping,[status(esa)],[c_4]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_1031,plain,
% 3.58/0.99      ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK4),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.58/0.99      | m1_subset_1(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.58/0.99      | ~ l1_pre_topc(sK2) ),
% 3.58/0.99      inference(instantiation,[status(thm)],[c_246]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_1032,plain,
% 3.58/0.99      ( m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK4),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.58/0.99      | m1_subset_1(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 3.58/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.58/0.99      inference(predicate_to_equality,[status(thm)],[c_1031]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_7,plain,
% 3.58/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.58/0.99      | ~ l1_pre_topc(X1)
% 3.58/0.99      | k2_pre_topc(X1,k2_pre_topc(X1,X0)) = k2_pre_topc(X1,X0) ),
% 3.58/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_243,plain,
% 3.58/0.99      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(X0_49)))
% 3.58/0.99      | ~ l1_pre_topc(X0_49)
% 3.58/0.99      | k2_pre_topc(X0_49,k2_pre_topc(X0_49,X0_50)) = k2_pre_topc(X0_49,X0_50) ),
% 3.58/0.99      inference(subtyping,[status(esa)],[c_7]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_1029,plain,
% 3.58/0.99      ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK4),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.58/0.99      | ~ l1_pre_topc(sK2)
% 3.58/0.99      | k2_pre_topc(sK2,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))) = k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)) ),
% 3.58/0.99      inference(instantiation,[status(thm)],[c_243]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_15,plain,
% 3.58/0.99      ( v3_pre_topc(X0,X1)
% 3.58/0.99      | ~ v4_pre_topc(X0,X1)
% 3.58/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.58/0.99      | ~ v3_tdlat_3(X1)
% 3.58/0.99      | ~ v2_pre_topc(X1)
% 3.58/0.99      | ~ l1_pre_topc(X1) ),
% 3.58/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_235,plain,
% 3.58/0.99      ( v3_pre_topc(X0_50,X0_49)
% 3.58/0.99      | ~ v4_pre_topc(X0_50,X0_49)
% 3.58/0.99      | ~ m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(X0_49)))
% 3.58/0.99      | ~ v3_tdlat_3(X0_49)
% 3.58/0.99      | ~ v2_pre_topc(X0_49)
% 3.58/0.99      | ~ l1_pre_topc(X0_49) ),
% 3.58/0.99      inference(subtyping,[status(esa)],[c_15]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_1156,plain,
% 3.58/0.99      ( v3_pre_topc(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)),sK2)
% 3.58/0.99      | ~ v4_pre_topc(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)),sK2)
% 3.58/0.99      | ~ m1_subset_1(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.58/0.99      | ~ v3_tdlat_3(sK2)
% 3.58/0.99      | ~ v2_pre_topc(sK2)
% 3.58/0.99      | ~ l1_pre_topc(sK2) ),
% 3.58/0.99      inference(instantiation,[status(thm)],[c_235]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_1166,plain,
% 3.58/0.99      ( v3_pre_topc(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)),sK2) = iProver_top
% 3.58/0.99      | v4_pre_topc(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)),sK2) != iProver_top
% 3.58/0.99      | m1_subset_1(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.58/0.99      | v3_tdlat_3(sK2) != iProver_top
% 3.58/0.99      | v2_pre_topc(sK2) != iProver_top
% 3.58/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.58/0.99      inference(predicate_to_equality,[status(thm)],[c_1156]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_8,plain,
% 3.58/0.99      ( v4_pre_topc(X0,X1)
% 3.58/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.58/0.99      | ~ v2_pre_topc(X1)
% 3.58/0.99      | ~ l1_pre_topc(X1)
% 3.58/0.99      | k2_pre_topc(X1,X0) != X0 ),
% 3.58/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_242,plain,
% 3.58/0.99      ( v4_pre_topc(X0_50,X0_49)
% 3.58/0.99      | ~ m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(X0_49)))
% 3.58/0.99      | ~ v2_pre_topc(X0_49)
% 3.58/0.99      | ~ l1_pre_topc(X0_49)
% 3.58/0.99      | k2_pre_topc(X0_49,X0_50) != X0_50 ),
% 3.58/0.99      inference(subtyping,[status(esa)],[c_8]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_1155,plain,
% 3.58/0.99      ( v4_pre_topc(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)),sK2)
% 3.58/0.99      | ~ m1_subset_1(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.58/0.99      | ~ v2_pre_topc(sK2)
% 3.58/0.99      | ~ l1_pre_topc(sK2)
% 3.58/0.99      | k2_pre_topc(sK2,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)) ),
% 3.58/0.99      inference(instantiation,[status(thm)],[c_242]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_1168,plain,
% 3.58/0.99      ( k2_pre_topc(sK2,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))
% 3.58/0.99      | v4_pre_topc(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)),sK2) = iProver_top
% 3.58/0.99      | m1_subset_1(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.58/0.99      | v2_pre_topc(sK2) != iProver_top
% 3.58/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.58/0.99      inference(predicate_to_equality,[status(thm)],[c_1155]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_2218,plain,
% 3.58/0.99      ( m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 3.58/0.99      | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
% 3.58/0.99      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 3.58/0.99      inference(superposition,[status(thm)],[c_2208,c_697]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_253,plain,
% 3.58/0.99      ( X0_50 != X1_50 | X2_50 != X1_50 | X2_50 = X0_50 ),
% 3.58/0.99      theory(equality) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_1292,plain,
% 3.58/0.99      ( X0_50 != X1_50
% 3.58/0.99      | X0_50 = k6_domain_1(u1_struct_0(sK2),sK4)
% 3.58/0.99      | k6_domain_1(u1_struct_0(sK2),sK4) != X1_50 ),
% 3.58/0.99      inference(instantiation,[status(thm)],[c_253]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_2143,plain,
% 3.58/0.99      ( X0_50 = k6_domain_1(u1_struct_0(sK2),sK4)
% 3.58/0.99      | X0_50 != k2_tarski(sK4,sK4)
% 3.58/0.99      | k6_domain_1(u1_struct_0(sK2),sK4) != k2_tarski(sK4,sK4) ),
% 3.58/0.99      inference(instantiation,[status(thm)],[c_1292]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_2378,plain,
% 3.58/0.99      ( k6_domain_1(u1_struct_0(sK2),sK4) != k2_tarski(sK4,sK4)
% 3.58/0.99      | k2_tarski(sK4,sK4) = k6_domain_1(u1_struct_0(sK2),sK4)
% 3.58/0.99      | k2_tarski(sK4,sK4) != k2_tarski(sK4,sK4) ),
% 3.58/0.99      inference(instantiation,[status(thm)],[c_2143]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_252,plain,( X0_50 = X0_50 ),theory(equality) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_2379,plain,
% 3.58/0.99      ( k2_tarski(sK4,sK4) = k2_tarski(sK4,sK4) ),
% 3.58/0.99      inference(instantiation,[status(thm)],[c_252]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_256,plain,
% 3.58/0.99      ( X0_50 != X1_50
% 3.58/0.99      | k2_pre_topc(X0_49,X0_50) = k2_pre_topc(X0_49,X1_50) ),
% 3.58/0.99      theory(equality) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_1801,plain,
% 3.58/0.99      ( X0_50 != k6_domain_1(u1_struct_0(sK2),sK4)
% 3.58/0.99      | k2_pre_topc(sK2,X0_50) = k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)) ),
% 3.58/0.99      inference(instantiation,[status(thm)],[c_256]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_3289,plain,
% 3.58/0.99      ( k2_pre_topc(sK2,k2_tarski(sK4,sK4)) = k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))
% 3.58/0.99      | k2_tarski(sK4,sK4) != k6_domain_1(u1_struct_0(sK2),sK4) ),
% 3.58/0.99      inference(instantiation,[status(thm)],[c_1801]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_5465,plain,
% 3.58/0.99      ( m1_subset_1(k2_pre_topc(sK2,k2_tarski(sK4,sK4)),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.58/0.99      | ~ m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.58/0.99      | ~ l1_pre_topc(sK2) ),
% 3.58/0.99      inference(instantiation,[status(thm)],[c_246]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_5466,plain,
% 3.58/0.99      ( m1_subset_1(k2_pre_topc(sK2,k2_tarski(sK4,sK4)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 3.58/0.99      | m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.58/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.58/0.99      inference(predicate_to_equality,[status(thm)],[c_5465]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_260,plain,
% 3.58/0.99      ( ~ v3_pre_topc(X0_50,X0_49)
% 3.58/0.99      | v3_pre_topc(X1_50,X0_49)
% 3.58/0.99      | X1_50 != X0_50 ),
% 3.58/0.99      theory(equality) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_1491,plain,
% 3.58/0.99      ( v3_pre_topc(X0_50,sK2)
% 3.58/0.99      | ~ v3_pre_topc(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)),sK2)
% 3.58/0.99      | X0_50 != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)) ),
% 3.58/0.99      inference(instantiation,[status(thm)],[c_260]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_5890,plain,
% 3.58/0.99      ( ~ v3_pre_topc(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)),sK2)
% 3.58/0.99      | v3_pre_topc(k2_pre_topc(sK2,k2_tarski(sK4,sK4)),sK2)
% 3.58/0.99      | k2_pre_topc(sK2,k2_tarski(sK4,sK4)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)) ),
% 3.58/0.99      inference(instantiation,[status(thm)],[c_1491]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_5895,plain,
% 3.58/0.99      ( k2_pre_topc(sK2,k2_tarski(sK4,sK4)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))
% 3.58/0.99      | v3_pre_topc(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)),sK2) != iProver_top
% 3.58/0.99      | v3_pre_topc(k2_pre_topc(sK2,k2_tarski(sK4,sK4)),sK2) = iProver_top ),
% 3.58/0.99      inference(predicate_to_equality,[status(thm)],[c_5890]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_5998,plain,
% 3.58/0.99      ( r1_xboole_0(k2_pre_topc(sK2,k2_tarski(sK4,sK4)),k2_tarski(sK3,sK3)) != iProver_top ),
% 3.58/0.99      inference(global_propositional_subsumption,
% 3.58/0.99                [status(thm)],
% 3.58/0.99                [c_5963,c_25,c_26,c_27,c_28,c_22,c_29,c_20,c_31,c_61,
% 3.58/0.99                 c_62,c_64,c_65,c_946,c_947,c_973,c_1032,c_1029,c_1166,
% 3.58/0.99                 c_1168,c_2218,c_2378,c_2379,c_3289,c_5466,c_5895]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_6004,plain,
% 3.58/0.99      ( r2_hidden(sK3,k2_pre_topc(sK2,k2_tarski(sK4,sK4))) = iProver_top ),
% 3.58/0.99      inference(superposition,[status(thm)],[c_1652,c_5998]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_17,plain,
% 3.58/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.58/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.58/0.99      | ~ r2_hidden(X2,k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X0)))
% 3.58/0.99      | ~ v3_tdlat_3(X1)
% 3.58/0.99      | ~ v2_pre_topc(X1)
% 3.58/0.99      | v2_struct_0(X1)
% 3.58/0.99      | ~ l1_pre_topc(X1)
% 3.58/0.99      | k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X0)) = k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2)) ),
% 3.58/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_233,plain,
% 3.58/0.99      ( ~ m1_subset_1(X0_50,u1_struct_0(X0_49))
% 3.58/0.99      | ~ m1_subset_1(X1_50,u1_struct_0(X0_49))
% 3.58/0.99      | ~ r2_hidden(X1_50,k2_pre_topc(X0_49,k6_domain_1(u1_struct_0(X0_49),X0_50)))
% 3.58/0.99      | ~ v3_tdlat_3(X0_49)
% 3.58/0.99      | ~ v2_pre_topc(X0_49)
% 3.58/0.99      | v2_struct_0(X0_49)
% 3.58/0.99      | ~ l1_pre_topc(X0_49)
% 3.58/0.99      | k2_pre_topc(X0_49,k6_domain_1(u1_struct_0(X0_49),X0_50)) = k2_pre_topc(X0_49,k6_domain_1(u1_struct_0(X0_49),X1_50)) ),
% 3.58/0.99      inference(subtyping,[status(esa)],[c_17]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_704,plain,
% 3.58/0.99      ( k2_pre_topc(X0_49,k6_domain_1(u1_struct_0(X0_49),X0_50)) = k2_pre_topc(X0_49,k6_domain_1(u1_struct_0(X0_49),X1_50))
% 3.58/0.99      | m1_subset_1(X1_50,u1_struct_0(X0_49)) != iProver_top
% 3.58/0.99      | m1_subset_1(X0_50,u1_struct_0(X0_49)) != iProver_top
% 3.58/0.99      | r2_hidden(X1_50,k2_pre_topc(X0_49,k6_domain_1(u1_struct_0(X0_49),X0_50))) != iProver_top
% 3.58/0.99      | v3_tdlat_3(X0_49) != iProver_top
% 3.58/0.99      | v2_pre_topc(X0_49) != iProver_top
% 3.58/0.99      | v2_struct_0(X0_49) = iProver_top
% 3.58/0.99      | l1_pre_topc(X0_49) != iProver_top ),
% 3.58/0.99      inference(predicate_to_equality,[status(thm)],[c_233]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_3684,plain,
% 3.58/0.99      ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0_50)) = k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))
% 3.58/0.99      | m1_subset_1(X0_50,u1_struct_0(sK2)) != iProver_top
% 3.58/0.99      | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
% 3.58/0.99      | r2_hidden(X0_50,k2_pre_topc(sK2,k2_tarski(sK4,sK4))) != iProver_top
% 3.58/0.99      | v3_tdlat_3(sK2) != iProver_top
% 3.58/0.99      | v2_pre_topc(sK2) != iProver_top
% 3.58/0.99      | v2_struct_0(sK2) = iProver_top
% 3.58/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.58/0.99      inference(superposition,[status(thm)],[c_2208,c_704]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_3693,plain,
% 3.58/0.99      ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0_50)) = k2_pre_topc(sK2,k2_tarski(sK4,sK4))
% 3.58/0.99      | m1_subset_1(X0_50,u1_struct_0(sK2)) != iProver_top
% 3.58/0.99      | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
% 3.58/0.99      | r2_hidden(X0_50,k2_pre_topc(sK2,k2_tarski(sK4,sK4))) != iProver_top
% 3.58/0.99      | v3_tdlat_3(sK2) != iProver_top
% 3.58/0.99      | v2_pre_topc(sK2) != iProver_top
% 3.58/0.99      | v2_struct_0(sK2) = iProver_top
% 3.58/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.58/0.99      inference(light_normalisation,[status(thm)],[c_3684,c_2208]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_3758,plain,
% 3.58/0.99      ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)) = k2_pre_topc(sK2,k2_tarski(sK4,sK4))
% 3.58/0.99      | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
% 3.58/0.99      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 3.58/0.99      | r2_hidden(sK3,k2_pre_topc(sK2,k2_tarski(sK4,sK4))) != iProver_top
% 3.58/0.99      | v3_tdlat_3(sK2) != iProver_top
% 3.58/0.99      | v2_pre_topc(sK2) != iProver_top
% 3.58/0.99      | v2_struct_0(sK2) = iProver_top
% 3.58/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.58/0.99      inference(instantiation,[status(thm)],[c_3693]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_18,negated_conjecture,
% 3.58/0.99      ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)) ),
% 3.58/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_232,negated_conjecture,
% 3.58/0.99      ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)) ),
% 3.58/0.99      inference(subtyping,[status(esa)],[c_18]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_2212,plain,
% 3.58/0.99      ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)) != k2_pre_topc(sK2,k2_tarski(sK4,sK4)) ),
% 3.58/0.99      inference(demodulation,[status(thm)],[c_2208,c_232]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(contradiction,plain,
% 3.58/0.99      ( $false ),
% 3.58/0.99      inference(minisat,
% 3.58/0.99                [status(thm)],
% 3.58/0.99                [c_6004,c_3758,c_2212,c_31,c_30,c_29,c_28,c_27,c_26]) ).
% 3.58/0.99  
% 3.58/0.99  
% 3.58/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.58/0.99  
% 3.58/0.99  ------                               Statistics
% 3.58/0.99  
% 3.58/0.99  ------ Selected
% 3.58/0.99  
% 3.58/0.99  total_time:                             0.221
% 3.58/0.99  
%------------------------------------------------------------------------------
