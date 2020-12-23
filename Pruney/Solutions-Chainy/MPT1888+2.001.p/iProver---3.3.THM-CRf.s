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
% DateTime   : Thu Dec  3 12:27:30 EST 2020

% Result     : Theorem 2.67s
% Output     : CNFRefutation 2.67s
% Verified   : 
% Statistics : Number of formulae       :  200 (1130 expanded)
%              Number of clauses        :  121 ( 320 expanded)
%              Number of leaves         :   23 ( 327 expanded)
%              Depth                    :   24
%              Number of atoms          :  698 (6212 expanded)
%              Number of equality atoms :  144 ( 960 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f81,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_tarski(X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f58,f57])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
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

fof(f64,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f13,axiom,(
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
    inference(ennf_transformation,[],[f13])).

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

fof(f46,plain,(
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

fof(f47,plain,(
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
    inference(rectify,[],[f46])).

fof(f48,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_pre_topc(X1,X0)
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK1(X0),X0)
        & v4_pre_topc(sK1(X0),X0)
        & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f47,f48])).

fof(f67,plain,(
    ! [X2,X0] :
      ( v3_pre_topc(X2,X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f16,conjecture,(
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

fof(f17,negated_conjecture,(
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
    inference(negated_conjecture,[],[f16])).

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
    inference(ennf_transformation,[],[f17])).

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

fof(f52,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))
          & ~ r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK4)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
        & ~ r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK4)))
        & m1_subset_1(sK4,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
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

fof(f50,plain,
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

fof(f53,plain,
    ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))
    & ~ r1_xboole_0(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)),k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)))
    & m1_subset_1(sK4,u1_struct_0(sK2))
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & l1_pre_topc(sK2)
    & v3_tdlat_3(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f41,f52,f51,f50])).

fof(f74,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f53])).

fof(f75,plain,(
    v3_tdlat_3(sK2) ),
    inference(cnf_transformation,[],[f53])).

fof(f76,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f53])).

fof(f14,axiom,(
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
    inference(ennf_transformation,[],[f14])).

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

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X1,k2_pre_topc(X0,X2))
      | ~ v3_pre_topc(X1,X0)
      | ~ r1_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f77,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f53])).

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

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k2_tarski(X1,X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f63,f57])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r2_hidden(X1,k1_connsp_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,k1_connsp_2(X0,X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,k1_connsp_2(X0,X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,k1_connsp_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f73,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f53])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

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

fof(f54,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f78,plain,(
    m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f53])).

fof(f79,plain,(
    ~ r1_xboole_0(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)),k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))) ),
    inference(cnf_transformation,[],[f53])).

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

fof(f61,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f82,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f59,f57])).

fof(f15,axiom,(
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
    inference(ennf_transformation,[],[f15])).

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

fof(f72,plain,(
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

fof(f80,plain,(
    k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_3,plain,
    ( r1_xboole_0(k2_tarski(X0,X0),X1)
    | r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_948,plain,
    ( r1_xboole_0(k2_tarski(X0_49,X0_49),X1_49)
    | r2_hidden(X0_49,X1_49) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1273,plain,
    ( r1_xboole_0(k2_tarski(X0_49,X0_49),X1_49) = iProver_top
    | r2_hidden(X0_49,X1_49) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_948])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_949,plain,
    ( ~ r1_xboole_0(X0_49,X1_49)
    | r1_xboole_0(X1_49,X0_49) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1272,plain,
    ( r1_xboole_0(X0_49,X1_49) != iProver_top
    | r1_xboole_0(X1_49,X0_49) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_949])).

cnf(c_1699,plain,
    ( r1_xboole_0(X0_49,k2_tarski(X1_49,X1_49)) = iProver_top
    | r2_hidden(X1_49,X0_49) = iProver_top ),
    inference(superposition,[status(thm)],[c_1273,c_1272])).

cnf(c_9,plain,
    ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_15,plain,
    ( v3_pre_topc(X0,X1)
    | ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_344,plain,
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
    inference(resolution_lifted,[status(thm)],[c_9,c_15])).

cnf(c_345,plain,
    ( v3_pre_topc(k2_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v3_tdlat_3(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(unflattening,[status(thm)],[c_344])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_361,plain,
    ( v3_pre_topc(k2_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v3_tdlat_3(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_345,c_7])).

cnf(c_24,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_378,plain,
    ( v3_pre_topc(k2_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v3_tdlat_3(X0)
    | ~ l1_pre_topc(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_361,c_24])).

cnf(c_379,plain,
    ( v3_pre_topc(k2_pre_topc(sK2,X0),sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v3_tdlat_3(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_378])).

cnf(c_23,negated_conjecture,
    ( v3_tdlat_3(sK2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_22,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_383,plain,
    ( v3_pre_topc(k2_pre_topc(sK2,X0),sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_379,c_23,c_22])).

cnf(c_16,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_xboole_0(X0,X2)
    | r1_xboole_0(X0,k2_pre_topc(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_400,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_xboole_0(X0,X2)
    | r1_xboole_0(X0,k2_pre_topc(X1,X2))
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_24])).

cnf(c_401,plain,
    ( ~ v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X0,k2_pre_topc(sK2,X1))
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_400])).

cnf(c_405,plain,
    ( r1_xboole_0(X0,k2_pre_topc(sK2,X1))
    | ~ r1_xboole_0(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v3_pre_topc(X0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_401,c_22])).

cnf(c_406,plain,
    ( ~ v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X0,k2_pre_topc(sK2,X1)) ),
    inference(renaming,[status(thm)],[c_405])).

cnf(c_451,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_xboole_0(X0,X2)
    | r1_xboole_0(X0,k2_pre_topc(sK2,X2))
    | k2_pre_topc(sK2,X1) != X0
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_383,c_406])).

cnf(c_452,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(k2_pre_topc(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_xboole_0(k2_pre_topc(sK2,X0),X1)
    | r1_xboole_0(k2_pre_topc(sK2,X0),k2_pre_topc(sK2,X1)) ),
    inference(unflattening,[status(thm)],[c_451])).

cnf(c_436,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_22])).

cnf(c_437,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(k2_pre_topc(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(unflattening,[status(thm)],[c_436])).

cnf(c_456,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_xboole_0(k2_pre_topc(sK2,X0),X1)
    | r1_xboole_0(k2_pre_topc(sK2,X0),k2_pre_topc(sK2,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_452,c_437])).

cnf(c_457,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_xboole_0(k2_pre_topc(sK2,X1),X0)
    | r1_xboole_0(k2_pre_topc(sK2,X1),k2_pre_topc(sK2,X0)) ),
    inference(renaming,[status(thm)],[c_456])).

cnf(c_935,plain,
    ( ~ m1_subset_1(X0_49,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1_49,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_xboole_0(k2_pre_topc(sK2,X1_49),X0_49)
    | r1_xboole_0(k2_pre_topc(sK2,X1_49),k2_pre_topc(sK2,X0_49)) ),
    inference(subtyping,[status(esa)],[c_457])).

cnf(c_1285,plain,
    ( m1_subset_1(X0_49,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X1_49,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_xboole_0(k2_pre_topc(sK2,X1_49),X0_49) != iProver_top
    | r1_xboole_0(k2_pre_topc(sK2,X1_49),k2_pre_topc(sK2,X0_49)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_935])).

cnf(c_1944,plain,
    ( m1_subset_1(X0_49,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X1_49,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_xboole_0(k2_pre_topc(sK2,X1_49),X0_49) != iProver_top
    | r1_xboole_0(k2_pre_topc(sK2,X0_49),k2_pre_topc(sK2,X1_49)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1285,c_1272])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_940,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1280,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_940])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_944,plain,
    ( ~ m1_subset_1(X0_49,X1_49)
    | v1_xboole_0(X1_49)
    | k6_domain_1(X1_49,X0_49) = k2_tarski(X0_49,X0_49) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1277,plain,
    ( k6_domain_1(X0_49,X1_49) = k2_tarski(X1_49,X1_49)
    | m1_subset_1(X1_49,X0_49) != iProver_top
    | v1_xboole_0(X0_49) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_944])).

cnf(c_2234,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK3) = k2_tarski(sK3,sK3)
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1280,c_1277])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | r2_hidden(X0,k1_connsp_2(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_25,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_297,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | r2_hidden(X0,k1_connsp_2(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_25])).

cnf(c_298,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | r2_hidden(X0,k1_connsp_2(sK2,X0))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_297])).

cnf(c_302,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | r2_hidden(X0,k1_connsp_2(sK2,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_298,c_24,c_22])).

cnf(c_938,plain,
    ( ~ m1_subset_1(X0_49,u1_struct_0(sK2))
    | r2_hidden(X0_49,k1_connsp_2(sK2,X0_49)) ),
    inference(subtyping,[status(esa)],[c_302])).

cnf(c_996,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | r2_hidden(sK3,k1_connsp_2(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_938])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k1_connsp_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_315,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k1_connsp_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_25])).

cnf(c_316,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | m1_subset_1(k1_connsp_2(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_315])).

cnf(c_320,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | m1_subset_1(k1_connsp_2(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_316,c_24,c_22])).

cnf(c_937,plain,
    ( ~ m1_subset_1(X0_49,u1_struct_0(sK2))
    | m1_subset_1(k1_connsp_2(sK2,X0_49),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(subtyping,[status(esa)],[c_320])).

cnf(c_999,plain,
    ( m1_subset_1(k1_connsp_2(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_937])).

cnf(c_1435,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2))
    | k6_domain_1(u1_struct_0(sK2),sK3) = k2_tarski(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_944])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_950,plain,
    ( ~ r2_hidden(X0_49,X1_49)
    | ~ v1_xboole_0(X1_49) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1666,plain,
    ( ~ r2_hidden(X0_49,k1_connsp_2(sK2,X0_49))
    | ~ v1_xboole_0(k1_connsp_2(sK2,X0_49)) ),
    inference(instantiation,[status(thm)],[c_950])).

cnf(c_1668,plain,
    ( ~ r2_hidden(sK3,k1_connsp_2(sK2,sK3))
    | ~ v1_xboole_0(k1_connsp_2(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_1666])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_946,plain,
    ( ~ m1_subset_1(X0_49,k1_zfmisc_1(X1_49))
    | ~ v1_xboole_0(X1_49)
    | v1_xboole_0(X0_49) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1503,plain,
    ( ~ m1_subset_1(X0_49,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(X0_49)
    | ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_946])).

cnf(c_1757,plain,
    ( ~ m1_subset_1(k1_connsp_2(sK2,X0_49),k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(k1_connsp_2(sK2,X0_49))
    | ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1503])).

cnf(c_1759,plain,
    ( ~ m1_subset_1(k1_connsp_2(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(k1_connsp_2(sK2,sK3))
    | ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1757])).

cnf(c_2586,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK3) = k2_tarski(sK3,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2234,c_21,c_996,c_999,c_1435,c_1668,c_1759])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_941,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1279,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_941])).

cnf(c_2233,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK4) = k2_tarski(sK4,sK4)
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1279,c_1277])).

cnf(c_1432,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2))
    | k6_domain_1(u1_struct_0(sK2),sK4) = k2_tarski(sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_944])).

cnf(c_2379,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK4) = k2_tarski(sK4,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2233,c_21,c_20,c_996,c_999,c_1432,c_1668,c_1759])).

cnf(c_19,negated_conjecture,
    ( ~ r1_xboole_0(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)),k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_942,negated_conjecture,
    ( ~ r1_xboole_0(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)),k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1278,plain,
    ( r1_xboole_0(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)),k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_942])).

cnf(c_2384,plain,
    ( r1_xboole_0(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)),k2_pre_topc(sK2,k2_tarski(sK4,sK4))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2379,c_1278])).

cnf(c_2589,plain,
    ( r1_xboole_0(k2_pre_topc(sK2,k2_tarski(sK3,sK3)),k2_pre_topc(sK2,k2_tarski(sK4,sK4))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2586,c_2384])).

cnf(c_2893,plain,
    ( m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(k2_tarski(sK3,sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_xboole_0(k2_pre_topc(sK2,k2_tarski(sK4,sK4)),k2_tarski(sK3,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1944,c_2589])).

cnf(c_30,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_31,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_995,plain,
    ( m1_subset_1(X0_49,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X0_49,k1_connsp_2(sK2,X0_49)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_938])).

cnf(c_997,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK3,k1_connsp_2(sK2,sK3)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_995])).

cnf(c_998,plain,
    ( m1_subset_1(X0_49,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k1_connsp_2(sK2,X0_49),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_937])).

cnf(c_1000,plain,
    ( m1_subset_1(k1_connsp_2(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_998])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_945,plain,
    ( ~ m1_subset_1(X0_49,X1_49)
    | r2_hidden(X0_49,X1_49)
    | v1_xboole_0(X1_49) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1408,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | r2_hidden(sK4,u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_945])).

cnf(c_1409,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK4,u1_struct_0(sK2)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1408])).

cnf(c_1411,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | r2_hidden(sK3,u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_945])).

cnf(c_1412,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK3,u1_struct_0(sK2)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1411])).

cnf(c_1667,plain,
    ( r2_hidden(X0_49,k1_connsp_2(sK2,X0_49)) != iProver_top
    | v1_xboole_0(k1_connsp_2(sK2,X0_49)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1666])).

cnf(c_1669,plain,
    ( r2_hidden(sK3,k1_connsp_2(sK2,sK3)) != iProver_top
    | v1_xboole_0(k1_connsp_2(sK2,sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1667])).

cnf(c_1758,plain,
    ( m1_subset_1(k1_connsp_2(sK2,X0_49),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v1_xboole_0(k1_connsp_2(sK2,X0_49)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1757])).

cnf(c_1760,plain,
    ( m1_subset_1(k1_connsp_2(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v1_xboole_0(k1_connsp_2(sK2,sK3)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1758])).

cnf(c_4,plain,
    ( m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_947,plain,
    ( m1_subset_1(k2_tarski(X0_49,X0_49),k1_zfmisc_1(X1_49))
    | ~ r2_hidden(X0_49,X1_49) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1854,plain,
    ( m1_subset_1(k2_tarski(X0_49,X0_49),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X0_49,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_947])).

cnf(c_1855,plain,
    ( m1_subset_1(k2_tarski(X0_49,X0_49),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | r2_hidden(X0_49,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1854])).

cnf(c_1857,plain,
    ( m1_subset_1(k2_tarski(sK3,sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | r2_hidden(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1855])).

cnf(c_4693,plain,
    ( m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(sK4,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1854])).

cnf(c_4694,plain,
    ( m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | r2_hidden(sK4,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4693])).

cnf(c_5261,plain,
    ( r1_xboole_0(k2_pre_topc(sK2,k2_tarski(sK4,sK4)),k2_tarski(sK3,sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2893,c_30,c_31,c_997,c_1000,c_1409,c_1412,c_1669,c_1760,c_1857,c_4694])).

cnf(c_5266,plain,
    ( r2_hidden(sK3,k2_pre_topc(sK2,k2_tarski(sK4,sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1699,c_5261])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X0,k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2)))
    | ~ v3_tdlat_3(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2)) = k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X0)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_273,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X0,k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2)))
    | ~ v3_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X0)) = k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_25])).

cnf(c_274,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ r2_hidden(X1,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0)))
    | ~ v3_tdlat_3(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X1)) = k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0)) ),
    inference(unflattening,[status(thm)],[c_273])).

cnf(c_278,plain,
    ( ~ r2_hidden(X1,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X1)) = k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_274,c_24,c_23,c_22])).

cnf(c_279,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ r2_hidden(X1,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0)))
    | k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X1)) = k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0)) ),
    inference(renaming,[status(thm)],[c_278])).

cnf(c_939,plain,
    ( ~ m1_subset_1(X0_49,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK2))
    | ~ r2_hidden(X1_49,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0_49)))
    | k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X1_49)) = k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0_49)) ),
    inference(subtyping,[status(esa)],[c_279])).

cnf(c_1281,plain,
    ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0_49)) = k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X1_49))
    | m1_subset_1(X0_49,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X0_49,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X1_49))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_939])).

cnf(c_2406,plain,
    ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0_49)) = k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))
    | m1_subset_1(X0_49,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X0_49,k2_pre_topc(sK2,k2_tarski(sK4,sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2379,c_1281])).

cnf(c_2411,plain,
    ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0_49)) = k2_pre_topc(sK2,k2_tarski(sK4,sK4))
    | m1_subset_1(X0_49,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X0_49,k2_pre_topc(sK2,k2_tarski(sK4,sK4))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2406,c_2379])).

cnf(c_2426,plain,
    ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)) = k2_pre_topc(sK2,k2_tarski(sK4,sK4))
    | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK3,k2_pre_topc(sK2,k2_tarski(sK4,sK4))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2411])).

cnf(c_954,plain,
    ( X0_49 != X1_49
    | X2_49 != X1_49
    | X2_49 = X0_49 ),
    theory(equality)).

cnf(c_1429,plain,
    ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)) != X0_49
    | k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)) != X0_49
    | k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)) = k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)) ),
    inference(instantiation,[status(thm)],[c_954])).

cnf(c_1529,plain,
    ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)) != k2_pre_topc(sK2,X0_49)
    | k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)) != k2_pre_topc(sK2,X0_49)
    | k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)) = k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)) ),
    inference(instantiation,[status(thm)],[c_1429])).

cnf(c_2181,plain,
    ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)) != k2_pre_topc(sK2,k2_tarski(sK4,sK4))
    | k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)) = k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))
    | k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)) != k2_pre_topc(sK2,k2_tarski(sK4,sK4)) ),
    inference(instantiation,[status(thm)],[c_1529])).

cnf(c_959,plain,
    ( X0_49 != X1_49
    | k2_pre_topc(X0_50,X0_49) = k2_pre_topc(X0_50,X1_49) ),
    theory(equality)).

cnf(c_1530,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK4) != X0_49
    | k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)) = k2_pre_topc(sK2,X0_49) ),
    inference(instantiation,[status(thm)],[c_959])).

cnf(c_1899,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK4) != k2_tarski(sK4,sK4)
    | k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)) = k2_pre_topc(sK2,k2_tarski(sK4,sK4)) ),
    inference(instantiation,[status(thm)],[c_1530])).

cnf(c_18,negated_conjecture,
    ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_943,negated_conjecture,
    ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5266,c_2426,c_2181,c_1899,c_1759,c_1668,c_1432,c_999,c_996,c_943,c_31,c_20,c_30,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:58:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.67/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.67/0.98  
% 2.67/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.67/0.98  
% 2.67/0.98  ------  iProver source info
% 2.67/0.98  
% 2.67/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.67/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.67/0.98  git: non_committed_changes: false
% 2.67/0.98  git: last_make_outside_of_git: false
% 2.67/0.98  
% 2.67/0.98  ------ 
% 2.67/0.98  
% 2.67/0.98  ------ Input Options
% 2.67/0.98  
% 2.67/0.98  --out_options                           all
% 2.67/0.98  --tptp_safe_out                         true
% 2.67/0.98  --problem_path                          ""
% 2.67/0.98  --include_path                          ""
% 2.67/0.98  --clausifier                            res/vclausify_rel
% 2.67/0.98  --clausifier_options                    --mode clausify
% 2.67/0.98  --stdin                                 false
% 2.67/0.98  --stats_out                             all
% 2.67/0.98  
% 2.67/0.98  ------ General Options
% 2.67/0.98  
% 2.67/0.98  --fof                                   false
% 2.67/0.98  --time_out_real                         305.
% 2.67/0.98  --time_out_virtual                      -1.
% 2.67/0.98  --symbol_type_check                     false
% 2.67/0.98  --clausify_out                          false
% 2.67/0.98  --sig_cnt_out                           false
% 2.67/0.98  --trig_cnt_out                          false
% 2.67/0.98  --trig_cnt_out_tolerance                1.
% 2.67/0.98  --trig_cnt_out_sk_spl                   false
% 2.67/0.98  --abstr_cl_out                          false
% 2.67/0.98  
% 2.67/0.98  ------ Global Options
% 2.67/0.98  
% 2.67/0.98  --schedule                              default
% 2.67/0.98  --add_important_lit                     false
% 2.67/0.98  --prop_solver_per_cl                    1000
% 2.67/0.98  --min_unsat_core                        false
% 2.67/0.98  --soft_assumptions                      false
% 2.67/0.98  --soft_lemma_size                       3
% 2.67/0.98  --prop_impl_unit_size                   0
% 2.67/0.98  --prop_impl_unit                        []
% 2.67/0.98  --share_sel_clauses                     true
% 2.67/0.98  --reset_solvers                         false
% 2.67/0.98  --bc_imp_inh                            [conj_cone]
% 2.67/0.98  --conj_cone_tolerance                   3.
% 2.67/0.98  --extra_neg_conj                        none
% 2.67/0.98  --large_theory_mode                     true
% 2.67/0.98  --prolific_symb_bound                   200
% 2.67/0.98  --lt_threshold                          2000
% 2.67/0.98  --clause_weak_htbl                      true
% 2.67/0.98  --gc_record_bc_elim                     false
% 2.67/0.98  
% 2.67/0.98  ------ Preprocessing Options
% 2.67/0.98  
% 2.67/0.98  --preprocessing_flag                    true
% 2.67/0.98  --time_out_prep_mult                    0.1
% 2.67/0.98  --splitting_mode                        input
% 2.67/0.98  --splitting_grd                         true
% 2.67/0.98  --splitting_cvd                         false
% 2.67/0.98  --splitting_cvd_svl                     false
% 2.67/0.98  --splitting_nvd                         32
% 2.67/0.98  --sub_typing                            true
% 2.67/0.98  --prep_gs_sim                           true
% 2.67/0.98  --prep_unflatten                        true
% 2.67/0.98  --prep_res_sim                          true
% 2.67/0.98  --prep_upred                            true
% 2.67/0.98  --prep_sem_filter                       exhaustive
% 2.67/0.98  --prep_sem_filter_out                   false
% 2.67/0.98  --pred_elim                             true
% 2.67/0.98  --res_sim_input                         true
% 2.67/0.98  --eq_ax_congr_red                       true
% 2.67/0.98  --pure_diseq_elim                       true
% 2.67/0.98  --brand_transform                       false
% 2.67/0.98  --non_eq_to_eq                          false
% 2.67/0.98  --prep_def_merge                        true
% 2.67/0.98  --prep_def_merge_prop_impl              false
% 2.67/0.98  --prep_def_merge_mbd                    true
% 2.67/0.98  --prep_def_merge_tr_red                 false
% 2.67/0.98  --prep_def_merge_tr_cl                  false
% 2.67/0.98  --smt_preprocessing                     true
% 2.67/0.98  --smt_ac_axioms                         fast
% 2.67/0.98  --preprocessed_out                      false
% 2.67/0.98  --preprocessed_stats                    false
% 2.67/0.98  
% 2.67/0.98  ------ Abstraction refinement Options
% 2.67/0.98  
% 2.67/0.98  --abstr_ref                             []
% 2.67/0.98  --abstr_ref_prep                        false
% 2.67/0.98  --abstr_ref_until_sat                   false
% 2.67/0.98  --abstr_ref_sig_restrict                funpre
% 2.67/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.67/0.98  --abstr_ref_under                       []
% 2.67/0.98  
% 2.67/0.98  ------ SAT Options
% 2.67/0.98  
% 2.67/0.98  --sat_mode                              false
% 2.67/0.98  --sat_fm_restart_options                ""
% 2.67/0.98  --sat_gr_def                            false
% 2.67/0.98  --sat_epr_types                         true
% 2.67/0.98  --sat_non_cyclic_types                  false
% 2.67/0.98  --sat_finite_models                     false
% 2.67/0.98  --sat_fm_lemmas                         false
% 2.67/0.98  --sat_fm_prep                           false
% 2.67/0.98  --sat_fm_uc_incr                        true
% 2.67/0.98  --sat_out_model                         small
% 2.67/0.98  --sat_out_clauses                       false
% 2.67/0.98  
% 2.67/0.98  ------ QBF Options
% 2.67/0.98  
% 2.67/0.98  --qbf_mode                              false
% 2.67/0.98  --qbf_elim_univ                         false
% 2.67/0.98  --qbf_dom_inst                          none
% 2.67/0.98  --qbf_dom_pre_inst                      false
% 2.67/0.98  --qbf_sk_in                             false
% 2.67/0.98  --qbf_pred_elim                         true
% 2.67/0.98  --qbf_split                             512
% 2.67/0.98  
% 2.67/0.98  ------ BMC1 Options
% 2.67/0.98  
% 2.67/0.98  --bmc1_incremental                      false
% 2.67/0.98  --bmc1_axioms                           reachable_all
% 2.67/0.98  --bmc1_min_bound                        0
% 2.67/0.98  --bmc1_max_bound                        -1
% 2.67/0.98  --bmc1_max_bound_default                -1
% 2.67/0.98  --bmc1_symbol_reachability              true
% 2.67/0.98  --bmc1_property_lemmas                  false
% 2.67/0.98  --bmc1_k_induction                      false
% 2.67/0.98  --bmc1_non_equiv_states                 false
% 2.67/0.98  --bmc1_deadlock                         false
% 2.67/0.98  --bmc1_ucm                              false
% 2.67/0.98  --bmc1_add_unsat_core                   none
% 2.67/0.98  --bmc1_unsat_core_children              false
% 2.67/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.67/0.98  --bmc1_out_stat                         full
% 2.67/0.98  --bmc1_ground_init                      false
% 2.67/0.98  --bmc1_pre_inst_next_state              false
% 2.67/0.98  --bmc1_pre_inst_state                   false
% 2.67/0.98  --bmc1_pre_inst_reach_state             false
% 2.67/0.98  --bmc1_out_unsat_core                   false
% 2.67/0.98  --bmc1_aig_witness_out                  false
% 2.67/0.98  --bmc1_verbose                          false
% 2.67/0.98  --bmc1_dump_clauses_tptp                false
% 2.67/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.67/0.98  --bmc1_dump_file                        -
% 2.67/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.67/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.67/0.98  --bmc1_ucm_extend_mode                  1
% 2.67/0.98  --bmc1_ucm_init_mode                    2
% 2.67/0.98  --bmc1_ucm_cone_mode                    none
% 2.67/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.67/0.98  --bmc1_ucm_relax_model                  4
% 2.67/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.67/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.67/0.98  --bmc1_ucm_layered_model                none
% 2.67/0.98  --bmc1_ucm_max_lemma_size               10
% 2.67/0.98  
% 2.67/0.98  ------ AIG Options
% 2.67/0.98  
% 2.67/0.98  --aig_mode                              false
% 2.67/0.98  
% 2.67/0.98  ------ Instantiation Options
% 2.67/0.98  
% 2.67/0.98  --instantiation_flag                    true
% 2.67/0.98  --inst_sos_flag                         false
% 2.67/0.98  --inst_sos_phase                        true
% 2.67/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.67/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.67/0.98  --inst_lit_sel_side                     num_symb
% 2.67/0.98  --inst_solver_per_active                1400
% 2.67/0.98  --inst_solver_calls_frac                1.
% 2.67/0.98  --inst_passive_queue_type               priority_queues
% 2.67/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.67/0.98  --inst_passive_queues_freq              [25;2]
% 2.67/0.98  --inst_dismatching                      true
% 2.67/0.98  --inst_eager_unprocessed_to_passive     true
% 2.67/0.98  --inst_prop_sim_given                   true
% 2.67/0.98  --inst_prop_sim_new                     false
% 2.67/0.98  --inst_subs_new                         false
% 2.67/0.98  --inst_eq_res_simp                      false
% 2.67/0.98  --inst_subs_given                       false
% 2.67/0.98  --inst_orphan_elimination               true
% 2.67/0.98  --inst_learning_loop_flag               true
% 2.67/0.98  --inst_learning_start                   3000
% 2.67/0.98  --inst_learning_factor                  2
% 2.67/0.98  --inst_start_prop_sim_after_learn       3
% 2.67/0.98  --inst_sel_renew                        solver
% 2.67/0.98  --inst_lit_activity_flag                true
% 2.67/0.98  --inst_restr_to_given                   false
% 2.67/0.98  --inst_activity_threshold               500
% 2.67/0.98  --inst_out_proof                        true
% 2.67/0.98  
% 2.67/0.98  ------ Resolution Options
% 2.67/0.98  
% 2.67/0.98  --resolution_flag                       true
% 2.67/0.98  --res_lit_sel                           adaptive
% 2.67/0.98  --res_lit_sel_side                      none
% 2.67/0.98  --res_ordering                          kbo
% 2.67/0.98  --res_to_prop_solver                    active
% 2.67/0.98  --res_prop_simpl_new                    false
% 2.67/0.98  --res_prop_simpl_given                  true
% 2.67/0.98  --res_passive_queue_type                priority_queues
% 2.67/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.67/0.98  --res_passive_queues_freq               [15;5]
% 2.67/0.98  --res_forward_subs                      full
% 2.67/0.98  --res_backward_subs                     full
% 2.67/0.98  --res_forward_subs_resolution           true
% 2.67/0.98  --res_backward_subs_resolution          true
% 2.67/0.98  --res_orphan_elimination                true
% 2.67/0.98  --res_time_limit                        2.
% 2.67/0.98  --res_out_proof                         true
% 2.67/0.98  
% 2.67/0.98  ------ Superposition Options
% 2.67/0.98  
% 2.67/0.98  --superposition_flag                    true
% 2.67/0.98  --sup_passive_queue_type                priority_queues
% 2.67/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.67/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.67/0.98  --demod_completeness_check              fast
% 2.67/0.98  --demod_use_ground                      true
% 2.67/0.98  --sup_to_prop_solver                    passive
% 2.67/0.98  --sup_prop_simpl_new                    true
% 2.67/0.98  --sup_prop_simpl_given                  true
% 2.67/0.98  --sup_fun_splitting                     false
% 2.67/0.98  --sup_smt_interval                      50000
% 2.67/0.98  
% 2.67/0.98  ------ Superposition Simplification Setup
% 2.67/0.98  
% 2.67/0.98  --sup_indices_passive                   []
% 2.67/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.67/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.67/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.67/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.67/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.67/0.98  --sup_full_bw                           [BwDemod]
% 2.67/0.98  --sup_immed_triv                        [TrivRules]
% 2.67/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.67/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.67/0.98  --sup_immed_bw_main                     []
% 2.67/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.67/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.67/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.67/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.67/0.98  
% 2.67/0.98  ------ Combination Options
% 2.67/0.98  
% 2.67/0.98  --comb_res_mult                         3
% 2.67/0.98  --comb_sup_mult                         2
% 2.67/0.98  --comb_inst_mult                        10
% 2.67/0.98  
% 2.67/0.98  ------ Debug Options
% 2.67/0.98  
% 2.67/0.98  --dbg_backtrace                         false
% 2.67/0.98  --dbg_dump_prop_clauses                 false
% 2.67/0.98  --dbg_dump_prop_clauses_file            -
% 2.67/0.98  --dbg_out_stat                          false
% 2.67/0.98  ------ Parsing...
% 2.67/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.67/0.98  
% 2.67/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 2.67/0.98  
% 2.67/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.67/0.98  
% 2.67/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.67/0.98  ------ Proving...
% 2.67/0.98  ------ Problem Properties 
% 2.67/0.98  
% 2.67/0.98  
% 2.67/0.98  clauses                                 17
% 2.67/0.98  conjectures                             4
% 2.67/0.98  EPR                                     3
% 2.67/0.98  Horn                                    13
% 2.67/0.98  unary                                   4
% 2.67/0.98  binary                                  8
% 2.67/0.98  lits                                    37
% 2.67/0.98  lits eq                                 3
% 2.67/0.98  fd_pure                                 0
% 2.67/0.98  fd_pseudo                               0
% 2.67/0.98  fd_cond                                 0
% 2.67/0.98  fd_pseudo_cond                          0
% 2.67/0.98  AC symbols                              0
% 2.67/0.98  
% 2.67/0.98  ------ Schedule dynamic 5 is on 
% 2.67/0.98  
% 2.67/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.67/0.98  
% 2.67/0.98  
% 2.67/0.98  ------ 
% 2.67/0.98  Current options:
% 2.67/0.98  ------ 
% 2.67/0.98  
% 2.67/0.98  ------ Input Options
% 2.67/0.98  
% 2.67/0.98  --out_options                           all
% 2.67/0.98  --tptp_safe_out                         true
% 2.67/0.98  --problem_path                          ""
% 2.67/0.98  --include_path                          ""
% 2.67/0.98  --clausifier                            res/vclausify_rel
% 2.67/0.98  --clausifier_options                    --mode clausify
% 2.67/0.98  --stdin                                 false
% 2.67/0.98  --stats_out                             all
% 2.67/0.98  
% 2.67/0.98  ------ General Options
% 2.67/0.98  
% 2.67/0.98  --fof                                   false
% 2.67/0.98  --time_out_real                         305.
% 2.67/0.98  --time_out_virtual                      -1.
% 2.67/0.98  --symbol_type_check                     false
% 2.67/0.98  --clausify_out                          false
% 2.67/0.98  --sig_cnt_out                           false
% 2.67/0.98  --trig_cnt_out                          false
% 2.67/0.98  --trig_cnt_out_tolerance                1.
% 2.67/0.98  --trig_cnt_out_sk_spl                   false
% 2.67/0.98  --abstr_cl_out                          false
% 2.67/0.98  
% 2.67/0.98  ------ Global Options
% 2.67/0.98  
% 2.67/0.98  --schedule                              default
% 2.67/0.98  --add_important_lit                     false
% 2.67/0.98  --prop_solver_per_cl                    1000
% 2.67/0.98  --min_unsat_core                        false
% 2.67/0.98  --soft_assumptions                      false
% 2.67/0.98  --soft_lemma_size                       3
% 2.67/0.98  --prop_impl_unit_size                   0
% 2.67/0.98  --prop_impl_unit                        []
% 2.67/0.98  --share_sel_clauses                     true
% 2.67/0.98  --reset_solvers                         false
% 2.67/0.98  --bc_imp_inh                            [conj_cone]
% 2.67/0.98  --conj_cone_tolerance                   3.
% 2.67/0.98  --extra_neg_conj                        none
% 2.67/0.98  --large_theory_mode                     true
% 2.67/0.98  --prolific_symb_bound                   200
% 2.67/0.98  --lt_threshold                          2000
% 2.67/0.98  --clause_weak_htbl                      true
% 2.67/0.98  --gc_record_bc_elim                     false
% 2.67/0.98  
% 2.67/0.98  ------ Preprocessing Options
% 2.67/0.98  
% 2.67/0.98  --preprocessing_flag                    true
% 2.67/0.98  --time_out_prep_mult                    0.1
% 2.67/0.98  --splitting_mode                        input
% 2.67/0.98  --splitting_grd                         true
% 2.67/0.98  --splitting_cvd                         false
% 2.67/0.98  --splitting_cvd_svl                     false
% 2.67/0.98  --splitting_nvd                         32
% 2.67/0.98  --sub_typing                            true
% 2.67/0.98  --prep_gs_sim                           true
% 2.67/0.98  --prep_unflatten                        true
% 2.67/0.98  --prep_res_sim                          true
% 2.67/0.98  --prep_upred                            true
% 2.67/0.98  --prep_sem_filter                       exhaustive
% 2.67/0.98  --prep_sem_filter_out                   false
% 2.67/0.98  --pred_elim                             true
% 2.67/0.98  --res_sim_input                         true
% 2.67/0.98  --eq_ax_congr_red                       true
% 2.67/0.98  --pure_diseq_elim                       true
% 2.67/0.98  --brand_transform                       false
% 2.67/0.98  --non_eq_to_eq                          false
% 2.67/0.98  --prep_def_merge                        true
% 2.67/0.98  --prep_def_merge_prop_impl              false
% 2.67/0.98  --prep_def_merge_mbd                    true
% 2.67/0.98  --prep_def_merge_tr_red                 false
% 2.67/0.98  --prep_def_merge_tr_cl                  false
% 2.67/0.98  --smt_preprocessing                     true
% 2.67/0.98  --smt_ac_axioms                         fast
% 2.67/0.98  --preprocessed_out                      false
% 2.67/0.98  --preprocessed_stats                    false
% 2.67/0.98  
% 2.67/0.98  ------ Abstraction refinement Options
% 2.67/0.98  
% 2.67/0.98  --abstr_ref                             []
% 2.67/0.98  --abstr_ref_prep                        false
% 2.67/0.98  --abstr_ref_until_sat                   false
% 2.67/0.98  --abstr_ref_sig_restrict                funpre
% 2.67/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.67/0.98  --abstr_ref_under                       []
% 2.67/0.98  
% 2.67/0.98  ------ SAT Options
% 2.67/0.98  
% 2.67/0.98  --sat_mode                              false
% 2.67/0.98  --sat_fm_restart_options                ""
% 2.67/0.98  --sat_gr_def                            false
% 2.67/0.98  --sat_epr_types                         true
% 2.67/0.98  --sat_non_cyclic_types                  false
% 2.67/0.98  --sat_finite_models                     false
% 2.67/0.98  --sat_fm_lemmas                         false
% 2.67/0.98  --sat_fm_prep                           false
% 2.67/0.98  --sat_fm_uc_incr                        true
% 2.67/0.98  --sat_out_model                         small
% 2.67/0.98  --sat_out_clauses                       false
% 2.67/0.98  
% 2.67/0.98  ------ QBF Options
% 2.67/0.98  
% 2.67/0.98  --qbf_mode                              false
% 2.67/0.98  --qbf_elim_univ                         false
% 2.67/0.98  --qbf_dom_inst                          none
% 2.67/0.98  --qbf_dom_pre_inst                      false
% 2.67/0.98  --qbf_sk_in                             false
% 2.67/0.98  --qbf_pred_elim                         true
% 2.67/0.98  --qbf_split                             512
% 2.67/0.98  
% 2.67/0.98  ------ BMC1 Options
% 2.67/0.98  
% 2.67/0.98  --bmc1_incremental                      false
% 2.67/0.98  --bmc1_axioms                           reachable_all
% 2.67/0.98  --bmc1_min_bound                        0
% 2.67/0.98  --bmc1_max_bound                        -1
% 2.67/0.98  --bmc1_max_bound_default                -1
% 2.67/0.98  --bmc1_symbol_reachability              true
% 2.67/0.98  --bmc1_property_lemmas                  false
% 2.67/0.98  --bmc1_k_induction                      false
% 2.67/0.98  --bmc1_non_equiv_states                 false
% 2.67/0.98  --bmc1_deadlock                         false
% 2.67/0.98  --bmc1_ucm                              false
% 2.67/0.98  --bmc1_add_unsat_core                   none
% 2.67/0.98  --bmc1_unsat_core_children              false
% 2.67/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.67/0.98  --bmc1_out_stat                         full
% 2.67/0.98  --bmc1_ground_init                      false
% 2.67/0.98  --bmc1_pre_inst_next_state              false
% 2.67/0.98  --bmc1_pre_inst_state                   false
% 2.67/0.98  --bmc1_pre_inst_reach_state             false
% 2.67/0.98  --bmc1_out_unsat_core                   false
% 2.67/0.98  --bmc1_aig_witness_out                  false
% 2.67/0.98  --bmc1_verbose                          false
% 2.67/0.98  --bmc1_dump_clauses_tptp                false
% 2.67/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.67/0.98  --bmc1_dump_file                        -
% 2.67/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.67/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.67/0.98  --bmc1_ucm_extend_mode                  1
% 2.67/0.98  --bmc1_ucm_init_mode                    2
% 2.67/0.98  --bmc1_ucm_cone_mode                    none
% 2.67/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.67/0.98  --bmc1_ucm_relax_model                  4
% 2.67/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.67/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.67/0.98  --bmc1_ucm_layered_model                none
% 2.67/0.98  --bmc1_ucm_max_lemma_size               10
% 2.67/0.98  
% 2.67/0.98  ------ AIG Options
% 2.67/0.98  
% 2.67/0.98  --aig_mode                              false
% 2.67/0.98  
% 2.67/0.98  ------ Instantiation Options
% 2.67/0.98  
% 2.67/0.98  --instantiation_flag                    true
% 2.67/0.98  --inst_sos_flag                         false
% 2.67/0.98  --inst_sos_phase                        true
% 2.67/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.67/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.67/0.98  --inst_lit_sel_side                     none
% 2.67/0.98  --inst_solver_per_active                1400
% 2.67/0.98  --inst_solver_calls_frac                1.
% 2.67/0.98  --inst_passive_queue_type               priority_queues
% 2.67/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.67/0.98  --inst_passive_queues_freq              [25;2]
% 2.67/0.98  --inst_dismatching                      true
% 2.67/0.98  --inst_eager_unprocessed_to_passive     true
% 2.67/0.98  --inst_prop_sim_given                   true
% 2.67/0.98  --inst_prop_sim_new                     false
% 2.67/0.98  --inst_subs_new                         false
% 2.67/0.98  --inst_eq_res_simp                      false
% 2.67/0.98  --inst_subs_given                       false
% 2.67/0.98  --inst_orphan_elimination               true
% 2.67/0.98  --inst_learning_loop_flag               true
% 2.67/0.98  --inst_learning_start                   3000
% 2.67/0.98  --inst_learning_factor                  2
% 2.67/0.98  --inst_start_prop_sim_after_learn       3
% 2.67/0.98  --inst_sel_renew                        solver
% 2.67/0.98  --inst_lit_activity_flag                true
% 2.67/0.98  --inst_restr_to_given                   false
% 2.67/0.98  --inst_activity_threshold               500
% 2.67/0.98  --inst_out_proof                        true
% 2.67/0.98  
% 2.67/0.98  ------ Resolution Options
% 2.67/0.98  
% 2.67/0.98  --resolution_flag                       false
% 2.67/0.98  --res_lit_sel                           adaptive
% 2.67/0.98  --res_lit_sel_side                      none
% 2.67/0.99  --res_ordering                          kbo
% 2.67/0.99  --res_to_prop_solver                    active
% 2.67/0.99  --res_prop_simpl_new                    false
% 2.67/0.99  --res_prop_simpl_given                  true
% 2.67/0.99  --res_passive_queue_type                priority_queues
% 2.67/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.67/0.99  --res_passive_queues_freq               [15;5]
% 2.67/0.99  --res_forward_subs                      full
% 2.67/0.99  --res_backward_subs                     full
% 2.67/0.99  --res_forward_subs_resolution           true
% 2.67/0.99  --res_backward_subs_resolution          true
% 2.67/0.99  --res_orphan_elimination                true
% 2.67/0.99  --res_time_limit                        2.
% 2.67/0.99  --res_out_proof                         true
% 2.67/0.99  
% 2.67/0.99  ------ Superposition Options
% 2.67/0.99  
% 2.67/0.99  --superposition_flag                    true
% 2.67/0.99  --sup_passive_queue_type                priority_queues
% 2.67/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.67/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.67/0.99  --demod_completeness_check              fast
% 2.67/0.99  --demod_use_ground                      true
% 2.67/0.99  --sup_to_prop_solver                    passive
% 2.67/0.99  --sup_prop_simpl_new                    true
% 2.67/0.99  --sup_prop_simpl_given                  true
% 2.67/0.99  --sup_fun_splitting                     false
% 2.67/0.99  --sup_smt_interval                      50000
% 2.67/0.99  
% 2.67/0.99  ------ Superposition Simplification Setup
% 2.67/0.99  
% 2.67/0.99  --sup_indices_passive                   []
% 2.67/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.67/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.67/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.67/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.67/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.67/0.99  --sup_full_bw                           [BwDemod]
% 2.67/0.99  --sup_immed_triv                        [TrivRules]
% 2.67/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.67/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.67/0.99  --sup_immed_bw_main                     []
% 2.67/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.67/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.67/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.67/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.67/0.99  
% 2.67/0.99  ------ Combination Options
% 2.67/0.99  
% 2.67/0.99  --comb_res_mult                         3
% 2.67/0.99  --comb_sup_mult                         2
% 2.67/0.99  --comb_inst_mult                        10
% 2.67/0.99  
% 2.67/0.99  ------ Debug Options
% 2.67/0.99  
% 2.67/0.99  --dbg_backtrace                         false
% 2.67/0.99  --dbg_dump_prop_clauses                 false
% 2.67/0.99  --dbg_dump_prop_clauses_file            -
% 2.67/0.99  --dbg_out_stat                          false
% 2.67/0.99  
% 2.67/0.99  
% 2.67/0.99  
% 2.67/0.99  
% 2.67/0.99  ------ Proving...
% 2.67/0.99  
% 2.67/0.99  
% 2.67/0.99  % SZS status Theorem for theBenchmark.p
% 2.67/0.99  
% 2.67/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.67/0.99  
% 2.67/0.99  fof(f4,axiom,(
% 2.67/0.99    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 2.67/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/0.99  
% 2.67/0.99  fof(f19,plain,(
% 2.67/0.99    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 2.67/0.99    inference(ennf_transformation,[],[f4])).
% 2.67/0.99  
% 2.67/0.99  fof(f58,plain,(
% 2.67/0.99    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 2.67/0.99    inference(cnf_transformation,[],[f19])).
% 2.67/0.99  
% 2.67/0.99  fof(f3,axiom,(
% 2.67/0.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.67/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/0.99  
% 2.67/0.99  fof(f57,plain,(
% 2.67/0.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.67/0.99    inference(cnf_transformation,[],[f3])).
% 2.67/0.99  
% 2.67/0.99  fof(f81,plain,(
% 2.67/0.99    ( ! [X0,X1] : (r1_xboole_0(k2_tarski(X0,X0),X1) | r2_hidden(X0,X1)) )),
% 2.67/0.99    inference(definition_unfolding,[],[f58,f57])).
% 2.67/0.99  
% 2.67/0.99  fof(f2,axiom,(
% 2.67/0.99    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 2.67/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/0.99  
% 2.67/0.99  fof(f18,plain,(
% 2.67/0.99    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 2.67/0.99    inference(ennf_transformation,[],[f2])).
% 2.67/0.99  
% 2.67/0.99  fof(f56,plain,(
% 2.67/0.99    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 2.67/0.99    inference(cnf_transformation,[],[f18])).
% 2.67/0.99  
% 2.67/0.99  fof(f10,axiom,(
% 2.67/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_pre_topc(X0,X1),X0))),
% 2.67/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/0.99  
% 2.67/0.99  fof(f28,plain,(
% 2.67/0.99    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.67/0.99    inference(ennf_transformation,[],[f10])).
% 2.67/0.99  
% 2.67/0.99  fof(f29,plain,(
% 2.67/0.99    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.67/0.99    inference(flattening,[],[f28])).
% 2.67/0.99  
% 2.67/0.99  fof(f64,plain,(
% 2.67/0.99    ( ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.67/0.99    inference(cnf_transformation,[],[f29])).
% 2.67/0.99  
% 2.67/0.99  fof(f13,axiom,(
% 2.67/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v3_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => v3_pre_topc(X1,X0)))))),
% 2.67/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/0.99  
% 2.67/0.99  fof(f34,plain,(
% 2.67/0.99    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : ((v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.67/0.99    inference(ennf_transformation,[],[f13])).
% 2.67/0.99  
% 2.67/0.99  fof(f35,plain,(
% 2.67/0.99    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.67/0.99    inference(flattening,[],[f34])).
% 2.67/0.99  
% 2.67/0.99  fof(f46,plain,(
% 2.67/0.99    ! [X0] : (((v3_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X1] : (v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.67/0.99    inference(nnf_transformation,[],[f35])).
% 2.67/0.99  
% 2.67/0.99  fof(f47,plain,(
% 2.67/0.99    ! [X0] : (((v3_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.67/0.99    inference(rectify,[],[f46])).
% 2.67/0.99  
% 2.67/0.99  fof(f48,plain,(
% 2.67/0.99    ! [X0] : (? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK1(X0),X0) & v4_pre_topc(sK1(X0),X0) & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.67/0.99    introduced(choice_axiom,[])).
% 2.67/0.99  
% 2.67/0.99  fof(f49,plain,(
% 2.67/0.99    ! [X0] : (((v3_tdlat_3(X0) | (~v3_pre_topc(sK1(X0),X0) & v4_pre_topc(sK1(X0),X0) & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.67/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f47,f48])).
% 2.67/0.99  
% 2.67/0.99  fof(f67,plain,(
% 2.67/0.99    ( ! [X2,X0] : (v3_pre_topc(X2,X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tdlat_3(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.67/0.99    inference(cnf_transformation,[],[f49])).
% 2.67/0.99  
% 2.67/0.99  fof(f8,axiom,(
% 2.67/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.67/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/0.99  
% 2.67/0.99  fof(f24,plain,(
% 2.67/0.99    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.67/0.99    inference(ennf_transformation,[],[f8])).
% 2.67/0.99  
% 2.67/0.99  fof(f25,plain,(
% 2.67/0.99    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.67/0.99    inference(flattening,[],[f24])).
% 2.67/0.99  
% 2.67/0.99  fof(f62,plain,(
% 2.67/0.99    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.67/0.99    inference(cnf_transformation,[],[f25])).
% 2.67/0.99  
% 2.67/0.99  fof(f16,conjecture,(
% 2.67/0.99    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) | r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))))))),
% 2.67/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/0.99  
% 2.67/0.99  fof(f17,negated_conjecture,(
% 2.67/0.99    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) | r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))))))),
% 2.67/0.99    inference(negated_conjecture,[],[f16])).
% 2.67/0.99  
% 2.67/0.99  fof(f40,plain,(
% 2.67/0.99    ? [X0] : (? [X1] : (? [X2] : ((k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.67/0.99    inference(ennf_transformation,[],[f17])).
% 2.67/0.99  
% 2.67/0.99  fof(f41,plain,(
% 2.67/0.99    ? [X0] : (? [X1] : (? [X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.67/0.99    inference(flattening,[],[f40])).
% 2.67/0.99  
% 2.67/0.99  fof(f52,plain,(
% 2.67/0.99    ( ! [X0,X1] : (? [X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & m1_subset_1(X2,u1_struct_0(X0))) => (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK4)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK4))) & m1_subset_1(sK4,u1_struct_0(X0)))) )),
% 2.67/0.99    introduced(choice_axiom,[])).
% 2.67/0.99  
% 2.67/0.99  fof(f51,plain,(
% 2.67/0.99    ( ! [X0] : (? [X1] : (? [X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK3)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK3,u1_struct_0(X0)))) )),
% 2.67/0.99    introduced(choice_axiom,[])).
% 2.67/0.99  
% 2.67/0.99  fof(f50,plain,(
% 2.67/0.99    ? [X0] : (? [X1] : (? [X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X1)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X2)) & ~r1_xboole_0(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X1)),k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X2))) & m1_subset_1(X2,u1_struct_0(sK2))) & m1_subset_1(X1,u1_struct_0(sK2))) & l1_pre_topc(sK2) & v3_tdlat_3(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 2.67/0.99    introduced(choice_axiom,[])).
% 2.67/0.99  
% 2.67/0.99  fof(f53,plain,(
% 2.67/0.99    ((k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)) & ~r1_xboole_0(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)),k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))) & m1_subset_1(sK4,u1_struct_0(sK2))) & m1_subset_1(sK3,u1_struct_0(sK2))) & l1_pre_topc(sK2) & v3_tdlat_3(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 2.67/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f41,f52,f51,f50])).
% 2.67/0.99  
% 2.67/0.99  fof(f74,plain,(
% 2.67/0.99    v2_pre_topc(sK2)),
% 2.67/0.99    inference(cnf_transformation,[],[f53])).
% 2.67/0.99  
% 2.67/0.99  fof(f75,plain,(
% 2.67/0.99    v3_tdlat_3(sK2)),
% 2.67/0.99    inference(cnf_transformation,[],[f53])).
% 2.67/0.99  
% 2.67/0.99  fof(f76,plain,(
% 2.67/0.99    l1_pre_topc(sK2)),
% 2.67/0.99    inference(cnf_transformation,[],[f53])).
% 2.67/0.99  
% 2.67/0.99  fof(f14,axiom,(
% 2.67/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X1,X0) & r1_xboole_0(X1,X2)) => r1_xboole_0(X1,k2_pre_topc(X0,X2))))))),
% 2.67/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/0.99  
% 2.67/0.99  fof(f36,plain,(
% 2.67/0.99    ! [X0] : (! [X1] : (! [X2] : ((r1_xboole_0(X1,k2_pre_topc(X0,X2)) | (~v3_pre_topc(X1,X0) | ~r1_xboole_0(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.67/0.99    inference(ennf_transformation,[],[f14])).
% 2.67/0.99  
% 2.67/0.99  fof(f37,plain,(
% 2.67/0.99    ! [X0] : (! [X1] : (! [X2] : (r1_xboole_0(X1,k2_pre_topc(X0,X2)) | ~v3_pre_topc(X1,X0) | ~r1_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.67/0.99    inference(flattening,[],[f36])).
% 2.67/0.99  
% 2.67/0.99  fof(f71,plain,(
% 2.67/0.99    ( ! [X2,X0,X1] : (r1_xboole_0(X1,k2_pre_topc(X0,X2)) | ~v3_pre_topc(X1,X0) | ~r1_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.67/0.99    inference(cnf_transformation,[],[f37])).
% 2.67/0.99  
% 2.67/0.99  fof(f77,plain,(
% 2.67/0.99    m1_subset_1(sK3,u1_struct_0(sK2))),
% 2.67/0.99    inference(cnf_transformation,[],[f53])).
% 2.67/0.99  
% 2.67/0.99  fof(f9,axiom,(
% 2.67/0.99    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 2.67/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/0.99  
% 2.67/0.99  fof(f26,plain,(
% 2.67/0.99    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 2.67/0.99    inference(ennf_transformation,[],[f9])).
% 2.67/0.99  
% 2.67/0.99  fof(f27,plain,(
% 2.67/0.99    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 2.67/0.99    inference(flattening,[],[f26])).
% 2.67/0.99  
% 2.67/0.99  fof(f63,plain,(
% 2.67/0.99    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.67/0.99    inference(cnf_transformation,[],[f27])).
% 2.67/0.99  
% 2.67/0.99  fof(f83,plain,(
% 2.67/0.99    ( ! [X0,X1] : (k2_tarski(X1,X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.67/0.99    inference(definition_unfolding,[],[f63,f57])).
% 2.67/0.99  
% 2.67/0.99  fof(f12,axiom,(
% 2.67/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r2_hidden(X1,k1_connsp_2(X0,X1))))),
% 2.67/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/0.99  
% 2.67/0.99  fof(f32,plain,(
% 2.67/0.99    ! [X0] : (! [X1] : (r2_hidden(X1,k1_connsp_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.67/0.99    inference(ennf_transformation,[],[f12])).
% 2.67/0.99  
% 2.67/0.99  fof(f33,plain,(
% 2.67/0.99    ! [X0] : (! [X1] : (r2_hidden(X1,k1_connsp_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.67/0.99    inference(flattening,[],[f32])).
% 2.67/0.99  
% 2.67/0.99  fof(f66,plain,(
% 2.67/0.99    ( ! [X0,X1] : (r2_hidden(X1,k1_connsp_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.67/0.99    inference(cnf_transformation,[],[f33])).
% 2.67/0.99  
% 2.67/0.99  fof(f73,plain,(
% 2.67/0.99    ~v2_struct_0(sK2)),
% 2.67/0.99    inference(cnf_transformation,[],[f53])).
% 2.67/0.99  
% 2.67/0.99  fof(f11,axiom,(
% 2.67/0.99    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.67/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/0.99  
% 2.67/0.99  fof(f30,plain,(
% 2.67/0.99    ! [X0,X1] : (m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.67/0.99    inference(ennf_transformation,[],[f11])).
% 2.67/0.99  
% 2.67/0.99  fof(f31,plain,(
% 2.67/0.99    ! [X0,X1] : (m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.67/0.99    inference(flattening,[],[f30])).
% 2.67/0.99  
% 2.67/0.99  fof(f65,plain,(
% 2.67/0.99    ( ! [X0,X1] : (m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.67/0.99    inference(cnf_transformation,[],[f31])).
% 2.67/0.99  
% 2.67/0.99  fof(f1,axiom,(
% 2.67/0.99    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.67/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/0.99  
% 2.67/0.99  fof(f42,plain,(
% 2.67/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.67/0.99    inference(nnf_transformation,[],[f1])).
% 2.67/0.99  
% 2.67/0.99  fof(f43,plain,(
% 2.67/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.67/0.99    inference(rectify,[],[f42])).
% 2.67/0.99  
% 2.67/0.99  fof(f44,plain,(
% 2.67/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.67/0.99    introduced(choice_axiom,[])).
% 2.67/0.99  
% 2.67/0.99  fof(f45,plain,(
% 2.67/0.99    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.67/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f43,f44])).
% 2.67/0.99  
% 2.67/0.99  fof(f54,plain,(
% 2.67/0.99    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 2.67/0.99    inference(cnf_transformation,[],[f45])).
% 2.67/0.99  
% 2.67/0.99  fof(f6,axiom,(
% 2.67/0.99    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 2.67/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/0.99  
% 2.67/0.99  fof(f21,plain,(
% 2.67/0.99    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 2.67/0.99    inference(ennf_transformation,[],[f6])).
% 2.67/0.99  
% 2.67/0.99  fof(f60,plain,(
% 2.67/0.99    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 2.67/0.99    inference(cnf_transformation,[],[f21])).
% 2.67/0.99  
% 2.67/0.99  fof(f78,plain,(
% 2.67/0.99    m1_subset_1(sK4,u1_struct_0(sK2))),
% 2.67/0.99    inference(cnf_transformation,[],[f53])).
% 2.67/0.99  
% 2.67/0.99  fof(f79,plain,(
% 2.67/0.99    ~r1_xboole_0(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)),k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)))),
% 2.67/0.99    inference(cnf_transformation,[],[f53])).
% 2.67/0.99  
% 2.67/0.99  fof(f7,axiom,(
% 2.67/0.99    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.67/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/0.99  
% 2.67/0.99  fof(f22,plain,(
% 2.67/0.99    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.67/0.99    inference(ennf_transformation,[],[f7])).
% 2.67/0.99  
% 2.67/0.99  fof(f23,plain,(
% 2.67/0.99    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.67/0.99    inference(flattening,[],[f22])).
% 2.67/0.99  
% 2.67/0.99  fof(f61,plain,(
% 2.67/0.99    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 2.67/0.99    inference(cnf_transformation,[],[f23])).
% 2.67/0.99  
% 2.67/0.99  fof(f5,axiom,(
% 2.67/0.99    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 2.67/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/0.99  
% 2.67/0.99  fof(f20,plain,(
% 2.67/0.99    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 2.67/0.99    inference(ennf_transformation,[],[f5])).
% 2.67/0.99  
% 2.67/0.99  fof(f59,plain,(
% 2.67/0.99    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 2.67/0.99    inference(cnf_transformation,[],[f20])).
% 2.67/0.99  
% 2.67/0.99  fof(f82,plain,(
% 2.67/0.99    ( ! [X0,X1] : (m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 2.67/0.99    inference(definition_unfolding,[],[f59,f57])).
% 2.67/0.99  
% 2.67/0.99  fof(f15,axiom,(
% 2.67/0.99    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) => k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))))))),
% 2.67/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/0.99  
% 2.67/0.99  fof(f38,plain,(
% 2.67/0.99    ! [X0] : (! [X1] : (! [X2] : ((k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) | ~r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.67/0.99    inference(ennf_transformation,[],[f15])).
% 2.67/0.99  
% 2.67/0.99  fof(f39,plain,(
% 2.67/0.99    ! [X0] : (! [X1] : (! [X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) | ~r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.67/0.99    inference(flattening,[],[f38])).
% 2.67/0.99  
% 2.67/0.99  fof(f72,plain,(
% 2.67/0.99    ( ! [X2,X0,X1] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) | ~r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.67/0.99    inference(cnf_transformation,[],[f39])).
% 2.67/0.99  
% 2.67/0.99  fof(f80,plain,(
% 2.67/0.99    k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))),
% 2.67/0.99    inference(cnf_transformation,[],[f53])).
% 2.67/0.99  
% 2.67/0.99  cnf(c_3,plain,
% 2.67/0.99      ( r1_xboole_0(k2_tarski(X0,X0),X1) | r2_hidden(X0,X1) ),
% 2.67/0.99      inference(cnf_transformation,[],[f81]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_948,plain,
% 2.67/0.99      ( r1_xboole_0(k2_tarski(X0_49,X0_49),X1_49)
% 2.67/0.99      | r2_hidden(X0_49,X1_49) ),
% 2.67/0.99      inference(subtyping,[status(esa)],[c_3]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1273,plain,
% 2.67/0.99      ( r1_xboole_0(k2_tarski(X0_49,X0_49),X1_49) = iProver_top
% 2.67/0.99      | r2_hidden(X0_49,X1_49) = iProver_top ),
% 2.67/0.99      inference(predicate_to_equality,[status(thm)],[c_948]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_2,plain,
% 2.67/0.99      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 2.67/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_949,plain,
% 2.67/0.99      ( ~ r1_xboole_0(X0_49,X1_49) | r1_xboole_0(X1_49,X0_49) ),
% 2.67/0.99      inference(subtyping,[status(esa)],[c_2]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1272,plain,
% 2.67/0.99      ( r1_xboole_0(X0_49,X1_49) != iProver_top
% 2.67/0.99      | r1_xboole_0(X1_49,X0_49) = iProver_top ),
% 2.67/0.99      inference(predicate_to_equality,[status(thm)],[c_949]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1699,plain,
% 2.67/0.99      ( r1_xboole_0(X0_49,k2_tarski(X1_49,X1_49)) = iProver_top
% 2.67/0.99      | r2_hidden(X1_49,X0_49) = iProver_top ),
% 2.67/0.99      inference(superposition,[status(thm)],[c_1273,c_1272]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_9,plain,
% 2.67/0.99      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
% 2.67/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.67/0.99      | ~ v2_pre_topc(X0)
% 2.67/0.99      | ~ l1_pre_topc(X0) ),
% 2.67/0.99      inference(cnf_transformation,[],[f64]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_15,plain,
% 2.67/0.99      ( v3_pre_topc(X0,X1)
% 2.67/0.99      | ~ v4_pre_topc(X0,X1)
% 2.67/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.67/0.99      | ~ v3_tdlat_3(X1)
% 2.67/0.99      | ~ v2_pre_topc(X1)
% 2.67/0.99      | ~ l1_pre_topc(X1) ),
% 2.67/0.99      inference(cnf_transformation,[],[f67]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_344,plain,
% 2.67/0.99      ( v3_pre_topc(X0,X1)
% 2.67/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 2.67/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.67/0.99      | ~ v3_tdlat_3(X1)
% 2.67/0.99      | ~ v2_pre_topc(X3)
% 2.67/0.99      | ~ v2_pre_topc(X1)
% 2.67/0.99      | ~ l1_pre_topc(X3)
% 2.67/0.99      | ~ l1_pre_topc(X1)
% 2.67/0.99      | X1 != X3
% 2.67/0.99      | k2_pre_topc(X3,X2) != X0 ),
% 2.67/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_15]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_345,plain,
% 2.67/0.99      ( v3_pre_topc(k2_pre_topc(X0,X1),X0)
% 2.67/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.67/0.99      | ~ m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
% 2.67/0.99      | ~ v3_tdlat_3(X0)
% 2.67/0.99      | ~ v2_pre_topc(X0)
% 2.67/0.99      | ~ l1_pre_topc(X0) ),
% 2.67/0.99      inference(unflattening,[status(thm)],[c_344]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_7,plain,
% 2.67/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.67/0.99      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.67/0.99      | ~ l1_pre_topc(X1) ),
% 2.67/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_361,plain,
% 2.67/0.99      ( v3_pre_topc(k2_pre_topc(X0,X1),X0)
% 2.67/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.67/0.99      | ~ v3_tdlat_3(X0)
% 2.67/0.99      | ~ v2_pre_topc(X0)
% 2.67/0.99      | ~ l1_pre_topc(X0) ),
% 2.67/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_345,c_7]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_24,negated_conjecture,
% 2.67/0.99      ( v2_pre_topc(sK2) ),
% 2.67/0.99      inference(cnf_transformation,[],[f74]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_378,plain,
% 2.67/0.99      ( v3_pre_topc(k2_pre_topc(X0,X1),X0)
% 2.67/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.67/0.99      | ~ v3_tdlat_3(X0)
% 2.67/0.99      | ~ l1_pre_topc(X0)
% 2.67/0.99      | sK2 != X0 ),
% 2.67/0.99      inference(resolution_lifted,[status(thm)],[c_361,c_24]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_379,plain,
% 2.67/0.99      ( v3_pre_topc(k2_pre_topc(sK2,X0),sK2)
% 2.67/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.67/0.99      | ~ v3_tdlat_3(sK2)
% 2.67/0.99      | ~ l1_pre_topc(sK2) ),
% 2.67/0.99      inference(unflattening,[status(thm)],[c_378]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_23,negated_conjecture,
% 2.67/0.99      ( v3_tdlat_3(sK2) ),
% 2.67/0.99      inference(cnf_transformation,[],[f75]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_22,negated_conjecture,
% 2.67/0.99      ( l1_pre_topc(sK2) ),
% 2.67/0.99      inference(cnf_transformation,[],[f76]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_383,plain,
% 2.67/0.99      ( v3_pre_topc(k2_pre_topc(sK2,X0),sK2)
% 2.67/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.67/0.99      inference(global_propositional_subsumption,
% 2.67/0.99                [status(thm)],
% 2.67/0.99                [c_379,c_23,c_22]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_16,plain,
% 2.67/0.99      ( ~ v3_pre_topc(X0,X1)
% 2.67/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.67/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.67/0.99      | ~ r1_xboole_0(X0,X2)
% 2.67/0.99      | r1_xboole_0(X0,k2_pre_topc(X1,X2))
% 2.67/0.99      | ~ v2_pre_topc(X1)
% 2.67/0.99      | ~ l1_pre_topc(X1) ),
% 2.67/0.99      inference(cnf_transformation,[],[f71]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_400,plain,
% 2.67/0.99      ( ~ v3_pre_topc(X0,X1)
% 2.67/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.67/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.67/0.99      | ~ r1_xboole_0(X0,X2)
% 2.67/0.99      | r1_xboole_0(X0,k2_pre_topc(X1,X2))
% 2.67/0.99      | ~ l1_pre_topc(X1)
% 2.67/0.99      | sK2 != X1 ),
% 2.67/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_24]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_401,plain,
% 2.67/0.99      ( ~ v3_pre_topc(X0,sK2)
% 2.67/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.67/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.67/0.99      | ~ r1_xboole_0(X0,X1)
% 2.67/0.99      | r1_xboole_0(X0,k2_pre_topc(sK2,X1))
% 2.67/0.99      | ~ l1_pre_topc(sK2) ),
% 2.67/0.99      inference(unflattening,[status(thm)],[c_400]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_405,plain,
% 2.67/0.99      ( r1_xboole_0(X0,k2_pre_topc(sK2,X1))
% 2.67/0.99      | ~ r1_xboole_0(X0,X1)
% 2.67/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.67/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.67/0.99      | ~ v3_pre_topc(X0,sK2) ),
% 2.67/0.99      inference(global_propositional_subsumption,
% 2.67/0.99                [status(thm)],
% 2.67/0.99                [c_401,c_22]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_406,plain,
% 2.67/0.99      ( ~ v3_pre_topc(X0,sK2)
% 2.67/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.67/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.67/0.99      | ~ r1_xboole_0(X0,X1)
% 2.67/0.99      | r1_xboole_0(X0,k2_pre_topc(sK2,X1)) ),
% 2.67/0.99      inference(renaming,[status(thm)],[c_405]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_451,plain,
% 2.67/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.67/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.67/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.67/0.99      | ~ r1_xboole_0(X0,X2)
% 2.67/0.99      | r1_xboole_0(X0,k2_pre_topc(sK2,X2))
% 2.67/0.99      | k2_pre_topc(sK2,X1) != X0
% 2.67/0.99      | sK2 != sK2 ),
% 2.67/0.99      inference(resolution_lifted,[status(thm)],[c_383,c_406]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_452,plain,
% 2.67/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.67/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.67/0.99      | ~ m1_subset_1(k2_pre_topc(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.67/0.99      | ~ r1_xboole_0(k2_pre_topc(sK2,X0),X1)
% 2.67/0.99      | r1_xboole_0(k2_pre_topc(sK2,X0),k2_pre_topc(sK2,X1)) ),
% 2.67/0.99      inference(unflattening,[status(thm)],[c_451]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_436,plain,
% 2.67/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.67/0.99      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.67/0.99      | sK2 != X1 ),
% 2.67/0.99      inference(resolution_lifted,[status(thm)],[c_7,c_22]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_437,plain,
% 2.67/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.67/0.99      | m1_subset_1(k2_pre_topc(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.67/0.99      inference(unflattening,[status(thm)],[c_436]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_456,plain,
% 2.67/0.99      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.67/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.67/0.99      | ~ r1_xboole_0(k2_pre_topc(sK2,X0),X1)
% 2.67/0.99      | r1_xboole_0(k2_pre_topc(sK2,X0),k2_pre_topc(sK2,X1)) ),
% 2.67/0.99      inference(global_propositional_subsumption,
% 2.67/0.99                [status(thm)],
% 2.67/0.99                [c_452,c_437]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_457,plain,
% 2.67/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.67/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.67/0.99      | ~ r1_xboole_0(k2_pre_topc(sK2,X1),X0)
% 2.67/0.99      | r1_xboole_0(k2_pre_topc(sK2,X1),k2_pre_topc(sK2,X0)) ),
% 2.67/0.99      inference(renaming,[status(thm)],[c_456]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_935,plain,
% 2.67/0.99      ( ~ m1_subset_1(X0_49,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.67/0.99      | ~ m1_subset_1(X1_49,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.67/0.99      | ~ r1_xboole_0(k2_pre_topc(sK2,X1_49),X0_49)
% 2.67/0.99      | r1_xboole_0(k2_pre_topc(sK2,X1_49),k2_pre_topc(sK2,X0_49)) ),
% 2.67/0.99      inference(subtyping,[status(esa)],[c_457]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1285,plain,
% 2.67/0.99      ( m1_subset_1(X0_49,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.67/0.99      | m1_subset_1(X1_49,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.67/0.99      | r1_xboole_0(k2_pre_topc(sK2,X1_49),X0_49) != iProver_top
% 2.67/0.99      | r1_xboole_0(k2_pre_topc(sK2,X1_49),k2_pre_topc(sK2,X0_49)) = iProver_top ),
% 2.67/0.99      inference(predicate_to_equality,[status(thm)],[c_935]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1944,plain,
% 2.67/0.99      ( m1_subset_1(X0_49,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.67/0.99      | m1_subset_1(X1_49,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.67/0.99      | r1_xboole_0(k2_pre_topc(sK2,X1_49),X0_49) != iProver_top
% 2.67/0.99      | r1_xboole_0(k2_pre_topc(sK2,X0_49),k2_pre_topc(sK2,X1_49)) = iProver_top ),
% 2.67/0.99      inference(superposition,[status(thm)],[c_1285,c_1272]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_21,negated_conjecture,
% 2.67/0.99      ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 2.67/0.99      inference(cnf_transformation,[],[f77]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_940,negated_conjecture,
% 2.67/0.99      ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 2.67/0.99      inference(subtyping,[status(esa)],[c_21]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1280,plain,
% 2.67/0.99      ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
% 2.67/0.99      inference(predicate_to_equality,[status(thm)],[c_940]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_8,plain,
% 2.67/0.99      ( ~ m1_subset_1(X0,X1)
% 2.67/0.99      | v1_xboole_0(X1)
% 2.67/0.99      | k6_domain_1(X1,X0) = k2_tarski(X0,X0) ),
% 2.67/0.99      inference(cnf_transformation,[],[f83]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_944,plain,
% 2.67/0.99      ( ~ m1_subset_1(X0_49,X1_49)
% 2.67/0.99      | v1_xboole_0(X1_49)
% 2.67/0.99      | k6_domain_1(X1_49,X0_49) = k2_tarski(X0_49,X0_49) ),
% 2.67/0.99      inference(subtyping,[status(esa)],[c_8]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1277,plain,
% 2.67/0.99      ( k6_domain_1(X0_49,X1_49) = k2_tarski(X1_49,X1_49)
% 2.67/0.99      | m1_subset_1(X1_49,X0_49) != iProver_top
% 2.67/0.99      | v1_xboole_0(X0_49) = iProver_top ),
% 2.67/0.99      inference(predicate_to_equality,[status(thm)],[c_944]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_2234,plain,
% 2.67/0.99      ( k6_domain_1(u1_struct_0(sK2),sK3) = k2_tarski(sK3,sK3)
% 2.67/0.99      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 2.67/0.99      inference(superposition,[status(thm)],[c_1280,c_1277]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_11,plain,
% 2.67/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.67/0.99      | r2_hidden(X0,k1_connsp_2(X1,X0))
% 2.67/0.99      | v2_struct_0(X1)
% 2.67/0.99      | ~ v2_pre_topc(X1)
% 2.67/0.99      | ~ l1_pre_topc(X1) ),
% 2.67/0.99      inference(cnf_transformation,[],[f66]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_25,negated_conjecture,
% 2.67/0.99      ( ~ v2_struct_0(sK2) ),
% 2.67/0.99      inference(cnf_transformation,[],[f73]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_297,plain,
% 2.67/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.67/0.99      | r2_hidden(X0,k1_connsp_2(X1,X0))
% 2.67/0.99      | ~ v2_pre_topc(X1)
% 2.67/0.99      | ~ l1_pre_topc(X1)
% 2.67/0.99      | sK2 != X1 ),
% 2.67/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_25]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_298,plain,
% 2.67/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.67/0.99      | r2_hidden(X0,k1_connsp_2(sK2,X0))
% 2.67/0.99      | ~ v2_pre_topc(sK2)
% 2.67/0.99      | ~ l1_pre_topc(sK2) ),
% 2.67/0.99      inference(unflattening,[status(thm)],[c_297]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_302,plain,
% 2.67/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.67/0.99      | r2_hidden(X0,k1_connsp_2(sK2,X0)) ),
% 2.67/0.99      inference(global_propositional_subsumption,
% 2.67/0.99                [status(thm)],
% 2.67/0.99                [c_298,c_24,c_22]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_938,plain,
% 2.67/0.99      ( ~ m1_subset_1(X0_49,u1_struct_0(sK2))
% 2.67/0.99      | r2_hidden(X0_49,k1_connsp_2(sK2,X0_49)) ),
% 2.67/0.99      inference(subtyping,[status(esa)],[c_302]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_996,plain,
% 2.67/0.99      ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 2.67/0.99      | r2_hidden(sK3,k1_connsp_2(sK2,sK3)) ),
% 2.67/0.99      inference(instantiation,[status(thm)],[c_938]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_10,plain,
% 2.67/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.67/0.99      | m1_subset_1(k1_connsp_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.67/0.99      | v2_struct_0(X1)
% 2.67/0.99      | ~ v2_pre_topc(X1)
% 2.67/0.99      | ~ l1_pre_topc(X1) ),
% 2.67/0.99      inference(cnf_transformation,[],[f65]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_315,plain,
% 2.67/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.67/0.99      | m1_subset_1(k1_connsp_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.67/0.99      | ~ v2_pre_topc(X1)
% 2.67/0.99      | ~ l1_pre_topc(X1)
% 2.67/0.99      | sK2 != X1 ),
% 2.67/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_25]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_316,plain,
% 2.67/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.67/0.99      | m1_subset_1(k1_connsp_2(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.67/0.99      | ~ v2_pre_topc(sK2)
% 2.67/0.99      | ~ l1_pre_topc(sK2) ),
% 2.67/0.99      inference(unflattening,[status(thm)],[c_315]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_320,plain,
% 2.67/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.67/0.99      | m1_subset_1(k1_connsp_2(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.67/0.99      inference(global_propositional_subsumption,
% 2.67/0.99                [status(thm)],
% 2.67/0.99                [c_316,c_24,c_22]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_937,plain,
% 2.67/0.99      ( ~ m1_subset_1(X0_49,u1_struct_0(sK2))
% 2.67/0.99      | m1_subset_1(k1_connsp_2(sK2,X0_49),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.67/0.99      inference(subtyping,[status(esa)],[c_320]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_999,plain,
% 2.67/0.99      ( m1_subset_1(k1_connsp_2(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.67/0.99      | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 2.67/0.99      inference(instantiation,[status(thm)],[c_937]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1435,plain,
% 2.67/0.99      ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 2.67/0.99      | v1_xboole_0(u1_struct_0(sK2))
% 2.67/0.99      | k6_domain_1(u1_struct_0(sK2),sK3) = k2_tarski(sK3,sK3) ),
% 2.67/0.99      inference(instantiation,[status(thm)],[c_944]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1,plain,
% 2.67/0.99      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 2.67/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_950,plain,
% 2.67/0.99      ( ~ r2_hidden(X0_49,X1_49) | ~ v1_xboole_0(X1_49) ),
% 2.67/0.99      inference(subtyping,[status(esa)],[c_1]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1666,plain,
% 2.67/0.99      ( ~ r2_hidden(X0_49,k1_connsp_2(sK2,X0_49))
% 2.67/0.99      | ~ v1_xboole_0(k1_connsp_2(sK2,X0_49)) ),
% 2.67/0.99      inference(instantiation,[status(thm)],[c_950]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1668,plain,
% 2.67/0.99      ( ~ r2_hidden(sK3,k1_connsp_2(sK2,sK3))
% 2.67/0.99      | ~ v1_xboole_0(k1_connsp_2(sK2,sK3)) ),
% 2.67/0.99      inference(instantiation,[status(thm)],[c_1666]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_5,plain,
% 2.67/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.67/0.99      | ~ v1_xboole_0(X1)
% 2.67/0.99      | v1_xboole_0(X0) ),
% 2.67/0.99      inference(cnf_transformation,[],[f60]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_946,plain,
% 2.67/0.99      ( ~ m1_subset_1(X0_49,k1_zfmisc_1(X1_49))
% 2.67/0.99      | ~ v1_xboole_0(X1_49)
% 2.67/0.99      | v1_xboole_0(X0_49) ),
% 2.67/0.99      inference(subtyping,[status(esa)],[c_5]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1503,plain,
% 2.67/0.99      ( ~ m1_subset_1(X0_49,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.67/0.99      | v1_xboole_0(X0_49)
% 2.67/0.99      | ~ v1_xboole_0(u1_struct_0(sK2)) ),
% 2.67/0.99      inference(instantiation,[status(thm)],[c_946]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1757,plain,
% 2.67/0.99      ( ~ m1_subset_1(k1_connsp_2(sK2,X0_49),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.67/0.99      | v1_xboole_0(k1_connsp_2(sK2,X0_49))
% 2.67/0.99      | ~ v1_xboole_0(u1_struct_0(sK2)) ),
% 2.67/0.99      inference(instantiation,[status(thm)],[c_1503]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1759,plain,
% 2.67/0.99      ( ~ m1_subset_1(k1_connsp_2(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.67/0.99      | v1_xboole_0(k1_connsp_2(sK2,sK3))
% 2.67/0.99      | ~ v1_xboole_0(u1_struct_0(sK2)) ),
% 2.67/0.99      inference(instantiation,[status(thm)],[c_1757]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_2586,plain,
% 2.67/0.99      ( k6_domain_1(u1_struct_0(sK2),sK3) = k2_tarski(sK3,sK3) ),
% 2.67/0.99      inference(global_propositional_subsumption,
% 2.67/0.99                [status(thm)],
% 2.67/0.99                [c_2234,c_21,c_996,c_999,c_1435,c_1668,c_1759]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_20,negated_conjecture,
% 2.67/0.99      ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
% 2.67/0.99      inference(cnf_transformation,[],[f78]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_941,negated_conjecture,
% 2.67/0.99      ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
% 2.67/0.99      inference(subtyping,[status(esa)],[c_20]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1279,plain,
% 2.67/0.99      ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
% 2.67/0.99      inference(predicate_to_equality,[status(thm)],[c_941]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_2233,plain,
% 2.67/0.99      ( k6_domain_1(u1_struct_0(sK2),sK4) = k2_tarski(sK4,sK4)
% 2.67/0.99      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 2.67/0.99      inference(superposition,[status(thm)],[c_1279,c_1277]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1432,plain,
% 2.67/0.99      ( ~ m1_subset_1(sK4,u1_struct_0(sK2))
% 2.67/0.99      | v1_xboole_0(u1_struct_0(sK2))
% 2.67/0.99      | k6_domain_1(u1_struct_0(sK2),sK4) = k2_tarski(sK4,sK4) ),
% 2.67/0.99      inference(instantiation,[status(thm)],[c_944]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_2379,plain,
% 2.67/0.99      ( k6_domain_1(u1_struct_0(sK2),sK4) = k2_tarski(sK4,sK4) ),
% 2.67/0.99      inference(global_propositional_subsumption,
% 2.67/0.99                [status(thm)],
% 2.67/0.99                [c_2233,c_21,c_20,c_996,c_999,c_1432,c_1668,c_1759]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_19,negated_conjecture,
% 2.67/0.99      ( ~ r1_xboole_0(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)),k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))) ),
% 2.67/0.99      inference(cnf_transformation,[],[f79]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_942,negated_conjecture,
% 2.67/0.99      ( ~ r1_xboole_0(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)),k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))) ),
% 2.67/0.99      inference(subtyping,[status(esa)],[c_19]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1278,plain,
% 2.67/0.99      ( r1_xboole_0(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)),k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))) != iProver_top ),
% 2.67/0.99      inference(predicate_to_equality,[status(thm)],[c_942]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_2384,plain,
% 2.67/0.99      ( r1_xboole_0(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)),k2_pre_topc(sK2,k2_tarski(sK4,sK4))) != iProver_top ),
% 2.67/0.99      inference(demodulation,[status(thm)],[c_2379,c_1278]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_2589,plain,
% 2.67/0.99      ( r1_xboole_0(k2_pre_topc(sK2,k2_tarski(sK3,sK3)),k2_pre_topc(sK2,k2_tarski(sK4,sK4))) != iProver_top ),
% 2.67/0.99      inference(demodulation,[status(thm)],[c_2586,c_2384]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_2893,plain,
% 2.67/0.99      ( m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.67/0.99      | m1_subset_1(k2_tarski(sK3,sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.67/0.99      | r1_xboole_0(k2_pre_topc(sK2,k2_tarski(sK4,sK4)),k2_tarski(sK3,sK3)) != iProver_top ),
% 2.67/0.99      inference(superposition,[status(thm)],[c_1944,c_2589]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_30,plain,
% 2.67/0.99      ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
% 2.67/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_31,plain,
% 2.67/0.99      ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
% 2.67/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_995,plain,
% 2.67/0.99      ( m1_subset_1(X0_49,u1_struct_0(sK2)) != iProver_top
% 2.67/0.99      | r2_hidden(X0_49,k1_connsp_2(sK2,X0_49)) = iProver_top ),
% 2.67/0.99      inference(predicate_to_equality,[status(thm)],[c_938]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_997,plain,
% 2.67/0.99      ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 2.67/0.99      | r2_hidden(sK3,k1_connsp_2(sK2,sK3)) = iProver_top ),
% 2.67/0.99      inference(instantiation,[status(thm)],[c_995]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_998,plain,
% 2.67/0.99      ( m1_subset_1(X0_49,u1_struct_0(sK2)) != iProver_top
% 2.67/0.99      | m1_subset_1(k1_connsp_2(sK2,X0_49),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 2.67/0.99      inference(predicate_to_equality,[status(thm)],[c_937]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1000,plain,
% 2.67/0.99      ( m1_subset_1(k1_connsp_2(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 2.67/0.99      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
% 2.67/0.99      inference(instantiation,[status(thm)],[c_998]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_6,plain,
% 2.67/0.99      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.67/0.99      inference(cnf_transformation,[],[f61]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_945,plain,
% 2.67/0.99      ( ~ m1_subset_1(X0_49,X1_49)
% 2.67/0.99      | r2_hidden(X0_49,X1_49)
% 2.67/0.99      | v1_xboole_0(X1_49) ),
% 2.67/0.99      inference(subtyping,[status(esa)],[c_6]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1408,plain,
% 2.67/0.99      ( ~ m1_subset_1(sK4,u1_struct_0(sK2))
% 2.67/0.99      | r2_hidden(sK4,u1_struct_0(sK2))
% 2.67/0.99      | v1_xboole_0(u1_struct_0(sK2)) ),
% 2.67/0.99      inference(instantiation,[status(thm)],[c_945]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1409,plain,
% 2.67/0.99      ( m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
% 2.67/0.99      | r2_hidden(sK4,u1_struct_0(sK2)) = iProver_top
% 2.67/0.99      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 2.67/0.99      inference(predicate_to_equality,[status(thm)],[c_1408]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1411,plain,
% 2.67/0.99      ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 2.67/0.99      | r2_hidden(sK3,u1_struct_0(sK2))
% 2.67/0.99      | v1_xboole_0(u1_struct_0(sK2)) ),
% 2.67/0.99      inference(instantiation,[status(thm)],[c_945]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1412,plain,
% 2.67/0.99      ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 2.67/0.99      | r2_hidden(sK3,u1_struct_0(sK2)) = iProver_top
% 2.67/0.99      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 2.67/0.99      inference(predicate_to_equality,[status(thm)],[c_1411]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1667,plain,
% 2.67/0.99      ( r2_hidden(X0_49,k1_connsp_2(sK2,X0_49)) != iProver_top
% 2.67/0.99      | v1_xboole_0(k1_connsp_2(sK2,X0_49)) != iProver_top ),
% 2.67/0.99      inference(predicate_to_equality,[status(thm)],[c_1666]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1669,plain,
% 2.67/0.99      ( r2_hidden(sK3,k1_connsp_2(sK2,sK3)) != iProver_top
% 2.67/0.99      | v1_xboole_0(k1_connsp_2(sK2,sK3)) != iProver_top ),
% 2.67/0.99      inference(instantiation,[status(thm)],[c_1667]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1758,plain,
% 2.67/0.99      ( m1_subset_1(k1_connsp_2(sK2,X0_49),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.67/0.99      | v1_xboole_0(k1_connsp_2(sK2,X0_49)) = iProver_top
% 2.67/0.99      | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
% 2.67/0.99      inference(predicate_to_equality,[status(thm)],[c_1757]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1760,plain,
% 2.67/0.99      ( m1_subset_1(k1_connsp_2(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.67/0.99      | v1_xboole_0(k1_connsp_2(sK2,sK3)) = iProver_top
% 2.67/0.99      | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
% 2.67/0.99      inference(instantiation,[status(thm)],[c_1758]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_4,plain,
% 2.67/0.99      ( m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1))
% 2.67/0.99      | ~ r2_hidden(X0,X1) ),
% 2.67/0.99      inference(cnf_transformation,[],[f82]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_947,plain,
% 2.67/0.99      ( m1_subset_1(k2_tarski(X0_49,X0_49),k1_zfmisc_1(X1_49))
% 2.67/0.99      | ~ r2_hidden(X0_49,X1_49) ),
% 2.67/0.99      inference(subtyping,[status(esa)],[c_4]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1854,plain,
% 2.67/0.99      ( m1_subset_1(k2_tarski(X0_49,X0_49),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.67/0.99      | ~ r2_hidden(X0_49,u1_struct_0(sK2)) ),
% 2.67/0.99      inference(instantiation,[status(thm)],[c_947]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1855,plain,
% 2.67/0.99      ( m1_subset_1(k2_tarski(X0_49,X0_49),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 2.67/0.99      | r2_hidden(X0_49,u1_struct_0(sK2)) != iProver_top ),
% 2.67/0.99      inference(predicate_to_equality,[status(thm)],[c_1854]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1857,plain,
% 2.67/0.99      ( m1_subset_1(k2_tarski(sK3,sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 2.67/0.99      | r2_hidden(sK3,u1_struct_0(sK2)) != iProver_top ),
% 2.67/0.99      inference(instantiation,[status(thm)],[c_1855]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_4693,plain,
% 2.67/0.99      ( m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.67/0.99      | ~ r2_hidden(sK4,u1_struct_0(sK2)) ),
% 2.67/0.99      inference(instantiation,[status(thm)],[c_1854]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_4694,plain,
% 2.67/0.99      ( m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 2.67/0.99      | r2_hidden(sK4,u1_struct_0(sK2)) != iProver_top ),
% 2.67/0.99      inference(predicate_to_equality,[status(thm)],[c_4693]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_5261,plain,
% 2.67/0.99      ( r1_xboole_0(k2_pre_topc(sK2,k2_tarski(sK4,sK4)),k2_tarski(sK3,sK3)) != iProver_top ),
% 2.67/0.99      inference(global_propositional_subsumption,
% 2.67/0.99                [status(thm)],
% 2.67/0.99                [c_2893,c_30,c_31,c_997,c_1000,c_1409,c_1412,c_1669,
% 2.67/0.99                 c_1760,c_1857,c_4694]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_5266,plain,
% 2.67/0.99      ( r2_hidden(sK3,k2_pre_topc(sK2,k2_tarski(sK4,sK4))) = iProver_top ),
% 2.67/0.99      inference(superposition,[status(thm)],[c_1699,c_5261]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_17,plain,
% 2.67/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.67/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.67/0.99      | ~ r2_hidden(X0,k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2)))
% 2.67/0.99      | ~ v3_tdlat_3(X1)
% 2.67/0.99      | v2_struct_0(X1)
% 2.67/0.99      | ~ v2_pre_topc(X1)
% 2.67/0.99      | ~ l1_pre_topc(X1)
% 2.67/0.99      | k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2)) = k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X0)) ),
% 2.67/0.99      inference(cnf_transformation,[],[f72]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_273,plain,
% 2.67/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.67/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.67/0.99      | ~ r2_hidden(X0,k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2)))
% 2.67/0.99      | ~ v3_tdlat_3(X1)
% 2.67/0.99      | ~ v2_pre_topc(X1)
% 2.67/0.99      | ~ l1_pre_topc(X1)
% 2.67/0.99      | k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X0)) = k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2))
% 2.67/0.99      | sK2 != X1 ),
% 2.67/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_25]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_274,plain,
% 2.67/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.67/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.67/0.99      | ~ r2_hidden(X1,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0)))
% 2.67/0.99      | ~ v3_tdlat_3(sK2)
% 2.67/0.99      | ~ v2_pre_topc(sK2)
% 2.67/0.99      | ~ l1_pre_topc(sK2)
% 2.67/0.99      | k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X1)) = k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0)) ),
% 2.67/0.99      inference(unflattening,[status(thm)],[c_273]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_278,plain,
% 2.67/0.99      ( ~ r2_hidden(X1,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0)))
% 2.67/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.67/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.67/0.99      | k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X1)) = k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0)) ),
% 2.67/0.99      inference(global_propositional_subsumption,
% 2.67/0.99                [status(thm)],
% 2.67/0.99                [c_274,c_24,c_23,c_22]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_279,plain,
% 2.67/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.67/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.67/0.99      | ~ r2_hidden(X1,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0)))
% 2.67/0.99      | k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X1)) = k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0)) ),
% 2.67/0.99      inference(renaming,[status(thm)],[c_278]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_939,plain,
% 2.67/0.99      ( ~ m1_subset_1(X0_49,u1_struct_0(sK2))
% 2.67/0.99      | ~ m1_subset_1(X1_49,u1_struct_0(sK2))
% 2.67/0.99      | ~ r2_hidden(X1_49,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0_49)))
% 2.67/0.99      | k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X1_49)) = k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0_49)) ),
% 2.67/0.99      inference(subtyping,[status(esa)],[c_279]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1281,plain,
% 2.67/0.99      ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0_49)) = k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X1_49))
% 2.67/0.99      | m1_subset_1(X0_49,u1_struct_0(sK2)) != iProver_top
% 2.67/0.99      | m1_subset_1(X1_49,u1_struct_0(sK2)) != iProver_top
% 2.67/0.99      | r2_hidden(X0_49,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X1_49))) != iProver_top ),
% 2.67/0.99      inference(predicate_to_equality,[status(thm)],[c_939]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_2406,plain,
% 2.67/0.99      ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0_49)) = k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))
% 2.67/0.99      | m1_subset_1(X0_49,u1_struct_0(sK2)) != iProver_top
% 2.67/0.99      | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
% 2.67/0.99      | r2_hidden(X0_49,k2_pre_topc(sK2,k2_tarski(sK4,sK4))) != iProver_top ),
% 2.67/0.99      inference(superposition,[status(thm)],[c_2379,c_1281]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_2411,plain,
% 2.67/0.99      ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0_49)) = k2_pre_topc(sK2,k2_tarski(sK4,sK4))
% 2.67/0.99      | m1_subset_1(X0_49,u1_struct_0(sK2)) != iProver_top
% 2.67/0.99      | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
% 2.67/0.99      | r2_hidden(X0_49,k2_pre_topc(sK2,k2_tarski(sK4,sK4))) != iProver_top ),
% 2.67/0.99      inference(light_normalisation,[status(thm)],[c_2406,c_2379]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_2426,plain,
% 2.67/0.99      ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)) = k2_pre_topc(sK2,k2_tarski(sK4,sK4))
% 2.67/0.99      | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
% 2.67/0.99      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 2.67/0.99      | r2_hidden(sK3,k2_pre_topc(sK2,k2_tarski(sK4,sK4))) != iProver_top ),
% 2.67/0.99      inference(instantiation,[status(thm)],[c_2411]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_954,plain,
% 2.67/0.99      ( X0_49 != X1_49 | X2_49 != X1_49 | X2_49 = X0_49 ),
% 2.67/0.99      theory(equality) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1429,plain,
% 2.67/0.99      ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)) != X0_49
% 2.67/0.99      | k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)) != X0_49
% 2.67/0.99      | k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)) = k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)) ),
% 2.67/0.99      inference(instantiation,[status(thm)],[c_954]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1529,plain,
% 2.67/0.99      ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)) != k2_pre_topc(sK2,X0_49)
% 2.67/0.99      | k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)) != k2_pre_topc(sK2,X0_49)
% 2.67/0.99      | k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)) = k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)) ),
% 2.67/0.99      inference(instantiation,[status(thm)],[c_1429]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_2181,plain,
% 2.67/0.99      ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)) != k2_pre_topc(sK2,k2_tarski(sK4,sK4))
% 2.67/0.99      | k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)) = k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))
% 2.67/0.99      | k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)) != k2_pre_topc(sK2,k2_tarski(sK4,sK4)) ),
% 2.67/0.99      inference(instantiation,[status(thm)],[c_1529]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_959,plain,
% 2.67/0.99      ( X0_49 != X1_49
% 2.67/0.99      | k2_pre_topc(X0_50,X0_49) = k2_pre_topc(X0_50,X1_49) ),
% 2.67/0.99      theory(equality) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1530,plain,
% 2.67/0.99      ( k6_domain_1(u1_struct_0(sK2),sK4) != X0_49
% 2.67/0.99      | k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)) = k2_pre_topc(sK2,X0_49) ),
% 2.67/0.99      inference(instantiation,[status(thm)],[c_959]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1899,plain,
% 2.67/0.99      ( k6_domain_1(u1_struct_0(sK2),sK4) != k2_tarski(sK4,sK4)
% 2.67/0.99      | k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)) = k2_pre_topc(sK2,k2_tarski(sK4,sK4)) ),
% 2.67/0.99      inference(instantiation,[status(thm)],[c_1530]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_18,negated_conjecture,
% 2.67/0.99      ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)) ),
% 2.67/0.99      inference(cnf_transformation,[],[f80]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_943,negated_conjecture,
% 2.67/0.99      ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)) ),
% 2.67/0.99      inference(subtyping,[status(esa)],[c_18]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(contradiction,plain,
% 2.67/0.99      ( $false ),
% 2.67/0.99      inference(minisat,
% 2.67/0.99                [status(thm)],
% 2.67/0.99                [c_5266,c_2426,c_2181,c_1899,c_1759,c_1668,c_1432,c_999,
% 2.67/0.99                 c_996,c_943,c_31,c_20,c_30,c_21]) ).
% 2.67/0.99  
% 2.67/0.99  
% 2.67/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.67/0.99  
% 2.67/0.99  ------                               Statistics
% 2.67/0.99  
% 2.67/0.99  ------ General
% 2.67/0.99  
% 2.67/0.99  abstr_ref_over_cycles:                  0
% 2.67/0.99  abstr_ref_under_cycles:                 0
% 2.67/0.99  gc_basic_clause_elim:                   0
% 2.67/0.99  forced_gc_time:                         0
% 2.67/0.99  parsing_time:                           0.011
% 2.67/0.99  unif_index_cands_time:                  0.
% 2.67/0.99  unif_index_add_time:                    0.
% 2.67/0.99  orderings_time:                         0.
% 2.67/0.99  out_proof_time:                         0.013
% 2.67/0.99  total_time:                             0.204
% 2.67/0.99  num_of_symbols:                         54
% 2.67/0.99  num_of_terms:                           5950
% 2.67/0.99  
% 2.67/0.99  ------ Preprocessing
% 2.67/0.99  
% 2.67/0.99  num_of_splits:                          0
% 2.67/0.99  num_of_split_atoms:                     0
% 2.67/0.99  num_of_reused_defs:                     0
% 2.67/0.99  num_eq_ax_congr_red:                    22
% 2.67/0.99  num_of_sem_filtered_clauses:            1
% 2.67/0.99  num_of_subtypes:                        2
% 2.67/0.99  monotx_restored_types:                  0
% 2.67/0.99  sat_num_of_epr_types:                   0
% 2.67/0.99  sat_num_of_non_cyclic_types:            0
% 2.67/0.99  sat_guarded_non_collapsed_types:        0
% 2.67/0.99  num_pure_diseq_elim:                    0
% 2.67/0.99  simp_replaced_by:                       0
% 2.67/0.99  res_preprocessed:                       94
% 2.67/0.99  prep_upred:                             0
% 2.67/0.99  prep_unflattend:                        43
% 2.67/0.99  smt_new_axioms:                         0
% 2.67/0.99  pred_elim_cands:                        4
% 2.67/0.99  pred_elim:                              6
% 2.67/0.99  pred_elim_cl:                           9
% 2.67/0.99  pred_elim_cycles:                       8
% 2.67/0.99  merged_defs:                            0
% 2.67/0.99  merged_defs_ncl:                        0
% 2.67/0.99  bin_hyper_res:                          0
% 2.67/0.99  prep_cycles:                            4
% 2.67/0.99  pred_elim_time:                         0.011
% 2.67/0.99  splitting_time:                         0.
% 2.67/0.99  sem_filter_time:                        0.
% 2.67/0.99  monotx_time:                            0.
% 2.67/0.99  subtype_inf_time:                       0.
% 2.67/0.99  
% 2.67/0.99  ------ Problem properties
% 2.67/0.99  
% 2.67/0.99  clauses:                                17
% 2.67/0.99  conjectures:                            4
% 2.67/0.99  epr:                                    3
% 2.67/0.99  horn:                                   13
% 2.67/0.99  ground:                                 4
% 2.67/0.99  unary:                                  4
% 2.67/0.99  binary:                                 8
% 2.67/0.99  lits:                                   37
% 2.67/0.99  lits_eq:                                3
% 2.67/0.99  fd_pure:                                0
% 2.67/0.99  fd_pseudo:                              0
% 2.67/0.99  fd_cond:                                0
% 2.67/0.99  fd_pseudo_cond:                         0
% 2.67/0.99  ac_symbols:                             0
% 2.67/0.99  
% 2.67/0.99  ------ Propositional Solver
% 2.67/0.99  
% 2.67/0.99  prop_solver_calls:                      30
% 2.67/0.99  prop_fast_solver_calls:                 815
% 2.67/0.99  smt_solver_calls:                       0
% 2.67/0.99  smt_fast_solver_calls:                  0
% 2.67/0.99  prop_num_of_clauses:                    2322
% 2.67/0.99  prop_preprocess_simplified:             5348
% 2.67/0.99  prop_fo_subsumed:                       28
% 2.67/0.99  prop_solver_time:                       0.
% 2.67/0.99  smt_solver_time:                        0.
% 2.67/0.99  smt_fast_solver_time:                   0.
% 2.67/0.99  prop_fast_solver_time:                  0.
% 2.67/0.99  prop_unsat_core_time:                   0.
% 2.67/0.99  
% 2.67/0.99  ------ QBF
% 2.67/0.99  
% 2.67/0.99  qbf_q_res:                              0
% 2.67/0.99  qbf_num_tautologies:                    0
% 2.67/0.99  qbf_prep_cycles:                        0
% 2.67/0.99  
% 2.67/0.99  ------ BMC1
% 2.67/0.99  
% 2.67/0.99  bmc1_current_bound:                     -1
% 2.67/0.99  bmc1_last_solved_bound:                 -1
% 2.67/0.99  bmc1_unsat_core_size:                   -1
% 2.67/0.99  bmc1_unsat_core_parents_size:           -1
% 2.67/0.99  bmc1_merge_next_fun:                    0
% 2.67/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.67/0.99  
% 2.67/0.99  ------ Instantiation
% 2.67/0.99  
% 2.67/0.99  inst_num_of_clauses:                    588
% 2.67/0.99  inst_num_in_passive:                    83
% 2.67/0.99  inst_num_in_active:                     352
% 2.67/0.99  inst_num_in_unprocessed:                153
% 2.67/0.99  inst_num_of_loops:                      390
% 2.67/0.99  inst_num_of_learning_restarts:          0
% 2.67/0.99  inst_num_moves_active_passive:          34
% 2.67/0.99  inst_lit_activity:                      0
% 2.67/0.99  inst_lit_activity_moves:                0
% 2.67/0.99  inst_num_tautologies:                   0
% 2.67/0.99  inst_num_prop_implied:                  0
% 2.67/0.99  inst_num_existing_simplified:           0
% 2.67/0.99  inst_num_eq_res_simplified:             0
% 2.67/0.99  inst_num_child_elim:                    0
% 2.67/0.99  inst_num_of_dismatching_blockings:      93
% 2.67/0.99  inst_num_of_non_proper_insts:           477
% 2.67/0.99  inst_num_of_duplicates:                 0
% 2.67/0.99  inst_inst_num_from_inst_to_res:         0
% 2.67/0.99  inst_dismatching_checking_time:         0.
% 2.67/0.99  
% 2.67/0.99  ------ Resolution
% 2.67/0.99  
% 2.67/0.99  res_num_of_clauses:                     0
% 2.67/0.99  res_num_in_passive:                     0
% 2.67/0.99  res_num_in_active:                      0
% 2.67/0.99  res_num_of_loops:                       98
% 2.67/0.99  res_forward_subset_subsumed:            37
% 2.67/0.99  res_backward_subset_subsumed:           0
% 2.67/0.99  res_forward_subsumed:                   0
% 2.67/0.99  res_backward_subsumed:                  0
% 2.67/0.99  res_forward_subsumption_resolution:     1
% 2.67/0.99  res_backward_subsumption_resolution:    0
% 2.67/0.99  res_clause_to_clause_subsumption:       217
% 2.67/0.99  res_orphan_elimination:                 0
% 2.67/0.99  res_tautology_del:                      53
% 2.67/0.99  res_num_eq_res_simplified:              0
% 2.67/0.99  res_num_sel_changes:                    0
% 2.67/0.99  res_moves_from_active_to_pass:          0
% 2.67/0.99  
% 2.67/0.99  ------ Superposition
% 2.67/0.99  
% 2.67/0.99  sup_time_total:                         0.
% 2.67/0.99  sup_time_generating:                    0.
% 2.67/0.99  sup_time_sim_full:                      0.
% 2.67/0.99  sup_time_sim_immed:                     0.
% 2.67/0.99  
% 2.67/0.99  sup_num_of_clauses:                     88
% 2.67/0.99  sup_num_in_active:                      72
% 2.67/0.99  sup_num_in_passive:                     16
% 2.67/0.99  sup_num_of_loops:                       77
% 2.67/0.99  sup_fw_superposition:                   66
% 2.67/0.99  sup_bw_superposition:                   16
% 2.67/0.99  sup_immediate_simplified:               5
% 2.67/0.99  sup_given_eliminated:                   0
% 2.67/0.99  comparisons_done:                       0
% 2.67/0.99  comparisons_avoided:                    0
% 2.67/0.99  
% 2.67/0.99  ------ Simplifications
% 2.67/0.99  
% 2.67/0.99  
% 2.67/0.99  sim_fw_subset_subsumed:                 1
% 2.67/0.99  sim_bw_subset_subsumed:                 0
% 2.67/0.99  sim_fw_subsumed:                        0
% 2.67/0.99  sim_bw_subsumed:                        0
% 2.67/0.99  sim_fw_subsumption_res:                 0
% 2.67/0.99  sim_bw_subsumption_res:                 0
% 2.67/0.99  sim_tautology_del:                      4
% 2.67/0.99  sim_eq_tautology_del:                   0
% 2.67/0.99  sim_eq_res_simp:                        0
% 2.67/0.99  sim_fw_demodulated:                     0
% 2.67/0.99  sim_bw_demodulated:                     6
% 2.67/0.99  sim_light_normalised:                   6
% 2.67/0.99  sim_joinable_taut:                      0
% 2.67/0.99  sim_joinable_simp:                      0
% 2.67/0.99  sim_ac_normalised:                      0
% 2.67/0.99  sim_smt_subsumption:                    0
% 2.67/0.99  
%------------------------------------------------------------------------------
