%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:27:31 EST 2020

% Result     : Theorem 11.70s
% Output     : CNFRefutation 11.70s
% Verified   : 
% Statistics : Number of formulae       :  167 (2721 expanded)
%              Number of clauses        :   89 ( 666 expanded)
%              Number of leaves         :   20 ( 787 expanded)
%              Depth                    :   23
%              Number of atoms          :  620 (13962 expanded)
%              Number of equality atoms :  237 (2720 expanded)
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

fof(f18,plain,(
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

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f47,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f47])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
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

fof(f50,plain,(
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
    inference(rectify,[],[f49])).

fof(f51,plain,(
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

fof(f52,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f50,f51])).

fof(f66,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f4,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f97,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f66,f70])).

fof(f101,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k2_tarski(X0,X0)) ) ),
    inference(equality_resolution,[],[f97])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f6,axiom,(
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
    inference(ennf_transformation,[],[f6])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f72,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

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
    inference(ennf_transformation,[],[f14])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X1,k2_pre_topc(X0,X2))
      | ~ v3_pre_topc(X1,X0)
      | ~ r1_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

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
    inference(ennf_transformation,[],[f17])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))
          & ~ r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK6)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
        & ~ r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK6)))
        & m1_subset_1(sK6,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
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

fof(f57,plain,
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

fof(f60,plain,
    ( k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK5)) != k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK6))
    & ~ r1_xboole_0(k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK5)),k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK6)))
    & m1_subset_1(sK6,u1_struct_0(sK4))
    & m1_subset_1(sK5,u1_struct_0(sK4))
    & l1_pre_topc(sK4)
    & v3_tdlat_3(sK4)
    & v2_pre_topc(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f42,f59,f58,f57])).

fof(f90,plain,(
    m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f60])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f98,plain,(
    ! [X0,X1] :
      ( k2_tarski(X1,X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f79,f70])).

fof(f86,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f60])).

fof(f89,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f60])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f74,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f73,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f91,plain,(
    m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f60])).

fof(f92,plain,(
    ~ r1_xboole_0(k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK5)),k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK6))) ),
    inference(cnf_transformation,[],[f60])).

fof(f87,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f60])).

fof(f88,plain,(
    v3_tdlat_3(sK4) ),
    inference(cnf_transformation,[],[f60])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f78,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f77,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

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

fof(f35,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f36,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f53,plain,(
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
    inference(nnf_transformation,[],[f36])).

fof(f54,plain,(
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
    inference(rectify,[],[f53])).

fof(f55,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_pre_topc(X1,X0)
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK3(X0),X0)
        & v4_pre_topc(sK3(X0),X0)
        & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f54,f55])).

fof(f80,plain,(
    ! [X2,X0] :
      ( v3_pre_topc(X2,X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f56])).

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
    inference(ennf_transformation,[],[f15])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))
      | ~ r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f93,plain,(
    k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK5)) != k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK6)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_3,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_876,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_4,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_875,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k2_tarski(X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f101])).

cnf(c_871,plain,
    ( X0 = X1
    | r2_hidden(X0,k2_tarski(X1,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2232,plain,
    ( sK1(k2_tarski(X0,X0),X1) = X0
    | r1_xboole_0(k2_tarski(X0,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_875,c_871])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_877,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_6878,plain,
    ( sK1(k2_tarski(X0,X0),X1) = X0
    | r2_hidden(X2,X1) != iProver_top
    | r2_hidden(X2,k2_tarski(X0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2232,c_877])).

cnf(c_8745,plain,
    ( sK1(k2_tarski(X0,X0),X1) = X0
    | r1_xboole_0(X2,k2_tarski(X0,X0)) = iProver_top
    | r2_hidden(sK1(X2,k2_tarski(X0,X0)),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_876,c_6878])).

cnf(c_18667,plain,
    ( sK1(k2_tarski(X0,X0),X1) = X0
    | r1_xboole_0(X1,k2_tarski(X0,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_875,c_8745])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_869,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_22,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_xboole_0(X0,X2)
    | r1_xboole_0(X0,k2_pre_topc(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_857,plain,
    ( v3_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_xboole_0(X0,X2) != iProver_top
    | r1_xboole_0(X0,k2_pre_topc(X1,X2)) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3596,plain,
    ( v3_pre_topc(k2_pre_topc(X0,X1),X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | r1_xboole_0(k2_pre_topc(X0,X1),X2) != iProver_top
    | r1_xboole_0(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_869,c_857])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_853,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_862,plain,
    ( k6_domain_1(X0,X1) = k2_tarski(X1,X1)
    | m1_subset_1(X1,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2450,plain,
    ( k6_domain_1(u1_struct_0(sK4),sK5) = k2_tarski(sK5,sK5)
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_853,c_862])).

cnf(c_31,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_28,negated_conjecture,
    ( l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_12,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_67,plain,
    ( v2_struct_0(sK4)
    | ~ l1_struct_0(sK4)
    | ~ v1_xboole_0(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_11,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_70,plain,
    ( l1_struct_0(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1230,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | v1_xboole_0(u1_struct_0(sK4))
    | k6_domain_1(u1_struct_0(sK4),sK5) = k2_tarski(sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_2799,plain,
    ( k6_domain_1(u1_struct_0(sK4),sK5) = k2_tarski(sK5,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2450,c_31,c_28,c_27,c_67,c_70,c_1230])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_854,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_2449,plain,
    ( k6_domain_1(u1_struct_0(sK4),sK6) = k2_tarski(sK6,sK6)
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_854,c_862])).

cnf(c_1227,plain,
    ( ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | v1_xboole_0(u1_struct_0(sK4))
    | k6_domain_1(u1_struct_0(sK4),sK6) = k2_tarski(sK6,sK6) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_2652,plain,
    ( k6_domain_1(u1_struct_0(sK4),sK6) = k2_tarski(sK6,sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2449,c_31,c_28,c_26,c_67,c_70,c_1227])).

cnf(c_25,negated_conjecture,
    ( ~ r1_xboole_0(k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK5)),k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK6))) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_855,plain,
    ( r1_xboole_0(k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK5)),k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK6))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2655,plain,
    ( r1_xboole_0(k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK5)),k2_pre_topc(sK4,k2_tarski(sK6,sK6))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2652,c_855])).

cnf(c_2802,plain,
    ( r1_xboole_0(k2_pre_topc(sK4,k2_tarski(sK5,sK5)),k2_pre_topc(sK4,k2_tarski(sK6,sK6))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2799,c_2655])).

cnf(c_32867,plain,
    ( v3_pre_topc(k2_pre_topc(sK4,k2_tarski(sK5,sK5)),sK4) != iProver_top
    | m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r1_xboole_0(k2_pre_topc(sK4,k2_tarski(sK5,sK5)),k2_tarski(sK6,sK6)) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3596,c_2802])).

cnf(c_32,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_30,negated_conjecture,
    ( v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_33,plain,
    ( v2_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_29,negated_conjecture,
    ( v3_tdlat_3(sK4) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_34,plain,
    ( v3_tdlat_3(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_35,plain,
    ( l1_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_36,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_37,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_66,plain,
    ( v2_struct_0(X0) = iProver_top
    | l1_struct_0(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_68,plain,
    ( v2_struct_0(sK4) = iProver_top
    | l1_struct_0(sK4) != iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_66])).

cnf(c_69,plain,
    ( l1_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_71,plain,
    ( l1_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_69])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_863,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3327,plain,
    ( m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2799,c_863])).

cnf(c_3328,plain,
    ( m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2652,c_863])).

cnf(c_3782,plain,
    ( m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3327,c_32,c_35,c_36,c_68,c_71])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k2_pre_topc(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_866,plain,
    ( k2_pre_topc(X0,k2_pre_topc(X0,X1)) = k2_pre_topc(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3790,plain,
    ( k2_pre_topc(sK4,k2_pre_topc(sK4,k2_tarski(sK5,sK5))) = k2_pre_topc(sK4,k2_tarski(sK5,sK5))
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3782,c_866])).

cnf(c_4651,plain,
    ( k2_pre_topc(sK4,k2_pre_topc(sK4,k2_tarski(sK5,sK5))) = k2_pre_topc(sK4,k2_tarski(sK5,sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3790,c_35])).

cnf(c_14,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_865,plain,
    ( k2_pre_topc(X0,X1) != X1
    | v4_pre_topc(X1,X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_4932,plain,
    ( v4_pre_topc(k2_pre_topc(sK4,k2_tarski(sK5,sK5)),sK4) = iProver_top
    | m1_subset_1(k2_pre_topc(sK4,k2_tarski(sK5,sK5)),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4651,c_865])).

cnf(c_11228,plain,
    ( m1_subset_1(k2_pre_topc(sK4,k2_tarski(sK5,sK5)),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_11229,plain,
    ( m1_subset_1(k2_pre_topc(sK4,k2_tarski(sK5,sK5)),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11228])).

cnf(c_21,plain,
    ( v3_pre_topc(X0,X1)
    | ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_858,plain,
    ( v3_pre_topc(X0,X1) = iProver_top
    | v4_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v3_tdlat_3(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3595,plain,
    ( v3_pre_topc(k2_pre_topc(X0,X1),X0) = iProver_top
    | v4_pre_topc(k2_pre_topc(X0,X1),X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v3_tdlat_3(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_869,c_858])).

cnf(c_29579,plain,
    ( v3_pre_topc(k2_pre_topc(sK4,k2_tarski(sK5,sK5)),sK4) = iProver_top
    | v4_pre_topc(k2_pre_topc(sK4,k2_tarski(sK5,sK5)),sK4) != iProver_top
    | v3_tdlat_3(sK4) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3782,c_3595])).

cnf(c_34786,plain,
    ( r1_xboole_0(k2_pre_topc(sK4,k2_tarski(sK5,sK5)),k2_tarski(sK6,sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_32867,c_32,c_33,c_34,c_35,c_36,c_37,c_68,c_71,c_3327,c_3328,c_4932,c_11229,c_29579])).

cnf(c_34800,plain,
    ( sK1(k2_tarski(sK6,sK6),k2_pre_topc(sK4,k2_tarski(sK5,sK5))) = sK6 ),
    inference(superposition,[status(thm)],[c_18667,c_34786])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X0)))
    | ~ v3_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X0)) = k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_856,plain,
    ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | r2_hidden(X2,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))) != iProver_top
    | v3_tdlat_3(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2809,plain,
    ( k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),X0)) = k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK5))
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0,k2_pre_topc(sK4,k2_tarski(sK5,sK5))) != iProver_top
    | v3_tdlat_3(sK4) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2799,c_856])).

cnf(c_2810,plain,
    ( k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),X0)) = k2_pre_topc(sK4,k2_tarski(sK5,sK5))
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0,k2_pre_topc(sK4,k2_tarski(sK5,sK5))) != iProver_top
    | v3_tdlat_3(sK4) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2809,c_2799])).

cnf(c_4442,plain,
    ( m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),X0)) = k2_pre_topc(sK4,k2_tarski(sK5,sK5))
    | r2_hidden(X0,k2_pre_topc(sK4,k2_tarski(sK5,sK5))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2810,c_32,c_33,c_34,c_35,c_36])).

cnf(c_4443,plain,
    ( k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),X0)) = k2_pre_topc(sK4,k2_tarski(sK5,sK5))
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0,k2_pre_topc(sK4,k2_tarski(sK5,sK5))) != iProver_top ),
    inference(renaming,[status(thm)],[c_4442])).

cnf(c_4452,plain,
    ( k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK1(X0,k2_pre_topc(sK4,k2_tarski(sK5,sK5))))) = k2_pre_topc(sK4,k2_tarski(sK5,sK5))
    | m1_subset_1(sK1(X0,k2_pre_topc(sK4,k2_tarski(sK5,sK5))),u1_struct_0(sK4)) != iProver_top
    | r1_xboole_0(X0,k2_pre_topc(sK4,k2_tarski(sK5,sK5))) = iProver_top ),
    inference(superposition,[status(thm)],[c_876,c_4443])).

cnf(c_40334,plain,
    ( k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK1(k2_tarski(sK6,sK6),k2_pre_topc(sK4,k2_tarski(sK5,sK5))))) = k2_pre_topc(sK4,k2_tarski(sK5,sK5))
    | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top
    | r1_xboole_0(k2_tarski(sK6,sK6),k2_pre_topc(sK4,k2_tarski(sK5,sK5))) = iProver_top ),
    inference(superposition,[status(thm)],[c_34800,c_4452])).

cnf(c_40345,plain,
    ( k2_pre_topc(sK4,k2_tarski(sK6,sK6)) = k2_pre_topc(sK4,k2_tarski(sK5,sK5))
    | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top
    | r1_xboole_0(k2_tarski(sK6,sK6),k2_pre_topc(sK4,k2_tarski(sK5,sK5))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_40334,c_2652,c_34800])).

cnf(c_24,negated_conjecture,
    ( k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK5)) != k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK6)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_2656,plain,
    ( k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK5)) != k2_pre_topc(sK4,k2_tarski(sK6,sK6)) ),
    inference(demodulation,[status(thm)],[c_2652,c_24])).

cnf(c_2803,plain,
    ( k2_pre_topc(sK4,k2_tarski(sK6,sK6)) != k2_pre_topc(sK4,k2_tarski(sK5,sK5)) ),
    inference(demodulation,[status(thm)],[c_2799,c_2656])).

cnf(c_40487,plain,
    ( r1_xboole_0(k2_tarski(sK6,sK6),k2_pre_topc(sK4,k2_tarski(sK5,sK5))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_40345,c_37,c_2803])).

cnf(c_40496,plain,
    ( r2_hidden(X0,k2_pre_topc(sK4,k2_tarski(sK5,sK5))) != iProver_top
    | r2_hidden(X0,k2_tarski(sK6,sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_40487,c_877])).

cnf(c_40545,plain,
    ( r1_xboole_0(k2_pre_topc(sK4,k2_tarski(sK5,sK5)),X0) = iProver_top
    | r2_hidden(sK1(k2_pre_topc(sK4,k2_tarski(sK5,sK5)),X0),k2_tarski(sK6,sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_875,c_40496])).

cnf(c_41809,plain,
    ( r1_xboole_0(k2_pre_topc(sK4,k2_tarski(sK5,sK5)),k2_tarski(sK6,sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_876,c_40545])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_41809,c_32867,c_29579,c_11229,c_4932,c_3328,c_3327,c_71,c_68,c_37,c_36,c_35,c_34,c_33,c_32])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:12:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 11.70/1.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.70/1.99  
% 11.70/1.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.70/1.99  
% 11.70/1.99  ------  iProver source info
% 11.70/1.99  
% 11.70/1.99  git: date: 2020-06-30 10:37:57 +0100
% 11.70/1.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.70/1.99  git: non_committed_changes: false
% 11.70/1.99  git: last_make_outside_of_git: false
% 11.70/1.99  
% 11.70/1.99  ------ 
% 11.70/1.99  ------ Parsing...
% 11.70/1.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.70/1.99  
% 11.70/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 11.70/1.99  
% 11.70/1.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.70/1.99  
% 11.70/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.70/1.99  ------ Proving...
% 11.70/1.99  ------ Problem Properties 
% 11.70/1.99  
% 11.70/1.99  
% 11.70/1.99  clauses                                 32
% 11.70/1.99  conjectures                             8
% 11.70/1.99  EPR                                     8
% 11.70/1.99  Horn                                    22
% 11.70/1.99  unary                                   9
% 11.70/1.99  binary                                  6
% 11.70/1.99  lits                                    90
% 11.70/1.99  lits eq                                 11
% 11.70/1.99  fd_pure                                 0
% 11.70/1.99  fd_pseudo                               0
% 11.70/1.99  fd_cond                                 0
% 11.70/1.99  fd_pseudo_cond                          2
% 11.70/1.99  AC symbols                              0
% 11.70/1.99  
% 11.70/1.99  ------ Input Options Time Limit: Unbounded
% 11.70/1.99  
% 11.70/1.99  
% 11.70/1.99  ------ 
% 11.70/1.99  Current options:
% 11.70/1.99  ------ 
% 11.70/1.99  
% 11.70/1.99  
% 11.70/1.99  
% 11.70/1.99  
% 11.70/1.99  ------ Proving...
% 11.70/1.99  
% 11.70/1.99  
% 11.70/1.99  % SZS status Theorem for theBenchmark.p
% 11.70/1.99  
% 11.70/1.99  % SZS output start CNFRefutation for theBenchmark.p
% 11.70/1.99  
% 11.70/1.99  fof(f2,axiom,(
% 11.70/1.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 11.70/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.70/1.99  
% 11.70/1.99  fof(f18,plain,(
% 11.70/1.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 11.70/1.99    inference(rectify,[],[f2])).
% 11.70/1.99  
% 11.70/1.99  fof(f19,plain,(
% 11.70/1.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 11.70/1.99    inference(ennf_transformation,[],[f18])).
% 11.70/1.99  
% 11.70/1.99  fof(f47,plain,(
% 11.70/1.99    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 11.70/1.99    introduced(choice_axiom,[])).
% 11.70/1.99  
% 11.70/1.99  fof(f48,plain,(
% 11.70/1.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 11.70/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f47])).
% 11.70/1.99  
% 11.70/1.99  fof(f64,plain,(
% 11.70/1.99    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 11.70/1.99    inference(cnf_transformation,[],[f48])).
% 11.70/1.99  
% 11.70/1.99  fof(f63,plain,(
% 11.70/1.99    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 11.70/1.99    inference(cnf_transformation,[],[f48])).
% 11.70/1.99  
% 11.70/1.99  fof(f3,axiom,(
% 11.70/1.99    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 11.70/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.70/1.99  
% 11.70/1.99  fof(f49,plain,(
% 11.70/1.99    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 11.70/1.99    inference(nnf_transformation,[],[f3])).
% 11.70/1.99  
% 11.70/1.99  fof(f50,plain,(
% 11.70/1.99    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 11.70/1.99    inference(rectify,[],[f49])).
% 11.70/1.99  
% 11.70/1.99  fof(f51,plain,(
% 11.70/1.99    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 11.70/1.99    introduced(choice_axiom,[])).
% 11.70/1.99  
% 11.70/1.99  fof(f52,plain,(
% 11.70/1.99    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 11.70/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f50,f51])).
% 11.70/1.99  
% 11.70/1.99  fof(f66,plain,(
% 11.70/1.99    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 11.70/1.99    inference(cnf_transformation,[],[f52])).
% 11.70/1.99  
% 11.70/1.99  fof(f4,axiom,(
% 11.70/1.99    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 11.70/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.70/1.99  
% 11.70/1.99  fof(f70,plain,(
% 11.70/1.99    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 11.70/1.99    inference(cnf_transformation,[],[f4])).
% 11.70/1.99  
% 11.70/1.99  fof(f97,plain,(
% 11.70/1.99    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_tarski(X0,X0) != X1) )),
% 11.70/1.99    inference(definition_unfolding,[],[f66,f70])).
% 11.70/1.99  
% 11.70/1.99  fof(f101,plain,(
% 11.70/1.99    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k2_tarski(X0,X0))) )),
% 11.70/1.99    inference(equality_resolution,[],[f97])).
% 11.70/1.99  
% 11.70/1.99  fof(f65,plain,(
% 11.70/1.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 11.70/1.99    inference(cnf_transformation,[],[f48])).
% 11.70/1.99  
% 11.70/1.99  fof(f6,axiom,(
% 11.70/1.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 11.70/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.70/1.99  
% 11.70/1.99  fof(f22,plain,(
% 11.70/1.99    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 11.70/1.99    inference(ennf_transformation,[],[f6])).
% 11.70/1.99  
% 11.70/1.99  fof(f23,plain,(
% 11.70/1.99    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 11.70/1.99    inference(flattening,[],[f22])).
% 11.70/1.99  
% 11.70/1.99  fof(f72,plain,(
% 11.70/1.99    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.70/1.99    inference(cnf_transformation,[],[f23])).
% 11.70/1.99  
% 11.70/1.99  fof(f14,axiom,(
% 11.70/1.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X1,X0) & r1_xboole_0(X1,X2)) => r1_xboole_0(X1,k2_pre_topc(X0,X2))))))),
% 11.70/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.70/1.99  
% 11.70/1.99  fof(f37,plain,(
% 11.70/1.99    ! [X0] : (! [X1] : (! [X2] : ((r1_xboole_0(X1,k2_pre_topc(X0,X2)) | (~v3_pre_topc(X1,X0) | ~r1_xboole_0(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 11.70/1.99    inference(ennf_transformation,[],[f14])).
% 11.70/1.99  
% 11.70/1.99  fof(f38,plain,(
% 11.70/1.99    ! [X0] : (! [X1] : (! [X2] : (r1_xboole_0(X1,k2_pre_topc(X0,X2)) | ~v3_pre_topc(X1,X0) | ~r1_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 11.70/1.99    inference(flattening,[],[f37])).
% 11.70/1.99  
% 11.70/1.99  fof(f84,plain,(
% 11.70/1.99    ( ! [X2,X0,X1] : (r1_xboole_0(X1,k2_pre_topc(X0,X2)) | ~v3_pre_topc(X1,X0) | ~r1_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 11.70/1.99    inference(cnf_transformation,[],[f38])).
% 11.70/1.99  
% 11.70/1.99  fof(f16,conjecture,(
% 11.70/1.99    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) | r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))))))),
% 11.70/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.70/1.99  
% 11.70/1.99  fof(f17,negated_conjecture,(
% 11.70/1.99    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) | r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))))))),
% 11.70/1.99    inference(negated_conjecture,[],[f16])).
% 11.70/1.99  
% 11.70/1.99  fof(f41,plain,(
% 11.70/1.99    ? [X0] : (? [X1] : (? [X2] : ((k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 11.70/1.99    inference(ennf_transformation,[],[f17])).
% 11.70/1.99  
% 11.70/1.99  fof(f42,plain,(
% 11.70/1.99    ? [X0] : (? [X1] : (? [X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 11.70/1.99    inference(flattening,[],[f41])).
% 11.70/1.99  
% 11.70/1.99  fof(f59,plain,(
% 11.70/1.99    ( ! [X0,X1] : (? [X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & m1_subset_1(X2,u1_struct_0(X0))) => (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK6)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK6))) & m1_subset_1(sK6,u1_struct_0(X0)))) )),
% 11.70/1.99    introduced(choice_axiom,[])).
% 11.70/1.99  
% 11.70/1.99  fof(f58,plain,(
% 11.70/1.99    ( ! [X0] : (? [X1] : (? [X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK5)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK5)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK5,u1_struct_0(X0)))) )),
% 11.70/1.99    introduced(choice_axiom,[])).
% 11.70/1.99  
% 11.70/1.99  fof(f57,plain,(
% 11.70/1.99    ? [X0] : (? [X1] : (? [X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),X1)) != k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),X2)) & ~r1_xboole_0(k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),X1)),k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),X2))) & m1_subset_1(X2,u1_struct_0(sK4))) & m1_subset_1(X1,u1_struct_0(sK4))) & l1_pre_topc(sK4) & v3_tdlat_3(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4))),
% 11.70/1.99    introduced(choice_axiom,[])).
% 11.70/1.99  
% 11.70/1.99  fof(f60,plain,(
% 11.70/1.99    ((k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK5)) != k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK6)) & ~r1_xboole_0(k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK5)),k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK6))) & m1_subset_1(sK6,u1_struct_0(sK4))) & m1_subset_1(sK5,u1_struct_0(sK4))) & l1_pre_topc(sK4) & v3_tdlat_3(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4)),
% 11.70/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f42,f59,f58,f57])).
% 11.70/1.99  
% 11.70/1.99  fof(f90,plain,(
% 11.70/1.99    m1_subset_1(sK5,u1_struct_0(sK4))),
% 11.70/1.99    inference(cnf_transformation,[],[f60])).
% 11.70/1.99  
% 11.70/1.99  fof(f12,axiom,(
% 11.70/1.99    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 11.70/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.70/1.99  
% 11.70/1.99  fof(f33,plain,(
% 11.70/1.99    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 11.70/1.99    inference(ennf_transformation,[],[f12])).
% 11.70/1.99  
% 11.70/1.99  fof(f34,plain,(
% 11.70/1.99    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 11.70/1.99    inference(flattening,[],[f33])).
% 11.70/1.99  
% 11.70/1.99  fof(f79,plain,(
% 11.70/1.99    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 11.70/1.99    inference(cnf_transformation,[],[f34])).
% 11.70/1.99  
% 11.70/1.99  fof(f98,plain,(
% 11.70/1.99    ( ! [X0,X1] : (k2_tarski(X1,X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 11.70/1.99    inference(definition_unfolding,[],[f79,f70])).
% 11.70/1.99  
% 11.70/1.99  fof(f86,plain,(
% 11.70/1.99    ~v2_struct_0(sK4)),
% 11.70/1.99    inference(cnf_transformation,[],[f60])).
% 11.70/1.99  
% 11.70/1.99  fof(f89,plain,(
% 11.70/1.99    l1_pre_topc(sK4)),
% 11.70/1.99    inference(cnf_transformation,[],[f60])).
% 11.70/1.99  
% 11.70/1.99  fof(f8,axiom,(
% 11.70/1.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 11.70/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.70/1.99  
% 11.70/1.99  fof(f25,plain,(
% 11.70/1.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 11.70/1.99    inference(ennf_transformation,[],[f8])).
% 11.70/1.99  
% 11.70/1.99  fof(f26,plain,(
% 11.70/1.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 11.70/1.99    inference(flattening,[],[f25])).
% 11.70/1.99  
% 11.70/1.99  fof(f74,plain,(
% 11.70/1.99    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 11.70/1.99    inference(cnf_transformation,[],[f26])).
% 11.70/1.99  
% 11.70/1.99  fof(f7,axiom,(
% 11.70/1.99    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 11.70/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.70/1.99  
% 11.70/1.99  fof(f24,plain,(
% 11.70/1.99    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 11.70/1.99    inference(ennf_transformation,[],[f7])).
% 11.70/1.99  
% 11.70/1.99  fof(f73,plain,(
% 11.70/1.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 11.70/1.99    inference(cnf_transformation,[],[f24])).
% 11.70/1.99  
% 11.70/1.99  fof(f91,plain,(
% 11.70/1.99    m1_subset_1(sK6,u1_struct_0(sK4))),
% 11.70/1.99    inference(cnf_transformation,[],[f60])).
% 11.70/1.99  
% 11.70/1.99  fof(f92,plain,(
% 11.70/1.99    ~r1_xboole_0(k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK5)),k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK6)))),
% 11.70/1.99    inference(cnf_transformation,[],[f60])).
% 11.70/1.99  
% 11.70/1.99  fof(f87,plain,(
% 11.70/1.99    v2_pre_topc(sK4)),
% 11.70/1.99    inference(cnf_transformation,[],[f60])).
% 11.70/1.99  
% 11.70/1.99  fof(f88,plain,(
% 11.70/1.99    v3_tdlat_3(sK4)),
% 11.70/1.99    inference(cnf_transformation,[],[f60])).
% 11.70/1.99  
% 11.70/1.99  fof(f11,axiom,(
% 11.70/1.99    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 11.70/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.70/1.99  
% 11.70/1.99  fof(f31,plain,(
% 11.70/1.99    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 11.70/1.99    inference(ennf_transformation,[],[f11])).
% 11.70/1.99  
% 11.70/1.99  fof(f32,plain,(
% 11.70/1.99    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 11.70/1.99    inference(flattening,[],[f31])).
% 11.70/1.99  
% 11.70/1.99  fof(f78,plain,(
% 11.70/1.99    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 11.70/1.99    inference(cnf_transformation,[],[f32])).
% 11.70/1.99  
% 11.70/1.99  fof(f9,axiom,(
% 11.70/1.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)))),
% 11.70/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.70/1.99  
% 11.70/1.99  fof(f27,plain,(
% 11.70/1.99    ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 11.70/1.99    inference(ennf_transformation,[],[f9])).
% 11.70/1.99  
% 11.70/1.99  fof(f28,plain,(
% 11.70/1.99    ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 11.70/1.99    inference(flattening,[],[f27])).
% 11.70/1.99  
% 11.70/1.99  fof(f75,plain,(
% 11.70/1.99    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.70/1.99    inference(cnf_transformation,[],[f28])).
% 11.70/1.99  
% 11.70/1.99  fof(f10,axiom,(
% 11.70/1.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 11.70/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.70/1.99  
% 11.70/1.99  fof(f29,plain,(
% 11.70/1.99    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.70/1.99    inference(ennf_transformation,[],[f10])).
% 11.70/1.99  
% 11.70/1.99  fof(f30,plain,(
% 11.70/1.99    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.70/1.99    inference(flattening,[],[f29])).
% 11.70/1.99  
% 11.70/1.99  fof(f77,plain,(
% 11.70/1.99    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.70/1.99    inference(cnf_transformation,[],[f30])).
% 11.70/1.99  
% 11.70/1.99  fof(f13,axiom,(
% 11.70/1.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v3_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => v3_pre_topc(X1,X0)))))),
% 11.70/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.70/1.99  
% 11.70/1.99  fof(f35,plain,(
% 11.70/1.99    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : ((v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 11.70/1.99    inference(ennf_transformation,[],[f13])).
% 11.70/1.99  
% 11.70/1.99  fof(f36,plain,(
% 11.70/1.99    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 11.70/1.99    inference(flattening,[],[f35])).
% 11.70/1.99  
% 11.70/1.99  fof(f53,plain,(
% 11.70/1.99    ! [X0] : (((v3_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X1] : (v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 11.70/1.99    inference(nnf_transformation,[],[f36])).
% 11.70/1.99  
% 11.70/1.99  fof(f54,plain,(
% 11.70/1.99    ! [X0] : (((v3_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 11.70/1.99    inference(rectify,[],[f53])).
% 11.70/1.99  
% 11.70/1.99  fof(f55,plain,(
% 11.70/1.99    ! [X0] : (? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK3(X0),X0) & v4_pre_topc(sK3(X0),X0) & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 11.70/1.99    introduced(choice_axiom,[])).
% 11.70/1.99  
% 11.70/1.99  fof(f56,plain,(
% 11.70/1.99    ! [X0] : (((v3_tdlat_3(X0) | (~v3_pre_topc(sK3(X0),X0) & v4_pre_topc(sK3(X0),X0) & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 11.70/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f54,f55])).
% 11.70/1.99  
% 11.70/1.99  fof(f80,plain,(
% 11.70/1.99    ( ! [X2,X0] : (v3_pre_topc(X2,X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tdlat_3(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 11.70/1.99    inference(cnf_transformation,[],[f56])).
% 11.70/1.99  
% 11.70/1.99  fof(f15,axiom,(
% 11.70/1.99    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) => k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))))))),
% 11.70/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.70/1.99  
% 11.70/1.99  fof(f39,plain,(
% 11.70/1.99    ! [X0] : (! [X1] : (! [X2] : ((k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) | ~r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 11.70/1.99    inference(ennf_transformation,[],[f15])).
% 11.70/1.99  
% 11.70/1.99  fof(f40,plain,(
% 11.70/1.99    ! [X0] : (! [X1] : (! [X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) | ~r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.70/1.99    inference(flattening,[],[f39])).
% 11.70/1.99  
% 11.70/1.99  fof(f85,plain,(
% 11.70/1.99    ( ! [X2,X0,X1] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) | ~r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.70/1.99    inference(cnf_transformation,[],[f40])).
% 11.70/1.99  
% 11.70/1.99  fof(f93,plain,(
% 11.70/1.99    k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK5)) != k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK6))),
% 11.70/1.99    inference(cnf_transformation,[],[f60])).
% 11.70/1.99  
% 11.70/1.99  cnf(c_3,plain,
% 11.70/1.99      ( r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X1) ),
% 11.70/1.99      inference(cnf_transformation,[],[f64]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_876,plain,
% 11.70/1.99      ( r1_xboole_0(X0,X1) = iProver_top
% 11.70/1.99      | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
% 11.70/1.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_4,plain,
% 11.70/1.99      ( r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 11.70/1.99      inference(cnf_transformation,[],[f63]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_875,plain,
% 11.70/1.99      ( r1_xboole_0(X0,X1) = iProver_top
% 11.70/1.99      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 11.70/1.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_8,plain,
% 11.70/1.99      ( ~ r2_hidden(X0,k2_tarski(X1,X1)) | X0 = X1 ),
% 11.70/1.99      inference(cnf_transformation,[],[f101]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_871,plain,
% 11.70/1.99      ( X0 = X1 | r2_hidden(X0,k2_tarski(X1,X1)) != iProver_top ),
% 11.70/1.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_2232,plain,
% 11.70/1.99      ( sK1(k2_tarski(X0,X0),X1) = X0
% 11.70/1.99      | r1_xboole_0(k2_tarski(X0,X0),X1) = iProver_top ),
% 11.70/1.99      inference(superposition,[status(thm)],[c_875,c_871]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_2,plain,
% 11.70/1.99      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,X0) | ~ r2_hidden(X2,X1) ),
% 11.70/1.99      inference(cnf_transformation,[],[f65]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_877,plain,
% 11.70/1.99      ( r1_xboole_0(X0,X1) != iProver_top
% 11.70/1.99      | r2_hidden(X2,X0) != iProver_top
% 11.70/1.99      | r2_hidden(X2,X1) != iProver_top ),
% 11.70/1.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_6878,plain,
% 11.70/1.99      ( sK1(k2_tarski(X0,X0),X1) = X0
% 11.70/1.99      | r2_hidden(X2,X1) != iProver_top
% 11.70/1.99      | r2_hidden(X2,k2_tarski(X0,X0)) != iProver_top ),
% 11.70/1.99      inference(superposition,[status(thm)],[c_2232,c_877]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_8745,plain,
% 11.70/1.99      ( sK1(k2_tarski(X0,X0),X1) = X0
% 11.70/1.99      | r1_xboole_0(X2,k2_tarski(X0,X0)) = iProver_top
% 11.70/1.99      | r2_hidden(sK1(X2,k2_tarski(X0,X0)),X1) != iProver_top ),
% 11.70/1.99      inference(superposition,[status(thm)],[c_876,c_6878]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_18667,plain,
% 11.70/1.99      ( sK1(k2_tarski(X0,X0),X1) = X0
% 11.70/1.99      | r1_xboole_0(X1,k2_tarski(X0,X0)) = iProver_top ),
% 11.70/1.99      inference(superposition,[status(thm)],[c_875,c_8745]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_10,plain,
% 11.70/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.70/1.99      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 11.70/1.99      | ~ l1_pre_topc(X1) ),
% 11.70/1.99      inference(cnf_transformation,[],[f72]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_869,plain,
% 11.70/1.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 11.70/1.99      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 11.70/1.99      | l1_pre_topc(X1) != iProver_top ),
% 11.70/1.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_22,plain,
% 11.70/1.99      ( ~ v3_pre_topc(X0,X1)
% 11.70/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.70/1.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 11.70/1.99      | ~ r1_xboole_0(X0,X2)
% 11.70/1.99      | r1_xboole_0(X0,k2_pre_topc(X1,X2))
% 11.70/1.99      | ~ v2_pre_topc(X1)
% 11.70/1.99      | ~ l1_pre_topc(X1) ),
% 11.70/1.99      inference(cnf_transformation,[],[f84]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_857,plain,
% 11.70/1.99      ( v3_pre_topc(X0,X1) != iProver_top
% 11.70/1.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 11.70/1.99      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 11.70/1.99      | r1_xboole_0(X0,X2) != iProver_top
% 11.70/1.99      | r1_xboole_0(X0,k2_pre_topc(X1,X2)) = iProver_top
% 11.70/1.99      | v2_pre_topc(X1) != iProver_top
% 11.70/1.99      | l1_pre_topc(X1) != iProver_top ),
% 11.70/1.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_3596,plain,
% 11.70/1.99      ( v3_pre_topc(k2_pre_topc(X0,X1),X0) != iProver_top
% 11.70/1.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 11.70/1.99      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 11.70/1.99      | r1_xboole_0(k2_pre_topc(X0,X1),X2) != iProver_top
% 11.70/1.99      | r1_xboole_0(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) = iProver_top
% 11.70/1.99      | v2_pre_topc(X0) != iProver_top
% 11.70/1.99      | l1_pre_topc(X0) != iProver_top ),
% 11.70/1.99      inference(superposition,[status(thm)],[c_869,c_857]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_27,negated_conjecture,
% 11.70/1.99      ( m1_subset_1(sK5,u1_struct_0(sK4)) ),
% 11.70/1.99      inference(cnf_transformation,[],[f90]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_853,plain,
% 11.70/1.99      ( m1_subset_1(sK5,u1_struct_0(sK4)) = iProver_top ),
% 11.70/1.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_17,plain,
% 11.70/1.99      ( ~ m1_subset_1(X0,X1)
% 11.70/1.99      | v1_xboole_0(X1)
% 11.70/1.99      | k6_domain_1(X1,X0) = k2_tarski(X0,X0) ),
% 11.70/1.99      inference(cnf_transformation,[],[f98]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_862,plain,
% 11.70/1.99      ( k6_domain_1(X0,X1) = k2_tarski(X1,X1)
% 11.70/1.99      | m1_subset_1(X1,X0) != iProver_top
% 11.70/1.99      | v1_xboole_0(X0) = iProver_top ),
% 11.70/1.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_2450,plain,
% 11.70/1.99      ( k6_domain_1(u1_struct_0(sK4),sK5) = k2_tarski(sK5,sK5)
% 11.70/1.99      | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
% 11.70/1.99      inference(superposition,[status(thm)],[c_853,c_862]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_31,negated_conjecture,
% 11.70/1.99      ( ~ v2_struct_0(sK4) ),
% 11.70/1.99      inference(cnf_transformation,[],[f86]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_28,negated_conjecture,
% 11.70/1.99      ( l1_pre_topc(sK4) ),
% 11.70/1.99      inference(cnf_transformation,[],[f89]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_12,plain,
% 11.70/1.99      ( v2_struct_0(X0)
% 11.70/1.99      | ~ l1_struct_0(X0)
% 11.70/1.99      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 11.70/1.99      inference(cnf_transformation,[],[f74]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_67,plain,
% 11.70/1.99      ( v2_struct_0(sK4)
% 11.70/1.99      | ~ l1_struct_0(sK4)
% 11.70/1.99      | ~ v1_xboole_0(u1_struct_0(sK4)) ),
% 11.70/1.99      inference(instantiation,[status(thm)],[c_12]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_11,plain,
% 11.70/1.99      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 11.70/1.99      inference(cnf_transformation,[],[f73]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_70,plain,
% 11.70/1.99      ( l1_struct_0(sK4) | ~ l1_pre_topc(sK4) ),
% 11.70/1.99      inference(instantiation,[status(thm)],[c_11]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_1230,plain,
% 11.70/1.99      ( ~ m1_subset_1(sK5,u1_struct_0(sK4))
% 11.70/1.99      | v1_xboole_0(u1_struct_0(sK4))
% 11.70/1.99      | k6_domain_1(u1_struct_0(sK4),sK5) = k2_tarski(sK5,sK5) ),
% 11.70/1.99      inference(instantiation,[status(thm)],[c_17]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_2799,plain,
% 11.70/1.99      ( k6_domain_1(u1_struct_0(sK4),sK5) = k2_tarski(sK5,sK5) ),
% 11.70/1.99      inference(global_propositional_subsumption,
% 11.70/1.99                [status(thm)],
% 11.70/1.99                [c_2450,c_31,c_28,c_27,c_67,c_70,c_1230]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_26,negated_conjecture,
% 11.70/1.99      ( m1_subset_1(sK6,u1_struct_0(sK4)) ),
% 11.70/1.99      inference(cnf_transformation,[],[f91]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_854,plain,
% 11.70/1.99      ( m1_subset_1(sK6,u1_struct_0(sK4)) = iProver_top ),
% 11.70/1.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_2449,plain,
% 11.70/1.99      ( k6_domain_1(u1_struct_0(sK4),sK6) = k2_tarski(sK6,sK6)
% 11.70/1.99      | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
% 11.70/1.99      inference(superposition,[status(thm)],[c_854,c_862]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_1227,plain,
% 11.70/1.99      ( ~ m1_subset_1(sK6,u1_struct_0(sK4))
% 11.70/1.99      | v1_xboole_0(u1_struct_0(sK4))
% 11.70/1.99      | k6_domain_1(u1_struct_0(sK4),sK6) = k2_tarski(sK6,sK6) ),
% 11.70/1.99      inference(instantiation,[status(thm)],[c_17]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_2652,plain,
% 11.70/1.99      ( k6_domain_1(u1_struct_0(sK4),sK6) = k2_tarski(sK6,sK6) ),
% 11.70/1.99      inference(global_propositional_subsumption,
% 11.70/1.99                [status(thm)],
% 11.70/1.99                [c_2449,c_31,c_28,c_26,c_67,c_70,c_1227]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_25,negated_conjecture,
% 11.70/1.99      ( ~ r1_xboole_0(k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK5)),k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK6))) ),
% 11.70/1.99      inference(cnf_transformation,[],[f92]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_855,plain,
% 11.70/1.99      ( r1_xboole_0(k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK5)),k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK6))) != iProver_top ),
% 11.70/1.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_2655,plain,
% 11.70/1.99      ( r1_xboole_0(k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK5)),k2_pre_topc(sK4,k2_tarski(sK6,sK6))) != iProver_top ),
% 11.70/1.99      inference(demodulation,[status(thm)],[c_2652,c_855]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_2802,plain,
% 11.70/1.99      ( r1_xboole_0(k2_pre_topc(sK4,k2_tarski(sK5,sK5)),k2_pre_topc(sK4,k2_tarski(sK6,sK6))) != iProver_top ),
% 11.70/1.99      inference(demodulation,[status(thm)],[c_2799,c_2655]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_32867,plain,
% 11.70/1.99      ( v3_pre_topc(k2_pre_topc(sK4,k2_tarski(sK5,sK5)),sK4) != iProver_top
% 11.70/1.99      | m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 11.70/1.99      | m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 11.70/1.99      | r1_xboole_0(k2_pre_topc(sK4,k2_tarski(sK5,sK5)),k2_tarski(sK6,sK6)) != iProver_top
% 11.70/1.99      | v2_pre_topc(sK4) != iProver_top
% 11.70/1.99      | l1_pre_topc(sK4) != iProver_top ),
% 11.70/1.99      inference(superposition,[status(thm)],[c_3596,c_2802]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_32,plain,
% 11.70/1.99      ( v2_struct_0(sK4) != iProver_top ),
% 11.70/1.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_30,negated_conjecture,
% 11.70/1.99      ( v2_pre_topc(sK4) ),
% 11.70/1.99      inference(cnf_transformation,[],[f87]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_33,plain,
% 11.70/1.99      ( v2_pre_topc(sK4) = iProver_top ),
% 11.70/1.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_29,negated_conjecture,
% 11.70/1.99      ( v3_tdlat_3(sK4) ),
% 11.70/1.99      inference(cnf_transformation,[],[f88]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_34,plain,
% 11.70/1.99      ( v3_tdlat_3(sK4) = iProver_top ),
% 11.70/1.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_35,plain,
% 11.70/1.99      ( l1_pre_topc(sK4) = iProver_top ),
% 11.70/1.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_36,plain,
% 11.70/1.99      ( m1_subset_1(sK5,u1_struct_0(sK4)) = iProver_top ),
% 11.70/1.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_37,plain,
% 11.70/1.99      ( m1_subset_1(sK6,u1_struct_0(sK4)) = iProver_top ),
% 11.70/1.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_66,plain,
% 11.70/1.99      ( v2_struct_0(X0) = iProver_top
% 11.70/1.99      | l1_struct_0(X0) != iProver_top
% 11.70/1.99      | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
% 11.70/1.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_68,plain,
% 11.70/1.99      ( v2_struct_0(sK4) = iProver_top
% 11.70/1.99      | l1_struct_0(sK4) != iProver_top
% 11.70/1.99      | v1_xboole_0(u1_struct_0(sK4)) != iProver_top ),
% 11.70/1.99      inference(instantiation,[status(thm)],[c_66]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_69,plain,
% 11.70/1.99      ( l1_struct_0(X0) = iProver_top | l1_pre_topc(X0) != iProver_top ),
% 11.70/1.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_71,plain,
% 11.70/1.99      ( l1_struct_0(sK4) = iProver_top
% 11.70/1.99      | l1_pre_topc(sK4) != iProver_top ),
% 11.70/1.99      inference(instantiation,[status(thm)],[c_69]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_16,plain,
% 11.70/1.99      ( ~ m1_subset_1(X0,X1)
% 11.70/1.99      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
% 11.70/1.99      | v1_xboole_0(X1) ),
% 11.70/1.99      inference(cnf_transformation,[],[f78]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_863,plain,
% 11.70/1.99      ( m1_subset_1(X0,X1) != iProver_top
% 11.70/1.99      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top
% 11.70/1.99      | v1_xboole_0(X1) = iProver_top ),
% 11.70/1.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_3327,plain,
% 11.70/1.99      ( m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
% 11.70/1.99      | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
% 11.70/1.99      | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
% 11.70/1.99      inference(superposition,[status(thm)],[c_2799,c_863]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_3328,plain,
% 11.70/1.99      ( m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
% 11.70/1.99      | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top
% 11.70/1.99      | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
% 11.70/1.99      inference(superposition,[status(thm)],[c_2652,c_863]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_3782,plain,
% 11.70/1.99      ( m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 11.70/1.99      inference(global_propositional_subsumption,
% 11.70/1.99                [status(thm)],
% 11.70/1.99                [c_3327,c_32,c_35,c_36,c_68,c_71]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_13,plain,
% 11.70/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.70/1.99      | ~ l1_pre_topc(X1)
% 11.70/1.99      | k2_pre_topc(X1,k2_pre_topc(X1,X0)) = k2_pre_topc(X1,X0) ),
% 11.70/1.99      inference(cnf_transformation,[],[f75]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_866,plain,
% 11.70/1.99      ( k2_pre_topc(X0,k2_pre_topc(X0,X1)) = k2_pre_topc(X0,X1)
% 11.70/1.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 11.70/1.99      | l1_pre_topc(X0) != iProver_top ),
% 11.70/1.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_3790,plain,
% 11.70/1.99      ( k2_pre_topc(sK4,k2_pre_topc(sK4,k2_tarski(sK5,sK5))) = k2_pre_topc(sK4,k2_tarski(sK5,sK5))
% 11.70/1.99      | l1_pre_topc(sK4) != iProver_top ),
% 11.70/1.99      inference(superposition,[status(thm)],[c_3782,c_866]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_4651,plain,
% 11.70/1.99      ( k2_pre_topc(sK4,k2_pre_topc(sK4,k2_tarski(sK5,sK5))) = k2_pre_topc(sK4,k2_tarski(sK5,sK5)) ),
% 11.70/1.99      inference(global_propositional_subsumption,
% 11.70/1.99                [status(thm)],
% 11.70/1.99                [c_3790,c_35]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_14,plain,
% 11.70/1.99      ( v4_pre_topc(X0,X1)
% 11.70/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.70/1.99      | ~ v2_pre_topc(X1)
% 11.70/1.99      | ~ l1_pre_topc(X1)
% 11.70/1.99      | k2_pre_topc(X1,X0) != X0 ),
% 11.70/1.99      inference(cnf_transformation,[],[f77]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_865,plain,
% 11.70/1.99      ( k2_pre_topc(X0,X1) != X1
% 11.70/1.99      | v4_pre_topc(X1,X0) = iProver_top
% 11.70/1.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 11.70/1.99      | v2_pre_topc(X0) != iProver_top
% 11.70/1.99      | l1_pre_topc(X0) != iProver_top ),
% 11.70/1.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_4932,plain,
% 11.70/1.99      ( v4_pre_topc(k2_pre_topc(sK4,k2_tarski(sK5,sK5)),sK4) = iProver_top
% 11.70/1.99      | m1_subset_1(k2_pre_topc(sK4,k2_tarski(sK5,sK5)),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 11.70/1.99      | v2_pre_topc(sK4) != iProver_top
% 11.70/1.99      | l1_pre_topc(sK4) != iProver_top ),
% 11.70/1.99      inference(superposition,[status(thm)],[c_4651,c_865]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_11228,plain,
% 11.70/1.99      ( m1_subset_1(k2_pre_topc(sK4,k2_tarski(sK5,sK5)),k1_zfmisc_1(u1_struct_0(sK4)))
% 11.70/1.99      | ~ m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK4)))
% 11.70/1.99      | ~ l1_pre_topc(sK4) ),
% 11.70/1.99      inference(instantiation,[status(thm)],[c_10]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_11229,plain,
% 11.70/1.99      ( m1_subset_1(k2_pre_topc(sK4,k2_tarski(sK5,sK5)),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
% 11.70/1.99      | m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 11.70/1.99      | l1_pre_topc(sK4) != iProver_top ),
% 11.70/1.99      inference(predicate_to_equality,[status(thm)],[c_11228]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_21,plain,
% 11.70/1.99      ( v3_pre_topc(X0,X1)
% 11.70/1.99      | ~ v4_pre_topc(X0,X1)
% 11.70/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.70/1.99      | ~ v3_tdlat_3(X1)
% 11.70/1.99      | ~ v2_pre_topc(X1)
% 11.70/1.99      | ~ l1_pre_topc(X1) ),
% 11.70/1.99      inference(cnf_transformation,[],[f80]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_858,plain,
% 11.70/1.99      ( v3_pre_topc(X0,X1) = iProver_top
% 11.70/1.99      | v4_pre_topc(X0,X1) != iProver_top
% 11.70/1.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 11.70/1.99      | v3_tdlat_3(X1) != iProver_top
% 11.70/1.99      | v2_pre_topc(X1) != iProver_top
% 11.70/1.99      | l1_pre_topc(X1) != iProver_top ),
% 11.70/1.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_3595,plain,
% 11.70/1.99      ( v3_pre_topc(k2_pre_topc(X0,X1),X0) = iProver_top
% 11.70/1.99      | v4_pre_topc(k2_pre_topc(X0,X1),X0) != iProver_top
% 11.70/1.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 11.70/1.99      | v3_tdlat_3(X0) != iProver_top
% 11.70/1.99      | v2_pre_topc(X0) != iProver_top
% 11.70/1.99      | l1_pre_topc(X0) != iProver_top ),
% 11.70/1.99      inference(superposition,[status(thm)],[c_869,c_858]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_29579,plain,
% 11.70/1.99      ( v3_pre_topc(k2_pre_topc(sK4,k2_tarski(sK5,sK5)),sK4) = iProver_top
% 11.70/1.99      | v4_pre_topc(k2_pre_topc(sK4,k2_tarski(sK5,sK5)),sK4) != iProver_top
% 11.70/1.99      | v3_tdlat_3(sK4) != iProver_top
% 11.70/1.99      | v2_pre_topc(sK4) != iProver_top
% 11.70/1.99      | l1_pre_topc(sK4) != iProver_top ),
% 11.70/1.99      inference(superposition,[status(thm)],[c_3782,c_3595]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_34786,plain,
% 11.70/1.99      ( r1_xboole_0(k2_pre_topc(sK4,k2_tarski(sK5,sK5)),k2_tarski(sK6,sK6)) != iProver_top ),
% 11.70/1.99      inference(global_propositional_subsumption,
% 11.70/1.99                [status(thm)],
% 11.70/1.99                [c_32867,c_32,c_33,c_34,c_35,c_36,c_37,c_68,c_71,c_3327,
% 11.70/1.99                 c_3328,c_4932,c_11229,c_29579]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_34800,plain,
% 11.70/1.99      ( sK1(k2_tarski(sK6,sK6),k2_pre_topc(sK4,k2_tarski(sK5,sK5))) = sK6 ),
% 11.70/1.99      inference(superposition,[status(thm)],[c_18667,c_34786]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_23,plain,
% 11.70/1.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 11.70/1.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 11.70/1.99      | ~ r2_hidden(X2,k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X0)))
% 11.70/1.99      | ~ v3_tdlat_3(X1)
% 11.70/1.99      | ~ v2_pre_topc(X1)
% 11.70/1.99      | v2_struct_0(X1)
% 11.70/1.99      | ~ l1_pre_topc(X1)
% 11.70/1.99      | k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X0)) = k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2)) ),
% 11.70/1.99      inference(cnf_transformation,[],[f85]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_856,plain,
% 11.70/1.99      ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))
% 11.70/1.99      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 11.70/1.99      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 11.70/1.99      | r2_hidden(X2,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))) != iProver_top
% 11.70/1.99      | v3_tdlat_3(X0) != iProver_top
% 11.70/1.99      | v2_pre_topc(X0) != iProver_top
% 11.70/1.99      | v2_struct_0(X0) = iProver_top
% 11.70/1.99      | l1_pre_topc(X0) != iProver_top ),
% 11.70/1.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_2809,plain,
% 11.70/1.99      ( k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),X0)) = k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK5))
% 11.70/1.99      | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
% 11.70/1.99      | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
% 11.70/1.99      | r2_hidden(X0,k2_pre_topc(sK4,k2_tarski(sK5,sK5))) != iProver_top
% 11.70/1.99      | v3_tdlat_3(sK4) != iProver_top
% 11.70/1.99      | v2_pre_topc(sK4) != iProver_top
% 11.70/1.99      | v2_struct_0(sK4) = iProver_top
% 11.70/1.99      | l1_pre_topc(sK4) != iProver_top ),
% 11.70/1.99      inference(superposition,[status(thm)],[c_2799,c_856]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_2810,plain,
% 11.70/1.99      ( k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),X0)) = k2_pre_topc(sK4,k2_tarski(sK5,sK5))
% 11.70/1.99      | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
% 11.70/1.99      | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
% 11.70/1.99      | r2_hidden(X0,k2_pre_topc(sK4,k2_tarski(sK5,sK5))) != iProver_top
% 11.70/1.99      | v3_tdlat_3(sK4) != iProver_top
% 11.70/1.99      | v2_pre_topc(sK4) != iProver_top
% 11.70/1.99      | v2_struct_0(sK4) = iProver_top
% 11.70/1.99      | l1_pre_topc(sK4) != iProver_top ),
% 11.70/1.99      inference(light_normalisation,[status(thm)],[c_2809,c_2799]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_4442,plain,
% 11.70/1.99      ( m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
% 11.70/1.99      | k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),X0)) = k2_pre_topc(sK4,k2_tarski(sK5,sK5))
% 11.70/1.99      | r2_hidden(X0,k2_pre_topc(sK4,k2_tarski(sK5,sK5))) != iProver_top ),
% 11.70/1.99      inference(global_propositional_subsumption,
% 11.70/1.99                [status(thm)],
% 11.70/1.99                [c_2810,c_32,c_33,c_34,c_35,c_36]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_4443,plain,
% 11.70/1.99      ( k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),X0)) = k2_pre_topc(sK4,k2_tarski(sK5,sK5))
% 11.70/1.99      | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
% 11.70/1.99      | r2_hidden(X0,k2_pre_topc(sK4,k2_tarski(sK5,sK5))) != iProver_top ),
% 11.70/1.99      inference(renaming,[status(thm)],[c_4442]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_4452,plain,
% 11.70/1.99      ( k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK1(X0,k2_pre_topc(sK4,k2_tarski(sK5,sK5))))) = k2_pre_topc(sK4,k2_tarski(sK5,sK5))
% 11.70/1.99      | m1_subset_1(sK1(X0,k2_pre_topc(sK4,k2_tarski(sK5,sK5))),u1_struct_0(sK4)) != iProver_top
% 11.70/1.99      | r1_xboole_0(X0,k2_pre_topc(sK4,k2_tarski(sK5,sK5))) = iProver_top ),
% 11.70/1.99      inference(superposition,[status(thm)],[c_876,c_4443]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_40334,plain,
% 11.70/1.99      ( k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK1(k2_tarski(sK6,sK6),k2_pre_topc(sK4,k2_tarski(sK5,sK5))))) = k2_pre_topc(sK4,k2_tarski(sK5,sK5))
% 11.70/1.99      | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top
% 11.70/1.99      | r1_xboole_0(k2_tarski(sK6,sK6),k2_pre_topc(sK4,k2_tarski(sK5,sK5))) = iProver_top ),
% 11.70/1.99      inference(superposition,[status(thm)],[c_34800,c_4452]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_40345,plain,
% 11.70/1.99      ( k2_pre_topc(sK4,k2_tarski(sK6,sK6)) = k2_pre_topc(sK4,k2_tarski(sK5,sK5))
% 11.70/1.99      | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top
% 11.70/1.99      | r1_xboole_0(k2_tarski(sK6,sK6),k2_pre_topc(sK4,k2_tarski(sK5,sK5))) = iProver_top ),
% 11.70/1.99      inference(light_normalisation,
% 11.70/1.99                [status(thm)],
% 11.70/1.99                [c_40334,c_2652,c_34800]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_24,negated_conjecture,
% 11.70/1.99      ( k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK5)) != k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK6)) ),
% 11.70/1.99      inference(cnf_transformation,[],[f93]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_2656,plain,
% 11.70/1.99      ( k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK5)) != k2_pre_topc(sK4,k2_tarski(sK6,sK6)) ),
% 11.70/1.99      inference(demodulation,[status(thm)],[c_2652,c_24]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_2803,plain,
% 11.70/1.99      ( k2_pre_topc(sK4,k2_tarski(sK6,sK6)) != k2_pre_topc(sK4,k2_tarski(sK5,sK5)) ),
% 11.70/1.99      inference(demodulation,[status(thm)],[c_2799,c_2656]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_40487,plain,
% 11.70/1.99      ( r1_xboole_0(k2_tarski(sK6,sK6),k2_pre_topc(sK4,k2_tarski(sK5,sK5))) = iProver_top ),
% 11.70/1.99      inference(global_propositional_subsumption,
% 11.70/1.99                [status(thm)],
% 11.70/1.99                [c_40345,c_37,c_2803]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_40496,plain,
% 11.70/1.99      ( r2_hidden(X0,k2_pre_topc(sK4,k2_tarski(sK5,sK5))) != iProver_top
% 11.70/1.99      | r2_hidden(X0,k2_tarski(sK6,sK6)) != iProver_top ),
% 11.70/1.99      inference(superposition,[status(thm)],[c_40487,c_877]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_40545,plain,
% 11.70/1.99      ( r1_xboole_0(k2_pre_topc(sK4,k2_tarski(sK5,sK5)),X0) = iProver_top
% 11.70/1.99      | r2_hidden(sK1(k2_pre_topc(sK4,k2_tarski(sK5,sK5)),X0),k2_tarski(sK6,sK6)) != iProver_top ),
% 11.70/1.99      inference(superposition,[status(thm)],[c_875,c_40496]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_41809,plain,
% 11.70/1.99      ( r1_xboole_0(k2_pre_topc(sK4,k2_tarski(sK5,sK5)),k2_tarski(sK6,sK6)) = iProver_top ),
% 11.70/1.99      inference(superposition,[status(thm)],[c_876,c_40545]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(contradiction,plain,
% 11.70/1.99      ( $false ),
% 11.70/1.99      inference(minisat,
% 11.70/1.99                [status(thm)],
% 11.70/1.99                [c_41809,c_32867,c_29579,c_11229,c_4932,c_3328,c_3327,
% 11.70/1.99                 c_71,c_68,c_37,c_36,c_35,c_34,c_33,c_32]) ).
% 11.70/1.99  
% 11.70/1.99  
% 11.70/1.99  % SZS output end CNFRefutation for theBenchmark.p
% 11.70/1.99  
% 11.70/1.99  ------                               Statistics
% 11.70/1.99  
% 11.70/1.99  ------ Selected
% 11.70/1.99  
% 11.70/1.99  total_time:                             1.06
% 11.70/1.99  
%------------------------------------------------------------------------------
