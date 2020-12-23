%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:27:31 EST 2020

% Result     : Theorem 11.65s
% Output     : CNFRefutation 11.65s
% Verified   : 
% Statistics : Number of formulae       :  177 (2608 expanded)
%              Number of clauses        :   95 ( 643 expanded)
%              Number of leaves         :   21 ( 744 expanded)
%              Depth                    :   21
%              Number of atoms          :  656 (13229 expanded)
%              Number of equality atoms :  227 (2442 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f46,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f46])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
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

fof(f49,plain,(
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
    inference(rectify,[],[f48])).

fof(f50,plain,(
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

fof(f51,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f49,f50])).

fof(f65,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f4,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f96,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f65,f69])).

fof(f101,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k2_tarski(X0,X0)) ) ),
    inference(equality_resolution,[],[f96])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f72,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X1,k2_pre_topc(X0,X2))
      | ~ v3_pre_topc(X1,X0)
      | ~ r1_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f58,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))
          & ~ r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK6)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
        & ~ r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK6)))
        & m1_subset_1(sK6,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
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

fof(f56,plain,
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

fof(f59,plain,
    ( k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK5)) != k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK6))
    & ~ r1_xboole_0(k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK5)),k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK6)))
    & m1_subset_1(sK6,u1_struct_0(sK4))
    & m1_subset_1(sK5,u1_struct_0(sK4))
    & l1_pre_topc(sK4)
    & v3_tdlat_3(sK4)
    & v2_pre_topc(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f41,f58,f57,f56])).

fof(f89,plain,(
    m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f59])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f98,plain,(
    ! [X0,X1] :
      ( k2_tarski(X1,X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f78,f69])).

fof(f85,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f59])).

fof(f88,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f59])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f74,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f73,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f90,plain,(
    m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f59])).

fof(f91,plain,(
    ~ r1_xboole_0(k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK5)),k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK6))) ),
    inference(cnf_transformation,[],[f59])).

fof(f86,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f59])).

fof(f87,plain,(
    v3_tdlat_3(sK4) ),
    inference(cnf_transformation,[],[f59])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f70,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f97,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f70,f69])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f11,axiom,(
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
    inference(ennf_transformation,[],[f11])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f77,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
             => v3_pre_topc(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f52,plain,(
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

fof(f53,plain,(
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
    inference(rectify,[],[f52])).

fof(f54,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_pre_topc(X1,X0)
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK3(X0),X0)
        & v4_pre_topc(sK3(X0),X0)
        & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f53,f54])).

fof(f79,plain,(
    ! [X2,X0] :
      ( v3_pre_topc(X2,X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f92,plain,(
    k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK5)) != k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK6)) ),
    inference(cnf_transformation,[],[f59])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f84,plain,(
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

cnf(c_3,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_879,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_4,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_878,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k2_tarski(X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f101])).

cnf(c_874,plain,
    ( X0 = X1
    | r2_hidden(X0,k2_tarski(X1,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2402,plain,
    ( sK1(k2_tarski(X0,X0),X1) = X0
    | r1_xboole_0(k2_tarski(X0,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_878,c_874])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_880,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_6630,plain,
    ( sK1(k2_tarski(X0,X0),X1) = X0
    | r2_hidden(X2,X1) != iProver_top
    | r2_hidden(X2,k2_tarski(X0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2402,c_880])).

cnf(c_7227,plain,
    ( sK1(k2_tarski(X0,X0),X1) = X0
    | r1_xboole_0(X2,k2_tarski(X0,X0)) = iProver_top
    | r2_hidden(sK1(X2,k2_tarski(X0,X0)),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_879,c_6630])).

cnf(c_16783,plain,
    ( sK1(k2_tarski(X0,X0),X1) = X0
    | r1_xboole_0(X1,k2_tarski(X0,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_878,c_7227])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_871,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_22,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_xboole_0(X0,X2)
    | r1_xboole_0(X0,k2_pre_topc(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_860,plain,
    ( v3_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_xboole_0(X0,X2) != iProver_top
    | r1_xboole_0(X0,k2_pre_topc(X1,X2)) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3673,plain,
    ( v3_pre_topc(k2_pre_topc(X0,X1),X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | r1_xboole_0(k2_pre_topc(X0,X1),X2) != iProver_top
    | r1_xboole_0(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_871,c_860])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_856,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_865,plain,
    ( k6_domain_1(X0,X1) = k2_tarski(X1,X1)
    | m1_subset_1(X1,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2581,plain,
    ( k6_domain_1(u1_struct_0(sK4),sK5) = k2_tarski(sK5,sK5)
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_856,c_865])).

cnf(c_31,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_28,negated_conjecture,
    ( l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_13,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_64,plain,
    ( v2_struct_0(sK4)
    | ~ l1_struct_0(sK4)
    | ~ v1_xboole_0(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_12,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_67,plain,
    ( l1_struct_0(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1230,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | v1_xboole_0(u1_struct_0(sK4))
    | k6_domain_1(u1_struct_0(sK4),sK5) = k2_tarski(sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_2961,plain,
    ( k6_domain_1(u1_struct_0(sK4),sK5) = k2_tarski(sK5,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2581,c_31,c_28,c_27,c_64,c_67,c_1230])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_857,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_2580,plain,
    ( k6_domain_1(u1_struct_0(sK4),sK6) = k2_tarski(sK6,sK6)
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_857,c_865])).

cnf(c_1227,plain,
    ( ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | v1_xboole_0(u1_struct_0(sK4))
    | k6_domain_1(u1_struct_0(sK4),sK6) = k2_tarski(sK6,sK6) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_2819,plain,
    ( k6_domain_1(u1_struct_0(sK4),sK6) = k2_tarski(sK6,sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2580,c_31,c_28,c_26,c_64,c_67,c_1227])).

cnf(c_25,negated_conjecture,
    ( ~ r1_xboole_0(k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK5)),k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK6))) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_858,plain,
    ( r1_xboole_0(k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK5)),k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK6))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2822,plain,
    ( r1_xboole_0(k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK5)),k2_pre_topc(sK4,k2_tarski(sK6,sK6))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2819,c_858])).

cnf(c_2964,plain,
    ( r1_xboole_0(k2_pre_topc(sK4,k2_tarski(sK5,sK5)),k2_pre_topc(sK4,k2_tarski(sK6,sK6))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2961,c_2822])).

cnf(c_27782,plain,
    ( v3_pre_topc(k2_pre_topc(sK4,k2_tarski(sK5,sK5)),sK4) != iProver_top
    | m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r1_xboole_0(k2_pre_topc(sK4,k2_tarski(sK5,sK5)),k2_tarski(sK6,sK6)) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3673,c_2964])).

cnf(c_32,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_30,negated_conjecture,
    ( v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_33,plain,
    ( v2_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_29,negated_conjecture,
    ( v3_tdlat_3(sK4) ),
    inference(cnf_transformation,[],[f87])).

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

cnf(c_63,plain,
    ( v2_struct_0(X0) = iProver_top
    | l1_struct_0(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_65,plain,
    ( v2_struct_0(sK4) = iProver_top
    | l1_struct_0(sK4) != iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_63])).

cnf(c_66,plain,
    ( l1_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_68,plain,
    ( l1_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_66])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1186,plain,
    ( ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | r2_hidden(sK6,u1_struct_0(sK4))
    | v1_xboole_0(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1187,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK6,u1_struct_0(sK4)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1186])).

cnf(c_1189,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | r2_hidden(sK5,u1_struct_0(sK4))
    | v1_xboole_0(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1190,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK5,u1_struct_0(sK4)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1189])).

cnf(c_9,plain,
    ( m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1357,plain,
    ( m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK6,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1358,plain,
    ( m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | r2_hidden(sK6,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1357])).

cnf(c_1403,plain,
    ( m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1404,plain,
    ( m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | r2_hidden(sK5,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1403])).

cnf(c_1679,plain,
    ( m1_subset_1(k2_pre_topc(sK4,k2_tarski(sK5,sK5)),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1680,plain,
    ( m1_subset_1(k2_pre_topc(sK4,k2_tarski(sK5,sK5)),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1679])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k2_pre_topc(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1678,plain,
    ( ~ m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_pre_topc(sK4)
    | k2_pre_topc(sK4,k2_pre_topc(sK4,k2_tarski(sK5,sK5))) = k2_pre_topc(sK4,k2_tarski(sK5,sK5)) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_15,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_2752,plain,
    ( v4_pre_topc(k2_pre_topc(sK4,k2_tarski(sK5,sK5)),sK4)
    | ~ m1_subset_1(k2_pre_topc(sK4,k2_tarski(sK5,sK5)),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK4)
    | k2_pre_topc(sK4,k2_pre_topc(sK4,k2_tarski(sK5,sK5))) != k2_pre_topc(sK4,k2_tarski(sK5,sK5)) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_2762,plain,
    ( k2_pre_topc(sK4,k2_pre_topc(sK4,k2_tarski(sK5,sK5))) != k2_pre_topc(sK4,k2_tarski(sK5,sK5))
    | v4_pre_topc(k2_pre_topc(sK4,k2_tarski(sK5,sK5)),sK4) = iProver_top
    | m1_subset_1(k2_pre_topc(sK4,k2_tarski(sK5,sK5)),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2752])).

cnf(c_21,plain,
    ( v3_pre_topc(X0,X1)
    | ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_2751,plain,
    ( v3_pre_topc(k2_pre_topc(sK4,k2_tarski(sK5,sK5)),sK4)
    | ~ v4_pre_topc(k2_pre_topc(sK4,k2_tarski(sK5,sK5)),sK4)
    | ~ m1_subset_1(k2_pre_topc(sK4,k2_tarski(sK5,sK5)),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v3_tdlat_3(sK4)
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_2764,plain,
    ( v3_pre_topc(k2_pre_topc(sK4,k2_tarski(sK5,sK5)),sK4) = iProver_top
    | v4_pre_topc(k2_pre_topc(sK4,k2_tarski(sK5,sK5)),sK4) != iProver_top
    | m1_subset_1(k2_pre_topc(sK4,k2_tarski(sK5,sK5)),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v3_tdlat_3(sK4) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2751])).

cnf(c_1657,plain,
    ( ~ v3_pre_topc(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK4)))
    | r1_xboole_0(X0,k2_pre_topc(sK4,k2_tarski(sK6,sK6)))
    | ~ r1_xboole_0(X0,k2_tarski(sK6,sK6))
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_6462,plain,
    ( ~ v3_pre_topc(k2_pre_topc(sK4,k2_tarski(sK5,sK5)),sK4)
    | ~ m1_subset_1(k2_pre_topc(sK4,k2_tarski(sK5,sK5)),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK4)))
    | r1_xboole_0(k2_pre_topc(sK4,k2_tarski(sK5,sK5)),k2_pre_topc(sK4,k2_tarski(sK6,sK6)))
    | ~ r1_xboole_0(k2_pre_topc(sK4,k2_tarski(sK5,sK5)),k2_tarski(sK6,sK6))
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_1657])).

cnf(c_6463,plain,
    ( v3_pre_topc(k2_pre_topc(sK4,k2_tarski(sK5,sK5)),sK4) != iProver_top
    | m1_subset_1(k2_pre_topc(sK4,k2_tarski(sK5,sK5)),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r1_xboole_0(k2_pre_topc(sK4,k2_tarski(sK5,sK5)),k2_pre_topc(sK4,k2_tarski(sK6,sK6))) = iProver_top
    | r1_xboole_0(k2_pre_topc(sK4,k2_tarski(sK5,sK5)),k2_tarski(sK6,sK6)) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6462])).

cnf(c_29433,plain,
    ( r1_xboole_0(k2_pre_topc(sK4,k2_tarski(sK5,sK5)),k2_tarski(sK6,sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_27782,c_31,c_32,c_33,c_34,c_28,c_35,c_27,c_36,c_37,c_64,c_65,c_67,c_68,c_1187,c_1189,c_1190,c_1358,c_1403,c_1404,c_1680,c_1678,c_2762,c_2764,c_2964,c_6463])).

cnf(c_29447,plain,
    ( sK1(k2_tarski(sK6,sK6),k2_pre_topc(sK4,k2_tarski(sK5,sK5))) = sK6 ),
    inference(superposition,[status(thm)],[c_16783,c_29433])).

cnf(c_37145,plain,
    ( r1_xboole_0(k2_tarski(sK6,sK6),k2_pre_topc(sK4,k2_tarski(sK5,sK5))) = iProver_top
    | r2_hidden(sK6,k2_pre_topc(sK4,k2_tarski(sK5,sK5))) = iProver_top ),
    inference(superposition,[status(thm)],[c_29447,c_879])).

cnf(c_24,negated_conjecture,
    ( k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK5)) != k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK6)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_2823,plain,
    ( k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK5)) != k2_pre_topc(sK4,k2_tarski(sK6,sK6)) ),
    inference(demodulation,[status(thm)],[c_2819,c_24])).

cnf(c_2965,plain,
    ( k2_pre_topc(sK4,k2_tarski(sK5,sK5)) != k2_pre_topc(sK4,k2_tarski(sK6,sK6)) ),
    inference(demodulation,[status(thm)],[c_2961,c_2823])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X0)))
    | ~ v3_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X0)) = k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_859,plain,
    ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | r2_hidden(X2,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))) != iProver_top
    | v3_tdlat_3(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2971,plain,
    ( k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),X0)) = k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK5))
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0,k2_pre_topc(sK4,k2_tarski(sK5,sK5))) != iProver_top
    | v3_tdlat_3(sK4) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2961,c_859])).

cnf(c_2972,plain,
    ( k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),X0)) = k2_pre_topc(sK4,k2_tarski(sK5,sK5))
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0,k2_pre_topc(sK4,k2_tarski(sK5,sK5))) != iProver_top
    | v3_tdlat_3(sK4) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2971,c_2961])).

cnf(c_3842,plain,
    ( m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),X0)) = k2_pre_topc(sK4,k2_tarski(sK5,sK5))
    | r2_hidden(X0,k2_pre_topc(sK4,k2_tarski(sK5,sK5))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2972,c_32,c_33,c_34,c_35,c_36])).

cnf(c_3843,plain,
    ( k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),X0)) = k2_pre_topc(sK4,k2_tarski(sK5,sK5))
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0,k2_pre_topc(sK4,k2_tarski(sK5,sK5))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3842])).

cnf(c_3852,plain,
    ( k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK1(X0,k2_pre_topc(sK4,k2_tarski(sK5,sK5))))) = k2_pre_topc(sK4,k2_tarski(sK5,sK5))
    | m1_subset_1(sK1(X0,k2_pre_topc(sK4,k2_tarski(sK5,sK5))),u1_struct_0(sK4)) != iProver_top
    | r1_xboole_0(X0,k2_pre_topc(sK4,k2_tarski(sK5,sK5))) = iProver_top ),
    inference(superposition,[status(thm)],[c_879,c_3843])).

cnf(c_37149,plain,
    ( k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK1(k2_tarski(sK6,sK6),k2_pre_topc(sK4,k2_tarski(sK5,sK5))))) = k2_pre_topc(sK4,k2_tarski(sK5,sK5))
    | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top
    | r1_xboole_0(k2_tarski(sK6,sK6),k2_pre_topc(sK4,k2_tarski(sK5,sK5))) = iProver_top ),
    inference(superposition,[status(thm)],[c_29447,c_3852])).

cnf(c_37160,plain,
    ( k2_pre_topc(sK4,k2_tarski(sK5,sK5)) = k2_pre_topc(sK4,k2_tarski(sK6,sK6))
    | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top
    | r1_xboole_0(k2_tarski(sK6,sK6),k2_pre_topc(sK4,k2_tarski(sK5,sK5))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_37149,c_2819,c_29447])).

cnf(c_37391,plain,
    ( r1_xboole_0(k2_tarski(sK6,sK6),k2_pre_topc(sK4,k2_tarski(sK5,sK5))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_37145,c_37,c_2965,c_37160])).

cnf(c_37400,plain,
    ( r2_hidden(X0,k2_pre_topc(sK4,k2_tarski(sK5,sK5))) != iProver_top
    | r2_hidden(X0,k2_tarski(sK6,sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_37391,c_880])).

cnf(c_37654,plain,
    ( r1_xboole_0(k2_pre_topc(sK4,k2_tarski(sK5,sK5)),X0) = iProver_top
    | r2_hidden(sK1(k2_pre_topc(sK4,k2_tarski(sK5,sK5)),X0),k2_tarski(sK6,sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_878,c_37400])).

cnf(c_39308,plain,
    ( r1_xboole_0(k2_pre_topc(sK4,k2_tarski(sK5,sK5)),k2_tarski(sK6,sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_879,c_37654])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_39308,c_6463,c_2964,c_2764,c_2762,c_1678,c_1680,c_1404,c_1403,c_1358,c_1190,c_1189,c_1187,c_68,c_67,c_65,c_64,c_37,c_36,c_27,c_35,c_28,c_34,c_33,c_32,c_31])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:26:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 11.65/2.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.65/2.00  
% 11.65/2.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.65/2.00  
% 11.65/2.00  ------  iProver source info
% 11.65/2.00  
% 11.65/2.00  git: date: 2020-06-30 10:37:57 +0100
% 11.65/2.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.65/2.00  git: non_committed_changes: false
% 11.65/2.00  git: last_make_outside_of_git: false
% 11.65/2.00  
% 11.65/2.00  ------ 
% 11.65/2.00  ------ Parsing...
% 11.65/2.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.65/2.00  
% 11.65/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 11.65/2.00  
% 11.65/2.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.65/2.00  
% 11.65/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.65/2.00  ------ Proving...
% 11.65/2.00  ------ Problem Properties 
% 11.65/2.00  
% 11.65/2.00  
% 11.65/2.00  clauses                                 32
% 11.65/2.00  conjectures                             8
% 11.65/2.00  EPR                                     8
% 11.65/2.00  Horn                                    23
% 11.65/2.00  unary                                   9
% 11.65/2.00  binary                                  7
% 11.65/2.00  lits                                    89
% 11.65/2.00  lits eq                                 11
% 11.65/2.00  fd_pure                                 0
% 11.65/2.00  fd_pseudo                               0
% 11.65/2.00  fd_cond                                 0
% 11.65/2.00  fd_pseudo_cond                          2
% 11.65/2.00  AC symbols                              0
% 11.65/2.00  
% 11.65/2.00  ------ Input Options Time Limit: Unbounded
% 11.65/2.00  
% 11.65/2.00  
% 11.65/2.00  ------ 
% 11.65/2.00  Current options:
% 11.65/2.00  ------ 
% 11.65/2.00  
% 11.65/2.00  
% 11.65/2.00  
% 11.65/2.00  
% 11.65/2.00  ------ Proving...
% 11.65/2.00  
% 11.65/2.00  
% 11.65/2.00  % SZS status Theorem for theBenchmark.p
% 11.65/2.00  
% 11.65/2.00  % SZS output start CNFRefutation for theBenchmark.p
% 11.65/2.00  
% 11.65/2.00  fof(f2,axiom,(
% 11.65/2.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 11.65/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.65/2.00  
% 11.65/2.00  fof(f18,plain,(
% 11.65/2.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 11.65/2.00    inference(rectify,[],[f2])).
% 11.65/2.00  
% 11.65/2.00  fof(f19,plain,(
% 11.65/2.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 11.65/2.00    inference(ennf_transformation,[],[f18])).
% 11.65/2.00  
% 11.65/2.00  fof(f46,plain,(
% 11.65/2.00    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 11.65/2.00    introduced(choice_axiom,[])).
% 11.65/2.00  
% 11.65/2.00  fof(f47,plain,(
% 11.65/2.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 11.65/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f46])).
% 11.65/2.00  
% 11.65/2.00  fof(f63,plain,(
% 11.65/2.00    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 11.65/2.00    inference(cnf_transformation,[],[f47])).
% 11.65/2.00  
% 11.65/2.00  fof(f62,plain,(
% 11.65/2.00    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 11.65/2.00    inference(cnf_transformation,[],[f47])).
% 11.65/2.00  
% 11.65/2.00  fof(f3,axiom,(
% 11.65/2.00    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 11.65/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.65/2.00  
% 11.65/2.00  fof(f48,plain,(
% 11.65/2.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 11.65/2.00    inference(nnf_transformation,[],[f3])).
% 11.65/2.00  
% 11.65/2.00  fof(f49,plain,(
% 11.65/2.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 11.65/2.00    inference(rectify,[],[f48])).
% 11.65/2.00  
% 11.65/2.00  fof(f50,plain,(
% 11.65/2.00    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 11.65/2.00    introduced(choice_axiom,[])).
% 11.65/2.00  
% 11.65/2.00  fof(f51,plain,(
% 11.65/2.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 11.65/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f49,f50])).
% 11.65/2.00  
% 11.65/2.00  fof(f65,plain,(
% 11.65/2.00    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 11.65/2.00    inference(cnf_transformation,[],[f51])).
% 11.65/2.00  
% 11.65/2.00  fof(f4,axiom,(
% 11.65/2.00    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 11.65/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.65/2.00  
% 11.65/2.00  fof(f69,plain,(
% 11.65/2.00    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 11.65/2.00    inference(cnf_transformation,[],[f4])).
% 11.65/2.00  
% 11.65/2.00  fof(f96,plain,(
% 11.65/2.00    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_tarski(X0,X0) != X1) )),
% 11.65/2.00    inference(definition_unfolding,[],[f65,f69])).
% 11.65/2.00  
% 11.65/2.00  fof(f101,plain,(
% 11.65/2.00    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k2_tarski(X0,X0))) )),
% 11.65/2.00    inference(equality_resolution,[],[f96])).
% 11.65/2.00  
% 11.65/2.00  fof(f64,plain,(
% 11.65/2.00    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 11.65/2.00    inference(cnf_transformation,[],[f47])).
% 11.65/2.00  
% 11.65/2.00  fof(f7,axiom,(
% 11.65/2.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 11.65/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.65/2.00  
% 11.65/2.00  fof(f23,plain,(
% 11.65/2.00    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 11.65/2.00    inference(ennf_transformation,[],[f7])).
% 11.65/2.00  
% 11.65/2.00  fof(f24,plain,(
% 11.65/2.00    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 11.65/2.00    inference(flattening,[],[f23])).
% 11.65/2.00  
% 11.65/2.00  fof(f72,plain,(
% 11.65/2.00    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.65/2.00    inference(cnf_transformation,[],[f24])).
% 11.65/2.00  
% 11.65/2.00  fof(f14,axiom,(
% 11.65/2.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X1,X0) & r1_xboole_0(X1,X2)) => r1_xboole_0(X1,k2_pre_topc(X0,X2))))))),
% 11.65/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.65/2.00  
% 11.65/2.00  fof(f36,plain,(
% 11.65/2.00    ! [X0] : (! [X1] : (! [X2] : ((r1_xboole_0(X1,k2_pre_topc(X0,X2)) | (~v3_pre_topc(X1,X0) | ~r1_xboole_0(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 11.65/2.00    inference(ennf_transformation,[],[f14])).
% 11.65/2.00  
% 11.65/2.00  fof(f37,plain,(
% 11.65/2.00    ! [X0] : (! [X1] : (! [X2] : (r1_xboole_0(X1,k2_pre_topc(X0,X2)) | ~v3_pre_topc(X1,X0) | ~r1_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 11.65/2.00    inference(flattening,[],[f36])).
% 11.65/2.00  
% 11.65/2.00  fof(f83,plain,(
% 11.65/2.00    ( ! [X2,X0,X1] : (r1_xboole_0(X1,k2_pre_topc(X0,X2)) | ~v3_pre_topc(X1,X0) | ~r1_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 11.65/2.00    inference(cnf_transformation,[],[f37])).
% 11.65/2.00  
% 11.65/2.00  fof(f16,conjecture,(
% 11.65/2.00    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) | r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))))))),
% 11.65/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.65/2.00  
% 11.65/2.00  fof(f17,negated_conjecture,(
% 11.65/2.00    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) | r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))))))),
% 11.65/2.00    inference(negated_conjecture,[],[f16])).
% 11.65/2.00  
% 11.65/2.00  fof(f40,plain,(
% 11.65/2.00    ? [X0] : (? [X1] : (? [X2] : ((k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 11.65/2.00    inference(ennf_transformation,[],[f17])).
% 11.65/2.00  
% 11.65/2.00  fof(f41,plain,(
% 11.65/2.00    ? [X0] : (? [X1] : (? [X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 11.65/2.00    inference(flattening,[],[f40])).
% 11.65/2.00  
% 11.65/2.00  fof(f58,plain,(
% 11.65/2.00    ( ! [X0,X1] : (? [X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & m1_subset_1(X2,u1_struct_0(X0))) => (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK6)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK6))) & m1_subset_1(sK6,u1_struct_0(X0)))) )),
% 11.65/2.00    introduced(choice_axiom,[])).
% 11.65/2.00  
% 11.65/2.00  fof(f57,plain,(
% 11.65/2.00    ( ! [X0] : (? [X1] : (? [X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK5)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK5)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK5,u1_struct_0(X0)))) )),
% 11.65/2.00    introduced(choice_axiom,[])).
% 11.65/2.00  
% 11.65/2.00  fof(f56,plain,(
% 11.65/2.00    ? [X0] : (? [X1] : (? [X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),X1)) != k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),X2)) & ~r1_xboole_0(k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),X1)),k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),X2))) & m1_subset_1(X2,u1_struct_0(sK4))) & m1_subset_1(X1,u1_struct_0(sK4))) & l1_pre_topc(sK4) & v3_tdlat_3(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4))),
% 11.65/2.00    introduced(choice_axiom,[])).
% 11.65/2.00  
% 11.65/2.00  fof(f59,plain,(
% 11.65/2.00    ((k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK5)) != k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK6)) & ~r1_xboole_0(k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK5)),k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK6))) & m1_subset_1(sK6,u1_struct_0(sK4))) & m1_subset_1(sK5,u1_struct_0(sK4))) & l1_pre_topc(sK4) & v3_tdlat_3(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4)),
% 11.65/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f41,f58,f57,f56])).
% 11.65/2.00  
% 11.65/2.00  fof(f89,plain,(
% 11.65/2.00    m1_subset_1(sK5,u1_struct_0(sK4))),
% 11.65/2.00    inference(cnf_transformation,[],[f59])).
% 11.65/2.00  
% 11.65/2.00  fof(f12,axiom,(
% 11.65/2.00    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 11.65/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.65/2.00  
% 11.65/2.00  fof(f32,plain,(
% 11.65/2.00    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 11.65/2.00    inference(ennf_transformation,[],[f12])).
% 11.65/2.00  
% 11.65/2.00  fof(f33,plain,(
% 11.65/2.00    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 11.65/2.00    inference(flattening,[],[f32])).
% 11.65/2.00  
% 11.65/2.00  fof(f78,plain,(
% 11.65/2.00    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 11.65/2.00    inference(cnf_transformation,[],[f33])).
% 11.65/2.00  
% 11.65/2.00  fof(f98,plain,(
% 11.65/2.00    ( ! [X0,X1] : (k2_tarski(X1,X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 11.65/2.00    inference(definition_unfolding,[],[f78,f69])).
% 11.65/2.00  
% 11.65/2.00  fof(f85,plain,(
% 11.65/2.00    ~v2_struct_0(sK4)),
% 11.65/2.00    inference(cnf_transformation,[],[f59])).
% 11.65/2.00  
% 11.65/2.00  fof(f88,plain,(
% 11.65/2.00    l1_pre_topc(sK4)),
% 11.65/2.00    inference(cnf_transformation,[],[f59])).
% 11.65/2.00  
% 11.65/2.00  fof(f9,axiom,(
% 11.65/2.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 11.65/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.65/2.00  
% 11.65/2.00  fof(f26,plain,(
% 11.65/2.00    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 11.65/2.00    inference(ennf_transformation,[],[f9])).
% 11.65/2.00  
% 11.65/2.00  fof(f27,plain,(
% 11.65/2.00    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 11.65/2.00    inference(flattening,[],[f26])).
% 11.65/2.00  
% 11.65/2.00  fof(f74,plain,(
% 11.65/2.00    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 11.65/2.00    inference(cnf_transformation,[],[f27])).
% 11.65/2.00  
% 11.65/2.00  fof(f8,axiom,(
% 11.65/2.00    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 11.65/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.65/2.00  
% 11.65/2.00  fof(f25,plain,(
% 11.65/2.00    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 11.65/2.00    inference(ennf_transformation,[],[f8])).
% 11.65/2.00  
% 11.65/2.00  fof(f73,plain,(
% 11.65/2.00    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 11.65/2.00    inference(cnf_transformation,[],[f25])).
% 11.65/2.00  
% 11.65/2.00  fof(f90,plain,(
% 11.65/2.00    m1_subset_1(sK6,u1_struct_0(sK4))),
% 11.65/2.00    inference(cnf_transformation,[],[f59])).
% 11.65/2.00  
% 11.65/2.00  fof(f91,plain,(
% 11.65/2.00    ~r1_xboole_0(k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK5)),k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK6)))),
% 11.65/2.00    inference(cnf_transformation,[],[f59])).
% 11.65/2.00  
% 11.65/2.00  fof(f86,plain,(
% 11.65/2.00    v2_pre_topc(sK4)),
% 11.65/2.00    inference(cnf_transformation,[],[f59])).
% 11.65/2.00  
% 11.65/2.00  fof(f87,plain,(
% 11.65/2.00    v3_tdlat_3(sK4)),
% 11.65/2.00    inference(cnf_transformation,[],[f59])).
% 11.65/2.00  
% 11.65/2.00  fof(f6,axiom,(
% 11.65/2.00    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 11.65/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.65/2.00  
% 11.65/2.00  fof(f21,plain,(
% 11.65/2.00    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 11.65/2.00    inference(ennf_transformation,[],[f6])).
% 11.65/2.00  
% 11.65/2.00  fof(f22,plain,(
% 11.65/2.00    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 11.65/2.00    inference(flattening,[],[f21])).
% 11.65/2.00  
% 11.65/2.00  fof(f71,plain,(
% 11.65/2.00    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 11.65/2.00    inference(cnf_transformation,[],[f22])).
% 11.65/2.00  
% 11.65/2.00  fof(f5,axiom,(
% 11.65/2.00    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 11.65/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.65/2.00  
% 11.65/2.00  fof(f20,plain,(
% 11.65/2.00    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 11.65/2.00    inference(ennf_transformation,[],[f5])).
% 11.65/2.00  
% 11.65/2.00  fof(f70,plain,(
% 11.65/2.00    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 11.65/2.00    inference(cnf_transformation,[],[f20])).
% 11.65/2.00  
% 11.65/2.00  fof(f97,plain,(
% 11.65/2.00    ( ! [X0,X1] : (m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 11.65/2.00    inference(definition_unfolding,[],[f70,f69])).
% 11.65/2.00  
% 11.65/2.00  fof(f10,axiom,(
% 11.65/2.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)))),
% 11.65/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.65/2.00  
% 11.65/2.00  fof(f28,plain,(
% 11.65/2.00    ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 11.65/2.00    inference(ennf_transformation,[],[f10])).
% 11.65/2.00  
% 11.65/2.00  fof(f29,plain,(
% 11.65/2.00    ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 11.65/2.00    inference(flattening,[],[f28])).
% 11.65/2.00  
% 11.65/2.00  fof(f75,plain,(
% 11.65/2.00    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.65/2.00    inference(cnf_transformation,[],[f29])).
% 11.65/2.00  
% 11.65/2.00  fof(f11,axiom,(
% 11.65/2.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 11.65/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.65/2.00  
% 11.65/2.00  fof(f30,plain,(
% 11.65/2.00    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.65/2.00    inference(ennf_transformation,[],[f11])).
% 11.65/2.00  
% 11.65/2.00  fof(f31,plain,(
% 11.65/2.00    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.65/2.00    inference(flattening,[],[f30])).
% 11.65/2.00  
% 11.65/2.00  fof(f77,plain,(
% 11.65/2.00    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.65/2.00    inference(cnf_transformation,[],[f31])).
% 11.65/2.00  
% 11.65/2.00  fof(f13,axiom,(
% 11.65/2.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v3_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => v3_pre_topc(X1,X0)))))),
% 11.65/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.65/2.00  
% 11.65/2.00  fof(f34,plain,(
% 11.65/2.00    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : ((v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 11.65/2.00    inference(ennf_transformation,[],[f13])).
% 11.65/2.00  
% 11.65/2.00  fof(f35,plain,(
% 11.65/2.00    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 11.65/2.00    inference(flattening,[],[f34])).
% 11.65/2.00  
% 11.65/2.00  fof(f52,plain,(
% 11.65/2.00    ! [X0] : (((v3_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X1] : (v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 11.65/2.00    inference(nnf_transformation,[],[f35])).
% 11.65/2.00  
% 11.65/2.00  fof(f53,plain,(
% 11.65/2.00    ! [X0] : (((v3_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 11.65/2.00    inference(rectify,[],[f52])).
% 11.65/2.00  
% 11.65/2.00  fof(f54,plain,(
% 11.65/2.00    ! [X0] : (? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK3(X0),X0) & v4_pre_topc(sK3(X0),X0) & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 11.65/2.00    introduced(choice_axiom,[])).
% 11.65/2.00  
% 11.65/2.00  fof(f55,plain,(
% 11.65/2.00    ! [X0] : (((v3_tdlat_3(X0) | (~v3_pre_topc(sK3(X0),X0) & v4_pre_topc(sK3(X0),X0) & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 11.65/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f53,f54])).
% 11.65/2.00  
% 11.65/2.00  fof(f79,plain,(
% 11.65/2.00    ( ! [X2,X0] : (v3_pre_topc(X2,X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tdlat_3(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 11.65/2.00    inference(cnf_transformation,[],[f55])).
% 11.65/2.00  
% 11.65/2.00  fof(f92,plain,(
% 11.65/2.00    k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK5)) != k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK6))),
% 11.65/2.00    inference(cnf_transformation,[],[f59])).
% 11.65/2.00  
% 11.65/2.00  fof(f15,axiom,(
% 11.65/2.00    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) => k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))))))),
% 11.65/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.65/2.00  
% 11.65/2.00  fof(f38,plain,(
% 11.65/2.00    ! [X0] : (! [X1] : (! [X2] : ((k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) | ~r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 11.65/2.00    inference(ennf_transformation,[],[f15])).
% 11.65/2.00  
% 11.65/2.00  fof(f39,plain,(
% 11.65/2.00    ! [X0] : (! [X1] : (! [X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) | ~r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.65/2.00    inference(flattening,[],[f38])).
% 11.65/2.00  
% 11.65/2.00  fof(f84,plain,(
% 11.65/2.00    ( ! [X2,X0,X1] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) | ~r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.65/2.00    inference(cnf_transformation,[],[f39])).
% 11.65/2.00  
% 11.65/2.00  cnf(c_3,plain,
% 11.65/2.00      ( r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X1) ),
% 11.65/2.00      inference(cnf_transformation,[],[f63]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_879,plain,
% 11.65/2.00      ( r1_xboole_0(X0,X1) = iProver_top
% 11.65/2.00      | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
% 11.65/2.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_4,plain,
% 11.65/2.00      ( r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 11.65/2.00      inference(cnf_transformation,[],[f62]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_878,plain,
% 11.65/2.00      ( r1_xboole_0(X0,X1) = iProver_top
% 11.65/2.00      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 11.65/2.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_8,plain,
% 11.65/2.00      ( ~ r2_hidden(X0,k2_tarski(X1,X1)) | X0 = X1 ),
% 11.65/2.00      inference(cnf_transformation,[],[f101]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_874,plain,
% 11.65/2.00      ( X0 = X1 | r2_hidden(X0,k2_tarski(X1,X1)) != iProver_top ),
% 11.65/2.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_2402,plain,
% 11.65/2.00      ( sK1(k2_tarski(X0,X0),X1) = X0
% 11.65/2.00      | r1_xboole_0(k2_tarski(X0,X0),X1) = iProver_top ),
% 11.65/2.00      inference(superposition,[status(thm)],[c_878,c_874]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_2,plain,
% 11.65/2.00      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,X0) | ~ r2_hidden(X2,X1) ),
% 11.65/2.00      inference(cnf_transformation,[],[f64]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_880,plain,
% 11.65/2.00      ( r1_xboole_0(X0,X1) != iProver_top
% 11.65/2.00      | r2_hidden(X2,X0) != iProver_top
% 11.65/2.00      | r2_hidden(X2,X1) != iProver_top ),
% 11.65/2.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_6630,plain,
% 11.65/2.00      ( sK1(k2_tarski(X0,X0),X1) = X0
% 11.65/2.00      | r2_hidden(X2,X1) != iProver_top
% 11.65/2.00      | r2_hidden(X2,k2_tarski(X0,X0)) != iProver_top ),
% 11.65/2.00      inference(superposition,[status(thm)],[c_2402,c_880]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_7227,plain,
% 11.65/2.00      ( sK1(k2_tarski(X0,X0),X1) = X0
% 11.65/2.00      | r1_xboole_0(X2,k2_tarski(X0,X0)) = iProver_top
% 11.65/2.00      | r2_hidden(sK1(X2,k2_tarski(X0,X0)),X1) != iProver_top ),
% 11.65/2.00      inference(superposition,[status(thm)],[c_879,c_6630]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_16783,plain,
% 11.65/2.00      ( sK1(k2_tarski(X0,X0),X1) = X0
% 11.65/2.00      | r1_xboole_0(X1,k2_tarski(X0,X0)) = iProver_top ),
% 11.65/2.00      inference(superposition,[status(thm)],[c_878,c_7227]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_11,plain,
% 11.65/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.65/2.00      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 11.65/2.00      | ~ l1_pre_topc(X1) ),
% 11.65/2.00      inference(cnf_transformation,[],[f72]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_871,plain,
% 11.65/2.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 11.65/2.00      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 11.65/2.00      | l1_pre_topc(X1) != iProver_top ),
% 11.65/2.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_22,plain,
% 11.65/2.00      ( ~ v3_pre_topc(X0,X1)
% 11.65/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.65/2.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 11.65/2.00      | ~ r1_xboole_0(X0,X2)
% 11.65/2.00      | r1_xboole_0(X0,k2_pre_topc(X1,X2))
% 11.65/2.00      | ~ v2_pre_topc(X1)
% 11.65/2.00      | ~ l1_pre_topc(X1) ),
% 11.65/2.00      inference(cnf_transformation,[],[f83]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_860,plain,
% 11.65/2.00      ( v3_pre_topc(X0,X1) != iProver_top
% 11.65/2.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 11.65/2.00      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 11.65/2.00      | r1_xboole_0(X0,X2) != iProver_top
% 11.65/2.00      | r1_xboole_0(X0,k2_pre_topc(X1,X2)) = iProver_top
% 11.65/2.00      | v2_pre_topc(X1) != iProver_top
% 11.65/2.00      | l1_pre_topc(X1) != iProver_top ),
% 11.65/2.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_3673,plain,
% 11.65/2.00      ( v3_pre_topc(k2_pre_topc(X0,X1),X0) != iProver_top
% 11.65/2.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 11.65/2.00      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 11.65/2.00      | r1_xboole_0(k2_pre_topc(X0,X1),X2) != iProver_top
% 11.65/2.00      | r1_xboole_0(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) = iProver_top
% 11.65/2.00      | v2_pre_topc(X0) != iProver_top
% 11.65/2.00      | l1_pre_topc(X0) != iProver_top ),
% 11.65/2.00      inference(superposition,[status(thm)],[c_871,c_860]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_27,negated_conjecture,
% 11.65/2.00      ( m1_subset_1(sK5,u1_struct_0(sK4)) ),
% 11.65/2.00      inference(cnf_transformation,[],[f89]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_856,plain,
% 11.65/2.00      ( m1_subset_1(sK5,u1_struct_0(sK4)) = iProver_top ),
% 11.65/2.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_17,plain,
% 11.65/2.00      ( ~ m1_subset_1(X0,X1)
% 11.65/2.00      | v1_xboole_0(X1)
% 11.65/2.00      | k6_domain_1(X1,X0) = k2_tarski(X0,X0) ),
% 11.65/2.00      inference(cnf_transformation,[],[f98]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_865,plain,
% 11.65/2.00      ( k6_domain_1(X0,X1) = k2_tarski(X1,X1)
% 11.65/2.00      | m1_subset_1(X1,X0) != iProver_top
% 11.65/2.00      | v1_xboole_0(X0) = iProver_top ),
% 11.65/2.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_2581,plain,
% 11.65/2.00      ( k6_domain_1(u1_struct_0(sK4),sK5) = k2_tarski(sK5,sK5)
% 11.65/2.00      | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
% 11.65/2.00      inference(superposition,[status(thm)],[c_856,c_865]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_31,negated_conjecture,
% 11.65/2.00      ( ~ v2_struct_0(sK4) ),
% 11.65/2.00      inference(cnf_transformation,[],[f85]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_28,negated_conjecture,
% 11.65/2.00      ( l1_pre_topc(sK4) ),
% 11.65/2.00      inference(cnf_transformation,[],[f88]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_13,plain,
% 11.65/2.00      ( v2_struct_0(X0)
% 11.65/2.00      | ~ l1_struct_0(X0)
% 11.65/2.00      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 11.65/2.00      inference(cnf_transformation,[],[f74]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_64,plain,
% 11.65/2.00      ( v2_struct_0(sK4)
% 11.65/2.00      | ~ l1_struct_0(sK4)
% 11.65/2.00      | ~ v1_xboole_0(u1_struct_0(sK4)) ),
% 11.65/2.00      inference(instantiation,[status(thm)],[c_13]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_12,plain,
% 11.65/2.00      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 11.65/2.00      inference(cnf_transformation,[],[f73]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_67,plain,
% 11.65/2.00      ( l1_struct_0(sK4) | ~ l1_pre_topc(sK4) ),
% 11.65/2.00      inference(instantiation,[status(thm)],[c_12]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_1230,plain,
% 11.65/2.00      ( ~ m1_subset_1(sK5,u1_struct_0(sK4))
% 11.65/2.00      | v1_xboole_0(u1_struct_0(sK4))
% 11.65/2.00      | k6_domain_1(u1_struct_0(sK4),sK5) = k2_tarski(sK5,sK5) ),
% 11.65/2.00      inference(instantiation,[status(thm)],[c_17]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_2961,plain,
% 11.65/2.00      ( k6_domain_1(u1_struct_0(sK4),sK5) = k2_tarski(sK5,sK5) ),
% 11.65/2.00      inference(global_propositional_subsumption,
% 11.65/2.00                [status(thm)],
% 11.65/2.00                [c_2581,c_31,c_28,c_27,c_64,c_67,c_1230]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_26,negated_conjecture,
% 11.65/2.00      ( m1_subset_1(sK6,u1_struct_0(sK4)) ),
% 11.65/2.00      inference(cnf_transformation,[],[f90]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_857,plain,
% 11.65/2.00      ( m1_subset_1(sK6,u1_struct_0(sK4)) = iProver_top ),
% 11.65/2.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_2580,plain,
% 11.65/2.00      ( k6_domain_1(u1_struct_0(sK4),sK6) = k2_tarski(sK6,sK6)
% 11.65/2.00      | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
% 11.65/2.00      inference(superposition,[status(thm)],[c_857,c_865]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_1227,plain,
% 11.65/2.00      ( ~ m1_subset_1(sK6,u1_struct_0(sK4))
% 11.65/2.00      | v1_xboole_0(u1_struct_0(sK4))
% 11.65/2.00      | k6_domain_1(u1_struct_0(sK4),sK6) = k2_tarski(sK6,sK6) ),
% 11.65/2.00      inference(instantiation,[status(thm)],[c_17]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_2819,plain,
% 11.65/2.00      ( k6_domain_1(u1_struct_0(sK4),sK6) = k2_tarski(sK6,sK6) ),
% 11.65/2.00      inference(global_propositional_subsumption,
% 11.65/2.00                [status(thm)],
% 11.65/2.00                [c_2580,c_31,c_28,c_26,c_64,c_67,c_1227]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_25,negated_conjecture,
% 11.65/2.00      ( ~ r1_xboole_0(k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK5)),k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK6))) ),
% 11.65/2.00      inference(cnf_transformation,[],[f91]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_858,plain,
% 11.65/2.00      ( r1_xboole_0(k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK5)),k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK6))) != iProver_top ),
% 11.65/2.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_2822,plain,
% 11.65/2.00      ( r1_xboole_0(k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK5)),k2_pre_topc(sK4,k2_tarski(sK6,sK6))) != iProver_top ),
% 11.65/2.00      inference(demodulation,[status(thm)],[c_2819,c_858]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_2964,plain,
% 11.65/2.00      ( r1_xboole_0(k2_pre_topc(sK4,k2_tarski(sK5,sK5)),k2_pre_topc(sK4,k2_tarski(sK6,sK6))) != iProver_top ),
% 11.65/2.00      inference(demodulation,[status(thm)],[c_2961,c_2822]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_27782,plain,
% 11.65/2.00      ( v3_pre_topc(k2_pre_topc(sK4,k2_tarski(sK5,sK5)),sK4) != iProver_top
% 11.65/2.00      | m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 11.65/2.00      | m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 11.65/2.00      | r1_xboole_0(k2_pre_topc(sK4,k2_tarski(sK5,sK5)),k2_tarski(sK6,sK6)) != iProver_top
% 11.65/2.00      | v2_pre_topc(sK4) != iProver_top
% 11.65/2.00      | l1_pre_topc(sK4) != iProver_top ),
% 11.65/2.00      inference(superposition,[status(thm)],[c_3673,c_2964]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_32,plain,
% 11.65/2.00      ( v2_struct_0(sK4) != iProver_top ),
% 11.65/2.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_30,negated_conjecture,
% 11.65/2.00      ( v2_pre_topc(sK4) ),
% 11.65/2.00      inference(cnf_transformation,[],[f86]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_33,plain,
% 11.65/2.00      ( v2_pre_topc(sK4) = iProver_top ),
% 11.65/2.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_29,negated_conjecture,
% 11.65/2.00      ( v3_tdlat_3(sK4) ),
% 11.65/2.00      inference(cnf_transformation,[],[f87]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_34,plain,
% 11.65/2.00      ( v3_tdlat_3(sK4) = iProver_top ),
% 11.65/2.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_35,plain,
% 11.65/2.00      ( l1_pre_topc(sK4) = iProver_top ),
% 11.65/2.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_36,plain,
% 11.65/2.00      ( m1_subset_1(sK5,u1_struct_0(sK4)) = iProver_top ),
% 11.65/2.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_37,plain,
% 11.65/2.00      ( m1_subset_1(sK6,u1_struct_0(sK4)) = iProver_top ),
% 11.65/2.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_63,plain,
% 11.65/2.00      ( v2_struct_0(X0) = iProver_top
% 11.65/2.00      | l1_struct_0(X0) != iProver_top
% 11.65/2.00      | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
% 11.65/2.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_65,plain,
% 11.65/2.00      ( v2_struct_0(sK4) = iProver_top
% 11.65/2.00      | l1_struct_0(sK4) != iProver_top
% 11.65/2.00      | v1_xboole_0(u1_struct_0(sK4)) != iProver_top ),
% 11.65/2.00      inference(instantiation,[status(thm)],[c_63]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_66,plain,
% 11.65/2.00      ( l1_struct_0(X0) = iProver_top | l1_pre_topc(X0) != iProver_top ),
% 11.65/2.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_68,plain,
% 11.65/2.00      ( l1_struct_0(sK4) = iProver_top
% 11.65/2.00      | l1_pre_topc(sK4) != iProver_top ),
% 11.65/2.00      inference(instantiation,[status(thm)],[c_66]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_10,plain,
% 11.65/2.00      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 11.65/2.00      inference(cnf_transformation,[],[f71]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_1186,plain,
% 11.65/2.00      ( ~ m1_subset_1(sK6,u1_struct_0(sK4))
% 11.65/2.00      | r2_hidden(sK6,u1_struct_0(sK4))
% 11.65/2.00      | v1_xboole_0(u1_struct_0(sK4)) ),
% 11.65/2.00      inference(instantiation,[status(thm)],[c_10]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_1187,plain,
% 11.65/2.00      ( m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top
% 11.65/2.00      | r2_hidden(sK6,u1_struct_0(sK4)) = iProver_top
% 11.65/2.00      | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
% 11.65/2.00      inference(predicate_to_equality,[status(thm)],[c_1186]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_1189,plain,
% 11.65/2.00      ( ~ m1_subset_1(sK5,u1_struct_0(sK4))
% 11.65/2.00      | r2_hidden(sK5,u1_struct_0(sK4))
% 11.65/2.00      | v1_xboole_0(u1_struct_0(sK4)) ),
% 11.65/2.00      inference(instantiation,[status(thm)],[c_10]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_1190,plain,
% 11.65/2.00      ( m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
% 11.65/2.00      | r2_hidden(sK5,u1_struct_0(sK4)) = iProver_top
% 11.65/2.00      | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
% 11.65/2.00      inference(predicate_to_equality,[status(thm)],[c_1189]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_9,plain,
% 11.65/2.00      ( m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1))
% 11.65/2.00      | ~ r2_hidden(X0,X1) ),
% 11.65/2.00      inference(cnf_transformation,[],[f97]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_1357,plain,
% 11.65/2.00      ( m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK4)))
% 11.65/2.00      | ~ r2_hidden(sK6,u1_struct_0(sK4)) ),
% 11.65/2.00      inference(instantiation,[status(thm)],[c_9]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_1358,plain,
% 11.65/2.00      ( m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
% 11.65/2.00      | r2_hidden(sK6,u1_struct_0(sK4)) != iProver_top ),
% 11.65/2.00      inference(predicate_to_equality,[status(thm)],[c_1357]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_1403,plain,
% 11.65/2.00      ( m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK4)))
% 11.65/2.00      | ~ r2_hidden(sK5,u1_struct_0(sK4)) ),
% 11.65/2.00      inference(instantiation,[status(thm)],[c_9]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_1404,plain,
% 11.65/2.00      ( m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
% 11.65/2.00      | r2_hidden(sK5,u1_struct_0(sK4)) != iProver_top ),
% 11.65/2.00      inference(predicate_to_equality,[status(thm)],[c_1403]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_1679,plain,
% 11.65/2.00      ( m1_subset_1(k2_pre_topc(sK4,k2_tarski(sK5,sK5)),k1_zfmisc_1(u1_struct_0(sK4)))
% 11.65/2.00      | ~ m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK4)))
% 11.65/2.00      | ~ l1_pre_topc(sK4) ),
% 11.65/2.00      inference(instantiation,[status(thm)],[c_11]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_1680,plain,
% 11.65/2.00      ( m1_subset_1(k2_pre_topc(sK4,k2_tarski(sK5,sK5)),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
% 11.65/2.00      | m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 11.65/2.00      | l1_pre_topc(sK4) != iProver_top ),
% 11.65/2.00      inference(predicate_to_equality,[status(thm)],[c_1679]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_14,plain,
% 11.65/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.65/2.00      | ~ l1_pre_topc(X1)
% 11.65/2.00      | k2_pre_topc(X1,k2_pre_topc(X1,X0)) = k2_pre_topc(X1,X0) ),
% 11.65/2.00      inference(cnf_transformation,[],[f75]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_1678,plain,
% 11.65/2.00      ( ~ m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK4)))
% 11.65/2.00      | ~ l1_pre_topc(sK4)
% 11.65/2.00      | k2_pre_topc(sK4,k2_pre_topc(sK4,k2_tarski(sK5,sK5))) = k2_pre_topc(sK4,k2_tarski(sK5,sK5)) ),
% 11.65/2.00      inference(instantiation,[status(thm)],[c_14]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_15,plain,
% 11.65/2.00      ( v4_pre_topc(X0,X1)
% 11.65/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.65/2.00      | ~ v2_pre_topc(X1)
% 11.65/2.00      | ~ l1_pre_topc(X1)
% 11.65/2.00      | k2_pre_topc(X1,X0) != X0 ),
% 11.65/2.00      inference(cnf_transformation,[],[f77]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_2752,plain,
% 11.65/2.00      ( v4_pre_topc(k2_pre_topc(sK4,k2_tarski(sK5,sK5)),sK4)
% 11.65/2.00      | ~ m1_subset_1(k2_pre_topc(sK4,k2_tarski(sK5,sK5)),k1_zfmisc_1(u1_struct_0(sK4)))
% 11.65/2.00      | ~ v2_pre_topc(sK4)
% 11.65/2.00      | ~ l1_pre_topc(sK4)
% 11.65/2.00      | k2_pre_topc(sK4,k2_pre_topc(sK4,k2_tarski(sK5,sK5))) != k2_pre_topc(sK4,k2_tarski(sK5,sK5)) ),
% 11.65/2.00      inference(instantiation,[status(thm)],[c_15]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_2762,plain,
% 11.65/2.00      ( k2_pre_topc(sK4,k2_pre_topc(sK4,k2_tarski(sK5,sK5))) != k2_pre_topc(sK4,k2_tarski(sK5,sK5))
% 11.65/2.00      | v4_pre_topc(k2_pre_topc(sK4,k2_tarski(sK5,sK5)),sK4) = iProver_top
% 11.65/2.00      | m1_subset_1(k2_pre_topc(sK4,k2_tarski(sK5,sK5)),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 11.65/2.00      | v2_pre_topc(sK4) != iProver_top
% 11.65/2.00      | l1_pre_topc(sK4) != iProver_top ),
% 11.65/2.00      inference(predicate_to_equality,[status(thm)],[c_2752]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_21,plain,
% 11.65/2.00      ( v3_pre_topc(X0,X1)
% 11.65/2.00      | ~ v4_pre_topc(X0,X1)
% 11.65/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.65/2.00      | ~ v3_tdlat_3(X1)
% 11.65/2.00      | ~ v2_pre_topc(X1)
% 11.65/2.00      | ~ l1_pre_topc(X1) ),
% 11.65/2.00      inference(cnf_transformation,[],[f79]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_2751,plain,
% 11.65/2.00      ( v3_pre_topc(k2_pre_topc(sK4,k2_tarski(sK5,sK5)),sK4)
% 11.65/2.00      | ~ v4_pre_topc(k2_pre_topc(sK4,k2_tarski(sK5,sK5)),sK4)
% 11.65/2.00      | ~ m1_subset_1(k2_pre_topc(sK4,k2_tarski(sK5,sK5)),k1_zfmisc_1(u1_struct_0(sK4)))
% 11.65/2.00      | ~ v3_tdlat_3(sK4)
% 11.65/2.00      | ~ v2_pre_topc(sK4)
% 11.65/2.00      | ~ l1_pre_topc(sK4) ),
% 11.65/2.00      inference(instantiation,[status(thm)],[c_21]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_2764,plain,
% 11.65/2.00      ( v3_pre_topc(k2_pre_topc(sK4,k2_tarski(sK5,sK5)),sK4) = iProver_top
% 11.65/2.00      | v4_pre_topc(k2_pre_topc(sK4,k2_tarski(sK5,sK5)),sK4) != iProver_top
% 11.65/2.00      | m1_subset_1(k2_pre_topc(sK4,k2_tarski(sK5,sK5)),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 11.65/2.00      | v3_tdlat_3(sK4) != iProver_top
% 11.65/2.00      | v2_pre_topc(sK4) != iProver_top
% 11.65/2.00      | l1_pre_topc(sK4) != iProver_top ),
% 11.65/2.00      inference(predicate_to_equality,[status(thm)],[c_2751]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_1657,plain,
% 11.65/2.00      ( ~ v3_pre_topc(X0,sK4)
% 11.65/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 11.65/2.00      | ~ m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK4)))
% 11.65/2.00      | r1_xboole_0(X0,k2_pre_topc(sK4,k2_tarski(sK6,sK6)))
% 11.65/2.00      | ~ r1_xboole_0(X0,k2_tarski(sK6,sK6))
% 11.65/2.00      | ~ v2_pre_topc(sK4)
% 11.65/2.00      | ~ l1_pre_topc(sK4) ),
% 11.65/2.00      inference(instantiation,[status(thm)],[c_22]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_6462,plain,
% 11.65/2.00      ( ~ v3_pre_topc(k2_pre_topc(sK4,k2_tarski(sK5,sK5)),sK4)
% 11.65/2.00      | ~ m1_subset_1(k2_pre_topc(sK4,k2_tarski(sK5,sK5)),k1_zfmisc_1(u1_struct_0(sK4)))
% 11.65/2.00      | ~ m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK4)))
% 11.65/2.00      | r1_xboole_0(k2_pre_topc(sK4,k2_tarski(sK5,sK5)),k2_pre_topc(sK4,k2_tarski(sK6,sK6)))
% 11.65/2.00      | ~ r1_xboole_0(k2_pre_topc(sK4,k2_tarski(sK5,sK5)),k2_tarski(sK6,sK6))
% 11.65/2.00      | ~ v2_pre_topc(sK4)
% 11.65/2.00      | ~ l1_pre_topc(sK4) ),
% 11.65/2.00      inference(instantiation,[status(thm)],[c_1657]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_6463,plain,
% 11.65/2.00      ( v3_pre_topc(k2_pre_topc(sK4,k2_tarski(sK5,sK5)),sK4) != iProver_top
% 11.65/2.00      | m1_subset_1(k2_pre_topc(sK4,k2_tarski(sK5,sK5)),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 11.65/2.00      | m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 11.65/2.00      | r1_xboole_0(k2_pre_topc(sK4,k2_tarski(sK5,sK5)),k2_pre_topc(sK4,k2_tarski(sK6,sK6))) = iProver_top
% 11.65/2.00      | r1_xboole_0(k2_pre_topc(sK4,k2_tarski(sK5,sK5)),k2_tarski(sK6,sK6)) != iProver_top
% 11.65/2.00      | v2_pre_topc(sK4) != iProver_top
% 11.65/2.00      | l1_pre_topc(sK4) != iProver_top ),
% 11.65/2.00      inference(predicate_to_equality,[status(thm)],[c_6462]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_29433,plain,
% 11.65/2.00      ( r1_xboole_0(k2_pre_topc(sK4,k2_tarski(sK5,sK5)),k2_tarski(sK6,sK6)) != iProver_top ),
% 11.65/2.00      inference(global_propositional_subsumption,
% 11.65/2.00                [status(thm)],
% 11.65/2.00                [c_27782,c_31,c_32,c_33,c_34,c_28,c_35,c_27,c_36,c_37,
% 11.65/2.00                 c_64,c_65,c_67,c_68,c_1187,c_1189,c_1190,c_1358,c_1403,
% 11.65/2.00                 c_1404,c_1680,c_1678,c_2762,c_2764,c_2964,c_6463]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_29447,plain,
% 11.65/2.00      ( sK1(k2_tarski(sK6,sK6),k2_pre_topc(sK4,k2_tarski(sK5,sK5))) = sK6 ),
% 11.65/2.00      inference(superposition,[status(thm)],[c_16783,c_29433]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_37145,plain,
% 11.65/2.00      ( r1_xboole_0(k2_tarski(sK6,sK6),k2_pre_topc(sK4,k2_tarski(sK5,sK5))) = iProver_top
% 11.65/2.00      | r2_hidden(sK6,k2_pre_topc(sK4,k2_tarski(sK5,sK5))) = iProver_top ),
% 11.65/2.00      inference(superposition,[status(thm)],[c_29447,c_879]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_24,negated_conjecture,
% 11.65/2.00      ( k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK5)) != k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK6)) ),
% 11.65/2.00      inference(cnf_transformation,[],[f92]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_2823,plain,
% 11.65/2.00      ( k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK5)) != k2_pre_topc(sK4,k2_tarski(sK6,sK6)) ),
% 11.65/2.00      inference(demodulation,[status(thm)],[c_2819,c_24]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_2965,plain,
% 11.65/2.00      ( k2_pre_topc(sK4,k2_tarski(sK5,sK5)) != k2_pre_topc(sK4,k2_tarski(sK6,sK6)) ),
% 11.65/2.00      inference(demodulation,[status(thm)],[c_2961,c_2823]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_23,plain,
% 11.65/2.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 11.65/2.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 11.65/2.00      | ~ r2_hidden(X2,k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X0)))
% 11.65/2.00      | ~ v3_tdlat_3(X1)
% 11.65/2.00      | ~ v2_pre_topc(X1)
% 11.65/2.00      | v2_struct_0(X1)
% 11.65/2.00      | ~ l1_pre_topc(X1)
% 11.65/2.00      | k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X0)) = k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2)) ),
% 11.65/2.00      inference(cnf_transformation,[],[f84]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_859,plain,
% 11.65/2.00      ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))
% 11.65/2.00      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 11.65/2.00      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 11.65/2.00      | r2_hidden(X2,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))) != iProver_top
% 11.65/2.00      | v3_tdlat_3(X0) != iProver_top
% 11.65/2.00      | v2_pre_topc(X0) != iProver_top
% 11.65/2.00      | v2_struct_0(X0) = iProver_top
% 11.65/2.00      | l1_pre_topc(X0) != iProver_top ),
% 11.65/2.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_2971,plain,
% 11.65/2.00      ( k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),X0)) = k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK5))
% 11.65/2.00      | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
% 11.65/2.00      | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
% 11.65/2.00      | r2_hidden(X0,k2_pre_topc(sK4,k2_tarski(sK5,sK5))) != iProver_top
% 11.65/2.00      | v3_tdlat_3(sK4) != iProver_top
% 11.65/2.00      | v2_pre_topc(sK4) != iProver_top
% 11.65/2.00      | v2_struct_0(sK4) = iProver_top
% 11.65/2.00      | l1_pre_topc(sK4) != iProver_top ),
% 11.65/2.00      inference(superposition,[status(thm)],[c_2961,c_859]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_2972,plain,
% 11.65/2.00      ( k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),X0)) = k2_pre_topc(sK4,k2_tarski(sK5,sK5))
% 11.65/2.00      | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
% 11.65/2.00      | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
% 11.65/2.00      | r2_hidden(X0,k2_pre_topc(sK4,k2_tarski(sK5,sK5))) != iProver_top
% 11.65/2.00      | v3_tdlat_3(sK4) != iProver_top
% 11.65/2.00      | v2_pre_topc(sK4) != iProver_top
% 11.65/2.00      | v2_struct_0(sK4) = iProver_top
% 11.65/2.00      | l1_pre_topc(sK4) != iProver_top ),
% 11.65/2.00      inference(light_normalisation,[status(thm)],[c_2971,c_2961]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_3842,plain,
% 11.65/2.00      ( m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
% 11.65/2.00      | k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),X0)) = k2_pre_topc(sK4,k2_tarski(sK5,sK5))
% 11.65/2.00      | r2_hidden(X0,k2_pre_topc(sK4,k2_tarski(sK5,sK5))) != iProver_top ),
% 11.65/2.00      inference(global_propositional_subsumption,
% 11.65/2.00                [status(thm)],
% 11.65/2.00                [c_2972,c_32,c_33,c_34,c_35,c_36]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_3843,plain,
% 11.65/2.00      ( k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),X0)) = k2_pre_topc(sK4,k2_tarski(sK5,sK5))
% 11.65/2.00      | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
% 11.65/2.00      | r2_hidden(X0,k2_pre_topc(sK4,k2_tarski(sK5,sK5))) != iProver_top ),
% 11.65/2.00      inference(renaming,[status(thm)],[c_3842]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_3852,plain,
% 11.65/2.00      ( k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK1(X0,k2_pre_topc(sK4,k2_tarski(sK5,sK5))))) = k2_pre_topc(sK4,k2_tarski(sK5,sK5))
% 11.65/2.00      | m1_subset_1(sK1(X0,k2_pre_topc(sK4,k2_tarski(sK5,sK5))),u1_struct_0(sK4)) != iProver_top
% 11.65/2.00      | r1_xboole_0(X0,k2_pre_topc(sK4,k2_tarski(sK5,sK5))) = iProver_top ),
% 11.65/2.00      inference(superposition,[status(thm)],[c_879,c_3843]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_37149,plain,
% 11.65/2.00      ( k2_pre_topc(sK4,k6_domain_1(u1_struct_0(sK4),sK1(k2_tarski(sK6,sK6),k2_pre_topc(sK4,k2_tarski(sK5,sK5))))) = k2_pre_topc(sK4,k2_tarski(sK5,sK5))
% 11.65/2.00      | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top
% 11.65/2.00      | r1_xboole_0(k2_tarski(sK6,sK6),k2_pre_topc(sK4,k2_tarski(sK5,sK5))) = iProver_top ),
% 11.65/2.00      inference(superposition,[status(thm)],[c_29447,c_3852]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_37160,plain,
% 11.65/2.00      ( k2_pre_topc(sK4,k2_tarski(sK5,sK5)) = k2_pre_topc(sK4,k2_tarski(sK6,sK6))
% 11.65/2.00      | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top
% 11.65/2.00      | r1_xboole_0(k2_tarski(sK6,sK6),k2_pre_topc(sK4,k2_tarski(sK5,sK5))) = iProver_top ),
% 11.65/2.00      inference(light_normalisation,
% 11.65/2.00                [status(thm)],
% 11.65/2.00                [c_37149,c_2819,c_29447]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_37391,plain,
% 11.65/2.00      ( r1_xboole_0(k2_tarski(sK6,sK6),k2_pre_topc(sK4,k2_tarski(sK5,sK5))) = iProver_top ),
% 11.65/2.00      inference(global_propositional_subsumption,
% 11.65/2.00                [status(thm)],
% 11.65/2.00                [c_37145,c_37,c_2965,c_37160]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_37400,plain,
% 11.65/2.00      ( r2_hidden(X0,k2_pre_topc(sK4,k2_tarski(sK5,sK5))) != iProver_top
% 11.65/2.00      | r2_hidden(X0,k2_tarski(sK6,sK6)) != iProver_top ),
% 11.65/2.00      inference(superposition,[status(thm)],[c_37391,c_880]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_37654,plain,
% 11.65/2.00      ( r1_xboole_0(k2_pre_topc(sK4,k2_tarski(sK5,sK5)),X0) = iProver_top
% 11.65/2.00      | r2_hidden(sK1(k2_pre_topc(sK4,k2_tarski(sK5,sK5)),X0),k2_tarski(sK6,sK6)) != iProver_top ),
% 11.65/2.00      inference(superposition,[status(thm)],[c_878,c_37400]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_39308,plain,
% 11.65/2.00      ( r1_xboole_0(k2_pre_topc(sK4,k2_tarski(sK5,sK5)),k2_tarski(sK6,sK6)) = iProver_top ),
% 11.65/2.00      inference(superposition,[status(thm)],[c_879,c_37654]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(contradiction,plain,
% 11.65/2.00      ( $false ),
% 11.65/2.00      inference(minisat,
% 11.65/2.00                [status(thm)],
% 11.65/2.00                [c_39308,c_6463,c_2964,c_2764,c_2762,c_1678,c_1680,
% 11.65/2.00                 c_1404,c_1403,c_1358,c_1190,c_1189,c_1187,c_68,c_67,
% 11.65/2.00                 c_65,c_64,c_37,c_36,c_27,c_35,c_28,c_34,c_33,c_32,c_31]) ).
% 11.65/2.00  
% 11.65/2.00  
% 11.65/2.00  % SZS output end CNFRefutation for theBenchmark.p
% 11.65/2.00  
% 11.65/2.00  ------                               Statistics
% 11.65/2.00  
% 11.65/2.00  ------ Selected
% 11.65/2.00  
% 11.65/2.00  total_time:                             1.098
% 11.65/2.00  
%------------------------------------------------------------------------------
