%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:27:31 EST 2020

% Result     : Theorem 7.44s
% Output     : CNFRefutation 7.44s
% Verified   : 
% Statistics : Number of formulae       :  155 (2248 expanded)
%              Number of clauses        :   82 ( 598 expanded)
%              Number of leaves         :   19 ( 639 expanded)
%              Depth                    :   24
%              Number of atoms          :  598 (11628 expanded)
%              Number of equality atoms :  136 (1798 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
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

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f36])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f39,plain,(
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
    inference(rectify,[],[f38])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK1(X0,X1) != X0
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( sK1(X0,X1) = X0
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK1(X0,X1) != X0
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( sK1(X0,X1) = X0
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f39,f40])).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f3,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f81,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f53,f57])).

fof(f85,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k2_tarski(X0,X0)) ) ),
    inference(equality_resolution,[],[f81])).

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

fof(f63,plain,(
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
    inference(nnf_transformation,[],[f29])).

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
     => ( ~ v3_pre_topc(sK2(X0),X0)
        & v4_pre_topc(sK2(X0),X0)
        & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] :
      ( ( ( v3_tdlat_3(X0)
          | ( ~ v3_pre_topc(sK2(X0),X0)
            & v4_pre_topc(sK2(X0),X0)
            & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v3_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f43,f44])).

fof(f64,plain,(
    ! [X2,X0] :
      ( v3_pre_topc(X2,X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

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

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

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

fof(f48,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))
          & ~ r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK5)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
        & ~ r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK5)))
        & m1_subset_1(sK5,u1_struct_0(X0)) ) ) ),
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
            ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK4)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))
            & ~ r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK4)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK4,u1_struct_0(X0)) ) ) ),
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
              ( k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),X1)) != k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),X2))
              & ~ r1_xboole_0(k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),X1)),k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),X2)))
              & m1_subset_1(X2,u1_struct_0(sK3)) )
          & m1_subset_1(X1,u1_struct_0(sK3)) )
      & l1_pre_topc(sK3)
      & v3_tdlat_3(sK3)
      & v2_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK4)) != k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5))
    & ~ r1_xboole_0(k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK4)),k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5)))
    & m1_subset_1(sK5,u1_struct_0(sK3))
    & m1_subset_1(sK4,u1_struct_0(sK3))
    & l1_pre_topc(sK3)
    & v3_tdlat_3(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f35,f48,f47,f46])).

fof(f71,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f72,plain,(
    v3_tdlat_3(sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f73,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f49])).

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

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X1,k2_pre_topc(X0,X2))
      | ~ v3_pre_topc(X1,X0)
      | ~ r1_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f75,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f49])).

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

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k2_tarski(X1,X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f62,f57])).

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

fof(f59,plain,(
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

fof(f60,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f70,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f76,plain,(
    ~ r1_xboole_0(k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK4)),k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) ),
    inference(cnf_transformation,[],[f49])).

fof(f74,plain,(
    m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f49])).

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

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

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

fof(f69,plain,(
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

fof(f77,plain,(
    k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK4)) != k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_945,plain,
    ( r2_hidden(sK0(X0,X1),X1) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k2_tarski(X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_940,plain,
    ( X0 = X1
    | r2_hidden(X0,k2_tarski(X1,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1619,plain,
    ( sK0(X0,k2_tarski(X1,X1)) = X1
    | r1_xboole_0(X0,k2_tarski(X1,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_945,c_940])).

cnf(c_12,plain,
    ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_16,plain,
    ( v3_pre_topc(X0,X1)
    | ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_420,plain,
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
    inference(resolution_lifted,[status(thm)],[c_12,c_16])).

cnf(c_421,plain,
    ( v3_pre_topc(k2_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v3_tdlat_3(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(unflattening,[status(thm)],[c_420])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_437,plain,
    ( v3_pre_topc(k2_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v3_tdlat_3(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_421,c_7])).

cnf(c_25,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_454,plain,
    ( v3_pre_topc(k2_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v3_tdlat_3(X0)
    | ~ l1_pre_topc(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_437,c_25])).

cnf(c_455,plain,
    ( v3_pre_topc(k2_pre_topc(sK3,X0),sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v3_tdlat_3(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_454])).

cnf(c_24,negated_conjecture,
    ( v3_tdlat_3(sK3) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_23,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_459,plain,
    ( v3_pre_topc(k2_pre_topc(sK3,X0),sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_455,c_24,c_23])).

cnf(c_17,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_xboole_0(X0,X2)
    | r1_xboole_0(X0,k2_pre_topc(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_476,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_xboole_0(X0,X2)
    | r1_xboole_0(X0,k2_pre_topc(X1,X2))
    | ~ l1_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_25])).

cnf(c_477,plain,
    ( ~ v3_pre_topc(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X0,k2_pre_topc(sK3,X1))
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_476])).

cnf(c_481,plain,
    ( r1_xboole_0(X0,k2_pre_topc(sK3,X1))
    | ~ r1_xboole_0(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v3_pre_topc(X0,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_477,c_23])).

cnf(c_482,plain,
    ( ~ v3_pre_topc(X0,sK3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X0,k2_pre_topc(sK3,X1)) ),
    inference(renaming,[status(thm)],[c_481])).

cnf(c_527,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_xboole_0(X0,X2)
    | r1_xboole_0(X0,k2_pre_topc(sK3,X2))
    | k2_pre_topc(sK3,X1) != X0
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_459,c_482])).

cnf(c_528,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(k2_pre_topc(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_xboole_0(k2_pre_topc(sK3,X0),X1)
    | r1_xboole_0(k2_pre_topc(sK3,X0),k2_pre_topc(sK3,X1)) ),
    inference(unflattening,[status(thm)],[c_527])).

cnf(c_512,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_23])).

cnf(c_513,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(k2_pre_topc(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(unflattening,[status(thm)],[c_512])).

cnf(c_532,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_xboole_0(k2_pre_topc(sK3,X0),X1)
    | r1_xboole_0(k2_pre_topc(sK3,X0),k2_pre_topc(sK3,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_528,c_513])).

cnf(c_533,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_xboole_0(k2_pre_topc(sK3,X1),X0)
    | r1_xboole_0(k2_pre_topc(sK3,X1),k2_pre_topc(sK3,X0)) ),
    inference(renaming,[status(thm)],[c_532])).

cnf(c_932,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r1_xboole_0(k2_pre_topc(sK3,X1),X0) != iProver_top
    | r1_xboole_0(k2_pre_topc(sK3,X1),k2_pre_topc(sK3,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_533])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_938,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_8,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_9,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_286,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_8,c_9])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_348,plain,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_pre_topc(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_286,c_26])).

cnf(c_349,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK3))
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_348])).

cnf(c_56,plain,
    ( v2_struct_0(sK3)
    | ~ v1_xboole_0(u1_struct_0(sK3))
    | ~ l1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_59,plain,
    ( l1_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_351,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_349,c_26,c_23,c_56,c_59])).

cnf(c_390,plain,
    ( ~ m1_subset_1(X0,X1)
    | k6_domain_1(X1,X0) = k2_tarski(X0,X0)
    | u1_struct_0(sK3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_351])).

cnf(c_391,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | k6_domain_1(u1_struct_0(sK3),X0) = k2_tarski(X0,X0) ),
    inference(unflattening,[status(thm)],[c_390])).

cnf(c_935,plain,
    ( k6_domain_1(u1_struct_0(sK3),X0) = k2_tarski(X0,X0)
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_391])).

cnf(c_1312,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK5) = k2_tarski(sK5,sK5) ),
    inference(superposition,[status(thm)],[c_938,c_935])).

cnf(c_20,negated_conjecture,
    ( ~ r1_xboole_0(k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK4)),k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_939,plain,
    ( r1_xboole_0(k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK4)),k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1314,plain,
    ( r1_xboole_0(k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK4)),k2_pre_topc(sK3,k2_tarski(sK5,sK5))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1312,c_939])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_937,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1313,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK4) = k2_tarski(sK4,sK4) ),
    inference(superposition,[status(thm)],[c_937,c_935])).

cnf(c_1317,plain,
    ( r1_xboole_0(k2_pre_topc(sK3,k2_tarski(sK4,sK4)),k2_pre_topc(sK3,k2_tarski(sK5,sK5))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1314,c_1313])).

cnf(c_1730,plain,
    ( m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r1_xboole_0(k2_pre_topc(sK3,k2_tarski(sK4,sK4)),k2_tarski(sK5,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_932,c_1317])).

cnf(c_31,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_32,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_402,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
    | u1_struct_0(sK3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_351])).

cnf(c_403,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | m1_subset_1(k6_domain_1(u1_struct_0(sK3),X0),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(unflattening,[status(thm)],[c_402])).

cnf(c_934,plain,
    ( m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k6_domain_1(u1_struct_0(sK3),X0),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_403])).

cnf(c_1891,plain,
    ( m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1313,c_934])).

cnf(c_1892,plain,
    ( m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1312,c_934])).

cnf(c_2589,plain,
    ( r1_xboole_0(k2_pre_topc(sK3,k2_tarski(sK4,sK4)),k2_tarski(sK5,sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1730,c_31,c_32,c_1891,c_1892])).

cnf(c_2594,plain,
    ( sK0(k2_pre_topc(sK3,k2_tarski(sK4,sK4)),k2_tarski(sK5,sK5)) = sK5 ),
    inference(superposition,[status(thm)],[c_1619,c_2589])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_944,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X0)))
    | ~ v3_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X0)) = k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_359,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X0)))
    | ~ v3_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2)) = k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X0))
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_26])).

cnf(c_360,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ r2_hidden(X0,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),X1)))
    | ~ v3_tdlat_3(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),X0)) = k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),X1)) ),
    inference(unflattening,[status(thm)],[c_359])).

cnf(c_364,plain,
    ( ~ r2_hidden(X0,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),X0)) = k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_360,c_25,c_24,c_23])).

cnf(c_365,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ r2_hidden(X0,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),X1)))
    | k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),X0)) = k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),X1)) ),
    inference(renaming,[status(thm)],[c_364])).

cnf(c_936,plain,
    ( k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),X0)) = k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),X1))
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_365])).

cnf(c_1627,plain,
    ( k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),X0)) = k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK4))
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0,k2_pre_topc(sK3,k2_tarski(sK4,sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1313,c_936])).

cnf(c_1628,plain,
    ( k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),X0)) = k2_pre_topc(sK3,k2_tarski(sK4,sK4))
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0,k2_pre_topc(sK3,k2_tarski(sK4,sK4))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1627,c_1313])).

cnf(c_2116,plain,
    ( m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),X0)) = k2_pre_topc(sK3,k2_tarski(sK4,sK4))
    | r2_hidden(X0,k2_pre_topc(sK3,k2_tarski(sK4,sK4))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1628,c_31])).

cnf(c_2117,plain,
    ( k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),X0)) = k2_pre_topc(sK3,k2_tarski(sK4,sK4))
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0,k2_pre_topc(sK3,k2_tarski(sK4,sK4))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2116])).

cnf(c_2123,plain,
    ( k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK0(k2_pre_topc(sK3,k2_tarski(sK4,sK4)),X0))) = k2_pre_topc(sK3,k2_tarski(sK4,sK4))
    | m1_subset_1(sK0(k2_pre_topc(sK3,k2_tarski(sK4,sK4)),X0),u1_struct_0(sK3)) != iProver_top
    | r1_xboole_0(k2_pre_topc(sK3,k2_tarski(sK4,sK4)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_944,c_2117])).

cnf(c_11272,plain,
    ( k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK0(k2_pre_topc(sK3,k2_tarski(sK4,sK4)),k2_tarski(sK5,sK5)))) = k2_pre_topc(sK3,k2_tarski(sK4,sK4))
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
    | r1_xboole_0(k2_pre_topc(sK3,k2_tarski(sK4,sK4)),k2_tarski(sK5,sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2594,c_2123])).

cnf(c_11273,plain,
    ( k2_pre_topc(sK3,k2_tarski(sK4,sK4)) = k2_pre_topc(sK3,k2_tarski(sK5,sK5))
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
    | r1_xboole_0(k2_pre_topc(sK3,k2_tarski(sK4,sK4)),k2_tarski(sK5,sK5)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11272,c_1312,c_2594])).

cnf(c_19,negated_conjecture,
    ( k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK4)) != k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1315,plain,
    ( k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK4)) != k2_pre_topc(sK3,k2_tarski(sK5,sK5)) ),
    inference(demodulation,[status(thm)],[c_1312,c_19])).

cnf(c_1316,plain,
    ( k2_pre_topc(sK3,k2_tarski(sK4,sK4)) != k2_pre_topc(sK3,k2_tarski(sK5,sK5)) ),
    inference(light_normalisation,[status(thm)],[c_1315,c_1313])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11273,c_1892,c_1891,c_1730,c_1316,c_32,c_31])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:16:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 7.44/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.44/1.49  
% 7.44/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.44/1.49  
% 7.44/1.49  ------  iProver source info
% 7.44/1.49  
% 7.44/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.44/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.44/1.49  git: non_committed_changes: false
% 7.44/1.49  git: last_make_outside_of_git: false
% 7.44/1.49  
% 7.44/1.49  ------ 
% 7.44/1.49  
% 7.44/1.49  ------ Input Options
% 7.44/1.49  
% 7.44/1.49  --out_options                           all
% 7.44/1.49  --tptp_safe_out                         true
% 7.44/1.49  --problem_path                          ""
% 7.44/1.49  --include_path                          ""
% 7.44/1.49  --clausifier                            res/vclausify_rel
% 7.44/1.49  --clausifier_options                    ""
% 7.44/1.49  --stdin                                 false
% 7.44/1.49  --stats_out                             all
% 7.44/1.49  
% 7.44/1.49  ------ General Options
% 7.44/1.49  
% 7.44/1.49  --fof                                   false
% 7.44/1.49  --time_out_real                         305.
% 7.44/1.49  --time_out_virtual                      -1.
% 7.44/1.49  --symbol_type_check                     false
% 7.44/1.49  --clausify_out                          false
% 7.44/1.49  --sig_cnt_out                           false
% 7.44/1.49  --trig_cnt_out                          false
% 7.44/1.49  --trig_cnt_out_tolerance                1.
% 7.44/1.49  --trig_cnt_out_sk_spl                   false
% 7.44/1.49  --abstr_cl_out                          false
% 7.44/1.49  
% 7.44/1.49  ------ Global Options
% 7.44/1.49  
% 7.44/1.49  --schedule                              default
% 7.44/1.49  --add_important_lit                     false
% 7.44/1.49  --prop_solver_per_cl                    1000
% 7.44/1.49  --min_unsat_core                        false
% 7.44/1.49  --soft_assumptions                      false
% 7.44/1.49  --soft_lemma_size                       3
% 7.44/1.49  --prop_impl_unit_size                   0
% 7.44/1.49  --prop_impl_unit                        []
% 7.44/1.49  --share_sel_clauses                     true
% 7.44/1.49  --reset_solvers                         false
% 7.44/1.49  --bc_imp_inh                            [conj_cone]
% 7.44/1.49  --conj_cone_tolerance                   3.
% 7.44/1.49  --extra_neg_conj                        none
% 7.44/1.49  --large_theory_mode                     true
% 7.44/1.49  --prolific_symb_bound                   200
% 7.44/1.49  --lt_threshold                          2000
% 7.44/1.49  --clause_weak_htbl                      true
% 7.44/1.49  --gc_record_bc_elim                     false
% 7.44/1.49  
% 7.44/1.49  ------ Preprocessing Options
% 7.44/1.49  
% 7.44/1.49  --preprocessing_flag                    true
% 7.44/1.49  --time_out_prep_mult                    0.1
% 7.44/1.49  --splitting_mode                        input
% 7.44/1.49  --splitting_grd                         true
% 7.44/1.49  --splitting_cvd                         false
% 7.44/1.49  --splitting_cvd_svl                     false
% 7.44/1.49  --splitting_nvd                         32
% 7.44/1.49  --sub_typing                            true
% 7.44/1.49  --prep_gs_sim                           true
% 7.44/1.49  --prep_unflatten                        true
% 7.44/1.49  --prep_res_sim                          true
% 7.44/1.49  --prep_upred                            true
% 7.44/1.49  --prep_sem_filter                       exhaustive
% 7.44/1.49  --prep_sem_filter_out                   false
% 7.44/1.49  --pred_elim                             true
% 7.44/1.49  --res_sim_input                         true
% 7.44/1.49  --eq_ax_congr_red                       true
% 7.44/1.49  --pure_diseq_elim                       true
% 7.44/1.49  --brand_transform                       false
% 7.44/1.49  --non_eq_to_eq                          false
% 7.44/1.49  --prep_def_merge                        true
% 7.44/1.49  --prep_def_merge_prop_impl              false
% 7.44/1.49  --prep_def_merge_mbd                    true
% 7.44/1.49  --prep_def_merge_tr_red                 false
% 7.44/1.49  --prep_def_merge_tr_cl                  false
% 7.44/1.49  --smt_preprocessing                     true
% 7.44/1.49  --smt_ac_axioms                         fast
% 7.44/1.49  --preprocessed_out                      false
% 7.44/1.49  --preprocessed_stats                    false
% 7.44/1.49  
% 7.44/1.49  ------ Abstraction refinement Options
% 7.44/1.49  
% 7.44/1.49  --abstr_ref                             []
% 7.44/1.49  --abstr_ref_prep                        false
% 7.44/1.49  --abstr_ref_until_sat                   false
% 7.44/1.49  --abstr_ref_sig_restrict                funpre
% 7.44/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.44/1.49  --abstr_ref_under                       []
% 7.44/1.49  
% 7.44/1.49  ------ SAT Options
% 7.44/1.49  
% 7.44/1.49  --sat_mode                              false
% 7.44/1.49  --sat_fm_restart_options                ""
% 7.44/1.49  --sat_gr_def                            false
% 7.44/1.49  --sat_epr_types                         true
% 7.44/1.49  --sat_non_cyclic_types                  false
% 7.44/1.49  --sat_finite_models                     false
% 7.44/1.49  --sat_fm_lemmas                         false
% 7.44/1.49  --sat_fm_prep                           false
% 7.44/1.49  --sat_fm_uc_incr                        true
% 7.44/1.49  --sat_out_model                         small
% 7.44/1.49  --sat_out_clauses                       false
% 7.44/1.49  
% 7.44/1.49  ------ QBF Options
% 7.44/1.49  
% 7.44/1.49  --qbf_mode                              false
% 7.44/1.49  --qbf_elim_univ                         false
% 7.44/1.49  --qbf_dom_inst                          none
% 7.44/1.49  --qbf_dom_pre_inst                      false
% 7.44/1.49  --qbf_sk_in                             false
% 7.44/1.49  --qbf_pred_elim                         true
% 7.44/1.49  --qbf_split                             512
% 7.44/1.49  
% 7.44/1.49  ------ BMC1 Options
% 7.44/1.49  
% 7.44/1.49  --bmc1_incremental                      false
% 7.44/1.49  --bmc1_axioms                           reachable_all
% 7.44/1.49  --bmc1_min_bound                        0
% 7.44/1.49  --bmc1_max_bound                        -1
% 7.44/1.49  --bmc1_max_bound_default                -1
% 7.44/1.49  --bmc1_symbol_reachability              true
% 7.44/1.49  --bmc1_property_lemmas                  false
% 7.44/1.49  --bmc1_k_induction                      false
% 7.44/1.49  --bmc1_non_equiv_states                 false
% 7.44/1.49  --bmc1_deadlock                         false
% 7.44/1.49  --bmc1_ucm                              false
% 7.44/1.49  --bmc1_add_unsat_core                   none
% 7.44/1.49  --bmc1_unsat_core_children              false
% 7.44/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.44/1.49  --bmc1_out_stat                         full
% 7.44/1.49  --bmc1_ground_init                      false
% 7.44/1.49  --bmc1_pre_inst_next_state              false
% 7.44/1.49  --bmc1_pre_inst_state                   false
% 7.44/1.49  --bmc1_pre_inst_reach_state             false
% 7.44/1.49  --bmc1_out_unsat_core                   false
% 7.44/1.49  --bmc1_aig_witness_out                  false
% 7.44/1.49  --bmc1_verbose                          false
% 7.44/1.49  --bmc1_dump_clauses_tptp                false
% 7.44/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.44/1.49  --bmc1_dump_file                        -
% 7.44/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.44/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.44/1.49  --bmc1_ucm_extend_mode                  1
% 7.44/1.49  --bmc1_ucm_init_mode                    2
% 7.44/1.49  --bmc1_ucm_cone_mode                    none
% 7.44/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.44/1.49  --bmc1_ucm_relax_model                  4
% 7.44/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.44/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.44/1.49  --bmc1_ucm_layered_model                none
% 7.44/1.49  --bmc1_ucm_max_lemma_size               10
% 7.44/1.49  
% 7.44/1.49  ------ AIG Options
% 7.44/1.49  
% 7.44/1.49  --aig_mode                              false
% 7.44/1.49  
% 7.44/1.49  ------ Instantiation Options
% 7.44/1.49  
% 7.44/1.49  --instantiation_flag                    true
% 7.44/1.49  --inst_sos_flag                         true
% 7.44/1.49  --inst_sos_phase                        true
% 7.44/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.44/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.44/1.49  --inst_lit_sel_side                     num_symb
% 7.44/1.49  --inst_solver_per_active                1400
% 7.44/1.49  --inst_solver_calls_frac                1.
% 7.44/1.49  --inst_passive_queue_type               priority_queues
% 7.44/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.44/1.49  --inst_passive_queues_freq              [25;2]
% 7.44/1.49  --inst_dismatching                      true
% 7.44/1.49  --inst_eager_unprocessed_to_passive     true
% 7.44/1.49  --inst_prop_sim_given                   true
% 7.44/1.49  --inst_prop_sim_new                     false
% 7.44/1.49  --inst_subs_new                         false
% 7.44/1.49  --inst_eq_res_simp                      false
% 7.44/1.49  --inst_subs_given                       false
% 7.44/1.49  --inst_orphan_elimination               true
% 7.44/1.49  --inst_learning_loop_flag               true
% 7.44/1.49  --inst_learning_start                   3000
% 7.44/1.49  --inst_learning_factor                  2
% 7.44/1.49  --inst_start_prop_sim_after_learn       3
% 7.44/1.49  --inst_sel_renew                        solver
% 7.44/1.49  --inst_lit_activity_flag                true
% 7.44/1.49  --inst_restr_to_given                   false
% 7.44/1.49  --inst_activity_threshold               500
% 7.44/1.49  --inst_out_proof                        true
% 7.44/1.49  
% 7.44/1.49  ------ Resolution Options
% 7.44/1.49  
% 7.44/1.49  --resolution_flag                       true
% 7.44/1.49  --res_lit_sel                           adaptive
% 7.44/1.49  --res_lit_sel_side                      none
% 7.44/1.49  --res_ordering                          kbo
% 7.44/1.49  --res_to_prop_solver                    active
% 7.44/1.49  --res_prop_simpl_new                    false
% 7.44/1.49  --res_prop_simpl_given                  true
% 7.44/1.49  --res_passive_queue_type                priority_queues
% 7.44/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.44/1.49  --res_passive_queues_freq               [15;5]
% 7.44/1.49  --res_forward_subs                      full
% 7.44/1.49  --res_backward_subs                     full
% 7.44/1.49  --res_forward_subs_resolution           true
% 7.44/1.49  --res_backward_subs_resolution          true
% 7.44/1.49  --res_orphan_elimination                true
% 7.44/1.49  --res_time_limit                        2.
% 7.44/1.49  --res_out_proof                         true
% 7.44/1.49  
% 7.44/1.49  ------ Superposition Options
% 7.44/1.49  
% 7.44/1.49  --superposition_flag                    true
% 7.44/1.49  --sup_passive_queue_type                priority_queues
% 7.44/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.44/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.44/1.49  --demod_completeness_check              fast
% 7.44/1.49  --demod_use_ground                      true
% 7.44/1.49  --sup_to_prop_solver                    passive
% 7.44/1.49  --sup_prop_simpl_new                    true
% 7.44/1.49  --sup_prop_simpl_given                  true
% 7.44/1.49  --sup_fun_splitting                     true
% 7.44/1.49  --sup_smt_interval                      50000
% 7.44/1.49  
% 7.44/1.49  ------ Superposition Simplification Setup
% 7.44/1.49  
% 7.44/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.44/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.44/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.44/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.44/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.44/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.44/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.44/1.49  --sup_immed_triv                        [TrivRules]
% 7.44/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.44/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.44/1.49  --sup_immed_bw_main                     []
% 7.44/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.44/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.44/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.44/1.49  --sup_input_bw                          []
% 7.44/1.49  
% 7.44/1.49  ------ Combination Options
% 7.44/1.49  
% 7.44/1.49  --comb_res_mult                         3
% 7.44/1.49  --comb_sup_mult                         2
% 7.44/1.49  --comb_inst_mult                        10
% 7.44/1.49  
% 7.44/1.49  ------ Debug Options
% 7.44/1.49  
% 7.44/1.49  --dbg_backtrace                         false
% 7.44/1.49  --dbg_dump_prop_clauses                 false
% 7.44/1.49  --dbg_dump_prop_clauses_file            -
% 7.44/1.49  --dbg_out_stat                          false
% 7.44/1.49  ------ Parsing...
% 7.44/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.44/1.49  
% 7.44/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 8 0s  sf_e  pe_s  pe_e 
% 7.44/1.49  
% 7.44/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.44/1.49  
% 7.44/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.44/1.49  ------ Proving...
% 7.44/1.49  ------ Problem Properties 
% 7.44/1.49  
% 7.44/1.49  
% 7.44/1.49  clauses                                 16
% 7.44/1.49  conjectures                             4
% 7.44/1.49  EPR                                     1
% 7.44/1.49  Horn                                    13
% 7.44/1.49  unary                                   5
% 7.44/1.49  binary                                  6
% 7.44/1.49  lits                                    34
% 7.44/1.49  lits eq                                 8
% 7.44/1.49  fd_pure                                 0
% 7.44/1.49  fd_pseudo                               0
% 7.44/1.49  fd_cond                                 0
% 7.44/1.49  fd_pseudo_cond                          2
% 7.44/1.49  AC symbols                              0
% 7.44/1.49  
% 7.44/1.49  ------ Schedule dynamic 5 is on 
% 7.44/1.49  
% 7.44/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.44/1.49  
% 7.44/1.49  
% 7.44/1.49  ------ 
% 7.44/1.49  Current options:
% 7.44/1.49  ------ 
% 7.44/1.49  
% 7.44/1.49  ------ Input Options
% 7.44/1.49  
% 7.44/1.49  --out_options                           all
% 7.44/1.49  --tptp_safe_out                         true
% 7.44/1.49  --problem_path                          ""
% 7.44/1.49  --include_path                          ""
% 7.44/1.49  --clausifier                            res/vclausify_rel
% 7.44/1.49  --clausifier_options                    ""
% 7.44/1.49  --stdin                                 false
% 7.44/1.49  --stats_out                             all
% 7.44/1.49  
% 7.44/1.49  ------ General Options
% 7.44/1.49  
% 7.44/1.49  --fof                                   false
% 7.44/1.49  --time_out_real                         305.
% 7.44/1.49  --time_out_virtual                      -1.
% 7.44/1.49  --symbol_type_check                     false
% 7.44/1.49  --clausify_out                          false
% 7.44/1.49  --sig_cnt_out                           false
% 7.44/1.49  --trig_cnt_out                          false
% 7.44/1.49  --trig_cnt_out_tolerance                1.
% 7.44/1.49  --trig_cnt_out_sk_spl                   false
% 7.44/1.49  --abstr_cl_out                          false
% 7.44/1.49  
% 7.44/1.49  ------ Global Options
% 7.44/1.49  
% 7.44/1.49  --schedule                              default
% 7.44/1.49  --add_important_lit                     false
% 7.44/1.49  --prop_solver_per_cl                    1000
% 7.44/1.49  --min_unsat_core                        false
% 7.44/1.49  --soft_assumptions                      false
% 7.44/1.49  --soft_lemma_size                       3
% 7.44/1.49  --prop_impl_unit_size                   0
% 7.44/1.49  --prop_impl_unit                        []
% 7.44/1.49  --share_sel_clauses                     true
% 7.44/1.49  --reset_solvers                         false
% 7.44/1.49  --bc_imp_inh                            [conj_cone]
% 7.44/1.49  --conj_cone_tolerance                   3.
% 7.44/1.49  --extra_neg_conj                        none
% 7.44/1.49  --large_theory_mode                     true
% 7.44/1.49  --prolific_symb_bound                   200
% 7.44/1.49  --lt_threshold                          2000
% 7.44/1.49  --clause_weak_htbl                      true
% 7.44/1.49  --gc_record_bc_elim                     false
% 7.44/1.49  
% 7.44/1.49  ------ Preprocessing Options
% 7.44/1.49  
% 7.44/1.49  --preprocessing_flag                    true
% 7.44/1.49  --time_out_prep_mult                    0.1
% 7.44/1.49  --splitting_mode                        input
% 7.44/1.49  --splitting_grd                         true
% 7.44/1.49  --splitting_cvd                         false
% 7.44/1.49  --splitting_cvd_svl                     false
% 7.44/1.49  --splitting_nvd                         32
% 7.44/1.49  --sub_typing                            true
% 7.44/1.49  --prep_gs_sim                           true
% 7.44/1.49  --prep_unflatten                        true
% 7.44/1.49  --prep_res_sim                          true
% 7.44/1.49  --prep_upred                            true
% 7.44/1.49  --prep_sem_filter                       exhaustive
% 7.44/1.49  --prep_sem_filter_out                   false
% 7.44/1.49  --pred_elim                             true
% 7.44/1.49  --res_sim_input                         true
% 7.44/1.49  --eq_ax_congr_red                       true
% 7.44/1.49  --pure_diseq_elim                       true
% 7.44/1.49  --brand_transform                       false
% 7.44/1.49  --non_eq_to_eq                          false
% 7.44/1.49  --prep_def_merge                        true
% 7.44/1.49  --prep_def_merge_prop_impl              false
% 7.44/1.49  --prep_def_merge_mbd                    true
% 7.44/1.49  --prep_def_merge_tr_red                 false
% 7.44/1.49  --prep_def_merge_tr_cl                  false
% 7.44/1.49  --smt_preprocessing                     true
% 7.44/1.49  --smt_ac_axioms                         fast
% 7.44/1.49  --preprocessed_out                      false
% 7.44/1.49  --preprocessed_stats                    false
% 7.44/1.49  
% 7.44/1.49  ------ Abstraction refinement Options
% 7.44/1.49  
% 7.44/1.49  --abstr_ref                             []
% 7.44/1.49  --abstr_ref_prep                        false
% 7.44/1.49  --abstr_ref_until_sat                   false
% 7.44/1.49  --abstr_ref_sig_restrict                funpre
% 7.44/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.44/1.49  --abstr_ref_under                       []
% 7.44/1.49  
% 7.44/1.49  ------ SAT Options
% 7.44/1.49  
% 7.44/1.49  --sat_mode                              false
% 7.44/1.49  --sat_fm_restart_options                ""
% 7.44/1.49  --sat_gr_def                            false
% 7.44/1.49  --sat_epr_types                         true
% 7.44/1.49  --sat_non_cyclic_types                  false
% 7.44/1.49  --sat_finite_models                     false
% 7.44/1.49  --sat_fm_lemmas                         false
% 7.44/1.49  --sat_fm_prep                           false
% 7.44/1.49  --sat_fm_uc_incr                        true
% 7.44/1.49  --sat_out_model                         small
% 7.44/1.49  --sat_out_clauses                       false
% 7.44/1.49  
% 7.44/1.49  ------ QBF Options
% 7.44/1.49  
% 7.44/1.49  --qbf_mode                              false
% 7.44/1.49  --qbf_elim_univ                         false
% 7.44/1.49  --qbf_dom_inst                          none
% 7.44/1.49  --qbf_dom_pre_inst                      false
% 7.44/1.49  --qbf_sk_in                             false
% 7.44/1.49  --qbf_pred_elim                         true
% 7.44/1.49  --qbf_split                             512
% 7.44/1.49  
% 7.44/1.49  ------ BMC1 Options
% 7.44/1.49  
% 7.44/1.49  --bmc1_incremental                      false
% 7.44/1.49  --bmc1_axioms                           reachable_all
% 7.44/1.49  --bmc1_min_bound                        0
% 7.44/1.49  --bmc1_max_bound                        -1
% 7.44/1.49  --bmc1_max_bound_default                -1
% 7.44/1.49  --bmc1_symbol_reachability              true
% 7.44/1.49  --bmc1_property_lemmas                  false
% 7.44/1.49  --bmc1_k_induction                      false
% 7.44/1.49  --bmc1_non_equiv_states                 false
% 7.44/1.49  --bmc1_deadlock                         false
% 7.44/1.49  --bmc1_ucm                              false
% 7.44/1.49  --bmc1_add_unsat_core                   none
% 7.44/1.49  --bmc1_unsat_core_children              false
% 7.44/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.44/1.49  --bmc1_out_stat                         full
% 7.44/1.49  --bmc1_ground_init                      false
% 7.44/1.49  --bmc1_pre_inst_next_state              false
% 7.44/1.49  --bmc1_pre_inst_state                   false
% 7.44/1.49  --bmc1_pre_inst_reach_state             false
% 7.44/1.49  --bmc1_out_unsat_core                   false
% 7.44/1.49  --bmc1_aig_witness_out                  false
% 7.44/1.49  --bmc1_verbose                          false
% 7.44/1.49  --bmc1_dump_clauses_tptp                false
% 7.44/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.44/1.49  --bmc1_dump_file                        -
% 7.44/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.44/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.44/1.49  --bmc1_ucm_extend_mode                  1
% 7.44/1.49  --bmc1_ucm_init_mode                    2
% 7.44/1.49  --bmc1_ucm_cone_mode                    none
% 7.44/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.44/1.49  --bmc1_ucm_relax_model                  4
% 7.44/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.44/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.44/1.49  --bmc1_ucm_layered_model                none
% 7.44/1.49  --bmc1_ucm_max_lemma_size               10
% 7.44/1.49  
% 7.44/1.49  ------ AIG Options
% 7.44/1.49  
% 7.44/1.49  --aig_mode                              false
% 7.44/1.49  
% 7.44/1.49  ------ Instantiation Options
% 7.44/1.49  
% 7.44/1.49  --instantiation_flag                    true
% 7.44/1.49  --inst_sos_flag                         true
% 7.44/1.49  --inst_sos_phase                        true
% 7.44/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.44/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.44/1.49  --inst_lit_sel_side                     none
% 7.44/1.49  --inst_solver_per_active                1400
% 7.44/1.49  --inst_solver_calls_frac                1.
% 7.44/1.49  --inst_passive_queue_type               priority_queues
% 7.44/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.44/1.49  --inst_passive_queues_freq              [25;2]
% 7.44/1.49  --inst_dismatching                      true
% 7.44/1.49  --inst_eager_unprocessed_to_passive     true
% 7.44/1.49  --inst_prop_sim_given                   true
% 7.44/1.49  --inst_prop_sim_new                     false
% 7.44/1.49  --inst_subs_new                         false
% 7.44/1.49  --inst_eq_res_simp                      false
% 7.44/1.49  --inst_subs_given                       false
% 7.44/1.49  --inst_orphan_elimination               true
% 7.44/1.49  --inst_learning_loop_flag               true
% 7.44/1.49  --inst_learning_start                   3000
% 7.44/1.49  --inst_learning_factor                  2
% 7.44/1.49  --inst_start_prop_sim_after_learn       3
% 7.44/1.49  --inst_sel_renew                        solver
% 7.44/1.49  --inst_lit_activity_flag                true
% 7.44/1.49  --inst_restr_to_given                   false
% 7.44/1.49  --inst_activity_threshold               500
% 7.44/1.49  --inst_out_proof                        true
% 7.44/1.49  
% 7.44/1.49  ------ Resolution Options
% 7.44/1.49  
% 7.44/1.49  --resolution_flag                       false
% 7.44/1.49  --res_lit_sel                           adaptive
% 7.44/1.49  --res_lit_sel_side                      none
% 7.44/1.49  --res_ordering                          kbo
% 7.44/1.49  --res_to_prop_solver                    active
% 7.44/1.49  --res_prop_simpl_new                    false
% 7.44/1.49  --res_prop_simpl_given                  true
% 7.44/1.49  --res_passive_queue_type                priority_queues
% 7.44/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.44/1.49  --res_passive_queues_freq               [15;5]
% 7.44/1.49  --res_forward_subs                      full
% 7.44/1.49  --res_backward_subs                     full
% 7.44/1.49  --res_forward_subs_resolution           true
% 7.44/1.49  --res_backward_subs_resolution          true
% 7.44/1.49  --res_orphan_elimination                true
% 7.44/1.49  --res_time_limit                        2.
% 7.44/1.49  --res_out_proof                         true
% 7.44/1.49  
% 7.44/1.49  ------ Superposition Options
% 7.44/1.49  
% 7.44/1.49  --superposition_flag                    true
% 7.44/1.49  --sup_passive_queue_type                priority_queues
% 7.44/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.44/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.44/1.49  --demod_completeness_check              fast
% 7.44/1.49  --demod_use_ground                      true
% 7.44/1.49  --sup_to_prop_solver                    passive
% 7.44/1.49  --sup_prop_simpl_new                    true
% 7.44/1.49  --sup_prop_simpl_given                  true
% 7.44/1.49  --sup_fun_splitting                     true
% 7.44/1.49  --sup_smt_interval                      50000
% 7.44/1.49  
% 7.44/1.49  ------ Superposition Simplification Setup
% 7.44/1.49  
% 7.44/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.44/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.44/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.44/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.44/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.44/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.44/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.44/1.49  --sup_immed_triv                        [TrivRules]
% 7.44/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.44/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.44/1.49  --sup_immed_bw_main                     []
% 7.44/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.44/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.44/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.44/1.49  --sup_input_bw                          []
% 7.44/1.49  
% 7.44/1.49  ------ Combination Options
% 7.44/1.49  
% 7.44/1.49  --comb_res_mult                         3
% 7.44/1.49  --comb_sup_mult                         2
% 7.44/1.49  --comb_inst_mult                        10
% 7.44/1.49  
% 7.44/1.49  ------ Debug Options
% 7.44/1.49  
% 7.44/1.49  --dbg_backtrace                         false
% 7.44/1.49  --dbg_dump_prop_clauses                 false
% 7.44/1.49  --dbg_dump_prop_clauses_file            -
% 7.44/1.49  --dbg_out_stat                          false
% 7.44/1.49  
% 7.44/1.49  
% 7.44/1.49  
% 7.44/1.49  
% 7.44/1.49  ------ Proving...
% 7.44/1.49  
% 7.44/1.49  
% 7.44/1.49  % SZS status Theorem for theBenchmark.p
% 7.44/1.49  
% 7.44/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.44/1.49  
% 7.44/1.49  fof(f1,axiom,(
% 7.44/1.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 7.44/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.44/1.49  
% 7.44/1.49  fof(f15,plain,(
% 7.44/1.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 7.44/1.49    inference(rectify,[],[f1])).
% 7.44/1.49  
% 7.44/1.49  fof(f16,plain,(
% 7.44/1.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 7.44/1.49    inference(ennf_transformation,[],[f15])).
% 7.44/1.49  
% 7.44/1.49  fof(f36,plain,(
% 7.44/1.49    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.44/1.49    introduced(choice_axiom,[])).
% 7.44/1.49  
% 7.44/1.49  fof(f37,plain,(
% 7.44/1.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 7.44/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f36])).
% 7.44/1.49  
% 7.44/1.49  fof(f51,plain,(
% 7.44/1.49    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 7.44/1.49    inference(cnf_transformation,[],[f37])).
% 7.44/1.49  
% 7.44/1.49  fof(f2,axiom,(
% 7.44/1.49    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 7.44/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.44/1.49  
% 7.44/1.49  fof(f38,plain,(
% 7.44/1.49    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 7.44/1.49    inference(nnf_transformation,[],[f2])).
% 7.44/1.49  
% 7.44/1.49  fof(f39,plain,(
% 7.44/1.49    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 7.44/1.49    inference(rectify,[],[f38])).
% 7.44/1.49  
% 7.44/1.49  fof(f40,plain,(
% 7.44/1.49    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1))))),
% 7.44/1.49    introduced(choice_axiom,[])).
% 7.44/1.49  
% 7.44/1.49  fof(f41,plain,(
% 7.44/1.49    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 7.44/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f39,f40])).
% 7.44/1.49  
% 7.44/1.49  fof(f53,plain,(
% 7.44/1.49    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 7.44/1.49    inference(cnf_transformation,[],[f41])).
% 7.44/1.49  
% 7.44/1.49  fof(f3,axiom,(
% 7.44/1.49    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 7.44/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.44/1.49  
% 7.44/1.49  fof(f57,plain,(
% 7.44/1.49    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 7.44/1.49    inference(cnf_transformation,[],[f3])).
% 7.44/1.49  
% 7.44/1.49  fof(f81,plain,(
% 7.44/1.49    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_tarski(X0,X0) != X1) )),
% 7.44/1.49    inference(definition_unfolding,[],[f53,f57])).
% 7.44/1.49  
% 7.44/1.49  fof(f85,plain,(
% 7.44/1.49    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k2_tarski(X0,X0))) )),
% 7.44/1.49    inference(equality_resolution,[],[f81])).
% 7.44/1.49  
% 7.44/1.49  fof(f9,axiom,(
% 7.44/1.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_pre_topc(X0,X1),X0))),
% 7.44/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.44/1.49  
% 7.44/1.49  fof(f26,plain,(
% 7.44/1.49    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.44/1.49    inference(ennf_transformation,[],[f9])).
% 7.44/1.49  
% 7.44/1.49  fof(f27,plain,(
% 7.44/1.49    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.44/1.49    inference(flattening,[],[f26])).
% 7.44/1.49  
% 7.44/1.49  fof(f63,plain,(
% 7.44/1.49    ( ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.44/1.49    inference(cnf_transformation,[],[f27])).
% 7.44/1.49  
% 7.44/1.49  fof(f10,axiom,(
% 7.44/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v3_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => v3_pre_topc(X1,X0)))))),
% 7.44/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.44/1.49  
% 7.44/1.49  fof(f28,plain,(
% 7.44/1.49    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : ((v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.44/1.49    inference(ennf_transformation,[],[f10])).
% 7.44/1.49  
% 7.44/1.49  fof(f29,plain,(
% 7.44/1.49    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.44/1.49    inference(flattening,[],[f28])).
% 7.44/1.49  
% 7.44/1.49  fof(f42,plain,(
% 7.44/1.49    ! [X0] : (((v3_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X1] : (v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.44/1.49    inference(nnf_transformation,[],[f29])).
% 7.44/1.49  
% 7.44/1.49  fof(f43,plain,(
% 7.44/1.49    ! [X0] : (((v3_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.44/1.49    inference(rectify,[],[f42])).
% 7.44/1.49  
% 7.44/1.49  fof(f44,plain,(
% 7.44/1.49    ! [X0] : (? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK2(X0),X0) & v4_pre_topc(sK2(X0),X0) & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 7.44/1.49    introduced(choice_axiom,[])).
% 7.44/1.49  
% 7.44/1.49  fof(f45,plain,(
% 7.44/1.49    ! [X0] : (((v3_tdlat_3(X0) | (~v3_pre_topc(sK2(X0),X0) & v4_pre_topc(sK2(X0),X0) & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.44/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f43,f44])).
% 7.44/1.49  
% 7.44/1.49  fof(f64,plain,(
% 7.44/1.49    ( ! [X2,X0] : (v3_pre_topc(X2,X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tdlat_3(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.44/1.49    inference(cnf_transformation,[],[f45])).
% 7.44/1.49  
% 7.44/1.49  fof(f4,axiom,(
% 7.44/1.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 7.44/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.44/1.49  
% 7.44/1.49  fof(f17,plain,(
% 7.44/1.49    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 7.44/1.49    inference(ennf_transformation,[],[f4])).
% 7.44/1.49  
% 7.44/1.49  fof(f18,plain,(
% 7.44/1.49    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 7.44/1.49    inference(flattening,[],[f17])).
% 7.44/1.49  
% 7.44/1.49  fof(f58,plain,(
% 7.44/1.49    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.44/1.49    inference(cnf_transformation,[],[f18])).
% 7.44/1.49  
% 7.44/1.49  fof(f13,conjecture,(
% 7.44/1.49    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) | r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))))))),
% 7.44/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.44/1.49  
% 7.44/1.49  fof(f14,negated_conjecture,(
% 7.44/1.49    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) | r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))))))),
% 7.44/1.49    inference(negated_conjecture,[],[f13])).
% 7.44/1.49  
% 7.44/1.49  fof(f34,plain,(
% 7.44/1.49    ? [X0] : (? [X1] : (? [X2] : ((k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 7.44/1.49    inference(ennf_transformation,[],[f14])).
% 7.44/1.49  
% 7.44/1.49  fof(f35,plain,(
% 7.44/1.49    ? [X0] : (? [X1] : (? [X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.44/1.49    inference(flattening,[],[f34])).
% 7.44/1.49  
% 7.44/1.49  fof(f48,plain,(
% 7.44/1.49    ( ! [X0,X1] : (? [X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & m1_subset_1(X2,u1_struct_0(X0))) => (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK5)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK5))) & m1_subset_1(sK5,u1_struct_0(X0)))) )),
% 7.44/1.49    introduced(choice_axiom,[])).
% 7.44/1.49  
% 7.44/1.49  fof(f47,plain,(
% 7.44/1.49    ( ! [X0] : (? [X1] : (? [X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK4)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK4)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK4,u1_struct_0(X0)))) )),
% 7.44/1.49    introduced(choice_axiom,[])).
% 7.44/1.49  
% 7.44/1.49  fof(f46,plain,(
% 7.44/1.49    ? [X0] : (? [X1] : (? [X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),X1)) != k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),X2)) & ~r1_xboole_0(k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),X1)),k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),X2))) & m1_subset_1(X2,u1_struct_0(sK3))) & m1_subset_1(X1,u1_struct_0(sK3))) & l1_pre_topc(sK3) & v3_tdlat_3(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 7.44/1.49    introduced(choice_axiom,[])).
% 7.44/1.49  
% 7.44/1.49  fof(f49,plain,(
% 7.44/1.49    ((k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK4)) != k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5)) & ~r1_xboole_0(k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK4)),k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) & m1_subset_1(sK5,u1_struct_0(sK3))) & m1_subset_1(sK4,u1_struct_0(sK3))) & l1_pre_topc(sK3) & v3_tdlat_3(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 7.44/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f35,f48,f47,f46])).
% 7.44/1.49  
% 7.44/1.49  fof(f71,plain,(
% 7.44/1.49    v2_pre_topc(sK3)),
% 7.44/1.49    inference(cnf_transformation,[],[f49])).
% 7.44/1.49  
% 7.44/1.49  fof(f72,plain,(
% 7.44/1.49    v3_tdlat_3(sK3)),
% 7.44/1.49    inference(cnf_transformation,[],[f49])).
% 7.44/1.49  
% 7.44/1.49  fof(f73,plain,(
% 7.44/1.49    l1_pre_topc(sK3)),
% 7.44/1.49    inference(cnf_transformation,[],[f49])).
% 7.44/1.49  
% 7.44/1.49  fof(f11,axiom,(
% 7.44/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X1,X0) & r1_xboole_0(X1,X2)) => r1_xboole_0(X1,k2_pre_topc(X0,X2))))))),
% 7.44/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.44/1.49  
% 7.44/1.49  fof(f30,plain,(
% 7.44/1.49    ! [X0] : (! [X1] : (! [X2] : ((r1_xboole_0(X1,k2_pre_topc(X0,X2)) | (~v3_pre_topc(X1,X0) | ~r1_xboole_0(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.44/1.49    inference(ennf_transformation,[],[f11])).
% 7.44/1.49  
% 7.44/1.49  fof(f31,plain,(
% 7.44/1.49    ! [X0] : (! [X1] : (! [X2] : (r1_xboole_0(X1,k2_pre_topc(X0,X2)) | ~v3_pre_topc(X1,X0) | ~r1_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.44/1.49    inference(flattening,[],[f30])).
% 7.44/1.49  
% 7.44/1.49  fof(f68,plain,(
% 7.44/1.49    ( ! [X2,X0,X1] : (r1_xboole_0(X1,k2_pre_topc(X0,X2)) | ~v3_pre_topc(X1,X0) | ~r1_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.44/1.49    inference(cnf_transformation,[],[f31])).
% 7.44/1.49  
% 7.44/1.49  fof(f75,plain,(
% 7.44/1.49    m1_subset_1(sK5,u1_struct_0(sK3))),
% 7.44/1.49    inference(cnf_transformation,[],[f49])).
% 7.44/1.49  
% 7.44/1.49  fof(f8,axiom,(
% 7.44/1.49    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 7.44/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.44/1.49  
% 7.44/1.49  fof(f24,plain,(
% 7.44/1.49    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 7.44/1.49    inference(ennf_transformation,[],[f8])).
% 7.44/1.49  
% 7.44/1.49  fof(f25,plain,(
% 7.44/1.49    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 7.44/1.49    inference(flattening,[],[f24])).
% 7.44/1.49  
% 7.44/1.49  fof(f62,plain,(
% 7.44/1.49    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 7.44/1.49    inference(cnf_transformation,[],[f25])).
% 7.44/1.49  
% 7.44/1.49  fof(f82,plain,(
% 7.44/1.49    ( ! [X0,X1] : (k2_tarski(X1,X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 7.44/1.49    inference(definition_unfolding,[],[f62,f57])).
% 7.44/1.49  
% 7.44/1.49  fof(f5,axiom,(
% 7.44/1.49    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 7.44/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.44/1.49  
% 7.44/1.49  fof(f19,plain,(
% 7.44/1.49    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 7.44/1.49    inference(ennf_transformation,[],[f5])).
% 7.44/1.49  
% 7.44/1.49  fof(f59,plain,(
% 7.44/1.49    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 7.44/1.49    inference(cnf_transformation,[],[f19])).
% 7.44/1.49  
% 7.44/1.49  fof(f6,axiom,(
% 7.44/1.49    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 7.44/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.44/1.49  
% 7.44/1.49  fof(f20,plain,(
% 7.44/1.49    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 7.44/1.49    inference(ennf_transformation,[],[f6])).
% 7.44/1.49  
% 7.44/1.49  fof(f21,plain,(
% 7.44/1.49    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 7.44/1.49    inference(flattening,[],[f20])).
% 7.44/1.49  
% 7.44/1.49  fof(f60,plain,(
% 7.44/1.49    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 7.44/1.49    inference(cnf_transformation,[],[f21])).
% 7.44/1.49  
% 7.44/1.49  fof(f70,plain,(
% 7.44/1.49    ~v2_struct_0(sK3)),
% 7.44/1.49    inference(cnf_transformation,[],[f49])).
% 7.44/1.49  
% 7.44/1.49  fof(f76,plain,(
% 7.44/1.49    ~r1_xboole_0(k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK4)),k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5)))),
% 7.44/1.49    inference(cnf_transformation,[],[f49])).
% 7.44/1.49  
% 7.44/1.49  fof(f74,plain,(
% 7.44/1.49    m1_subset_1(sK4,u1_struct_0(sK3))),
% 7.44/1.49    inference(cnf_transformation,[],[f49])).
% 7.44/1.49  
% 7.44/1.49  fof(f7,axiom,(
% 7.44/1.49    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 7.44/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.44/1.49  
% 7.44/1.49  fof(f22,plain,(
% 7.44/1.49    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 7.44/1.49    inference(ennf_transformation,[],[f7])).
% 7.44/1.49  
% 7.44/1.49  fof(f23,plain,(
% 7.44/1.49    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 7.44/1.49    inference(flattening,[],[f22])).
% 7.44/1.49  
% 7.44/1.49  fof(f61,plain,(
% 7.44/1.49    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 7.44/1.49    inference(cnf_transformation,[],[f23])).
% 7.44/1.49  
% 7.44/1.49  fof(f50,plain,(
% 7.44/1.49    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 7.44/1.49    inference(cnf_transformation,[],[f37])).
% 7.44/1.49  
% 7.44/1.49  fof(f12,axiom,(
% 7.44/1.49    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) => k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))))))),
% 7.44/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.44/1.49  
% 7.44/1.49  fof(f32,plain,(
% 7.44/1.49    ! [X0] : (! [X1] : (! [X2] : ((k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) | ~r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.44/1.49    inference(ennf_transformation,[],[f12])).
% 7.44/1.49  
% 7.44/1.49  fof(f33,plain,(
% 7.44/1.49    ! [X0] : (! [X1] : (! [X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) | ~r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.44/1.49    inference(flattening,[],[f32])).
% 7.44/1.49  
% 7.44/1.49  fof(f69,plain,(
% 7.44/1.49    ( ! [X2,X0,X1] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) | ~r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.44/1.49    inference(cnf_transformation,[],[f33])).
% 7.44/1.49  
% 7.44/1.49  fof(f77,plain,(
% 7.44/1.49    k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK4)) != k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5))),
% 7.44/1.49    inference(cnf_transformation,[],[f49])).
% 7.44/1.49  
% 7.44/1.49  cnf(c_1,plain,
% 7.44/1.49      ( r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1) ),
% 7.44/1.49      inference(cnf_transformation,[],[f51]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_945,plain,
% 7.44/1.49      ( r2_hidden(sK0(X0,X1),X1) = iProver_top
% 7.44/1.49      | r1_xboole_0(X0,X1) = iProver_top ),
% 7.44/1.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_6,plain,
% 7.44/1.49      ( ~ r2_hidden(X0,k2_tarski(X1,X1)) | X0 = X1 ),
% 7.44/1.49      inference(cnf_transformation,[],[f85]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_940,plain,
% 7.44/1.49      ( X0 = X1 | r2_hidden(X0,k2_tarski(X1,X1)) != iProver_top ),
% 7.44/1.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_1619,plain,
% 7.44/1.49      ( sK0(X0,k2_tarski(X1,X1)) = X1
% 7.44/1.49      | r1_xboole_0(X0,k2_tarski(X1,X1)) = iProver_top ),
% 7.44/1.49      inference(superposition,[status(thm)],[c_945,c_940]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_12,plain,
% 7.44/1.49      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
% 7.44/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 7.44/1.49      | ~ v2_pre_topc(X0)
% 7.44/1.49      | ~ l1_pre_topc(X0) ),
% 7.44/1.49      inference(cnf_transformation,[],[f63]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_16,plain,
% 7.44/1.49      ( v3_pre_topc(X0,X1)
% 7.44/1.49      | ~ v4_pre_topc(X0,X1)
% 7.44/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.44/1.49      | ~ v3_tdlat_3(X1)
% 7.44/1.49      | ~ v2_pre_topc(X1)
% 7.44/1.49      | ~ l1_pre_topc(X1) ),
% 7.44/1.49      inference(cnf_transformation,[],[f64]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_420,plain,
% 7.44/1.49      ( v3_pre_topc(X0,X1)
% 7.44/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 7.44/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.44/1.49      | ~ v3_tdlat_3(X1)
% 7.44/1.49      | ~ v2_pre_topc(X3)
% 7.44/1.49      | ~ v2_pre_topc(X1)
% 7.44/1.49      | ~ l1_pre_topc(X3)
% 7.44/1.49      | ~ l1_pre_topc(X1)
% 7.44/1.49      | X1 != X3
% 7.44/1.49      | k2_pre_topc(X3,X2) != X0 ),
% 7.44/1.49      inference(resolution_lifted,[status(thm)],[c_12,c_16]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_421,plain,
% 7.44/1.49      ( v3_pre_topc(k2_pre_topc(X0,X1),X0)
% 7.44/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 7.44/1.49      | ~ m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
% 7.44/1.49      | ~ v3_tdlat_3(X0)
% 7.44/1.49      | ~ v2_pre_topc(X0)
% 7.44/1.49      | ~ l1_pre_topc(X0) ),
% 7.44/1.49      inference(unflattening,[status(thm)],[c_420]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_7,plain,
% 7.44/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.44/1.49      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.44/1.49      | ~ l1_pre_topc(X1) ),
% 7.44/1.49      inference(cnf_transformation,[],[f58]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_437,plain,
% 7.44/1.49      ( v3_pre_topc(k2_pre_topc(X0,X1),X0)
% 7.44/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 7.44/1.49      | ~ v3_tdlat_3(X0)
% 7.44/1.49      | ~ v2_pre_topc(X0)
% 7.44/1.49      | ~ l1_pre_topc(X0) ),
% 7.44/1.49      inference(forward_subsumption_resolution,[status(thm)],[c_421,c_7]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_25,negated_conjecture,
% 7.44/1.49      ( v2_pre_topc(sK3) ),
% 7.44/1.49      inference(cnf_transformation,[],[f71]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_454,plain,
% 7.44/1.49      ( v3_pre_topc(k2_pre_topc(X0,X1),X0)
% 7.44/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 7.44/1.49      | ~ v3_tdlat_3(X0)
% 7.44/1.49      | ~ l1_pre_topc(X0)
% 7.44/1.49      | sK3 != X0 ),
% 7.44/1.49      inference(resolution_lifted,[status(thm)],[c_437,c_25]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_455,plain,
% 7.44/1.49      ( v3_pre_topc(k2_pre_topc(sK3,X0),sK3)
% 7.44/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 7.44/1.49      | ~ v3_tdlat_3(sK3)
% 7.44/1.49      | ~ l1_pre_topc(sK3) ),
% 7.44/1.49      inference(unflattening,[status(thm)],[c_454]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_24,negated_conjecture,
% 7.44/1.49      ( v3_tdlat_3(sK3) ),
% 7.44/1.49      inference(cnf_transformation,[],[f72]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_23,negated_conjecture,
% 7.44/1.49      ( l1_pre_topc(sK3) ),
% 7.44/1.49      inference(cnf_transformation,[],[f73]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_459,plain,
% 7.44/1.49      ( v3_pre_topc(k2_pre_topc(sK3,X0),sK3)
% 7.44/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 7.44/1.49      inference(global_propositional_subsumption,
% 7.44/1.49                [status(thm)],
% 7.44/1.49                [c_455,c_24,c_23]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_17,plain,
% 7.44/1.49      ( ~ v3_pre_topc(X0,X1)
% 7.44/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.44/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 7.44/1.49      | ~ r1_xboole_0(X0,X2)
% 7.44/1.49      | r1_xboole_0(X0,k2_pre_topc(X1,X2))
% 7.44/1.49      | ~ v2_pre_topc(X1)
% 7.44/1.49      | ~ l1_pre_topc(X1) ),
% 7.44/1.49      inference(cnf_transformation,[],[f68]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_476,plain,
% 7.44/1.49      ( ~ v3_pre_topc(X0,X1)
% 7.44/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.44/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 7.44/1.49      | ~ r1_xboole_0(X0,X2)
% 7.44/1.49      | r1_xboole_0(X0,k2_pre_topc(X1,X2))
% 7.44/1.49      | ~ l1_pre_topc(X1)
% 7.44/1.49      | sK3 != X1 ),
% 7.44/1.49      inference(resolution_lifted,[status(thm)],[c_17,c_25]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_477,plain,
% 7.44/1.49      ( ~ v3_pre_topc(X0,sK3)
% 7.44/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 7.44/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 7.44/1.49      | ~ r1_xboole_0(X0,X1)
% 7.44/1.49      | r1_xboole_0(X0,k2_pre_topc(sK3,X1))
% 7.44/1.49      | ~ l1_pre_topc(sK3) ),
% 7.44/1.49      inference(unflattening,[status(thm)],[c_476]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_481,plain,
% 7.44/1.49      ( r1_xboole_0(X0,k2_pre_topc(sK3,X1))
% 7.44/1.49      | ~ r1_xboole_0(X0,X1)
% 7.44/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 7.44/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 7.44/1.49      | ~ v3_pre_topc(X0,sK3) ),
% 7.44/1.49      inference(global_propositional_subsumption,
% 7.44/1.49                [status(thm)],
% 7.44/1.49                [c_477,c_23]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_482,plain,
% 7.44/1.49      ( ~ v3_pre_topc(X0,sK3)
% 7.44/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 7.44/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 7.44/1.49      | ~ r1_xboole_0(X0,X1)
% 7.44/1.49      | r1_xboole_0(X0,k2_pre_topc(sK3,X1)) ),
% 7.44/1.49      inference(renaming,[status(thm)],[c_481]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_527,plain,
% 7.44/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 7.44/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 7.44/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 7.44/1.49      | ~ r1_xboole_0(X0,X2)
% 7.44/1.49      | r1_xboole_0(X0,k2_pre_topc(sK3,X2))
% 7.44/1.49      | k2_pre_topc(sK3,X1) != X0
% 7.44/1.49      | sK3 != sK3 ),
% 7.44/1.49      inference(resolution_lifted,[status(thm)],[c_459,c_482]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_528,plain,
% 7.44/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 7.44/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 7.44/1.49      | ~ m1_subset_1(k2_pre_topc(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3)))
% 7.44/1.49      | ~ r1_xboole_0(k2_pre_topc(sK3,X0),X1)
% 7.44/1.49      | r1_xboole_0(k2_pre_topc(sK3,X0),k2_pre_topc(sK3,X1)) ),
% 7.44/1.49      inference(unflattening,[status(thm)],[c_527]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_512,plain,
% 7.44/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.44/1.49      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.44/1.49      | sK3 != X1 ),
% 7.44/1.49      inference(resolution_lifted,[status(thm)],[c_7,c_23]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_513,plain,
% 7.44/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 7.44/1.49      | m1_subset_1(k2_pre_topc(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 7.44/1.49      inference(unflattening,[status(thm)],[c_512]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_532,plain,
% 7.44/1.49      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 7.44/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 7.44/1.49      | ~ r1_xboole_0(k2_pre_topc(sK3,X0),X1)
% 7.44/1.49      | r1_xboole_0(k2_pre_topc(sK3,X0),k2_pre_topc(sK3,X1)) ),
% 7.44/1.49      inference(global_propositional_subsumption,
% 7.44/1.49                [status(thm)],
% 7.44/1.49                [c_528,c_513]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_533,plain,
% 7.44/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 7.44/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 7.44/1.49      | ~ r1_xboole_0(k2_pre_topc(sK3,X1),X0)
% 7.44/1.49      | r1_xboole_0(k2_pre_topc(sK3,X1),k2_pre_topc(sK3,X0)) ),
% 7.44/1.49      inference(renaming,[status(thm)],[c_532]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_932,plain,
% 7.44/1.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 7.44/1.49      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 7.44/1.49      | r1_xboole_0(k2_pre_topc(sK3,X1),X0) != iProver_top
% 7.44/1.49      | r1_xboole_0(k2_pre_topc(sK3,X1),k2_pre_topc(sK3,X0)) = iProver_top ),
% 7.44/1.49      inference(predicate_to_equality,[status(thm)],[c_533]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_21,negated_conjecture,
% 7.44/1.49      ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
% 7.44/1.49      inference(cnf_transformation,[],[f75]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_938,plain,
% 7.44/1.49      ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
% 7.44/1.49      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_11,plain,
% 7.44/1.49      ( ~ m1_subset_1(X0,X1)
% 7.44/1.49      | v1_xboole_0(X1)
% 7.44/1.49      | k6_domain_1(X1,X0) = k2_tarski(X0,X0) ),
% 7.44/1.49      inference(cnf_transformation,[],[f82]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_8,plain,
% 7.44/1.49      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 7.44/1.49      inference(cnf_transformation,[],[f59]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_9,plain,
% 7.44/1.49      ( v2_struct_0(X0)
% 7.44/1.49      | ~ v1_xboole_0(u1_struct_0(X0))
% 7.44/1.49      | ~ l1_struct_0(X0) ),
% 7.44/1.49      inference(cnf_transformation,[],[f60]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_286,plain,
% 7.44/1.49      ( v2_struct_0(X0)
% 7.44/1.49      | ~ v1_xboole_0(u1_struct_0(X0))
% 7.44/1.49      | ~ l1_pre_topc(X0) ),
% 7.44/1.49      inference(resolution,[status(thm)],[c_8,c_9]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_26,negated_conjecture,
% 7.44/1.49      ( ~ v2_struct_0(sK3) ),
% 7.44/1.49      inference(cnf_transformation,[],[f70]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_348,plain,
% 7.44/1.49      ( ~ v1_xboole_0(u1_struct_0(X0)) | ~ l1_pre_topc(X0) | sK3 != X0 ),
% 7.44/1.49      inference(resolution_lifted,[status(thm)],[c_286,c_26]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_349,plain,
% 7.44/1.49      ( ~ v1_xboole_0(u1_struct_0(sK3)) | ~ l1_pre_topc(sK3) ),
% 7.44/1.49      inference(unflattening,[status(thm)],[c_348]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_56,plain,
% 7.44/1.49      ( v2_struct_0(sK3)
% 7.44/1.49      | ~ v1_xboole_0(u1_struct_0(sK3))
% 7.44/1.49      | ~ l1_struct_0(sK3) ),
% 7.44/1.49      inference(instantiation,[status(thm)],[c_9]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_59,plain,
% 7.44/1.49      ( l1_struct_0(sK3) | ~ l1_pre_topc(sK3) ),
% 7.44/1.49      inference(instantiation,[status(thm)],[c_8]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_351,plain,
% 7.44/1.49      ( ~ v1_xboole_0(u1_struct_0(sK3)) ),
% 7.44/1.49      inference(global_propositional_subsumption,
% 7.44/1.49                [status(thm)],
% 7.44/1.49                [c_349,c_26,c_23,c_56,c_59]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_390,plain,
% 7.44/1.49      ( ~ m1_subset_1(X0,X1)
% 7.44/1.49      | k6_domain_1(X1,X0) = k2_tarski(X0,X0)
% 7.44/1.49      | u1_struct_0(sK3) != X1 ),
% 7.44/1.49      inference(resolution_lifted,[status(thm)],[c_11,c_351]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_391,plain,
% 7.44/1.49      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 7.44/1.49      | k6_domain_1(u1_struct_0(sK3),X0) = k2_tarski(X0,X0) ),
% 7.44/1.49      inference(unflattening,[status(thm)],[c_390]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_935,plain,
% 7.44/1.49      ( k6_domain_1(u1_struct_0(sK3),X0) = k2_tarski(X0,X0)
% 7.44/1.49      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
% 7.44/1.49      inference(predicate_to_equality,[status(thm)],[c_391]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_1312,plain,
% 7.44/1.49      ( k6_domain_1(u1_struct_0(sK3),sK5) = k2_tarski(sK5,sK5) ),
% 7.44/1.49      inference(superposition,[status(thm)],[c_938,c_935]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_20,negated_conjecture,
% 7.44/1.49      ( ~ r1_xboole_0(k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK4)),k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) ),
% 7.44/1.49      inference(cnf_transformation,[],[f76]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_939,plain,
% 7.44/1.49      ( r1_xboole_0(k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK4)),k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) != iProver_top ),
% 7.44/1.49      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_1314,plain,
% 7.44/1.49      ( r1_xboole_0(k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK4)),k2_pre_topc(sK3,k2_tarski(sK5,sK5))) != iProver_top ),
% 7.44/1.49      inference(demodulation,[status(thm)],[c_1312,c_939]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_22,negated_conjecture,
% 7.44/1.49      ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 7.44/1.49      inference(cnf_transformation,[],[f74]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_937,plain,
% 7.44/1.49      ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
% 7.44/1.49      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_1313,plain,
% 7.44/1.49      ( k6_domain_1(u1_struct_0(sK3),sK4) = k2_tarski(sK4,sK4) ),
% 7.44/1.49      inference(superposition,[status(thm)],[c_937,c_935]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_1317,plain,
% 7.44/1.49      ( r1_xboole_0(k2_pre_topc(sK3,k2_tarski(sK4,sK4)),k2_pre_topc(sK3,k2_tarski(sK5,sK5))) != iProver_top ),
% 7.44/1.49      inference(light_normalisation,[status(thm)],[c_1314,c_1313]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_1730,plain,
% 7.44/1.49      ( m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 7.44/1.49      | m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 7.44/1.49      | r1_xboole_0(k2_pre_topc(sK3,k2_tarski(sK4,sK4)),k2_tarski(sK5,sK5)) != iProver_top ),
% 7.44/1.49      inference(superposition,[status(thm)],[c_932,c_1317]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_31,plain,
% 7.44/1.49      ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
% 7.44/1.49      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_32,plain,
% 7.44/1.49      ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
% 7.44/1.49      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_10,plain,
% 7.44/1.49      ( ~ m1_subset_1(X0,X1)
% 7.44/1.49      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
% 7.44/1.49      | v1_xboole_0(X1) ),
% 7.44/1.49      inference(cnf_transformation,[],[f61]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_402,plain,
% 7.44/1.49      ( ~ m1_subset_1(X0,X1)
% 7.44/1.49      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
% 7.44/1.49      | u1_struct_0(sK3) != X1 ),
% 7.44/1.49      inference(resolution_lifted,[status(thm)],[c_10,c_351]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_403,plain,
% 7.44/1.49      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 7.44/1.49      | m1_subset_1(k6_domain_1(u1_struct_0(sK3),X0),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 7.44/1.49      inference(unflattening,[status(thm)],[c_402]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_934,plain,
% 7.44/1.49      ( m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 7.44/1.49      | m1_subset_1(k6_domain_1(u1_struct_0(sK3),X0),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 7.44/1.49      inference(predicate_to_equality,[status(thm)],[c_403]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_1891,plain,
% 7.44/1.49      ( m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 7.44/1.49      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
% 7.44/1.49      inference(superposition,[status(thm)],[c_1313,c_934]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_1892,plain,
% 7.44/1.49      ( m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 7.44/1.49      | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top ),
% 7.44/1.49      inference(superposition,[status(thm)],[c_1312,c_934]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_2589,plain,
% 7.44/1.49      ( r1_xboole_0(k2_pre_topc(sK3,k2_tarski(sK4,sK4)),k2_tarski(sK5,sK5)) != iProver_top ),
% 7.44/1.49      inference(global_propositional_subsumption,
% 7.44/1.49                [status(thm)],
% 7.44/1.49                [c_1730,c_31,c_32,c_1891,c_1892]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_2594,plain,
% 7.44/1.49      ( sK0(k2_pre_topc(sK3,k2_tarski(sK4,sK4)),k2_tarski(sK5,sK5)) = sK5 ),
% 7.44/1.49      inference(superposition,[status(thm)],[c_1619,c_2589]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_2,plain,
% 7.44/1.49      ( r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1) ),
% 7.44/1.49      inference(cnf_transformation,[],[f50]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_944,plain,
% 7.44/1.49      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 7.44/1.49      | r1_xboole_0(X0,X1) = iProver_top ),
% 7.44/1.49      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_18,plain,
% 7.44/1.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.44/1.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.44/1.49      | ~ r2_hidden(X2,k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X0)))
% 7.44/1.49      | ~ v3_tdlat_3(X1)
% 7.44/1.49      | ~ v2_pre_topc(X1)
% 7.44/1.49      | v2_struct_0(X1)
% 7.44/1.49      | ~ l1_pre_topc(X1)
% 7.44/1.49      | k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X0)) = k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2)) ),
% 7.44/1.49      inference(cnf_transformation,[],[f69]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_359,plain,
% 7.44/1.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.44/1.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.44/1.49      | ~ r2_hidden(X2,k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X0)))
% 7.44/1.49      | ~ v3_tdlat_3(X1)
% 7.44/1.49      | ~ v2_pre_topc(X1)
% 7.44/1.49      | ~ l1_pre_topc(X1)
% 7.44/1.49      | k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2)) = k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X0))
% 7.44/1.49      | sK3 != X1 ),
% 7.44/1.49      inference(resolution_lifted,[status(thm)],[c_18,c_26]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_360,plain,
% 7.44/1.49      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 7.44/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 7.44/1.49      | ~ r2_hidden(X0,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),X1)))
% 7.44/1.49      | ~ v3_tdlat_3(sK3)
% 7.44/1.49      | ~ v2_pre_topc(sK3)
% 7.44/1.49      | ~ l1_pre_topc(sK3)
% 7.44/1.49      | k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),X0)) = k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),X1)) ),
% 7.44/1.49      inference(unflattening,[status(thm)],[c_359]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_364,plain,
% 7.44/1.49      ( ~ r2_hidden(X0,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),X1)))
% 7.44/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 7.44/1.49      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 7.44/1.49      | k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),X0)) = k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),X1)) ),
% 7.44/1.49      inference(global_propositional_subsumption,
% 7.44/1.49                [status(thm)],
% 7.44/1.49                [c_360,c_25,c_24,c_23]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_365,plain,
% 7.44/1.49      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 7.44/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 7.44/1.49      | ~ r2_hidden(X0,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),X1)))
% 7.44/1.49      | k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),X0)) = k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),X1)) ),
% 7.44/1.49      inference(renaming,[status(thm)],[c_364]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_936,plain,
% 7.44/1.49      ( k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),X0)) = k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),X1))
% 7.44/1.49      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 7.44/1.49      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
% 7.44/1.49      | r2_hidden(X0,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),X1))) != iProver_top ),
% 7.44/1.49      inference(predicate_to_equality,[status(thm)],[c_365]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_1627,plain,
% 7.44/1.49      ( k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),X0)) = k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK4))
% 7.44/1.49      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 7.44/1.49      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 7.44/1.49      | r2_hidden(X0,k2_pre_topc(sK3,k2_tarski(sK4,sK4))) != iProver_top ),
% 7.44/1.49      inference(superposition,[status(thm)],[c_1313,c_936]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_1628,plain,
% 7.44/1.49      ( k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),X0)) = k2_pre_topc(sK3,k2_tarski(sK4,sK4))
% 7.44/1.49      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 7.44/1.49      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 7.44/1.49      | r2_hidden(X0,k2_pre_topc(sK3,k2_tarski(sK4,sK4))) != iProver_top ),
% 7.44/1.49      inference(light_normalisation,[status(thm)],[c_1627,c_1313]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_2116,plain,
% 7.44/1.49      ( m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 7.44/1.49      | k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),X0)) = k2_pre_topc(sK3,k2_tarski(sK4,sK4))
% 7.44/1.49      | r2_hidden(X0,k2_pre_topc(sK3,k2_tarski(sK4,sK4))) != iProver_top ),
% 7.44/1.49      inference(global_propositional_subsumption,
% 7.44/1.49                [status(thm)],
% 7.44/1.49                [c_1628,c_31]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_2117,plain,
% 7.44/1.49      ( k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),X0)) = k2_pre_topc(sK3,k2_tarski(sK4,sK4))
% 7.44/1.49      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 7.44/1.49      | r2_hidden(X0,k2_pre_topc(sK3,k2_tarski(sK4,sK4))) != iProver_top ),
% 7.44/1.49      inference(renaming,[status(thm)],[c_2116]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_2123,plain,
% 7.44/1.49      ( k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK0(k2_pre_topc(sK3,k2_tarski(sK4,sK4)),X0))) = k2_pre_topc(sK3,k2_tarski(sK4,sK4))
% 7.44/1.49      | m1_subset_1(sK0(k2_pre_topc(sK3,k2_tarski(sK4,sK4)),X0),u1_struct_0(sK3)) != iProver_top
% 7.44/1.49      | r1_xboole_0(k2_pre_topc(sK3,k2_tarski(sK4,sK4)),X0) = iProver_top ),
% 7.44/1.49      inference(superposition,[status(thm)],[c_944,c_2117]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_11272,plain,
% 7.44/1.49      ( k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK0(k2_pre_topc(sK3,k2_tarski(sK4,sK4)),k2_tarski(sK5,sK5)))) = k2_pre_topc(sK3,k2_tarski(sK4,sK4))
% 7.44/1.49      | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
% 7.44/1.49      | r1_xboole_0(k2_pre_topc(sK3,k2_tarski(sK4,sK4)),k2_tarski(sK5,sK5)) = iProver_top ),
% 7.44/1.49      inference(superposition,[status(thm)],[c_2594,c_2123]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_11273,plain,
% 7.44/1.49      ( k2_pre_topc(sK3,k2_tarski(sK4,sK4)) = k2_pre_topc(sK3,k2_tarski(sK5,sK5))
% 7.44/1.49      | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
% 7.44/1.49      | r1_xboole_0(k2_pre_topc(sK3,k2_tarski(sK4,sK4)),k2_tarski(sK5,sK5)) = iProver_top ),
% 7.44/1.49      inference(light_normalisation,
% 7.44/1.49                [status(thm)],
% 7.44/1.49                [c_11272,c_1312,c_2594]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_19,negated_conjecture,
% 7.44/1.49      ( k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK4)) != k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5)) ),
% 7.44/1.49      inference(cnf_transformation,[],[f77]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_1315,plain,
% 7.44/1.49      ( k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK4)) != k2_pre_topc(sK3,k2_tarski(sK5,sK5)) ),
% 7.44/1.49      inference(demodulation,[status(thm)],[c_1312,c_19]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_1316,plain,
% 7.44/1.49      ( k2_pre_topc(sK3,k2_tarski(sK4,sK4)) != k2_pre_topc(sK3,k2_tarski(sK5,sK5)) ),
% 7.44/1.49      inference(light_normalisation,[status(thm)],[c_1315,c_1313]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(contradiction,plain,
% 7.44/1.49      ( $false ),
% 7.44/1.49      inference(minisat,
% 7.44/1.49                [status(thm)],
% 7.44/1.49                [c_11273,c_1892,c_1891,c_1730,c_1316,c_32,c_31]) ).
% 7.44/1.49  
% 7.44/1.49  
% 7.44/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.44/1.49  
% 7.44/1.49  ------                               Statistics
% 7.44/1.49  
% 7.44/1.49  ------ General
% 7.44/1.49  
% 7.44/1.49  abstr_ref_over_cycles:                  0
% 7.44/1.49  abstr_ref_under_cycles:                 0
% 7.44/1.49  gc_basic_clause_elim:                   0
% 7.44/1.49  forced_gc_time:                         0
% 7.44/1.49  parsing_time:                           0.014
% 7.44/1.49  unif_index_cands_time:                  0.
% 7.44/1.49  unif_index_add_time:                    0.
% 7.44/1.49  orderings_time:                         0.
% 7.44/1.49  out_proof_time:                         0.011
% 7.44/1.49  total_time:                             0.613
% 7.44/1.49  num_of_symbols:                         53
% 7.44/1.49  num_of_terms:                           10702
% 7.44/1.49  
% 7.44/1.49  ------ Preprocessing
% 7.44/1.49  
% 7.44/1.49  num_of_splits:                          0
% 7.44/1.49  num_of_split_atoms:                     0
% 7.44/1.49  num_of_reused_defs:                     0
% 7.44/1.49  num_eq_ax_congr_red:                    22
% 7.44/1.49  num_of_sem_filtered_clauses:            1
% 7.44/1.49  num_of_subtypes:                        0
% 7.44/1.49  monotx_restored_types:                  0
% 7.44/1.49  sat_num_of_epr_types:                   0
% 7.44/1.49  sat_num_of_non_cyclic_types:            0
% 7.44/1.49  sat_guarded_non_collapsed_types:        0
% 7.44/1.49  num_pure_diseq_elim:                    0
% 7.44/1.49  simp_replaced_by:                       0
% 7.44/1.49  res_preprocessed:                       94
% 7.44/1.49  prep_upred:                             0
% 7.44/1.49  prep_unflattend:                        16
% 7.44/1.49  smt_new_axioms:                         0
% 7.44/1.49  pred_elim_cands:                        3
% 7.44/1.49  pred_elim:                              8
% 7.44/1.49  pred_elim_cl:                           11
% 7.44/1.49  pred_elim_cycles:                       11
% 7.44/1.49  merged_defs:                            0
% 7.44/1.49  merged_defs_ncl:                        0
% 7.44/1.49  bin_hyper_res:                          0
% 7.44/1.49  prep_cycles:                            4
% 7.44/1.49  pred_elim_time:                         0.006
% 7.44/1.49  splitting_time:                         0.
% 7.44/1.49  sem_filter_time:                        0.
% 7.44/1.49  monotx_time:                            0.
% 7.44/1.49  subtype_inf_time:                       0.
% 7.44/1.49  
% 7.44/1.49  ------ Problem properties
% 7.44/1.49  
% 7.44/1.49  clauses:                                16
% 7.44/1.49  conjectures:                            4
% 7.44/1.49  epr:                                    1
% 7.44/1.49  horn:                                   13
% 7.44/1.49  ground:                                 4
% 7.44/1.49  unary:                                  5
% 7.44/1.49  binary:                                 6
% 7.44/1.49  lits:                                   34
% 7.44/1.49  lits_eq:                                8
% 7.44/1.49  fd_pure:                                0
% 7.44/1.49  fd_pseudo:                              0
% 7.44/1.49  fd_cond:                                0
% 7.44/1.49  fd_pseudo_cond:                         2
% 7.44/1.49  ac_symbols:                             0
% 7.44/1.49  
% 7.44/1.49  ------ Propositional Solver
% 7.44/1.49  
% 7.44/1.49  prop_solver_calls:                      28
% 7.44/1.49  prop_fast_solver_calls:                 1060
% 7.44/1.49  smt_solver_calls:                       0
% 7.44/1.49  smt_fast_solver_calls:                  0
% 7.44/1.49  prop_num_of_clauses:                    6773
% 7.44/1.49  prop_preprocess_simplified:             11104
% 7.44/1.49  prop_fo_subsumed:                       38
% 7.44/1.49  prop_solver_time:                       0.
% 7.44/1.49  smt_solver_time:                        0.
% 7.44/1.49  smt_fast_solver_time:                   0.
% 7.44/1.49  prop_fast_solver_time:                  0.
% 7.44/1.49  prop_unsat_core_time:                   0.
% 7.44/1.49  
% 7.44/1.49  ------ QBF
% 7.44/1.49  
% 7.44/1.49  qbf_q_res:                              0
% 7.44/1.49  qbf_num_tautologies:                    0
% 7.44/1.49  qbf_prep_cycles:                        0
% 7.44/1.49  
% 7.44/1.49  ------ BMC1
% 7.44/1.49  
% 7.44/1.49  bmc1_current_bound:                     -1
% 7.44/1.49  bmc1_last_solved_bound:                 -1
% 7.44/1.49  bmc1_unsat_core_size:                   -1
% 7.44/1.49  bmc1_unsat_core_parents_size:           -1
% 7.44/1.49  bmc1_merge_next_fun:                    0
% 7.44/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.44/1.49  
% 7.44/1.49  ------ Instantiation
% 7.44/1.49  
% 7.44/1.49  inst_num_of_clauses:                    1301
% 7.44/1.49  inst_num_in_passive:                    196
% 7.44/1.49  inst_num_in_active:                     555
% 7.44/1.49  inst_num_in_unprocessed:                550
% 7.44/1.49  inst_num_of_loops:                      610
% 7.44/1.49  inst_num_of_learning_restarts:          0
% 7.44/1.49  inst_num_moves_active_passive:          55
% 7.44/1.49  inst_lit_activity:                      0
% 7.44/1.49  inst_lit_activity_moves:                0
% 7.44/1.49  inst_num_tautologies:                   0
% 7.44/1.49  inst_num_prop_implied:                  0
% 7.44/1.49  inst_num_existing_simplified:           0
% 7.44/1.49  inst_num_eq_res_simplified:             0
% 7.44/1.49  inst_num_child_elim:                    0
% 7.44/1.49  inst_num_of_dismatching_blockings:      302
% 7.44/1.49  inst_num_of_non_proper_insts:           1506
% 7.44/1.49  inst_num_of_duplicates:                 0
% 7.44/1.49  inst_inst_num_from_inst_to_res:         0
% 7.44/1.49  inst_dismatching_checking_time:         0.
% 7.44/1.49  
% 7.44/1.49  ------ Resolution
% 7.44/1.49  
% 7.44/1.49  res_num_of_clauses:                     0
% 7.44/1.49  res_num_in_passive:                     0
% 7.44/1.49  res_num_in_active:                      0
% 7.44/1.49  res_num_of_loops:                       98
% 7.44/1.49  res_forward_subset_subsumed:            106
% 7.44/1.49  res_backward_subset_subsumed:           2
% 7.44/1.49  res_forward_subsumed:                   0
% 7.44/1.49  res_backward_subsumed:                  0
% 7.44/1.49  res_forward_subsumption_resolution:     1
% 7.44/1.49  res_backward_subsumption_resolution:    0
% 7.44/1.49  res_clause_to_clause_subsumption:       24098
% 7.44/1.49  res_orphan_elimination:                 0
% 7.44/1.49  res_tautology_del:                      55
% 7.44/1.49  res_num_eq_res_simplified:              0
% 7.44/1.49  res_num_sel_changes:                    0
% 7.44/1.49  res_moves_from_active_to_pass:          0
% 7.44/1.49  
% 7.44/1.49  ------ Superposition
% 7.44/1.49  
% 7.44/1.49  sup_time_total:                         0.
% 7.44/1.49  sup_time_generating:                    0.
% 7.44/1.49  sup_time_sim_full:                      0.
% 7.44/1.49  sup_time_sim_immed:                     0.
% 7.44/1.49  
% 7.44/1.49  sup_num_of_clauses:                     1452
% 7.44/1.49  sup_num_in_active:                      117
% 7.44/1.49  sup_num_in_passive:                     1335
% 7.44/1.49  sup_num_of_loops:                       120
% 7.44/1.49  sup_fw_superposition:                   706
% 7.44/1.49  sup_bw_superposition:                   1186
% 7.44/1.49  sup_immediate_simplified:               227
% 7.44/1.49  sup_given_eliminated:                   0
% 7.44/1.49  comparisons_done:                       0
% 7.44/1.49  comparisons_avoided:                    178
% 7.44/1.49  
% 7.44/1.49  ------ Simplifications
% 7.44/1.49  
% 7.44/1.49  
% 7.44/1.49  sim_fw_subset_subsumed:                 46
% 7.44/1.49  sim_bw_subset_subsumed:                 6
% 7.44/1.49  sim_fw_subsumed:                        156
% 7.44/1.49  sim_bw_subsumed:                        16
% 7.44/1.49  sim_fw_subsumption_res:                 0
% 7.44/1.49  sim_bw_subsumption_res:                 0
% 7.44/1.49  sim_tautology_del:                      14
% 7.44/1.49  sim_eq_tautology_del:                   11
% 7.44/1.49  sim_eq_res_simp:                        4
% 7.44/1.49  sim_fw_demodulated:                     4
% 7.44/1.49  sim_bw_demodulated:                     2
% 7.44/1.49  sim_light_normalised:                   18
% 7.44/1.49  sim_joinable_taut:                      0
% 7.44/1.49  sim_joinable_simp:                      0
% 7.44/1.49  sim_ac_normalised:                      0
% 7.44/1.49  sim_smt_subsumption:                    0
% 7.44/1.49  
%------------------------------------------------------------------------------
