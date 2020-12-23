%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:12:20 EST 2020

% Result     : Theorem 1.81s
% Output     : CNFRefutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 316 expanded)
%              Number of clauses        :   64 (  85 expanded)
%              Number of leaves         :   17 (  82 expanded)
%              Depth                    :   21
%              Number of atoms          :  593 (1844 expanded)
%              Number of equality atoms :  131 ( 134 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ~ r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ~ r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] :
          ( r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( r2_hidden(sK4,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),sK4)))
        & m1_subset_1(sK4,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( r2_hidden(X1,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),X1)))
          & m1_subset_1(X1,u1_struct_0(sK3)) )
      & l1_orders_2(sK3)
      & v5_orders_2(sK3)
      & v4_orders_2(sK3)
      & v3_orders_2(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( r2_hidden(sK4,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4)))
    & m1_subset_1(sK4,u1_struct_0(sK3))
    & l1_orders_2(sK3)
    & v5_orders_2(sK3)
    & v4_orders_2(sK3)
    & v3_orders_2(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f27,f41,f40])).

fof(f72,plain,(
    m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f42])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X2,X3)
          & r2_hidden(X1,X3)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
          & v6_orders_2(X3,X0) )
      | ( ~ r1_orders_2(X0,X2,X1)
        & ~ r1_orders_2(X0,X1,X2) )
      | ~ sP0(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X2,X3)
          & r2_hidden(X1,X3)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
          & v6_orders_2(X3,X0) )
      | ( ~ r1_orders_2(X0,X2,X1)
        & ~ r1_orders_2(X0,X1,X2) )
      | ~ sP0(X2,X1,X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ? [X3] :
          ( r2_hidden(X0,X3)
          & r2_hidden(X1,X3)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
          & v6_orders_2(X3,X2) )
      | ( ~ r1_orders_2(X2,X0,X1)
        & ~ r1_orders_2(X2,X1,X0) )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f35])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X0,X3)
          & r2_hidden(X1,X3)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
          & v6_orders_2(X3,X2) )
     => ( r2_hidden(X0,sK2(X0,X1,X2))
        & r2_hidden(X1,sK2(X0,X1,X2))
        & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2)))
        & v6_orders_2(sK2(X0,X1,X2),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,sK2(X0,X1,X2))
        & r2_hidden(X1,sK2(X0,X1,X2))
        & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2)))
        & v6_orders_2(sK2(X0,X1,X2),X2) )
      | ( ~ r1_orders_2(X2,X0,X1)
        & ~ r1_orders_2(X2,X1,X0) )
      | ~ sP0(X0,X1,X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f36,f37])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,sK2(X0,X1,X2))
      | ~ r1_orders_2(X2,X0,X1)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ~ ( ! [X3] :
                        ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                          & v6_orders_2(X3,X0) )
                       => ~ ( r2_hidden(X2,X3)
                            & r2_hidden(X1,X3) ) )
                    & ( r1_orders_2(X0,X2,X1)
                      | r1_orders_2(X0,X1,X2) ) )
                & ~ ( ~ r1_orders_2(X0,X2,X1)
                    & ~ r1_orders_2(X0,X1,X2)
                    & ? [X3] :
                        ( r2_hidden(X2,X3)
                        & r2_hidden(X1,X3)
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                        & v6_orders_2(X3,X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ~ ( ! [X3] :
                        ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                          & v6_orders_2(X3,X0) )
                       => ~ ( r2_hidden(X2,X3)
                            & r2_hidden(X1,X3) ) )
                    & ( r1_orders_2(X0,X2,X1)
                      | r1_orders_2(X0,X1,X2) ) )
                & ~ ( ~ r1_orders_2(X0,X2,X1)
                    & ~ r1_orders_2(X0,X1,X2)
                    & ? [X4] :
                        ( r2_hidden(X2,X4)
                        & r2_hidden(X1,X4)
                        & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                        & v6_orders_2(X4,X0) ) ) ) ) ) ) ),
    inference(rectify,[],[f8])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ? [X3] :
                      ( r2_hidden(X2,X3)
                      & r2_hidden(X1,X3)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                      & v6_orders_2(X3,X0) )
                  | ( ~ r1_orders_2(X0,X2,X1)
                    & ~ r1_orders_2(X0,X1,X2) ) )
                & ( r1_orders_2(X0,X2,X1)
                  | r1_orders_2(X0,X1,X2)
                  | ! [X4] :
                      ( ~ r2_hidden(X2,X4)
                      | ~ r2_hidden(X1,X4)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                      | ~ v6_orders_2(X4,X0) ) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ? [X3] :
                      ( r2_hidden(X2,X3)
                      & r2_hidden(X1,X3)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                      & v6_orders_2(X3,X0) )
                  | ( ~ r1_orders_2(X0,X2,X1)
                    & ~ r1_orders_2(X0,X1,X2) ) )
                & ( r1_orders_2(X0,X2,X1)
                  | r1_orders_2(X0,X1,X2)
                  | ! [X4] :
                      ( ~ r2_hidden(X2,X4)
                      | ~ r2_hidden(X1,X4)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                      | ~ v6_orders_2(X4,X0) ) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f22])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( sP0(X2,X1,X0)
                & ( r1_orders_2(X0,X2,X1)
                  | r1_orders_2(X0,X1,X2)
                  | ! [X4] :
                      ( ~ r2_hidden(X2,X4)
                      | ~ r2_hidden(X1,X4)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                      | ~ v6_orders_2(X4,X0) ) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(definition_folding,[],[f23,f28])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( sP0(X2,X1,X0)
                & ( r1_orders_2(X0,X2,X1)
                  | r1_orders_2(X0,X1,X2)
                  | ! [X3] :
                      ( ~ r2_hidden(X2,X3)
                      | ~ r2_hidden(X1,X3)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                      | ~ v6_orders_2(X3,X0) ) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(rectify,[],[f29])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f71,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f68,plain,(
    v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ r1_orders_2(X2,X0,X1)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k2_tarski(X1,X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f52,f49])).

fof(f73,plain,(
    r2_hidden(sK4,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))) ),
    inference(cnf_transformation,[],[f42])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f67,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ~ ( r2_hidden(X1,k1_orders_2(X0,X2))
                  & r2_hidden(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ r2_hidden(X1,k1_orders_2(X0,X2))
              | ~ r2_hidden(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ r2_hidden(X1,k1_orders_2(X0,X2))
              | ~ r2_hidden(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k1_orders_2(X0,X2))
      | ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f70,plain,(
    v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f69,plain,(
    v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f30])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f31])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK1(X0,X1,X2) != X1
            & sK1(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( sK1(X0,X1,X2) = X1
          | sK1(X0,X1,X2) = X0
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK1(X0,X1,X2) != X1
              & sK1(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( sK1(X0,X1,X2) = X1
            | sK1(X0,X1,X2) = X0
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f32,f33])).

fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f75,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f45])).

fof(f76,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_tarski(X0,X4)) ),
    inference(equality_resolution,[],[f75])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r1_orders_2(X0,X1,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,X1,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,X1,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1571,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_12,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r1_orders_2(X2,X0,X1)
    | r2_hidden(X0,sK2(X0,X1,X2)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_20,plain,
    ( sP0(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X0,u1_struct_0(X2))
    | ~ v3_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_25,negated_conjecture,
    ( l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_468,plain,
    ( sP0(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X0,u1_struct_0(X2))
    | ~ v3_orders_2(X2)
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_25])).

cnf(c_469,plain,
    ( sP0(X0,X1,sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ v3_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_468])).

cnf(c_28,negated_conjecture,
    ( v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_473,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | sP0(X0,X1,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_469,c_28])).

cnf(c_474,plain,
    ( sP0(X0,X1,sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_473])).

cnf(c_707,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(sK3))
    | ~ m1_subset_1(X4,u1_struct_0(sK3))
    | r2_hidden(X1,sK2(X1,X2,X0))
    | X4 != X2
    | X3 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_474])).

cnf(c_708,plain,
    ( ~ r1_orders_2(sK3,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | r2_hidden(X0,sK2(X0,X1,sK3)) ),
    inference(unflattening,[status(thm)],[c_707])).

cnf(c_1558,plain,
    ( r1_orders_2(sK3,X0,X1) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0,sK2(X0,X1,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_708])).

cnf(c_16,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r1_orders_2(X2,X0,X1)
    | m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_641,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(sK3))
    | ~ m1_subset_1(X4,u1_struct_0(sK3))
    | m1_subset_1(sK2(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X0)))
    | X4 != X2
    | X3 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_474])).

cnf(c_642,plain,
    ( ~ r1_orders_2(sK3,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | m1_subset_1(sK2(X0,X1,sK3),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(unflattening,[status(thm)],[c_641])).

cnf(c_1562,plain,
    ( r1_orders_2(sK3,X0,X1) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK2(X0,X1,sK3),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_642])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1574,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2794,plain,
    ( r1_orders_2(sK3,X0,X1) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X2,sK2(X0,X1,sK3)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1562,c_1574])).

cnf(c_35,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1853,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK3))
    | k6_domain_1(u1_struct_0(sK3),sK4) = k2_tarski(sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1854,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK4) = k2_tarski(sK4,sK4)
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1853])).

cnf(c_23,negated_conjecture,
    ( r2_hidden(sK4,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1572,plain,
    ( r2_hidden(sK4,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k6_domain_1(u1_struct_0(X1),X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_404,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k6_domain_1(u1_struct_0(X1),X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_29])).

cnf(c_405,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | m1_subset_1(k6_domain_1(u1_struct_0(sK3),X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v3_orders_2(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_404])).

cnf(c_409,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | m1_subset_1(k6_domain_1(u1_struct_0(sK3),X0),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_405,c_28,c_25])).

cnf(c_1567,plain,
    ( m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k6_domain_1(u1_struct_0(sK3),X0),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_409])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k1_orders_2(X1,X2))
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_26,negated_conjecture,
    ( v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_338,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k1_orders_2(X1,X2))
    | ~ v4_orders_2(X1)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_26])).

cnf(c_339,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_orders_2(sK3,X1))
    | ~ v4_orders_2(sK3)
    | v2_struct_0(sK3)
    | ~ v3_orders_2(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_338])).

cnf(c_27,negated_conjecture,
    ( v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_343,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_orders_2(sK3,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_339,c_29,c_28,c_27,c_25])).

cnf(c_6,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_357,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X1,X0)
    | ~ r2_hidden(X1,k1_orders_2(sK3,X0)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_343,c_6])).

cnf(c_1570,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(X1,X0) != iProver_top
    | r2_hidden(X1,k1_orders_2(sK3,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_357])).

cnf(c_1915,plain,
    ( m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X1,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),X0))) != iProver_top
    | r2_hidden(X1,k6_domain_1(u1_struct_0(sK3),X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1567,c_1570])).

cnf(c_1923,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK4,k6_domain_1(u1_struct_0(sK3),sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1572,c_1915])).

cnf(c_1924,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ r2_hidden(sK4,k6_domain_1(u1_struct_0(sK3),sK4)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1923])).

cnf(c_1142,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2020,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_1142])).

cnf(c_1144,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1856,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k2_tarski(X3,X2))
    | X0 != X2
    | X1 != k2_tarski(X3,X2) ),
    inference(instantiation,[status(thm)],[c_1144])).

cnf(c_2170,plain,
    ( r2_hidden(X0,k6_domain_1(u1_struct_0(sK3),sK4))
    | ~ r2_hidden(sK4,k2_tarski(sK4,sK4))
    | X0 != sK4
    | k6_domain_1(u1_struct_0(sK3),sK4) != k2_tarski(sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_1856])).

cnf(c_2266,plain,
    ( r2_hidden(sK4,k6_domain_1(u1_struct_0(sK3),sK4))
    | ~ r2_hidden(sK4,k2_tarski(sK4,sK4))
    | k6_domain_1(u1_struct_0(sK3),sK4) != k2_tarski(sK4,sK4)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_2170])).

cnf(c_3,plain,
    ( r2_hidden(X0,k2_tarski(X1,X0)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_2474,plain,
    ( r2_hidden(sK4,k2_tarski(sK4,sK4)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_3746,plain,
    ( r2_hidden(X2,sK2(X0,X1,sK3)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | r1_orders_2(sK3,X0,X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2794,c_24,c_35,c_1854,c_1924,c_2020,c_2266,c_2474])).

cnf(c_3747,plain,
    ( r1_orders_2(sK3,X0,X1) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X2,sK2(X0,X1,sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3746])).

cnf(c_3759,plain,
    ( r1_orders_2(sK3,X0,X1) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1558,c_3747])).

cnf(c_3773,plain,
    ( r1_orders_2(sK3,sK4,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1571,c_3759])).

cnf(c_3837,plain,
    ( r1_orders_2(sK3,sK4,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1571,c_3773])).

cnf(c_9,plain,
    ( r1_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_386,plain,
    ( r1_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_29])).

cnf(c_387,plain,
    ( r1_orders_2(sK3,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ v3_orders_2(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_386])).

cnf(c_391,plain,
    ( r1_orders_2(sK3,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_387,c_28,c_25])).

cnf(c_1786,plain,
    ( r1_orders_2(sK3,sK4,sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_391])).

cnf(c_1787,plain,
    ( r1_orders_2(sK3,sK4,sK4) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1786])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3837,c_1787,c_35])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:44:57 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 1.81/1.02  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.81/1.02  
% 1.81/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.81/1.02  
% 1.81/1.02  ------  iProver source info
% 1.81/1.02  
% 1.81/1.02  git: date: 2020-06-30 10:37:57 +0100
% 1.81/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.81/1.02  git: non_committed_changes: false
% 1.81/1.02  git: last_make_outside_of_git: false
% 1.81/1.02  
% 1.81/1.02  ------ 
% 1.81/1.02  
% 1.81/1.02  ------ Input Options
% 1.81/1.02  
% 1.81/1.02  --out_options                           all
% 1.81/1.02  --tptp_safe_out                         true
% 1.81/1.02  --problem_path                          ""
% 1.81/1.02  --include_path                          ""
% 1.81/1.02  --clausifier                            res/vclausify_rel
% 1.81/1.02  --clausifier_options                    --mode clausify
% 1.81/1.02  --stdin                                 false
% 1.81/1.02  --stats_out                             all
% 1.81/1.02  
% 1.81/1.02  ------ General Options
% 1.81/1.02  
% 1.81/1.02  --fof                                   false
% 1.81/1.02  --time_out_real                         305.
% 1.81/1.02  --time_out_virtual                      -1.
% 1.81/1.02  --symbol_type_check                     false
% 1.81/1.02  --clausify_out                          false
% 1.81/1.02  --sig_cnt_out                           false
% 1.81/1.02  --trig_cnt_out                          false
% 1.81/1.02  --trig_cnt_out_tolerance                1.
% 1.81/1.02  --trig_cnt_out_sk_spl                   false
% 1.81/1.02  --abstr_cl_out                          false
% 1.81/1.02  
% 1.81/1.02  ------ Global Options
% 1.81/1.02  
% 1.81/1.02  --schedule                              default
% 1.81/1.02  --add_important_lit                     false
% 1.81/1.02  --prop_solver_per_cl                    1000
% 1.81/1.02  --min_unsat_core                        false
% 1.81/1.02  --soft_assumptions                      false
% 1.81/1.02  --soft_lemma_size                       3
% 1.81/1.02  --prop_impl_unit_size                   0
% 1.81/1.02  --prop_impl_unit                        []
% 1.81/1.02  --share_sel_clauses                     true
% 1.81/1.02  --reset_solvers                         false
% 1.81/1.02  --bc_imp_inh                            [conj_cone]
% 1.81/1.02  --conj_cone_tolerance                   3.
% 1.81/1.02  --extra_neg_conj                        none
% 1.81/1.02  --large_theory_mode                     true
% 1.81/1.02  --prolific_symb_bound                   200
% 1.81/1.02  --lt_threshold                          2000
% 1.81/1.02  --clause_weak_htbl                      true
% 1.81/1.02  --gc_record_bc_elim                     false
% 1.81/1.02  
% 1.81/1.02  ------ Preprocessing Options
% 1.81/1.02  
% 1.81/1.02  --preprocessing_flag                    true
% 1.81/1.02  --time_out_prep_mult                    0.1
% 1.81/1.02  --splitting_mode                        input
% 1.81/1.02  --splitting_grd                         true
% 1.81/1.02  --splitting_cvd                         false
% 1.81/1.02  --splitting_cvd_svl                     false
% 1.81/1.02  --splitting_nvd                         32
% 1.81/1.02  --sub_typing                            true
% 1.81/1.02  --prep_gs_sim                           true
% 1.81/1.02  --prep_unflatten                        true
% 1.81/1.02  --prep_res_sim                          true
% 1.81/1.02  --prep_upred                            true
% 1.81/1.02  --prep_sem_filter                       exhaustive
% 1.81/1.02  --prep_sem_filter_out                   false
% 1.81/1.02  --pred_elim                             true
% 1.81/1.02  --res_sim_input                         true
% 1.81/1.02  --eq_ax_congr_red                       true
% 1.81/1.02  --pure_diseq_elim                       true
% 1.81/1.02  --brand_transform                       false
% 1.81/1.02  --non_eq_to_eq                          false
% 1.81/1.02  --prep_def_merge                        true
% 1.81/1.02  --prep_def_merge_prop_impl              false
% 1.81/1.02  --prep_def_merge_mbd                    true
% 1.81/1.02  --prep_def_merge_tr_red                 false
% 1.81/1.02  --prep_def_merge_tr_cl                  false
% 1.81/1.02  --smt_preprocessing                     true
% 1.81/1.02  --smt_ac_axioms                         fast
% 1.81/1.02  --preprocessed_out                      false
% 1.81/1.02  --preprocessed_stats                    false
% 1.81/1.02  
% 1.81/1.02  ------ Abstraction refinement Options
% 1.81/1.02  
% 1.81/1.02  --abstr_ref                             []
% 1.81/1.02  --abstr_ref_prep                        false
% 1.81/1.02  --abstr_ref_until_sat                   false
% 1.81/1.02  --abstr_ref_sig_restrict                funpre
% 1.81/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 1.81/1.02  --abstr_ref_under                       []
% 1.81/1.02  
% 1.81/1.02  ------ SAT Options
% 1.81/1.02  
% 1.81/1.02  --sat_mode                              false
% 1.81/1.02  --sat_fm_restart_options                ""
% 1.81/1.02  --sat_gr_def                            false
% 1.81/1.02  --sat_epr_types                         true
% 1.81/1.02  --sat_non_cyclic_types                  false
% 1.81/1.02  --sat_finite_models                     false
% 1.81/1.02  --sat_fm_lemmas                         false
% 1.81/1.02  --sat_fm_prep                           false
% 1.81/1.02  --sat_fm_uc_incr                        true
% 1.81/1.02  --sat_out_model                         small
% 1.81/1.02  --sat_out_clauses                       false
% 1.81/1.02  
% 1.81/1.02  ------ QBF Options
% 1.81/1.02  
% 1.81/1.02  --qbf_mode                              false
% 1.81/1.02  --qbf_elim_univ                         false
% 1.81/1.02  --qbf_dom_inst                          none
% 1.81/1.02  --qbf_dom_pre_inst                      false
% 1.81/1.02  --qbf_sk_in                             false
% 1.81/1.02  --qbf_pred_elim                         true
% 1.81/1.02  --qbf_split                             512
% 1.81/1.02  
% 1.81/1.02  ------ BMC1 Options
% 1.81/1.02  
% 1.81/1.02  --bmc1_incremental                      false
% 1.81/1.02  --bmc1_axioms                           reachable_all
% 1.81/1.02  --bmc1_min_bound                        0
% 1.81/1.02  --bmc1_max_bound                        -1
% 1.81/1.02  --bmc1_max_bound_default                -1
% 1.81/1.02  --bmc1_symbol_reachability              true
% 1.81/1.02  --bmc1_property_lemmas                  false
% 1.81/1.02  --bmc1_k_induction                      false
% 1.81/1.02  --bmc1_non_equiv_states                 false
% 1.81/1.02  --bmc1_deadlock                         false
% 1.81/1.02  --bmc1_ucm                              false
% 1.81/1.02  --bmc1_add_unsat_core                   none
% 1.81/1.02  --bmc1_unsat_core_children              false
% 1.81/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 1.81/1.02  --bmc1_out_stat                         full
% 1.81/1.02  --bmc1_ground_init                      false
% 1.81/1.02  --bmc1_pre_inst_next_state              false
% 1.81/1.02  --bmc1_pre_inst_state                   false
% 1.81/1.02  --bmc1_pre_inst_reach_state             false
% 1.81/1.02  --bmc1_out_unsat_core                   false
% 1.81/1.02  --bmc1_aig_witness_out                  false
% 1.81/1.02  --bmc1_verbose                          false
% 1.81/1.02  --bmc1_dump_clauses_tptp                false
% 1.81/1.02  --bmc1_dump_unsat_core_tptp             false
% 1.81/1.02  --bmc1_dump_file                        -
% 1.81/1.02  --bmc1_ucm_expand_uc_limit              128
% 1.81/1.02  --bmc1_ucm_n_expand_iterations          6
% 1.81/1.02  --bmc1_ucm_extend_mode                  1
% 1.81/1.02  --bmc1_ucm_init_mode                    2
% 1.81/1.02  --bmc1_ucm_cone_mode                    none
% 1.81/1.02  --bmc1_ucm_reduced_relation_type        0
% 1.81/1.02  --bmc1_ucm_relax_model                  4
% 1.81/1.02  --bmc1_ucm_full_tr_after_sat            true
% 1.81/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 1.81/1.02  --bmc1_ucm_layered_model                none
% 1.81/1.02  --bmc1_ucm_max_lemma_size               10
% 1.81/1.02  
% 1.81/1.02  ------ AIG Options
% 1.81/1.02  
% 1.81/1.02  --aig_mode                              false
% 1.81/1.02  
% 1.81/1.02  ------ Instantiation Options
% 1.81/1.02  
% 1.81/1.02  --instantiation_flag                    true
% 1.81/1.02  --inst_sos_flag                         false
% 1.81/1.02  --inst_sos_phase                        true
% 1.81/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.81/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.81/1.02  --inst_lit_sel_side                     num_symb
% 1.81/1.02  --inst_solver_per_active                1400
% 1.81/1.02  --inst_solver_calls_frac                1.
% 1.81/1.02  --inst_passive_queue_type               priority_queues
% 1.81/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.81/1.02  --inst_passive_queues_freq              [25;2]
% 1.81/1.02  --inst_dismatching                      true
% 1.81/1.02  --inst_eager_unprocessed_to_passive     true
% 1.81/1.02  --inst_prop_sim_given                   true
% 1.81/1.02  --inst_prop_sim_new                     false
% 1.81/1.02  --inst_subs_new                         false
% 1.81/1.02  --inst_eq_res_simp                      false
% 1.81/1.02  --inst_subs_given                       false
% 1.81/1.02  --inst_orphan_elimination               true
% 1.81/1.02  --inst_learning_loop_flag               true
% 1.81/1.02  --inst_learning_start                   3000
% 1.81/1.02  --inst_learning_factor                  2
% 1.81/1.02  --inst_start_prop_sim_after_learn       3
% 1.81/1.02  --inst_sel_renew                        solver
% 1.81/1.02  --inst_lit_activity_flag                true
% 1.81/1.02  --inst_restr_to_given                   false
% 1.81/1.02  --inst_activity_threshold               500
% 1.81/1.02  --inst_out_proof                        true
% 1.81/1.02  
% 1.81/1.02  ------ Resolution Options
% 1.81/1.02  
% 1.81/1.02  --resolution_flag                       true
% 1.81/1.02  --res_lit_sel                           adaptive
% 1.81/1.02  --res_lit_sel_side                      none
% 1.81/1.02  --res_ordering                          kbo
% 1.81/1.02  --res_to_prop_solver                    active
% 1.81/1.02  --res_prop_simpl_new                    false
% 1.81/1.02  --res_prop_simpl_given                  true
% 1.81/1.02  --res_passive_queue_type                priority_queues
% 1.81/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.81/1.02  --res_passive_queues_freq               [15;5]
% 1.81/1.02  --res_forward_subs                      full
% 1.81/1.02  --res_backward_subs                     full
% 1.81/1.02  --res_forward_subs_resolution           true
% 1.81/1.02  --res_backward_subs_resolution          true
% 1.81/1.02  --res_orphan_elimination                true
% 1.81/1.02  --res_time_limit                        2.
% 1.81/1.02  --res_out_proof                         true
% 1.81/1.02  
% 1.81/1.02  ------ Superposition Options
% 1.81/1.02  
% 1.81/1.02  --superposition_flag                    true
% 1.81/1.02  --sup_passive_queue_type                priority_queues
% 1.81/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.81/1.02  --sup_passive_queues_freq               [8;1;4]
% 1.81/1.02  --demod_completeness_check              fast
% 1.81/1.02  --demod_use_ground                      true
% 1.81/1.02  --sup_to_prop_solver                    passive
% 1.81/1.02  --sup_prop_simpl_new                    true
% 1.81/1.02  --sup_prop_simpl_given                  true
% 1.81/1.02  --sup_fun_splitting                     false
% 1.81/1.02  --sup_smt_interval                      50000
% 1.81/1.02  
% 1.81/1.02  ------ Superposition Simplification Setup
% 1.81/1.02  
% 1.81/1.02  --sup_indices_passive                   []
% 1.81/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.81/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.81/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.81/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 1.81/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.81/1.02  --sup_full_bw                           [BwDemod]
% 1.81/1.02  --sup_immed_triv                        [TrivRules]
% 1.81/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.81/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.81/1.02  --sup_immed_bw_main                     []
% 1.81/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.81/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 1.81/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.81/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.81/1.02  
% 1.81/1.02  ------ Combination Options
% 1.81/1.02  
% 1.81/1.02  --comb_res_mult                         3
% 1.81/1.02  --comb_sup_mult                         2
% 1.81/1.02  --comb_inst_mult                        10
% 1.81/1.02  
% 1.81/1.02  ------ Debug Options
% 1.81/1.02  
% 1.81/1.02  --dbg_backtrace                         false
% 1.81/1.02  --dbg_dump_prop_clauses                 false
% 1.81/1.02  --dbg_dump_prop_clauses_file            -
% 1.81/1.02  --dbg_out_stat                          false
% 1.81/1.02  ------ Parsing...
% 1.81/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.81/1.02  
% 1.81/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 1.81/1.02  
% 1.81/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.81/1.02  
% 1.81/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.81/1.02  ------ Proving...
% 1.81/1.02  ------ Problem Properties 
% 1.81/1.02  
% 1.81/1.02  
% 1.81/1.02  clauses                                 24
% 1.81/1.02  conjectures                             2
% 1.81/1.02  EPR                                     0
% 1.81/1.02  Horn                                    20
% 1.81/1.02  unary                                   4
% 1.81/1.02  binary                                  3
% 1.81/1.02  lits                                    73
% 1.81/1.02  lits eq                                 10
% 1.81/1.02  fd_pure                                 0
% 1.81/1.02  fd_pseudo                               0
% 1.81/1.02  fd_cond                                 0
% 1.81/1.02  fd_pseudo_cond                          3
% 1.81/1.02  AC symbols                              0
% 1.81/1.02  
% 1.81/1.02  ------ Schedule dynamic 5 is on 
% 1.81/1.02  
% 1.81/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.81/1.02  
% 1.81/1.02  
% 1.81/1.02  ------ 
% 1.81/1.02  Current options:
% 1.81/1.02  ------ 
% 1.81/1.02  
% 1.81/1.02  ------ Input Options
% 1.81/1.02  
% 1.81/1.02  --out_options                           all
% 1.81/1.02  --tptp_safe_out                         true
% 1.81/1.02  --problem_path                          ""
% 1.81/1.02  --include_path                          ""
% 1.81/1.02  --clausifier                            res/vclausify_rel
% 1.81/1.02  --clausifier_options                    --mode clausify
% 1.81/1.02  --stdin                                 false
% 1.81/1.02  --stats_out                             all
% 1.81/1.02  
% 1.81/1.02  ------ General Options
% 1.81/1.02  
% 1.81/1.02  --fof                                   false
% 1.81/1.02  --time_out_real                         305.
% 1.81/1.02  --time_out_virtual                      -1.
% 1.81/1.02  --symbol_type_check                     false
% 1.81/1.02  --clausify_out                          false
% 1.81/1.02  --sig_cnt_out                           false
% 1.81/1.02  --trig_cnt_out                          false
% 1.81/1.02  --trig_cnt_out_tolerance                1.
% 1.81/1.02  --trig_cnt_out_sk_spl                   false
% 1.81/1.02  --abstr_cl_out                          false
% 1.81/1.02  
% 1.81/1.02  ------ Global Options
% 1.81/1.02  
% 1.81/1.02  --schedule                              default
% 1.81/1.02  --add_important_lit                     false
% 1.81/1.02  --prop_solver_per_cl                    1000
% 1.81/1.02  --min_unsat_core                        false
% 1.81/1.02  --soft_assumptions                      false
% 1.81/1.02  --soft_lemma_size                       3
% 1.81/1.02  --prop_impl_unit_size                   0
% 1.81/1.02  --prop_impl_unit                        []
% 1.81/1.02  --share_sel_clauses                     true
% 1.81/1.02  --reset_solvers                         false
% 1.81/1.02  --bc_imp_inh                            [conj_cone]
% 1.81/1.02  --conj_cone_tolerance                   3.
% 1.81/1.02  --extra_neg_conj                        none
% 1.81/1.02  --large_theory_mode                     true
% 1.81/1.02  --prolific_symb_bound                   200
% 1.81/1.02  --lt_threshold                          2000
% 1.81/1.02  --clause_weak_htbl                      true
% 1.81/1.02  --gc_record_bc_elim                     false
% 1.81/1.02  
% 1.81/1.02  ------ Preprocessing Options
% 1.81/1.02  
% 1.81/1.02  --preprocessing_flag                    true
% 1.81/1.02  --time_out_prep_mult                    0.1
% 1.81/1.02  --splitting_mode                        input
% 1.81/1.02  --splitting_grd                         true
% 1.81/1.02  --splitting_cvd                         false
% 1.81/1.02  --splitting_cvd_svl                     false
% 1.81/1.02  --splitting_nvd                         32
% 1.81/1.02  --sub_typing                            true
% 1.81/1.02  --prep_gs_sim                           true
% 1.81/1.02  --prep_unflatten                        true
% 1.81/1.02  --prep_res_sim                          true
% 1.81/1.02  --prep_upred                            true
% 1.81/1.02  --prep_sem_filter                       exhaustive
% 1.81/1.02  --prep_sem_filter_out                   false
% 1.81/1.02  --pred_elim                             true
% 1.81/1.02  --res_sim_input                         true
% 1.81/1.02  --eq_ax_congr_red                       true
% 1.81/1.02  --pure_diseq_elim                       true
% 1.81/1.02  --brand_transform                       false
% 1.81/1.02  --non_eq_to_eq                          false
% 1.81/1.02  --prep_def_merge                        true
% 1.81/1.02  --prep_def_merge_prop_impl              false
% 1.81/1.02  --prep_def_merge_mbd                    true
% 1.81/1.02  --prep_def_merge_tr_red                 false
% 1.81/1.02  --prep_def_merge_tr_cl                  false
% 1.81/1.02  --smt_preprocessing                     true
% 1.81/1.02  --smt_ac_axioms                         fast
% 1.81/1.02  --preprocessed_out                      false
% 1.81/1.02  --preprocessed_stats                    false
% 1.81/1.02  
% 1.81/1.02  ------ Abstraction refinement Options
% 1.81/1.02  
% 1.81/1.02  --abstr_ref                             []
% 1.81/1.02  --abstr_ref_prep                        false
% 1.81/1.02  --abstr_ref_until_sat                   false
% 1.81/1.02  --abstr_ref_sig_restrict                funpre
% 1.81/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 1.81/1.02  --abstr_ref_under                       []
% 1.81/1.02  
% 1.81/1.02  ------ SAT Options
% 1.81/1.02  
% 1.81/1.02  --sat_mode                              false
% 1.81/1.02  --sat_fm_restart_options                ""
% 1.81/1.02  --sat_gr_def                            false
% 1.81/1.02  --sat_epr_types                         true
% 1.81/1.02  --sat_non_cyclic_types                  false
% 1.81/1.02  --sat_finite_models                     false
% 1.81/1.02  --sat_fm_lemmas                         false
% 1.81/1.02  --sat_fm_prep                           false
% 1.81/1.02  --sat_fm_uc_incr                        true
% 1.81/1.02  --sat_out_model                         small
% 1.81/1.02  --sat_out_clauses                       false
% 1.81/1.02  
% 1.81/1.02  ------ QBF Options
% 1.81/1.02  
% 1.81/1.02  --qbf_mode                              false
% 1.81/1.02  --qbf_elim_univ                         false
% 1.81/1.02  --qbf_dom_inst                          none
% 1.81/1.02  --qbf_dom_pre_inst                      false
% 1.81/1.02  --qbf_sk_in                             false
% 1.81/1.02  --qbf_pred_elim                         true
% 1.81/1.02  --qbf_split                             512
% 1.81/1.02  
% 1.81/1.02  ------ BMC1 Options
% 1.81/1.02  
% 1.81/1.02  --bmc1_incremental                      false
% 1.81/1.02  --bmc1_axioms                           reachable_all
% 1.81/1.02  --bmc1_min_bound                        0
% 1.81/1.02  --bmc1_max_bound                        -1
% 1.81/1.02  --bmc1_max_bound_default                -1
% 1.81/1.02  --bmc1_symbol_reachability              true
% 1.81/1.02  --bmc1_property_lemmas                  false
% 1.81/1.02  --bmc1_k_induction                      false
% 1.81/1.02  --bmc1_non_equiv_states                 false
% 1.81/1.02  --bmc1_deadlock                         false
% 1.81/1.02  --bmc1_ucm                              false
% 1.81/1.02  --bmc1_add_unsat_core                   none
% 1.81/1.02  --bmc1_unsat_core_children              false
% 1.81/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 1.81/1.02  --bmc1_out_stat                         full
% 1.81/1.02  --bmc1_ground_init                      false
% 1.81/1.02  --bmc1_pre_inst_next_state              false
% 1.81/1.02  --bmc1_pre_inst_state                   false
% 1.81/1.02  --bmc1_pre_inst_reach_state             false
% 1.81/1.02  --bmc1_out_unsat_core                   false
% 1.81/1.02  --bmc1_aig_witness_out                  false
% 1.81/1.02  --bmc1_verbose                          false
% 1.81/1.02  --bmc1_dump_clauses_tptp                false
% 1.81/1.02  --bmc1_dump_unsat_core_tptp             false
% 1.81/1.02  --bmc1_dump_file                        -
% 1.81/1.02  --bmc1_ucm_expand_uc_limit              128
% 1.81/1.02  --bmc1_ucm_n_expand_iterations          6
% 1.81/1.02  --bmc1_ucm_extend_mode                  1
% 1.81/1.02  --bmc1_ucm_init_mode                    2
% 1.81/1.02  --bmc1_ucm_cone_mode                    none
% 1.81/1.02  --bmc1_ucm_reduced_relation_type        0
% 1.81/1.02  --bmc1_ucm_relax_model                  4
% 1.81/1.02  --bmc1_ucm_full_tr_after_sat            true
% 1.81/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 1.81/1.02  --bmc1_ucm_layered_model                none
% 1.81/1.02  --bmc1_ucm_max_lemma_size               10
% 1.81/1.02  
% 1.81/1.02  ------ AIG Options
% 1.81/1.02  
% 1.81/1.02  --aig_mode                              false
% 1.81/1.02  
% 1.81/1.02  ------ Instantiation Options
% 1.81/1.02  
% 1.81/1.02  --instantiation_flag                    true
% 1.81/1.02  --inst_sos_flag                         false
% 1.81/1.02  --inst_sos_phase                        true
% 1.81/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.81/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.81/1.02  --inst_lit_sel_side                     none
% 1.81/1.02  --inst_solver_per_active                1400
% 1.81/1.02  --inst_solver_calls_frac                1.
% 1.81/1.02  --inst_passive_queue_type               priority_queues
% 1.81/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.81/1.02  --inst_passive_queues_freq              [25;2]
% 1.81/1.02  --inst_dismatching                      true
% 1.81/1.02  --inst_eager_unprocessed_to_passive     true
% 1.81/1.02  --inst_prop_sim_given                   true
% 1.81/1.02  --inst_prop_sim_new                     false
% 1.81/1.02  --inst_subs_new                         false
% 1.81/1.02  --inst_eq_res_simp                      false
% 1.81/1.02  --inst_subs_given                       false
% 1.81/1.02  --inst_orphan_elimination               true
% 1.81/1.02  --inst_learning_loop_flag               true
% 1.81/1.02  --inst_learning_start                   3000
% 1.81/1.02  --inst_learning_factor                  2
% 1.81/1.02  --inst_start_prop_sim_after_learn       3
% 1.81/1.02  --inst_sel_renew                        solver
% 1.81/1.02  --inst_lit_activity_flag                true
% 1.81/1.02  --inst_restr_to_given                   false
% 1.81/1.02  --inst_activity_threshold               500
% 1.81/1.02  --inst_out_proof                        true
% 1.81/1.02  
% 1.81/1.02  ------ Resolution Options
% 1.81/1.02  
% 1.81/1.02  --resolution_flag                       false
% 1.81/1.02  --res_lit_sel                           adaptive
% 1.81/1.02  --res_lit_sel_side                      none
% 1.81/1.02  --res_ordering                          kbo
% 1.81/1.02  --res_to_prop_solver                    active
% 1.81/1.02  --res_prop_simpl_new                    false
% 1.81/1.02  --res_prop_simpl_given                  true
% 1.81/1.02  --res_passive_queue_type                priority_queues
% 1.81/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.81/1.02  --res_passive_queues_freq               [15;5]
% 1.81/1.02  --res_forward_subs                      full
% 1.81/1.02  --res_backward_subs                     full
% 1.81/1.02  --res_forward_subs_resolution           true
% 1.81/1.02  --res_backward_subs_resolution          true
% 1.81/1.02  --res_orphan_elimination                true
% 1.81/1.02  --res_time_limit                        2.
% 1.81/1.02  --res_out_proof                         true
% 1.81/1.02  
% 1.81/1.02  ------ Superposition Options
% 1.81/1.02  
% 1.81/1.02  --superposition_flag                    true
% 1.81/1.02  --sup_passive_queue_type                priority_queues
% 1.81/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.81/1.02  --sup_passive_queues_freq               [8;1;4]
% 1.81/1.02  --demod_completeness_check              fast
% 1.81/1.02  --demod_use_ground                      true
% 1.81/1.02  --sup_to_prop_solver                    passive
% 1.81/1.02  --sup_prop_simpl_new                    true
% 1.81/1.02  --sup_prop_simpl_given                  true
% 1.81/1.02  --sup_fun_splitting                     false
% 1.81/1.02  --sup_smt_interval                      50000
% 1.81/1.02  
% 1.81/1.02  ------ Superposition Simplification Setup
% 1.81/1.02  
% 1.81/1.02  --sup_indices_passive                   []
% 1.81/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.81/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.81/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.81/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 1.81/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.81/1.02  --sup_full_bw                           [BwDemod]
% 1.81/1.02  --sup_immed_triv                        [TrivRules]
% 1.81/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.81/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.81/1.02  --sup_immed_bw_main                     []
% 1.81/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.81/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 1.81/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.81/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.81/1.02  
% 1.81/1.02  ------ Combination Options
% 1.81/1.02  
% 1.81/1.02  --comb_res_mult                         3
% 1.81/1.02  --comb_sup_mult                         2
% 1.81/1.02  --comb_inst_mult                        10
% 1.81/1.02  
% 1.81/1.02  ------ Debug Options
% 1.81/1.02  
% 1.81/1.02  --dbg_backtrace                         false
% 1.81/1.02  --dbg_dump_prop_clauses                 false
% 1.81/1.02  --dbg_dump_prop_clauses_file            -
% 1.81/1.02  --dbg_out_stat                          false
% 1.81/1.02  
% 1.81/1.02  
% 1.81/1.02  
% 1.81/1.02  
% 1.81/1.02  ------ Proving...
% 1.81/1.02  
% 1.81/1.02  
% 1.81/1.02  % SZS status Theorem for theBenchmark.p
% 1.81/1.02  
% 1.81/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 1.81/1.02  
% 1.81/1.02  fof(f10,conjecture,(
% 1.81/1.02    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ~r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))))),
% 1.81/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.81/1.02  
% 1.81/1.02  fof(f11,negated_conjecture,(
% 1.81/1.02    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ~r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))))),
% 1.81/1.02    inference(negated_conjecture,[],[f10])).
% 1.81/1.02  
% 1.81/1.02  fof(f26,plain,(
% 1.81/1.02    ? [X0] : (? [X1] : (r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 1.81/1.02    inference(ennf_transformation,[],[f11])).
% 1.81/1.02  
% 1.81/1.02  fof(f27,plain,(
% 1.81/1.02    ? [X0] : (? [X1] : (r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.81/1.02    inference(flattening,[],[f26])).
% 1.81/1.02  
% 1.81/1.02  fof(f41,plain,(
% 1.81/1.02    ( ! [X0] : (? [X1] : (r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X1,u1_struct_0(X0))) => (r2_hidden(sK4,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),sK4))) & m1_subset_1(sK4,u1_struct_0(X0)))) )),
% 1.81/1.02    introduced(choice_axiom,[])).
% 1.81/1.02  
% 1.81/1.02  fof(f40,plain,(
% 1.81/1.02    ? [X0] : (? [X1] : (r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (r2_hidden(X1,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),X1))) & m1_subset_1(X1,u1_struct_0(sK3))) & l1_orders_2(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3))),
% 1.81/1.02    introduced(choice_axiom,[])).
% 1.81/1.02  
% 1.81/1.02  fof(f42,plain,(
% 1.81/1.02    (r2_hidden(sK4,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))) & m1_subset_1(sK4,u1_struct_0(sK3))) & l1_orders_2(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3)),
% 1.81/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f27,f41,f40])).
% 1.81/1.02  
% 1.81/1.02  fof(f72,plain,(
% 1.81/1.02    m1_subset_1(sK4,u1_struct_0(sK3))),
% 1.81/1.02    inference(cnf_transformation,[],[f42])).
% 1.81/1.02  
% 1.81/1.02  fof(f28,plain,(
% 1.81/1.02    ! [X2,X1,X0] : (? [X3] : (r2_hidden(X2,X3) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X3,X0)) | (~r1_orders_2(X0,X2,X1) & ~r1_orders_2(X0,X1,X2)) | ~sP0(X2,X1,X0))),
% 1.81/1.02    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.81/1.02  
% 1.81/1.02  fof(f35,plain,(
% 1.81/1.02    ! [X2,X1,X0] : (? [X3] : (r2_hidden(X2,X3) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X3,X0)) | (~r1_orders_2(X0,X2,X1) & ~r1_orders_2(X0,X1,X2)) | ~sP0(X2,X1,X0))),
% 1.81/1.02    inference(nnf_transformation,[],[f28])).
% 1.81/1.02  
% 1.81/1.02  fof(f36,plain,(
% 1.81/1.02    ! [X0,X1,X2] : (? [X3] : (r2_hidden(X0,X3) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) & v6_orders_2(X3,X2)) | (~r1_orders_2(X2,X0,X1) & ~r1_orders_2(X2,X1,X0)) | ~sP0(X0,X1,X2))),
% 1.81/1.02    inference(rectify,[],[f35])).
% 1.81/1.02  
% 1.81/1.02  fof(f37,plain,(
% 1.81/1.02    ! [X2,X1,X0] : (? [X3] : (r2_hidden(X0,X3) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) & v6_orders_2(X3,X2)) => (r2_hidden(X0,sK2(X0,X1,X2)) & r2_hidden(X1,sK2(X0,X1,X2)) & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) & v6_orders_2(sK2(X0,X1,X2),X2)))),
% 1.81/1.02    introduced(choice_axiom,[])).
% 1.81/1.02  
% 1.81/1.02  fof(f38,plain,(
% 1.81/1.02    ! [X0,X1,X2] : ((r2_hidden(X0,sK2(X0,X1,X2)) & r2_hidden(X1,sK2(X0,X1,X2)) & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) & v6_orders_2(sK2(X0,X1,X2),X2)) | (~r1_orders_2(X2,X0,X1) & ~r1_orders_2(X2,X1,X0)) | ~sP0(X0,X1,X2))),
% 1.81/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f36,f37])).
% 1.81/1.02  
% 1.81/1.02  fof(f63,plain,(
% 1.81/1.02    ( ! [X2,X0,X1] : (r2_hidden(X0,sK2(X0,X1,X2)) | ~r1_orders_2(X2,X0,X1) | ~sP0(X0,X1,X2)) )),
% 1.81/1.02    inference(cnf_transformation,[],[f38])).
% 1.81/1.02  
% 1.81/1.02  fof(f8,axiom,(
% 1.81/1.02    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (~(! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X3,X0)) => ~(r2_hidden(X2,X3) & r2_hidden(X1,X3))) & (r1_orders_2(X0,X2,X1) | r1_orders_2(X0,X1,X2))) & ~(~r1_orders_2(X0,X2,X1) & ~r1_orders_2(X0,X1,X2) & ? [X3] : (r2_hidden(X2,X3) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X3,X0)))))))),
% 1.81/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.81/1.02  
% 1.81/1.02  fof(f12,plain,(
% 1.81/1.02    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (~(! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X3,X0)) => ~(r2_hidden(X2,X3) & r2_hidden(X1,X3))) & (r1_orders_2(X0,X2,X1) | r1_orders_2(X0,X1,X2))) & ~(~r1_orders_2(X0,X2,X1) & ~r1_orders_2(X0,X1,X2) & ? [X4] : (r2_hidden(X2,X4) & r2_hidden(X1,X4) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X4,X0)))))))),
% 1.81/1.02    inference(rectify,[],[f8])).
% 1.81/1.02  
% 1.81/1.02  fof(f22,plain,(
% 1.81/1.02    ! [X0] : (! [X1] : (! [X2] : (((? [X3] : ((r2_hidden(X2,X3) & r2_hidden(X1,X3)) & (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X3,X0))) | (~r1_orders_2(X0,X2,X1) & ~r1_orders_2(X0,X1,X2))) & (r1_orders_2(X0,X2,X1) | r1_orders_2(X0,X1,X2) | ! [X4] : (~r2_hidden(X2,X4) | ~r2_hidden(X1,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X4,X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v3_orders_2(X0)))),
% 1.81/1.02    inference(ennf_transformation,[],[f12])).
% 1.81/1.02  
% 1.81/1.02  fof(f23,plain,(
% 1.81/1.02    ! [X0] : (! [X1] : (! [X2] : (((? [X3] : (r2_hidden(X2,X3) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X3,X0)) | (~r1_orders_2(X0,X2,X1) & ~r1_orders_2(X0,X1,X2))) & (r1_orders_2(X0,X2,X1) | r1_orders_2(X0,X1,X2) | ! [X4] : (~r2_hidden(X2,X4) | ~r2_hidden(X1,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X4,X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_orders_2(X0))),
% 1.81/1.02    inference(flattening,[],[f22])).
% 1.81/1.02  
% 1.81/1.02  fof(f29,plain,(
% 1.81/1.02    ! [X0] : (! [X1] : (! [X2] : ((sP0(X2,X1,X0) & (r1_orders_2(X0,X2,X1) | r1_orders_2(X0,X1,X2) | ! [X4] : (~r2_hidden(X2,X4) | ~r2_hidden(X1,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X4,X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_orders_2(X0))),
% 1.81/1.02    inference(definition_folding,[],[f23,f28])).
% 1.81/1.02  
% 1.81/1.02  fof(f39,plain,(
% 1.81/1.02    ! [X0] : (! [X1] : (! [X2] : ((sP0(X2,X1,X0) & (r1_orders_2(X0,X2,X1) | r1_orders_2(X0,X1,X2) | ! [X3] : (~r2_hidden(X2,X3) | ~r2_hidden(X1,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X3,X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_orders_2(X0))),
% 1.81/1.02    inference(rectify,[],[f29])).
% 1.81/1.02  
% 1.81/1.02  fof(f65,plain,(
% 1.81/1.02    ( ! [X2,X0,X1] : (sP0(X2,X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0)) )),
% 1.81/1.02    inference(cnf_transformation,[],[f39])).
% 1.81/1.02  
% 1.81/1.02  fof(f71,plain,(
% 1.81/1.02    l1_orders_2(sK3)),
% 1.81/1.02    inference(cnf_transformation,[],[f42])).
% 1.81/1.02  
% 1.81/1.02  fof(f68,plain,(
% 1.81/1.02    v3_orders_2(sK3)),
% 1.81/1.02    inference(cnf_transformation,[],[f42])).
% 1.81/1.02  
% 1.81/1.02  fof(f59,plain,(
% 1.81/1.02    ( ! [X2,X0,X1] : (m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) | ~r1_orders_2(X2,X0,X1) | ~sP0(X0,X1,X2)) )),
% 1.81/1.02    inference(cnf_transformation,[],[f38])).
% 1.81/1.02  
% 1.81/1.02  fof(f4,axiom,(
% 1.81/1.02    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.81/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.81/1.02  
% 1.81/1.02  fof(f15,plain,(
% 1.81/1.02    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.81/1.02    inference(ennf_transformation,[],[f4])).
% 1.81/1.02  
% 1.81/1.02  fof(f51,plain,(
% 1.81/1.02    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.81/1.02    inference(cnf_transformation,[],[f15])).
% 1.81/1.02  
% 1.81/1.02  fof(f5,axiom,(
% 1.81/1.02    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 1.81/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.81/1.02  
% 1.81/1.02  fof(f16,plain,(
% 1.81/1.02    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.81/1.02    inference(ennf_transformation,[],[f5])).
% 1.81/1.02  
% 1.81/1.02  fof(f17,plain,(
% 1.81/1.02    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.81/1.02    inference(flattening,[],[f16])).
% 1.81/1.02  
% 1.81/1.02  fof(f52,plain,(
% 1.81/1.02    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.81/1.02    inference(cnf_transformation,[],[f17])).
% 1.81/1.02  
% 1.81/1.02  fof(f2,axiom,(
% 1.81/1.02    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.81/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.81/1.02  
% 1.81/1.02  fof(f49,plain,(
% 1.81/1.02    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.81/1.02    inference(cnf_transformation,[],[f2])).
% 1.81/1.02  
% 1.81/1.02  fof(f74,plain,(
% 1.81/1.02    ( ! [X0,X1] : (k2_tarski(X1,X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.81/1.02    inference(definition_unfolding,[],[f52,f49])).
% 1.81/1.02  
% 1.81/1.02  fof(f73,plain,(
% 1.81/1.02    r2_hidden(sK4,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4)))),
% 1.81/1.02    inference(cnf_transformation,[],[f42])).
% 1.81/1.02  
% 1.81/1.02  fof(f7,axiom,(
% 1.81/1.02    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0))))),
% 1.81/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.81/1.02  
% 1.81/1.02  fof(f20,plain,(
% 1.81/1.02    ! [X0] : (! [X1] : ((m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.81/1.02    inference(ennf_transformation,[],[f7])).
% 1.81/1.02  
% 1.81/1.02  fof(f21,plain,(
% 1.81/1.02    ! [X0] : (! [X1] : ((m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.81/1.02    inference(flattening,[],[f20])).
% 1.81/1.02  
% 1.81/1.02  fof(f55,plain,(
% 1.81/1.02    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.81/1.02    inference(cnf_transformation,[],[f21])).
% 1.81/1.02  
% 1.81/1.02  fof(f67,plain,(
% 1.81/1.02    ~v2_struct_0(sK3)),
% 1.81/1.02    inference(cnf_transformation,[],[f42])).
% 1.81/1.02  
% 1.81/1.02  fof(f9,axiom,(
% 1.81/1.02    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(r2_hidden(X1,k1_orders_2(X0,X2)) & r2_hidden(X1,X2)))))),
% 1.81/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.81/1.02  
% 1.81/1.02  fof(f24,plain,(
% 1.81/1.02    ! [X0] : (! [X1] : (! [X2] : ((~r2_hidden(X1,k1_orders_2(X0,X2)) | ~r2_hidden(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.81/1.02    inference(ennf_transformation,[],[f9])).
% 1.81/1.02  
% 1.81/1.02  fof(f25,plain,(
% 1.81/1.02    ! [X0] : (! [X1] : (! [X2] : (~r2_hidden(X1,k1_orders_2(X0,X2)) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.81/1.02    inference(flattening,[],[f24])).
% 1.81/1.02  
% 1.81/1.02  fof(f66,plain,(
% 1.81/1.02    ( ! [X2,X0,X1] : (~r2_hidden(X1,k1_orders_2(X0,X2)) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.81/1.02    inference(cnf_transformation,[],[f25])).
% 1.81/1.02  
% 1.81/1.02  fof(f70,plain,(
% 1.81/1.02    v5_orders_2(sK3)),
% 1.81/1.02    inference(cnf_transformation,[],[f42])).
% 1.81/1.02  
% 1.81/1.02  fof(f69,plain,(
% 1.81/1.02    v4_orders_2(sK3)),
% 1.81/1.02    inference(cnf_transformation,[],[f42])).
% 1.81/1.02  
% 1.81/1.02  fof(f3,axiom,(
% 1.81/1.02    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 1.81/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.81/1.02  
% 1.81/1.02  fof(f13,plain,(
% 1.81/1.02    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 1.81/1.02    inference(ennf_transformation,[],[f3])).
% 1.81/1.02  
% 1.81/1.02  fof(f14,plain,(
% 1.81/1.02    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.81/1.02    inference(flattening,[],[f13])).
% 1.81/1.02  
% 1.81/1.02  fof(f50,plain,(
% 1.81/1.02    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.81/1.02    inference(cnf_transformation,[],[f14])).
% 1.81/1.02  
% 1.81/1.02  fof(f1,axiom,(
% 1.81/1.02    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.81/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.81/1.02  
% 1.81/1.02  fof(f30,plain,(
% 1.81/1.02    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 1.81/1.02    inference(nnf_transformation,[],[f1])).
% 1.81/1.02  
% 1.81/1.02  fof(f31,plain,(
% 1.81/1.02    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 1.81/1.02    inference(flattening,[],[f30])).
% 1.81/1.02  
% 1.81/1.02  fof(f32,plain,(
% 1.81/1.02    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 1.81/1.02    inference(rectify,[],[f31])).
% 1.81/1.02  
% 1.81/1.02  fof(f33,plain,(
% 1.81/1.02    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK1(X0,X1,X2) != X1 & sK1(X0,X1,X2) != X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (sK1(X0,X1,X2) = X1 | sK1(X0,X1,X2) = X0 | r2_hidden(sK1(X0,X1,X2),X2))))),
% 1.81/1.02    introduced(choice_axiom,[])).
% 1.81/1.02  
% 1.81/1.02  fof(f34,plain,(
% 1.81/1.02    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK1(X0,X1,X2) != X1 & sK1(X0,X1,X2) != X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (sK1(X0,X1,X2) = X1 | sK1(X0,X1,X2) = X0 | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 1.81/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f32,f33])).
% 1.81/1.02  
% 1.81/1.02  fof(f45,plain,(
% 1.81/1.02    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 1.81/1.02    inference(cnf_transformation,[],[f34])).
% 1.81/1.02  
% 1.81/1.02  fof(f75,plain,(
% 1.81/1.02    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k2_tarski(X0,X4) != X2) )),
% 1.81/1.02    inference(equality_resolution,[],[f45])).
% 1.81/1.02  
% 1.81/1.02  fof(f76,plain,(
% 1.81/1.02    ( ! [X4,X0] : (r2_hidden(X4,k2_tarski(X0,X4))) )),
% 1.81/1.02    inference(equality_resolution,[],[f75])).
% 1.81/1.02  
% 1.81/1.02  fof(f6,axiom,(
% 1.81/1.02    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r1_orders_2(X0,X1,X1)))),
% 1.81/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.81/1.02  
% 1.81/1.02  fof(f18,plain,(
% 1.81/1.02    ! [X0] : (! [X1] : (r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.81/1.02    inference(ennf_transformation,[],[f6])).
% 1.81/1.02  
% 1.81/1.02  fof(f19,plain,(
% 1.81/1.02    ! [X0] : (! [X1] : (r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.81/1.02    inference(flattening,[],[f18])).
% 1.81/1.02  
% 1.81/1.02  fof(f53,plain,(
% 1.81/1.02    ( ! [X0,X1] : (r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.81/1.02    inference(cnf_transformation,[],[f19])).
% 1.81/1.02  
% 1.81/1.02  cnf(c_24,negated_conjecture,
% 1.81/1.02      ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 1.81/1.02      inference(cnf_transformation,[],[f72]) ).
% 1.81/1.02  
% 1.81/1.02  cnf(c_1571,plain,
% 1.81/1.02      ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
% 1.81/1.02      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 1.81/1.02  
% 1.81/1.02  cnf(c_12,plain,
% 1.81/1.02      ( ~ sP0(X0,X1,X2)
% 1.81/1.02      | ~ r1_orders_2(X2,X0,X1)
% 1.81/1.02      | r2_hidden(X0,sK2(X0,X1,X2)) ),
% 1.81/1.02      inference(cnf_transformation,[],[f63]) ).
% 1.81/1.02  
% 1.81/1.02  cnf(c_20,plain,
% 1.81/1.02      ( sP0(X0,X1,X2)
% 1.81/1.02      | ~ m1_subset_1(X1,u1_struct_0(X2))
% 1.81/1.02      | ~ m1_subset_1(X0,u1_struct_0(X2))
% 1.81/1.02      | ~ v3_orders_2(X2)
% 1.81/1.02      | ~ l1_orders_2(X2) ),
% 1.81/1.02      inference(cnf_transformation,[],[f65]) ).
% 1.81/1.02  
% 1.81/1.02  cnf(c_25,negated_conjecture,
% 1.81/1.02      ( l1_orders_2(sK3) ),
% 1.81/1.02      inference(cnf_transformation,[],[f71]) ).
% 1.81/1.02  
% 1.81/1.02  cnf(c_468,plain,
% 1.81/1.02      ( sP0(X0,X1,X2)
% 1.81/1.02      | ~ m1_subset_1(X1,u1_struct_0(X2))
% 1.81/1.02      | ~ m1_subset_1(X0,u1_struct_0(X2))
% 1.81/1.02      | ~ v3_orders_2(X2)
% 1.81/1.02      | sK3 != X2 ),
% 1.81/1.02      inference(resolution_lifted,[status(thm)],[c_20,c_25]) ).
% 1.81/1.02  
% 1.81/1.02  cnf(c_469,plain,
% 1.81/1.02      ( sP0(X0,X1,sK3)
% 1.81/1.02      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.81/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.81/1.02      | ~ v3_orders_2(sK3) ),
% 1.81/1.02      inference(unflattening,[status(thm)],[c_468]) ).
% 1.81/1.02  
% 1.81/1.02  cnf(c_28,negated_conjecture,
% 1.81/1.02      ( v3_orders_2(sK3) ),
% 1.81/1.02      inference(cnf_transformation,[],[f68]) ).
% 1.81/1.02  
% 1.81/1.02  cnf(c_473,plain,
% 1.81/1.02      ( ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.81/1.02      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.81/1.02      | sP0(X0,X1,sK3) ),
% 1.81/1.02      inference(global_propositional_subsumption,
% 1.81/1.02                [status(thm)],
% 1.81/1.02                [c_469,c_28]) ).
% 1.81/1.02  
% 1.81/1.02  cnf(c_474,plain,
% 1.81/1.02      ( sP0(X0,X1,sK3)
% 1.81/1.02      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.81/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK3)) ),
% 1.81/1.02      inference(renaming,[status(thm)],[c_473]) ).
% 1.81/1.02  
% 1.81/1.02  cnf(c_707,plain,
% 1.81/1.02      ( ~ r1_orders_2(X0,X1,X2)
% 1.81/1.02      | ~ m1_subset_1(X3,u1_struct_0(sK3))
% 1.81/1.02      | ~ m1_subset_1(X4,u1_struct_0(sK3))
% 1.81/1.02      | r2_hidden(X1,sK2(X1,X2,X0))
% 1.81/1.02      | X4 != X2
% 1.81/1.02      | X3 != X1
% 1.81/1.02      | sK3 != X0 ),
% 1.81/1.02      inference(resolution_lifted,[status(thm)],[c_12,c_474]) ).
% 1.81/1.02  
% 1.81/1.02  cnf(c_708,plain,
% 1.81/1.02      ( ~ r1_orders_2(sK3,X0,X1)
% 1.81/1.02      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.81/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.81/1.02      | r2_hidden(X0,sK2(X0,X1,sK3)) ),
% 1.81/1.02      inference(unflattening,[status(thm)],[c_707]) ).
% 1.81/1.02  
% 1.81/1.02  cnf(c_1558,plain,
% 1.81/1.02      ( r1_orders_2(sK3,X0,X1) != iProver_top
% 1.81/1.02      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 1.81/1.02      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
% 1.81/1.02      | r2_hidden(X0,sK2(X0,X1,sK3)) = iProver_top ),
% 1.81/1.02      inference(predicate_to_equality,[status(thm)],[c_708]) ).
% 1.81/1.02  
% 1.81/1.02  cnf(c_16,plain,
% 1.81/1.02      ( ~ sP0(X0,X1,X2)
% 1.81/1.02      | ~ r1_orders_2(X2,X0,X1)
% 1.81/1.02      | m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) ),
% 1.81/1.02      inference(cnf_transformation,[],[f59]) ).
% 1.81/1.02  
% 1.81/1.02  cnf(c_641,plain,
% 1.81/1.02      ( ~ r1_orders_2(X0,X1,X2)
% 1.81/1.02      | ~ m1_subset_1(X3,u1_struct_0(sK3))
% 1.81/1.02      | ~ m1_subset_1(X4,u1_struct_0(sK3))
% 1.81/1.02      | m1_subset_1(sK2(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X0)))
% 1.81/1.02      | X4 != X2
% 1.81/1.02      | X3 != X1
% 1.81/1.02      | sK3 != X0 ),
% 1.81/1.02      inference(resolution_lifted,[status(thm)],[c_16,c_474]) ).
% 1.81/1.02  
% 1.81/1.02  cnf(c_642,plain,
% 1.81/1.02      ( ~ r1_orders_2(sK3,X0,X1)
% 1.81/1.02      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.81/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.81/1.02      | m1_subset_1(sK2(X0,X1,sK3),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 1.81/1.02      inference(unflattening,[status(thm)],[c_641]) ).
% 1.81/1.02  
% 1.81/1.02  cnf(c_1562,plain,
% 1.81/1.02      ( r1_orders_2(sK3,X0,X1) != iProver_top
% 1.81/1.02      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 1.81/1.02      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
% 1.81/1.02      | m1_subset_1(sK2(X0,X1,sK3),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 1.81/1.02      inference(predicate_to_equality,[status(thm)],[c_642]) ).
% 1.81/1.02  
% 1.81/1.02  cnf(c_7,plain,
% 1.81/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.81/1.02      | ~ r2_hidden(X2,X0)
% 1.81/1.02      | ~ v1_xboole_0(X1) ),
% 1.81/1.02      inference(cnf_transformation,[],[f51]) ).
% 1.81/1.02  
% 1.81/1.02  cnf(c_1574,plain,
% 1.81/1.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 1.81/1.02      | r2_hidden(X2,X0) != iProver_top
% 1.81/1.02      | v1_xboole_0(X1) != iProver_top ),
% 1.81/1.02      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 1.81/1.02  
% 1.81/1.02  cnf(c_2794,plain,
% 1.81/1.02      ( r1_orders_2(sK3,X0,X1) != iProver_top
% 1.81/1.02      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 1.81/1.02      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
% 1.81/1.02      | r2_hidden(X2,sK2(X0,X1,sK3)) != iProver_top
% 1.81/1.02      | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
% 1.81/1.02      inference(superposition,[status(thm)],[c_1562,c_1574]) ).
% 1.81/1.02  
% 1.81/1.02  cnf(c_35,plain,
% 1.81/1.02      ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
% 1.81/1.02      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 1.81/1.02  
% 1.81/1.02  cnf(c_8,plain,
% 1.81/1.02      ( ~ m1_subset_1(X0,X1)
% 1.81/1.02      | v1_xboole_0(X1)
% 1.81/1.02      | k6_domain_1(X1,X0) = k2_tarski(X0,X0) ),
% 1.81/1.02      inference(cnf_transformation,[],[f74]) ).
% 1.81/1.02  
% 1.81/1.02  cnf(c_1853,plain,
% 1.81/1.02      ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
% 1.81/1.02      | v1_xboole_0(u1_struct_0(sK3))
% 1.81/1.02      | k6_domain_1(u1_struct_0(sK3),sK4) = k2_tarski(sK4,sK4) ),
% 1.81/1.02      inference(instantiation,[status(thm)],[c_8]) ).
% 1.81/1.02  
% 1.81/1.02  cnf(c_1854,plain,
% 1.81/1.02      ( k6_domain_1(u1_struct_0(sK3),sK4) = k2_tarski(sK4,sK4)
% 1.81/1.02      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 1.81/1.02      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 1.81/1.02      inference(predicate_to_equality,[status(thm)],[c_1853]) ).
% 1.81/1.02  
% 1.81/1.02  cnf(c_23,negated_conjecture,
% 1.81/1.02      ( r2_hidden(sK4,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))) ),
% 1.81/1.02      inference(cnf_transformation,[],[f73]) ).
% 1.81/1.02  
% 1.81/1.02  cnf(c_1572,plain,
% 1.81/1.02      ( r2_hidden(sK4,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))) = iProver_top ),
% 1.81/1.02      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 1.81/1.02  
% 1.81/1.02  cnf(c_10,plain,
% 1.81/1.02      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.81/1.02      | m1_subset_1(k6_domain_1(u1_struct_0(X1),X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.81/1.02      | v2_struct_0(X1)
% 1.81/1.02      | ~ v3_orders_2(X1)
% 1.81/1.02      | ~ l1_orders_2(X1) ),
% 1.81/1.02      inference(cnf_transformation,[],[f55]) ).
% 1.81/1.02  
% 1.81/1.02  cnf(c_29,negated_conjecture,
% 1.81/1.02      ( ~ v2_struct_0(sK3) ),
% 1.81/1.02      inference(cnf_transformation,[],[f67]) ).
% 1.81/1.02  
% 1.81/1.02  cnf(c_404,plain,
% 1.81/1.02      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.81/1.02      | m1_subset_1(k6_domain_1(u1_struct_0(X1),X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.81/1.02      | ~ v3_orders_2(X1)
% 1.81/1.02      | ~ l1_orders_2(X1)
% 1.81/1.02      | sK3 != X1 ),
% 1.81/1.02      inference(resolution_lifted,[status(thm)],[c_10,c_29]) ).
% 1.81/1.02  
% 1.81/1.02  cnf(c_405,plain,
% 1.81/1.02      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.81/1.02      | m1_subset_1(k6_domain_1(u1_struct_0(sK3),X0),k1_zfmisc_1(u1_struct_0(sK3)))
% 1.81/1.02      | ~ v3_orders_2(sK3)
% 1.81/1.02      | ~ l1_orders_2(sK3) ),
% 1.81/1.02      inference(unflattening,[status(thm)],[c_404]) ).
% 1.81/1.02  
% 1.81/1.02  cnf(c_409,plain,
% 1.81/1.02      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.81/1.02      | m1_subset_1(k6_domain_1(u1_struct_0(sK3),X0),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 1.81/1.02      inference(global_propositional_subsumption,
% 1.81/1.02                [status(thm)],
% 1.81/1.02                [c_405,c_28,c_25]) ).
% 1.81/1.02  
% 1.81/1.02  cnf(c_1567,plain,
% 1.81/1.02      ( m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 1.81/1.02      | m1_subset_1(k6_domain_1(u1_struct_0(sK3),X0),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 1.81/1.02      inference(predicate_to_equality,[status(thm)],[c_409]) ).
% 1.81/1.02  
% 1.81/1.02  cnf(c_22,plain,
% 1.81/1.02      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.81/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.81/1.02      | ~ r2_hidden(X0,X2)
% 1.81/1.02      | ~ r2_hidden(X0,k1_orders_2(X1,X2))
% 1.81/1.02      | ~ v4_orders_2(X1)
% 1.81/1.02      | ~ v5_orders_2(X1)
% 1.81/1.02      | v2_struct_0(X1)
% 1.81/1.02      | ~ v3_orders_2(X1)
% 1.81/1.02      | ~ l1_orders_2(X1) ),
% 1.81/1.02      inference(cnf_transformation,[],[f66]) ).
% 1.81/1.02  
% 1.81/1.02  cnf(c_26,negated_conjecture,
% 1.81/1.02      ( v5_orders_2(sK3) ),
% 1.81/1.02      inference(cnf_transformation,[],[f70]) ).
% 1.81/1.02  
% 1.81/1.02  cnf(c_338,plain,
% 1.81/1.02      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.81/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.81/1.02      | ~ r2_hidden(X0,X2)
% 1.81/1.02      | ~ r2_hidden(X0,k1_orders_2(X1,X2))
% 1.81/1.02      | ~ v4_orders_2(X1)
% 1.81/1.02      | v2_struct_0(X1)
% 1.81/1.02      | ~ v3_orders_2(X1)
% 1.81/1.02      | ~ l1_orders_2(X1)
% 1.81/1.02      | sK3 != X1 ),
% 1.81/1.02      inference(resolution_lifted,[status(thm)],[c_22,c_26]) ).
% 1.81/1.02  
% 1.81/1.02  cnf(c_339,plain,
% 1.81/1.02      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.81/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.81/1.02      | ~ r2_hidden(X0,X1)
% 1.81/1.02      | ~ r2_hidden(X0,k1_orders_2(sK3,X1))
% 1.81/1.02      | ~ v4_orders_2(sK3)
% 1.81/1.02      | v2_struct_0(sK3)
% 1.81/1.02      | ~ v3_orders_2(sK3)
% 1.81/1.02      | ~ l1_orders_2(sK3) ),
% 1.81/1.02      inference(unflattening,[status(thm)],[c_338]) ).
% 1.81/1.02  
% 1.81/1.02  cnf(c_27,negated_conjecture,
% 1.81/1.02      ( v4_orders_2(sK3) ),
% 1.81/1.02      inference(cnf_transformation,[],[f69]) ).
% 1.81/1.02  
% 1.81/1.02  cnf(c_343,plain,
% 1.81/1.02      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.81/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.81/1.02      | ~ r2_hidden(X0,X1)
% 1.81/1.02      | ~ r2_hidden(X0,k1_orders_2(sK3,X1)) ),
% 1.81/1.02      inference(global_propositional_subsumption,
% 1.81/1.02                [status(thm)],
% 1.81/1.02                [c_339,c_29,c_28,c_27,c_25]) ).
% 1.81/1.02  
% 1.81/1.02  cnf(c_6,plain,
% 1.81/1.02      ( m1_subset_1(X0,X1)
% 1.81/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 1.81/1.02      | ~ r2_hidden(X0,X2) ),
% 1.81/1.02      inference(cnf_transformation,[],[f50]) ).
% 1.81/1.02  
% 1.81/1.02  cnf(c_357,plain,
% 1.81/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.81/1.02      | ~ r2_hidden(X1,X0)
% 1.81/1.02      | ~ r2_hidden(X1,k1_orders_2(sK3,X0)) ),
% 1.81/1.02      inference(forward_subsumption_resolution,[status(thm)],[c_343,c_6]) ).
% 1.81/1.02  
% 1.81/1.02  cnf(c_1570,plain,
% 1.81/1.02      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 1.81/1.02      | r2_hidden(X1,X0) != iProver_top
% 1.81/1.02      | r2_hidden(X1,k1_orders_2(sK3,X0)) != iProver_top ),
% 1.81/1.02      inference(predicate_to_equality,[status(thm)],[c_357]) ).
% 1.81/1.02  
% 1.81/1.02  cnf(c_1915,plain,
% 1.81/1.02      ( m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 1.81/1.02      | r2_hidden(X1,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),X0))) != iProver_top
% 1.81/1.02      | r2_hidden(X1,k6_domain_1(u1_struct_0(sK3),X0)) != iProver_top ),
% 1.81/1.02      inference(superposition,[status(thm)],[c_1567,c_1570]) ).
% 1.81/1.02  
% 1.81/1.02  cnf(c_1923,plain,
% 1.81/1.02      ( m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 1.81/1.02      | r2_hidden(sK4,k6_domain_1(u1_struct_0(sK3),sK4)) != iProver_top ),
% 1.81/1.02      inference(superposition,[status(thm)],[c_1572,c_1915]) ).
% 1.81/1.02  
% 1.81/1.02  cnf(c_1924,plain,
% 1.81/1.02      ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
% 1.81/1.02      | ~ r2_hidden(sK4,k6_domain_1(u1_struct_0(sK3),sK4)) ),
% 1.81/1.02      inference(predicate_to_equality_rev,[status(thm)],[c_1923]) ).
% 1.81/1.02  
% 1.81/1.02  cnf(c_1142,plain,( X0 = X0 ),theory(equality) ).
% 1.81/1.02  
% 1.81/1.02  cnf(c_2020,plain,
% 1.81/1.02      ( sK4 = sK4 ),
% 1.81/1.02      inference(instantiation,[status(thm)],[c_1142]) ).
% 1.81/1.02  
% 1.81/1.02  cnf(c_1144,plain,
% 1.81/1.02      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 1.81/1.02      theory(equality) ).
% 1.81/1.02  
% 1.81/1.02  cnf(c_1856,plain,
% 1.81/1.02      ( r2_hidden(X0,X1)
% 1.81/1.02      | ~ r2_hidden(X2,k2_tarski(X3,X2))
% 1.81/1.02      | X0 != X2
% 1.81/1.02      | X1 != k2_tarski(X3,X2) ),
% 1.81/1.02      inference(instantiation,[status(thm)],[c_1144]) ).
% 1.81/1.02  
% 1.81/1.02  cnf(c_2170,plain,
% 1.81/1.02      ( r2_hidden(X0,k6_domain_1(u1_struct_0(sK3),sK4))
% 1.81/1.02      | ~ r2_hidden(sK4,k2_tarski(sK4,sK4))
% 1.81/1.02      | X0 != sK4
% 1.81/1.02      | k6_domain_1(u1_struct_0(sK3),sK4) != k2_tarski(sK4,sK4) ),
% 1.81/1.02      inference(instantiation,[status(thm)],[c_1856]) ).
% 1.81/1.02  
% 1.81/1.02  cnf(c_2266,plain,
% 1.81/1.02      ( r2_hidden(sK4,k6_domain_1(u1_struct_0(sK3),sK4))
% 1.81/1.02      | ~ r2_hidden(sK4,k2_tarski(sK4,sK4))
% 1.81/1.02      | k6_domain_1(u1_struct_0(sK3),sK4) != k2_tarski(sK4,sK4)
% 1.81/1.02      | sK4 != sK4 ),
% 1.81/1.02      inference(instantiation,[status(thm)],[c_2170]) ).
% 1.81/1.02  
% 1.81/1.02  cnf(c_3,plain,
% 1.81/1.02      ( r2_hidden(X0,k2_tarski(X1,X0)) ),
% 1.81/1.02      inference(cnf_transformation,[],[f76]) ).
% 1.81/1.02  
% 1.81/1.02  cnf(c_2474,plain,
% 1.81/1.02      ( r2_hidden(sK4,k2_tarski(sK4,sK4)) ),
% 1.81/1.02      inference(instantiation,[status(thm)],[c_3]) ).
% 1.81/1.02  
% 1.81/1.02  cnf(c_3746,plain,
% 1.81/1.02      ( r2_hidden(X2,sK2(X0,X1,sK3)) != iProver_top
% 1.81/1.02      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
% 1.81/1.02      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 1.81/1.02      | r1_orders_2(sK3,X0,X1) != iProver_top ),
% 1.81/1.02      inference(global_propositional_subsumption,
% 1.81/1.02                [status(thm)],
% 1.81/1.02                [c_2794,c_24,c_35,c_1854,c_1924,c_2020,c_2266,c_2474]) ).
% 1.81/1.02  
% 1.81/1.02  cnf(c_3747,plain,
% 1.81/1.02      ( r1_orders_2(sK3,X0,X1) != iProver_top
% 1.81/1.02      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 1.81/1.02      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
% 1.81/1.02      | r2_hidden(X2,sK2(X0,X1,sK3)) != iProver_top ),
% 1.81/1.02      inference(renaming,[status(thm)],[c_3746]) ).
% 1.81/1.02  
% 1.81/1.02  cnf(c_3759,plain,
% 1.81/1.02      ( r1_orders_2(sK3,X0,X1) != iProver_top
% 1.81/1.02      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 1.81/1.02      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top ),
% 1.81/1.02      inference(superposition,[status(thm)],[c_1558,c_3747]) ).
% 1.81/1.02  
% 1.81/1.02  cnf(c_3773,plain,
% 1.81/1.02      ( r1_orders_2(sK3,sK4,X0) != iProver_top
% 1.81/1.02      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
% 1.81/1.02      inference(superposition,[status(thm)],[c_1571,c_3759]) ).
% 1.81/1.02  
% 1.81/1.02  cnf(c_3837,plain,
% 1.81/1.02      ( r1_orders_2(sK3,sK4,sK4) != iProver_top ),
% 1.81/1.02      inference(superposition,[status(thm)],[c_1571,c_3773]) ).
% 1.81/1.02  
% 1.81/1.02  cnf(c_9,plain,
% 1.81/1.02      ( r1_orders_2(X0,X1,X1)
% 1.81/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.81/1.02      | v2_struct_0(X0)
% 1.81/1.02      | ~ v3_orders_2(X0)
% 1.81/1.02      | ~ l1_orders_2(X0) ),
% 1.81/1.02      inference(cnf_transformation,[],[f53]) ).
% 1.81/1.02  
% 1.81/1.02  cnf(c_386,plain,
% 1.81/1.02      ( r1_orders_2(X0,X1,X1)
% 1.81/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.81/1.02      | ~ v3_orders_2(X0)
% 1.81/1.02      | ~ l1_orders_2(X0)
% 1.81/1.02      | sK3 != X0 ),
% 1.81/1.02      inference(resolution_lifted,[status(thm)],[c_9,c_29]) ).
% 1.81/1.02  
% 1.81/1.02  cnf(c_387,plain,
% 1.81/1.02      ( r1_orders_2(sK3,X0,X0)
% 1.81/1.02      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.81/1.02      | ~ v3_orders_2(sK3)
% 1.81/1.02      | ~ l1_orders_2(sK3) ),
% 1.81/1.02      inference(unflattening,[status(thm)],[c_386]) ).
% 1.81/1.02  
% 1.81/1.02  cnf(c_391,plain,
% 1.81/1.02      ( r1_orders_2(sK3,X0,X0) | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 1.81/1.02      inference(global_propositional_subsumption,
% 1.81/1.02                [status(thm)],
% 1.81/1.02                [c_387,c_28,c_25]) ).
% 1.81/1.02  
% 1.81/1.02  cnf(c_1786,plain,
% 1.81/1.02      ( r1_orders_2(sK3,sK4,sK4) | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 1.81/1.02      inference(instantiation,[status(thm)],[c_391]) ).
% 1.81/1.02  
% 1.81/1.02  cnf(c_1787,plain,
% 1.81/1.02      ( r1_orders_2(sK3,sK4,sK4) = iProver_top
% 1.81/1.02      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
% 1.81/1.02      inference(predicate_to_equality,[status(thm)],[c_1786]) ).
% 1.81/1.02  
% 1.81/1.02  cnf(contradiction,plain,
% 1.81/1.02      ( $false ),
% 1.81/1.02      inference(minisat,[status(thm)],[c_3837,c_1787,c_35]) ).
% 1.81/1.02  
% 1.81/1.02  
% 1.81/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 1.81/1.02  
% 1.81/1.02  ------                               Statistics
% 1.81/1.02  
% 1.81/1.02  ------ General
% 1.81/1.02  
% 1.81/1.02  abstr_ref_over_cycles:                  0
% 1.81/1.02  abstr_ref_under_cycles:                 0
% 1.81/1.02  gc_basic_clause_elim:                   0
% 1.81/1.02  forced_gc_time:                         0
% 1.81/1.02  parsing_time:                           0.03
% 1.81/1.02  unif_index_cands_time:                  0.
% 1.81/1.02  unif_index_add_time:                    0.
% 1.81/1.02  orderings_time:                         0.
% 1.81/1.02  out_proof_time:                         0.007
% 1.81/1.02  total_time:                             0.177
% 1.81/1.02  num_of_symbols:                         51
% 1.81/1.02  num_of_terms:                           3534
% 1.81/1.02  
% 1.81/1.02  ------ Preprocessing
% 1.81/1.02  
% 1.81/1.02  num_of_splits:                          0
% 1.81/1.02  num_of_split_atoms:                     0
% 1.81/1.02  num_of_reused_defs:                     0
% 1.81/1.02  num_eq_ax_congr_red:                    36
% 1.81/1.02  num_of_sem_filtered_clauses:            1
% 1.81/1.02  num_of_subtypes:                        0
% 1.81/1.02  monotx_restored_types:                  0
% 1.81/1.02  sat_num_of_epr_types:                   0
% 1.81/1.02  sat_num_of_non_cyclic_types:            0
% 1.81/1.02  sat_guarded_non_collapsed_types:        0
% 1.81/1.02  num_pure_diseq_elim:                    0
% 1.81/1.02  simp_replaced_by:                       0
% 1.81/1.02  res_preprocessed:                       125
% 1.81/1.02  prep_upred:                             0
% 1.81/1.02  prep_unflattend:                        41
% 1.81/1.02  smt_new_axioms:                         0
% 1.81/1.02  pred_elim_cands:                        5
% 1.81/1.02  pred_elim:                              6
% 1.81/1.02  pred_elim_cl:                           6
% 1.81/1.02  pred_elim_cycles:                       11
% 1.81/1.02  merged_defs:                            0
% 1.81/1.02  merged_defs_ncl:                        0
% 1.81/1.02  bin_hyper_res:                          0
% 1.81/1.02  prep_cycles:                            4
% 1.81/1.02  pred_elim_time:                         0.018
% 1.81/1.02  splitting_time:                         0.
% 1.81/1.02  sem_filter_time:                        0.
% 1.81/1.02  monotx_time:                            0.
% 1.81/1.02  subtype_inf_time:                       0.
% 1.81/1.02  
% 1.81/1.02  ------ Problem properties
% 1.81/1.02  
% 1.81/1.02  clauses:                                24
% 1.81/1.02  conjectures:                            2
% 1.81/1.02  epr:                                    0
% 1.81/1.02  horn:                                   20
% 1.81/1.02  ground:                                 2
% 1.81/1.02  unary:                                  4
% 1.81/1.02  binary:                                 3
% 1.81/1.02  lits:                                   73
% 1.81/1.02  lits_eq:                                10
% 1.81/1.02  fd_pure:                                0
% 1.81/1.02  fd_pseudo:                              0
% 1.81/1.02  fd_cond:                                0
% 1.81/1.02  fd_pseudo_cond:                         3
% 1.81/1.02  ac_symbols:                             0
% 1.81/1.02  
% 1.81/1.02  ------ Propositional Solver
% 1.81/1.02  
% 1.81/1.02  prop_solver_calls:                      26
% 1.81/1.02  prop_fast_solver_calls:                 1055
% 1.81/1.02  smt_solver_calls:                       0
% 1.81/1.02  smt_fast_solver_calls:                  0
% 1.81/1.02  prop_num_of_clauses:                    1222
% 1.81/1.02  prop_preprocess_simplified:             5537
% 1.81/1.02  prop_fo_subsumed:                       22
% 1.81/1.02  prop_solver_time:                       0.
% 1.81/1.02  smt_solver_time:                        0.
% 1.81/1.02  smt_fast_solver_time:                   0.
% 1.81/1.02  prop_fast_solver_time:                  0.
% 1.81/1.02  prop_unsat_core_time:                   0.
% 1.81/1.02  
% 1.81/1.02  ------ QBF
% 1.81/1.02  
% 1.81/1.02  qbf_q_res:                              0
% 1.81/1.02  qbf_num_tautologies:                    0
% 1.81/1.02  qbf_prep_cycles:                        0
% 1.81/1.02  
% 1.81/1.02  ------ BMC1
% 1.81/1.02  
% 1.81/1.02  bmc1_current_bound:                     -1
% 1.81/1.02  bmc1_last_solved_bound:                 -1
% 1.81/1.02  bmc1_unsat_core_size:                   -1
% 1.81/1.02  bmc1_unsat_core_parents_size:           -1
% 1.81/1.02  bmc1_merge_next_fun:                    0
% 1.81/1.02  bmc1_unsat_core_clauses_time:           0.
% 1.81/1.02  
% 1.81/1.02  ------ Instantiation
% 1.81/1.02  
% 1.81/1.02  inst_num_of_clauses:                    319
% 1.81/1.02  inst_num_in_passive:                    141
% 1.81/1.02  inst_num_in_active:                     159
% 1.81/1.02  inst_num_in_unprocessed:                19
% 1.81/1.02  inst_num_of_loops:                      170
% 1.81/1.02  inst_num_of_learning_restarts:          0
% 1.81/1.02  inst_num_moves_active_passive:          9
% 1.81/1.02  inst_lit_activity:                      0
% 1.81/1.02  inst_lit_activity_moves:                0
% 1.81/1.02  inst_num_tautologies:                   0
% 1.81/1.02  inst_num_prop_implied:                  0
% 1.81/1.02  inst_num_existing_simplified:           0
% 1.81/1.02  inst_num_eq_res_simplified:             0
% 1.81/1.02  inst_num_child_elim:                    0
% 1.81/1.02  inst_num_of_dismatching_blockings:      48
% 1.81/1.02  inst_num_of_non_proper_insts:           259
% 1.81/1.02  inst_num_of_duplicates:                 0
% 1.81/1.02  inst_inst_num_from_inst_to_res:         0
% 1.81/1.02  inst_dismatching_checking_time:         0.
% 1.81/1.02  
% 1.81/1.02  ------ Resolution
% 1.81/1.02  
% 1.81/1.02  res_num_of_clauses:                     0
% 1.81/1.02  res_num_in_passive:                     0
% 1.81/1.02  res_num_in_active:                      0
% 1.81/1.02  res_num_of_loops:                       129
% 1.81/1.02  res_forward_subset_subsumed:            47
% 1.81/1.02  res_backward_subset_subsumed:           0
% 1.81/1.02  res_forward_subsumed:                   0
% 1.81/1.02  res_backward_subsumed:                  0
% 1.81/1.02  res_forward_subsumption_resolution:     6
% 1.81/1.02  res_backward_subsumption_resolution:    0
% 1.81/1.02  res_clause_to_clause_subsumption:       265
% 1.81/1.02  res_orphan_elimination:                 0
% 1.81/1.02  res_tautology_del:                      18
% 1.81/1.02  res_num_eq_res_simplified:              0
% 1.81/1.02  res_num_sel_changes:                    0
% 1.81/1.02  res_moves_from_active_to_pass:          0
% 1.81/1.02  
% 1.81/1.02  ------ Superposition
% 1.81/1.02  
% 1.81/1.02  sup_time_total:                         0.
% 1.81/1.02  sup_time_generating:                    0.
% 1.81/1.02  sup_time_sim_full:                      0.
% 1.81/1.02  sup_time_sim_immed:                     0.
% 1.81/1.02  
% 1.81/1.02  sup_num_of_clauses:                     33
% 1.81/1.02  sup_num_in_active:                      26
% 1.81/1.02  sup_num_in_passive:                     7
% 1.81/1.02  sup_num_of_loops:                       32
% 1.81/1.02  sup_fw_superposition:                   23
% 1.81/1.02  sup_bw_superposition:                   4
% 1.81/1.02  sup_immediate_simplified:               3
% 1.81/1.02  sup_given_eliminated:                   0
% 1.81/1.02  comparisons_done:                       0
% 1.81/1.02  comparisons_avoided:                    0
% 1.81/1.02  
% 1.81/1.02  ------ Simplifications
% 1.81/1.02  
% 1.81/1.02  
% 1.81/1.02  sim_fw_subset_subsumed:                 0
% 1.81/1.02  sim_bw_subset_subsumed:                 13
% 1.81/1.02  sim_fw_subsumed:                        2
% 1.81/1.02  sim_bw_subsumed:                        0
% 1.81/1.02  sim_fw_subsumption_res:                 0
% 1.81/1.02  sim_bw_subsumption_res:                 0
% 1.81/1.02  sim_tautology_del:                      0
% 1.81/1.02  sim_eq_tautology_del:                   0
% 1.81/1.02  sim_eq_res_simp:                        0
% 1.81/1.02  sim_fw_demodulated:                     0
% 1.81/1.02  sim_bw_demodulated:                     0
% 1.81/1.02  sim_light_normalised:                   0
% 1.81/1.02  sim_joinable_taut:                      0
% 1.81/1.02  sim_joinable_simp:                      0
% 1.81/1.02  sim_ac_normalised:                      0
% 1.81/1.02  sim_smt_subsumption:                    0
% 1.81/1.02  
%------------------------------------------------------------------------------
