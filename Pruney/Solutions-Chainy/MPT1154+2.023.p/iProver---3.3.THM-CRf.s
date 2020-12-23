%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:12:20 EST 2020

% Result     : Theorem 2.61s
% Output     : CNFRefutation 2.61s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 756 expanded)
%              Number of clauses        :   64 ( 217 expanded)
%              Number of leaves         :   17 ( 184 expanded)
%              Depth                    :   23
%              Number of atoms          :  582 (4335 expanded)
%              Number of equality atoms :  122 ( 230 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ~ r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ~ r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] :
          ( r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( r2_hidden(sK4,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),sK4)))
        & m1_subset_1(sK4,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
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

fof(f45,plain,
    ( r2_hidden(sK4,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4)))
    & m1_subset_1(sK4,u1_struct_0(sK3))
    & l1_orders_2(sK3)
    & v5_orders_2(sK3)
    & v4_orders_2(sK3)
    & v3_orders_2(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f30,f44,f43])).

fof(f77,plain,(
    r2_hidden(sK4,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))) ),
    inference(cnf_transformation,[],[f45])).

fof(f76,plain,(
    m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f45])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f78,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f52,f53])).

fof(f86,plain,(
    ! [X0,X1] :
      ( k1_enumset1(X1,X1,X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f58,f78])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r1_orders_2(X0,X1,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,X1,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,X1,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f71,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f72,plain,(
    v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f75,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f31,plain,(
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

fof(f38,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X2,X3)
          & r2_hidden(X1,X3)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
          & v6_orders_2(X3,X0) )
      | ( ~ r1_orders_2(X0,X2,X1)
        & ~ r1_orders_2(X0,X1,X2) )
      | ~ sP0(X2,X1,X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ? [X3] :
          ( r2_hidden(X0,X3)
          & r2_hidden(X1,X3)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
          & v6_orders_2(X3,X2) )
      | ( ~ r1_orders_2(X2,X0,X1)
        & ~ r1_orders_2(X2,X1,X0) )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f38])).

fof(f40,plain,(
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

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,sK2(X0,X1,X2))
        & r2_hidden(X1,sK2(X0,X1,X2))
        & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2)))
        & v6_orders_2(sK2(X0,X1,X2),X2) )
      | ( ~ r1_orders_2(X2,X0,X1)
        & ~ r1_orders_2(X2,X1,X0) )
      | ~ sP0(X0,X1,X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f39,f40])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ r1_orders_2(X2,X0,X1)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f10,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
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
    inference(rectify,[],[f10])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f32,plain,(
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
    inference(definition_folding,[],[f26,f31])).

fof(f42,plain,(
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
    inference(rectify,[],[f32])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,sK2(X0,X1,X2))
      | ~ r1_orders_2(X2,X1,X0)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f85,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_enumset1(X0,X0,X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f54,f78])).

fof(f11,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f70,plain,(
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
    inference(cnf_transformation,[],[f28])).

fof(f74,plain,(
    v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f73,plain,(
    v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
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

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f36,plain,(
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

fof(f37,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f35,f36])).

fof(f47,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f83,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f47,f53])).

fof(f89,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k1_enumset1(X4,X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f83])).

fof(f90,plain,(
    ! [X4,X1] : r2_hidden(X4,k1_enumset1(X4,X4,X1)) ),
    inference(equality_resolution,[],[f89])).

cnf(c_23,negated_conjecture,
    ( r2_hidden(sK4,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1481,plain,
    ( r2_hidden(sK4,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1480,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k1_enumset1(X0,X0,X0) = k6_domain_1(X1,X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1482,plain,
    ( k1_enumset1(X0,X0,X0) = k6_domain_1(X1,X0)
    | m1_subset_1(X0,X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2596,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK4) = k1_enumset1(sK4,sK4,sK4)
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1480,c_1482])).

cnf(c_35,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_11,plain,
    ( r1_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_388,plain,
    ( r1_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_29])).

cnf(c_389,plain,
    ( r1_orders_2(sK3,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ v3_orders_2(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_388])).

cnf(c_28,negated_conjecture,
    ( v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_25,negated_conjecture,
    ( l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_393,plain,
    ( r1_orders_2(sK3,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_389,c_28,c_25])).

cnf(c_1693,plain,
    ( r1_orders_2(sK3,sK4,sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_393])).

cnf(c_1694,plain,
    ( r1_orders_2(sK3,sK4,sK4) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1693])).

cnf(c_16,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r1_orders_2(X2,X0,X1)
    | m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_20,plain,
    ( sP0(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X0,u1_struct_0(X2))
    | ~ v3_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_446,plain,
    ( sP0(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X0,u1_struct_0(X2))
    | ~ v3_orders_2(X2)
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_25])).

cnf(c_447,plain,
    ( sP0(X0,X1,sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ v3_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_446])).

cnf(c_451,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | sP0(X0,X1,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_447,c_28])).

cnf(c_452,plain,
    ( sP0(X0,X1,sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_451])).

cnf(c_592,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(sK3))
    | ~ m1_subset_1(X4,u1_struct_0(sK3))
    | m1_subset_1(sK2(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X0)))
    | X4 != X2
    | X3 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_452])).

cnf(c_593,plain,
    ( ~ r1_orders_2(sK3,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | m1_subset_1(sK2(X0,X1,sK3),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(unflattening,[status(thm)],[c_592])).

cnf(c_1711,plain,
    ( ~ r1_orders_2(sK3,sK4,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | m1_subset_1(sK2(sK4,X0,sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_593])).

cnf(c_1916,plain,
    ( ~ r1_orders_2(sK3,sK4,sK4)
    | m1_subset_1(sK2(sK4,sK4,sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1711])).

cnf(c_1917,plain,
    ( r1_orders_2(sK3,sK4,sK4) != iProver_top
    | m1_subset_1(sK2(sK4,sK4,sK3),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1916])).

cnf(c_15,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r1_orders_2(X2,X1,X0)
    | r2_hidden(X1,sK2(X0,X1,X2)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_608,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(sK3))
    | ~ m1_subset_1(X4,u1_struct_0(sK3))
    | r2_hidden(X1,sK2(X2,X1,X0))
    | X4 != X1
    | X3 != X2
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_452])).

cnf(c_609,plain,
    ( ~ r1_orders_2(sK3,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | r2_hidden(X0,sK2(X1,X0,sK3)) ),
    inference(unflattening,[status(thm)],[c_608])).

cnf(c_1716,plain,
    ( ~ r1_orders_2(sK3,sK4,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | r2_hidden(sK4,sK2(X0,sK4,sK3)) ),
    inference(instantiation,[status(thm)],[c_609])).

cnf(c_1919,plain,
    ( ~ r1_orders_2(sK3,sK4,sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | r2_hidden(sK4,sK2(sK4,sK4,sK3)) ),
    inference(instantiation,[status(thm)],[c_1716])).

cnf(c_1920,plain,
    ( r1_orders_2(sK3,sK4,sK4) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK4,sK2(sK4,sK4,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1919])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1807,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X1,X0)
    | ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2138,plain,
    ( ~ m1_subset_1(sK2(sK4,sK4,sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X0,sK2(sK4,sK4,sK3))
    | ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1807])).

cnf(c_2537,plain,
    ( ~ m1_subset_1(sK2(sK4,sK4,sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(sK4,sK2(sK4,sK4,sK3))
    | ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_2138])).

cnf(c_2538,plain,
    ( m1_subset_1(sK2(sK4,sK4,sK3),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(sK4,sK2(sK4,sK4,sK3)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2537])).

cnf(c_3332,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK4) = k1_enumset1(sK4,sK4,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2596,c_35,c_1694,c_1917,c_1920,c_2538])).

cnf(c_6,plain,
    ( m1_subset_1(k1_enumset1(X0,X0,X0),k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1486,plain,
    ( m1_subset_1(k1_enumset1(X0,X0,X0),k1_zfmisc_1(X1)) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

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
    inference(cnf_transformation,[],[f70])).

cnf(c_26,negated_conjecture,
    ( v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_358,plain,
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

cnf(c_359,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_orders_2(sK3,X1))
    | ~ v4_orders_2(sK3)
    | v2_struct_0(sK3)
    | ~ v3_orders_2(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_358])).

cnf(c_27,negated_conjecture,
    ( v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_363,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_orders_2(sK3,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_359,c_29,c_28,c_27,c_25])).

cnf(c_8,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_377,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X1,X0)
    | ~ r2_hidden(X1,k1_orders_2(sK3,X0)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_363,c_8])).

cnf(c_1479,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(X1,X0) != iProver_top
    | r2_hidden(X1,k1_orders_2(sK3,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_377])).

cnf(c_1998,plain,
    ( r2_hidden(X0,k1_enumset1(X1,X1,X1)) != iProver_top
    | r2_hidden(X0,k1_orders_2(sK3,k1_enumset1(X1,X1,X1))) != iProver_top
    | r2_hidden(X1,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1486,c_1479])).

cnf(c_3339,plain,
    ( r2_hidden(X0,k1_enumset1(sK4,sK4,sK4)) != iProver_top
    | r2_hidden(X0,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))) != iProver_top
    | r2_hidden(sK4,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3332,c_1998])).

cnf(c_3340,plain,
    ( r2_hidden(X0,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))) != iProver_top
    | r2_hidden(X0,k6_domain_1(u1_struct_0(sK3),sK4)) != iProver_top
    | r2_hidden(sK4,u1_struct_0(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3339,c_3332])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1485,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2037,plain,
    ( r2_hidden(sK4,u1_struct_0(sK3)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1480,c_1485])).

cnf(c_3818,plain,
    ( r2_hidden(X0,k6_domain_1(u1_struct_0(sK3),sK4)) != iProver_top
    | r2_hidden(X0,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3340,c_35,c_1694,c_1917,c_1920,c_2037,c_2538])).

cnf(c_3819,plain,
    ( r2_hidden(X0,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))) != iProver_top
    | r2_hidden(X0,k6_domain_1(u1_struct_0(sK3),sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3818])).

cnf(c_3826,plain,
    ( r2_hidden(sK4,k6_domain_1(u1_struct_0(sK3),sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1481,c_3819])).

cnf(c_4,plain,
    ( r2_hidden(X0,k1_enumset1(X0,X0,X1)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1488,plain,
    ( r2_hidden(X0,k1_enumset1(X0,X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3335,plain,
    ( r2_hidden(sK4,k6_domain_1(u1_struct_0(sK3),sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3332,c_1488])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3826,c_3335])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:07:30 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.61/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/0.99  
% 2.61/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.61/0.99  
% 2.61/0.99  ------  iProver source info
% 2.61/0.99  
% 2.61/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.61/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.61/0.99  git: non_committed_changes: false
% 2.61/0.99  git: last_make_outside_of_git: false
% 2.61/0.99  
% 2.61/0.99  ------ 
% 2.61/0.99  
% 2.61/0.99  ------ Input Options
% 2.61/0.99  
% 2.61/0.99  --out_options                           all
% 2.61/0.99  --tptp_safe_out                         true
% 2.61/0.99  --problem_path                          ""
% 2.61/0.99  --include_path                          ""
% 2.61/0.99  --clausifier                            res/vclausify_rel
% 2.61/0.99  --clausifier_options                    --mode clausify
% 2.61/0.99  --stdin                                 false
% 2.61/0.99  --stats_out                             all
% 2.61/0.99  
% 2.61/0.99  ------ General Options
% 2.61/0.99  
% 2.61/0.99  --fof                                   false
% 2.61/0.99  --time_out_real                         305.
% 2.61/0.99  --time_out_virtual                      -1.
% 2.61/0.99  --symbol_type_check                     false
% 2.61/0.99  --clausify_out                          false
% 2.61/0.99  --sig_cnt_out                           false
% 2.61/0.99  --trig_cnt_out                          false
% 2.61/0.99  --trig_cnt_out_tolerance                1.
% 2.61/0.99  --trig_cnt_out_sk_spl                   false
% 2.61/0.99  --abstr_cl_out                          false
% 2.61/0.99  
% 2.61/0.99  ------ Global Options
% 2.61/0.99  
% 2.61/0.99  --schedule                              default
% 2.61/0.99  --add_important_lit                     false
% 2.61/0.99  --prop_solver_per_cl                    1000
% 2.61/0.99  --min_unsat_core                        false
% 2.61/0.99  --soft_assumptions                      false
% 2.61/0.99  --soft_lemma_size                       3
% 2.61/0.99  --prop_impl_unit_size                   0
% 2.61/0.99  --prop_impl_unit                        []
% 2.61/0.99  --share_sel_clauses                     true
% 2.61/0.99  --reset_solvers                         false
% 2.61/0.99  --bc_imp_inh                            [conj_cone]
% 2.61/0.99  --conj_cone_tolerance                   3.
% 2.61/0.99  --extra_neg_conj                        none
% 2.61/0.99  --large_theory_mode                     true
% 2.61/0.99  --prolific_symb_bound                   200
% 2.61/0.99  --lt_threshold                          2000
% 2.61/0.99  --clause_weak_htbl                      true
% 2.61/0.99  --gc_record_bc_elim                     false
% 2.61/0.99  
% 2.61/0.99  ------ Preprocessing Options
% 2.61/0.99  
% 2.61/0.99  --preprocessing_flag                    true
% 2.61/0.99  --time_out_prep_mult                    0.1
% 2.61/0.99  --splitting_mode                        input
% 2.61/0.99  --splitting_grd                         true
% 2.61/0.99  --splitting_cvd                         false
% 2.61/0.99  --splitting_cvd_svl                     false
% 2.61/0.99  --splitting_nvd                         32
% 2.61/0.99  --sub_typing                            true
% 2.61/0.99  --prep_gs_sim                           true
% 2.61/0.99  --prep_unflatten                        true
% 2.61/0.99  --prep_res_sim                          true
% 2.61/0.99  --prep_upred                            true
% 2.61/0.99  --prep_sem_filter                       exhaustive
% 2.61/0.99  --prep_sem_filter_out                   false
% 2.61/0.99  --pred_elim                             true
% 2.61/0.99  --res_sim_input                         true
% 2.61/0.99  --eq_ax_congr_red                       true
% 2.61/0.99  --pure_diseq_elim                       true
% 2.61/0.99  --brand_transform                       false
% 2.61/0.99  --non_eq_to_eq                          false
% 2.61/0.99  --prep_def_merge                        true
% 2.61/0.99  --prep_def_merge_prop_impl              false
% 2.61/0.99  --prep_def_merge_mbd                    true
% 2.61/0.99  --prep_def_merge_tr_red                 false
% 2.61/0.99  --prep_def_merge_tr_cl                  false
% 2.61/0.99  --smt_preprocessing                     true
% 2.61/0.99  --smt_ac_axioms                         fast
% 2.61/0.99  --preprocessed_out                      false
% 2.61/0.99  --preprocessed_stats                    false
% 2.61/0.99  
% 2.61/0.99  ------ Abstraction refinement Options
% 2.61/0.99  
% 2.61/0.99  --abstr_ref                             []
% 2.61/0.99  --abstr_ref_prep                        false
% 2.61/0.99  --abstr_ref_until_sat                   false
% 2.61/0.99  --abstr_ref_sig_restrict                funpre
% 2.61/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.61/0.99  --abstr_ref_under                       []
% 2.61/0.99  
% 2.61/0.99  ------ SAT Options
% 2.61/0.99  
% 2.61/0.99  --sat_mode                              false
% 2.61/0.99  --sat_fm_restart_options                ""
% 2.61/0.99  --sat_gr_def                            false
% 2.61/0.99  --sat_epr_types                         true
% 2.61/0.99  --sat_non_cyclic_types                  false
% 2.61/0.99  --sat_finite_models                     false
% 2.61/0.99  --sat_fm_lemmas                         false
% 2.61/0.99  --sat_fm_prep                           false
% 2.61/0.99  --sat_fm_uc_incr                        true
% 2.61/0.99  --sat_out_model                         small
% 2.61/0.99  --sat_out_clauses                       false
% 2.61/0.99  
% 2.61/0.99  ------ QBF Options
% 2.61/0.99  
% 2.61/0.99  --qbf_mode                              false
% 2.61/0.99  --qbf_elim_univ                         false
% 2.61/0.99  --qbf_dom_inst                          none
% 2.61/0.99  --qbf_dom_pre_inst                      false
% 2.61/0.99  --qbf_sk_in                             false
% 2.61/0.99  --qbf_pred_elim                         true
% 2.61/0.99  --qbf_split                             512
% 2.61/0.99  
% 2.61/0.99  ------ BMC1 Options
% 2.61/0.99  
% 2.61/0.99  --bmc1_incremental                      false
% 2.61/0.99  --bmc1_axioms                           reachable_all
% 2.61/0.99  --bmc1_min_bound                        0
% 2.61/0.99  --bmc1_max_bound                        -1
% 2.61/0.99  --bmc1_max_bound_default                -1
% 2.61/0.99  --bmc1_symbol_reachability              true
% 2.61/0.99  --bmc1_property_lemmas                  false
% 2.61/0.99  --bmc1_k_induction                      false
% 2.61/0.99  --bmc1_non_equiv_states                 false
% 2.61/0.99  --bmc1_deadlock                         false
% 2.61/0.99  --bmc1_ucm                              false
% 2.61/0.99  --bmc1_add_unsat_core                   none
% 2.61/0.99  --bmc1_unsat_core_children              false
% 2.61/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.61/0.99  --bmc1_out_stat                         full
% 2.61/0.99  --bmc1_ground_init                      false
% 2.61/0.99  --bmc1_pre_inst_next_state              false
% 2.61/0.99  --bmc1_pre_inst_state                   false
% 2.61/0.99  --bmc1_pre_inst_reach_state             false
% 2.61/0.99  --bmc1_out_unsat_core                   false
% 2.61/0.99  --bmc1_aig_witness_out                  false
% 2.61/0.99  --bmc1_verbose                          false
% 2.61/0.99  --bmc1_dump_clauses_tptp                false
% 2.61/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.61/0.99  --bmc1_dump_file                        -
% 2.61/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.61/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.61/0.99  --bmc1_ucm_extend_mode                  1
% 2.61/0.99  --bmc1_ucm_init_mode                    2
% 2.61/0.99  --bmc1_ucm_cone_mode                    none
% 2.61/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.61/0.99  --bmc1_ucm_relax_model                  4
% 2.61/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.61/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.61/0.99  --bmc1_ucm_layered_model                none
% 2.61/0.99  --bmc1_ucm_max_lemma_size               10
% 2.61/0.99  
% 2.61/0.99  ------ AIG Options
% 2.61/0.99  
% 2.61/0.99  --aig_mode                              false
% 2.61/0.99  
% 2.61/0.99  ------ Instantiation Options
% 2.61/0.99  
% 2.61/0.99  --instantiation_flag                    true
% 2.61/0.99  --inst_sos_flag                         false
% 2.61/0.99  --inst_sos_phase                        true
% 2.61/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.61/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.61/0.99  --inst_lit_sel_side                     num_symb
% 2.61/0.99  --inst_solver_per_active                1400
% 2.61/0.99  --inst_solver_calls_frac                1.
% 2.61/0.99  --inst_passive_queue_type               priority_queues
% 2.61/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.61/0.99  --inst_passive_queues_freq              [25;2]
% 2.61/0.99  --inst_dismatching                      true
% 2.61/0.99  --inst_eager_unprocessed_to_passive     true
% 2.61/0.99  --inst_prop_sim_given                   true
% 2.61/0.99  --inst_prop_sim_new                     false
% 2.61/0.99  --inst_subs_new                         false
% 2.61/0.99  --inst_eq_res_simp                      false
% 2.61/0.99  --inst_subs_given                       false
% 2.61/0.99  --inst_orphan_elimination               true
% 2.61/0.99  --inst_learning_loop_flag               true
% 2.61/0.99  --inst_learning_start                   3000
% 2.61/0.99  --inst_learning_factor                  2
% 2.61/0.99  --inst_start_prop_sim_after_learn       3
% 2.61/0.99  --inst_sel_renew                        solver
% 2.61/0.99  --inst_lit_activity_flag                true
% 2.61/0.99  --inst_restr_to_given                   false
% 2.61/0.99  --inst_activity_threshold               500
% 2.61/0.99  --inst_out_proof                        true
% 2.61/0.99  
% 2.61/0.99  ------ Resolution Options
% 2.61/0.99  
% 2.61/0.99  --resolution_flag                       true
% 2.61/0.99  --res_lit_sel                           adaptive
% 2.61/0.99  --res_lit_sel_side                      none
% 2.61/0.99  --res_ordering                          kbo
% 2.61/0.99  --res_to_prop_solver                    active
% 2.61/0.99  --res_prop_simpl_new                    false
% 2.61/0.99  --res_prop_simpl_given                  true
% 2.61/0.99  --res_passive_queue_type                priority_queues
% 2.61/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.61/0.99  --res_passive_queues_freq               [15;5]
% 2.61/0.99  --res_forward_subs                      full
% 2.61/0.99  --res_backward_subs                     full
% 2.61/0.99  --res_forward_subs_resolution           true
% 2.61/0.99  --res_backward_subs_resolution          true
% 2.61/0.99  --res_orphan_elimination                true
% 2.61/0.99  --res_time_limit                        2.
% 2.61/0.99  --res_out_proof                         true
% 2.61/0.99  
% 2.61/0.99  ------ Superposition Options
% 2.61/0.99  
% 2.61/0.99  --superposition_flag                    true
% 2.61/0.99  --sup_passive_queue_type                priority_queues
% 2.61/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.61/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.61/0.99  --demod_completeness_check              fast
% 2.61/0.99  --demod_use_ground                      true
% 2.61/0.99  --sup_to_prop_solver                    passive
% 2.61/0.99  --sup_prop_simpl_new                    true
% 2.61/0.99  --sup_prop_simpl_given                  true
% 2.61/0.99  --sup_fun_splitting                     false
% 2.61/0.99  --sup_smt_interval                      50000
% 2.61/0.99  
% 2.61/0.99  ------ Superposition Simplification Setup
% 2.61/0.99  
% 2.61/0.99  --sup_indices_passive                   []
% 2.61/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.61/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.61/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.61/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.61/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.61/0.99  --sup_full_bw                           [BwDemod]
% 2.61/0.99  --sup_immed_triv                        [TrivRules]
% 2.61/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.61/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.61/0.99  --sup_immed_bw_main                     []
% 2.61/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.61/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.61/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.61/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.61/0.99  
% 2.61/0.99  ------ Combination Options
% 2.61/0.99  
% 2.61/0.99  --comb_res_mult                         3
% 2.61/0.99  --comb_sup_mult                         2
% 2.61/0.99  --comb_inst_mult                        10
% 2.61/0.99  
% 2.61/0.99  ------ Debug Options
% 2.61/0.99  
% 2.61/0.99  --dbg_backtrace                         false
% 2.61/0.99  --dbg_dump_prop_clauses                 false
% 2.61/0.99  --dbg_dump_prop_clauses_file            -
% 2.61/0.99  --dbg_out_stat                          false
% 2.61/0.99  ------ Parsing...
% 2.61/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.61/0.99  
% 2.61/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 2.61/0.99  
% 2.61/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.61/0.99  
% 2.61/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.61/0.99  ------ Proving...
% 2.61/0.99  ------ Problem Properties 
% 2.61/0.99  
% 2.61/0.99  
% 2.61/0.99  clauses                                 24
% 2.61/0.99  conjectures                             2
% 2.61/0.99  EPR                                     1
% 2.61/0.99  Horn                                    19
% 2.61/0.99  unary                                   4
% 2.61/0.99  binary                                  2
% 2.61/0.99  lits                                    74
% 2.61/0.99  lits eq                                 10
% 2.61/0.99  fd_pure                                 0
% 2.61/0.99  fd_pseudo                               0
% 2.61/0.99  fd_cond                                 0
% 2.61/0.99  fd_pseudo_cond                          3
% 2.61/0.99  AC symbols                              0
% 2.61/0.99  
% 2.61/0.99  ------ Schedule dynamic 5 is on 
% 2.61/0.99  
% 2.61/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.61/0.99  
% 2.61/0.99  
% 2.61/0.99  ------ 
% 2.61/0.99  Current options:
% 2.61/0.99  ------ 
% 2.61/0.99  
% 2.61/0.99  ------ Input Options
% 2.61/0.99  
% 2.61/0.99  --out_options                           all
% 2.61/0.99  --tptp_safe_out                         true
% 2.61/0.99  --problem_path                          ""
% 2.61/0.99  --include_path                          ""
% 2.61/0.99  --clausifier                            res/vclausify_rel
% 2.61/0.99  --clausifier_options                    --mode clausify
% 2.61/0.99  --stdin                                 false
% 2.61/0.99  --stats_out                             all
% 2.61/0.99  
% 2.61/0.99  ------ General Options
% 2.61/0.99  
% 2.61/0.99  --fof                                   false
% 2.61/0.99  --time_out_real                         305.
% 2.61/0.99  --time_out_virtual                      -1.
% 2.61/0.99  --symbol_type_check                     false
% 2.61/0.99  --clausify_out                          false
% 2.61/0.99  --sig_cnt_out                           false
% 2.61/0.99  --trig_cnt_out                          false
% 2.61/0.99  --trig_cnt_out_tolerance                1.
% 2.61/0.99  --trig_cnt_out_sk_spl                   false
% 2.61/0.99  --abstr_cl_out                          false
% 2.61/0.99  
% 2.61/0.99  ------ Global Options
% 2.61/0.99  
% 2.61/0.99  --schedule                              default
% 2.61/0.99  --add_important_lit                     false
% 2.61/0.99  --prop_solver_per_cl                    1000
% 2.61/0.99  --min_unsat_core                        false
% 2.61/0.99  --soft_assumptions                      false
% 2.61/0.99  --soft_lemma_size                       3
% 2.61/0.99  --prop_impl_unit_size                   0
% 2.61/0.99  --prop_impl_unit                        []
% 2.61/0.99  --share_sel_clauses                     true
% 2.61/0.99  --reset_solvers                         false
% 2.61/0.99  --bc_imp_inh                            [conj_cone]
% 2.61/0.99  --conj_cone_tolerance                   3.
% 2.61/0.99  --extra_neg_conj                        none
% 2.61/0.99  --large_theory_mode                     true
% 2.61/0.99  --prolific_symb_bound                   200
% 2.61/0.99  --lt_threshold                          2000
% 2.61/0.99  --clause_weak_htbl                      true
% 2.61/0.99  --gc_record_bc_elim                     false
% 2.61/0.99  
% 2.61/0.99  ------ Preprocessing Options
% 2.61/0.99  
% 2.61/0.99  --preprocessing_flag                    true
% 2.61/0.99  --time_out_prep_mult                    0.1
% 2.61/0.99  --splitting_mode                        input
% 2.61/0.99  --splitting_grd                         true
% 2.61/0.99  --splitting_cvd                         false
% 2.61/0.99  --splitting_cvd_svl                     false
% 2.61/0.99  --splitting_nvd                         32
% 2.61/0.99  --sub_typing                            true
% 2.61/0.99  --prep_gs_sim                           true
% 2.61/0.99  --prep_unflatten                        true
% 2.61/0.99  --prep_res_sim                          true
% 2.61/0.99  --prep_upred                            true
% 2.61/0.99  --prep_sem_filter                       exhaustive
% 2.61/0.99  --prep_sem_filter_out                   false
% 2.61/0.99  --pred_elim                             true
% 2.61/0.99  --res_sim_input                         true
% 2.61/0.99  --eq_ax_congr_red                       true
% 2.61/0.99  --pure_diseq_elim                       true
% 2.61/0.99  --brand_transform                       false
% 2.61/0.99  --non_eq_to_eq                          false
% 2.61/0.99  --prep_def_merge                        true
% 2.61/0.99  --prep_def_merge_prop_impl              false
% 2.61/0.99  --prep_def_merge_mbd                    true
% 2.61/0.99  --prep_def_merge_tr_red                 false
% 2.61/0.99  --prep_def_merge_tr_cl                  false
% 2.61/0.99  --smt_preprocessing                     true
% 2.61/0.99  --smt_ac_axioms                         fast
% 2.61/0.99  --preprocessed_out                      false
% 2.61/0.99  --preprocessed_stats                    false
% 2.61/0.99  
% 2.61/0.99  ------ Abstraction refinement Options
% 2.61/0.99  
% 2.61/0.99  --abstr_ref                             []
% 2.61/0.99  --abstr_ref_prep                        false
% 2.61/0.99  --abstr_ref_until_sat                   false
% 2.61/0.99  --abstr_ref_sig_restrict                funpre
% 2.61/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.61/0.99  --abstr_ref_under                       []
% 2.61/0.99  
% 2.61/0.99  ------ SAT Options
% 2.61/0.99  
% 2.61/0.99  --sat_mode                              false
% 2.61/0.99  --sat_fm_restart_options                ""
% 2.61/0.99  --sat_gr_def                            false
% 2.61/0.99  --sat_epr_types                         true
% 2.61/0.99  --sat_non_cyclic_types                  false
% 2.61/0.99  --sat_finite_models                     false
% 2.61/0.99  --sat_fm_lemmas                         false
% 2.61/0.99  --sat_fm_prep                           false
% 2.61/0.99  --sat_fm_uc_incr                        true
% 2.61/0.99  --sat_out_model                         small
% 2.61/0.99  --sat_out_clauses                       false
% 2.61/0.99  
% 2.61/0.99  ------ QBF Options
% 2.61/0.99  
% 2.61/0.99  --qbf_mode                              false
% 2.61/0.99  --qbf_elim_univ                         false
% 2.61/0.99  --qbf_dom_inst                          none
% 2.61/0.99  --qbf_dom_pre_inst                      false
% 2.61/0.99  --qbf_sk_in                             false
% 2.61/0.99  --qbf_pred_elim                         true
% 2.61/0.99  --qbf_split                             512
% 2.61/0.99  
% 2.61/0.99  ------ BMC1 Options
% 2.61/0.99  
% 2.61/0.99  --bmc1_incremental                      false
% 2.61/0.99  --bmc1_axioms                           reachable_all
% 2.61/0.99  --bmc1_min_bound                        0
% 2.61/0.99  --bmc1_max_bound                        -1
% 2.61/0.99  --bmc1_max_bound_default                -1
% 2.61/0.99  --bmc1_symbol_reachability              true
% 2.61/0.99  --bmc1_property_lemmas                  false
% 2.61/0.99  --bmc1_k_induction                      false
% 2.61/0.99  --bmc1_non_equiv_states                 false
% 2.61/0.99  --bmc1_deadlock                         false
% 2.61/0.99  --bmc1_ucm                              false
% 2.61/0.99  --bmc1_add_unsat_core                   none
% 2.61/0.99  --bmc1_unsat_core_children              false
% 2.61/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.61/0.99  --bmc1_out_stat                         full
% 2.61/0.99  --bmc1_ground_init                      false
% 2.61/0.99  --bmc1_pre_inst_next_state              false
% 2.61/0.99  --bmc1_pre_inst_state                   false
% 2.61/0.99  --bmc1_pre_inst_reach_state             false
% 2.61/0.99  --bmc1_out_unsat_core                   false
% 2.61/0.99  --bmc1_aig_witness_out                  false
% 2.61/0.99  --bmc1_verbose                          false
% 2.61/0.99  --bmc1_dump_clauses_tptp                false
% 2.61/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.61/0.99  --bmc1_dump_file                        -
% 2.61/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.61/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.61/0.99  --bmc1_ucm_extend_mode                  1
% 2.61/0.99  --bmc1_ucm_init_mode                    2
% 2.61/0.99  --bmc1_ucm_cone_mode                    none
% 2.61/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.61/0.99  --bmc1_ucm_relax_model                  4
% 2.61/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.61/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.61/0.99  --bmc1_ucm_layered_model                none
% 2.61/0.99  --bmc1_ucm_max_lemma_size               10
% 2.61/0.99  
% 2.61/0.99  ------ AIG Options
% 2.61/0.99  
% 2.61/0.99  --aig_mode                              false
% 2.61/0.99  
% 2.61/0.99  ------ Instantiation Options
% 2.61/0.99  
% 2.61/0.99  --instantiation_flag                    true
% 2.61/0.99  --inst_sos_flag                         false
% 2.61/0.99  --inst_sos_phase                        true
% 2.61/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.61/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.61/0.99  --inst_lit_sel_side                     none
% 2.61/0.99  --inst_solver_per_active                1400
% 2.61/0.99  --inst_solver_calls_frac                1.
% 2.61/0.99  --inst_passive_queue_type               priority_queues
% 2.61/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.61/0.99  --inst_passive_queues_freq              [25;2]
% 2.61/0.99  --inst_dismatching                      true
% 2.61/0.99  --inst_eager_unprocessed_to_passive     true
% 2.61/0.99  --inst_prop_sim_given                   true
% 2.61/0.99  --inst_prop_sim_new                     false
% 2.61/0.99  --inst_subs_new                         false
% 2.61/0.99  --inst_eq_res_simp                      false
% 2.61/0.99  --inst_subs_given                       false
% 2.61/0.99  --inst_orphan_elimination               true
% 2.61/0.99  --inst_learning_loop_flag               true
% 2.61/0.99  --inst_learning_start                   3000
% 2.61/0.99  --inst_learning_factor                  2
% 2.61/0.99  --inst_start_prop_sim_after_learn       3
% 2.61/0.99  --inst_sel_renew                        solver
% 2.61/0.99  --inst_lit_activity_flag                true
% 2.61/0.99  --inst_restr_to_given                   false
% 2.61/0.99  --inst_activity_threshold               500
% 2.61/0.99  --inst_out_proof                        true
% 2.61/0.99  
% 2.61/0.99  ------ Resolution Options
% 2.61/0.99  
% 2.61/0.99  --resolution_flag                       false
% 2.61/0.99  --res_lit_sel                           adaptive
% 2.61/0.99  --res_lit_sel_side                      none
% 2.61/0.99  --res_ordering                          kbo
% 2.61/0.99  --res_to_prop_solver                    active
% 2.61/0.99  --res_prop_simpl_new                    false
% 2.61/0.99  --res_prop_simpl_given                  true
% 2.61/0.99  --res_passive_queue_type                priority_queues
% 2.61/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.61/0.99  --res_passive_queues_freq               [15;5]
% 2.61/0.99  --res_forward_subs                      full
% 2.61/0.99  --res_backward_subs                     full
% 2.61/0.99  --res_forward_subs_resolution           true
% 2.61/0.99  --res_backward_subs_resolution          true
% 2.61/0.99  --res_orphan_elimination                true
% 2.61/0.99  --res_time_limit                        2.
% 2.61/0.99  --res_out_proof                         true
% 2.61/0.99  
% 2.61/0.99  ------ Superposition Options
% 2.61/0.99  
% 2.61/0.99  --superposition_flag                    true
% 2.61/0.99  --sup_passive_queue_type                priority_queues
% 2.61/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.61/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.61/0.99  --demod_completeness_check              fast
% 2.61/0.99  --demod_use_ground                      true
% 2.61/0.99  --sup_to_prop_solver                    passive
% 2.61/0.99  --sup_prop_simpl_new                    true
% 2.61/0.99  --sup_prop_simpl_given                  true
% 2.61/0.99  --sup_fun_splitting                     false
% 2.61/0.99  --sup_smt_interval                      50000
% 2.61/0.99  
% 2.61/0.99  ------ Superposition Simplification Setup
% 2.61/0.99  
% 2.61/0.99  --sup_indices_passive                   []
% 2.61/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.61/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.61/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.61/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.61/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.61/0.99  --sup_full_bw                           [BwDemod]
% 2.61/0.99  --sup_immed_triv                        [TrivRules]
% 2.61/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.61/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.61/0.99  --sup_immed_bw_main                     []
% 2.61/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.61/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.61/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.61/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.61/0.99  
% 2.61/0.99  ------ Combination Options
% 2.61/0.99  
% 2.61/0.99  --comb_res_mult                         3
% 2.61/0.99  --comb_sup_mult                         2
% 2.61/0.99  --comb_inst_mult                        10
% 2.61/0.99  
% 2.61/0.99  ------ Debug Options
% 2.61/0.99  
% 2.61/0.99  --dbg_backtrace                         false
% 2.61/0.99  --dbg_dump_prop_clauses                 false
% 2.61/0.99  --dbg_dump_prop_clauses_file            -
% 2.61/0.99  --dbg_out_stat                          false
% 2.61/0.99  
% 2.61/0.99  
% 2.61/0.99  
% 2.61/0.99  
% 2.61/0.99  ------ Proving...
% 2.61/0.99  
% 2.61/0.99  
% 2.61/0.99  % SZS status Theorem for theBenchmark.p
% 2.61/0.99  
% 2.61/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.61/0.99  
% 2.61/0.99  fof(f12,conjecture,(
% 2.61/0.99    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ~r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))))),
% 2.61/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.61/0.99  
% 2.61/0.99  fof(f13,negated_conjecture,(
% 2.61/0.99    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ~r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))))),
% 2.61/0.99    inference(negated_conjecture,[],[f12])).
% 2.61/0.99  
% 2.61/0.99  fof(f29,plain,(
% 2.61/0.99    ? [X0] : (? [X1] : (r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 2.61/0.99    inference(ennf_transformation,[],[f13])).
% 2.61/0.99  
% 2.61/0.99  fof(f30,plain,(
% 2.61/0.99    ? [X0] : (? [X1] : (r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 2.61/0.99    inference(flattening,[],[f29])).
% 2.61/0.99  
% 2.61/0.99  fof(f44,plain,(
% 2.61/0.99    ( ! [X0] : (? [X1] : (r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X1,u1_struct_0(X0))) => (r2_hidden(sK4,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),sK4))) & m1_subset_1(sK4,u1_struct_0(X0)))) )),
% 2.61/0.99    introduced(choice_axiom,[])).
% 2.61/0.99  
% 2.61/0.99  fof(f43,plain,(
% 2.61/0.99    ? [X0] : (? [X1] : (r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (r2_hidden(X1,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),X1))) & m1_subset_1(X1,u1_struct_0(sK3))) & l1_orders_2(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3))),
% 2.61/0.99    introduced(choice_axiom,[])).
% 2.61/0.99  
% 2.61/0.99  fof(f45,plain,(
% 2.61/0.99    (r2_hidden(sK4,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))) & m1_subset_1(sK4,u1_struct_0(sK3))) & l1_orders_2(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3)),
% 2.61/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f30,f44,f43])).
% 2.61/0.99  
% 2.61/0.99  fof(f77,plain,(
% 2.61/0.99    r2_hidden(sK4,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4)))),
% 2.61/0.99    inference(cnf_transformation,[],[f45])).
% 2.61/0.99  
% 2.61/0.99  fof(f76,plain,(
% 2.61/0.99    m1_subset_1(sK4,u1_struct_0(sK3))),
% 2.61/0.99    inference(cnf_transformation,[],[f45])).
% 2.61/0.99  
% 2.61/0.99  fof(f8,axiom,(
% 2.61/0.99    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 2.61/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.61/0.99  
% 2.61/0.99  fof(f21,plain,(
% 2.61/0.99    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 2.61/0.99    inference(ennf_transformation,[],[f8])).
% 2.61/0.99  
% 2.61/0.99  fof(f22,plain,(
% 2.61/0.99    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 2.61/0.99    inference(flattening,[],[f21])).
% 2.61/0.99  
% 2.61/0.99  fof(f58,plain,(
% 2.61/0.99    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.61/0.99    inference(cnf_transformation,[],[f22])).
% 2.61/0.99  
% 2.61/0.99  fof(f2,axiom,(
% 2.61/0.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.61/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.61/0.99  
% 2.61/0.99  fof(f52,plain,(
% 2.61/0.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.61/0.99    inference(cnf_transformation,[],[f2])).
% 2.61/0.99  
% 2.61/0.99  fof(f3,axiom,(
% 2.61/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.61/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.61/0.99  
% 2.61/0.99  fof(f53,plain,(
% 2.61/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.61/0.99    inference(cnf_transformation,[],[f3])).
% 2.61/0.99  
% 2.61/0.99  fof(f78,plain,(
% 2.61/0.99    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 2.61/0.99    inference(definition_unfolding,[],[f52,f53])).
% 2.61/0.99  
% 2.61/0.99  fof(f86,plain,(
% 2.61/0.99    ( ! [X0,X1] : (k1_enumset1(X1,X1,X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.61/0.99    inference(definition_unfolding,[],[f58,f78])).
% 2.61/0.99  
% 2.61/0.99  fof(f9,axiom,(
% 2.61/0.99    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r1_orders_2(X0,X1,X1)))),
% 2.61/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.61/0.99  
% 2.61/0.99  fof(f23,plain,(
% 2.61/0.99    ! [X0] : (! [X1] : (r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.61/0.99    inference(ennf_transformation,[],[f9])).
% 2.61/0.99  
% 2.61/0.99  fof(f24,plain,(
% 2.61/0.99    ! [X0] : (! [X1] : (r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.61/0.99    inference(flattening,[],[f23])).
% 2.61/0.99  
% 2.61/0.99  fof(f59,plain,(
% 2.61/0.99    ( ! [X0,X1] : (r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.61/0.99    inference(cnf_transformation,[],[f24])).
% 2.61/0.99  
% 2.61/0.99  fof(f71,plain,(
% 2.61/0.99    ~v2_struct_0(sK3)),
% 2.61/0.99    inference(cnf_transformation,[],[f45])).
% 2.61/0.99  
% 2.61/0.99  fof(f72,plain,(
% 2.61/0.99    v3_orders_2(sK3)),
% 2.61/0.99    inference(cnf_transformation,[],[f45])).
% 2.61/0.99  
% 2.61/0.99  fof(f75,plain,(
% 2.61/0.99    l1_orders_2(sK3)),
% 2.61/0.99    inference(cnf_transformation,[],[f45])).
% 2.61/0.99  
% 2.61/0.99  fof(f31,plain,(
% 2.61/0.99    ! [X2,X1,X0] : (? [X3] : (r2_hidden(X2,X3) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X3,X0)) | (~r1_orders_2(X0,X2,X1) & ~r1_orders_2(X0,X1,X2)) | ~sP0(X2,X1,X0))),
% 2.61/0.99    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.61/0.99  
% 2.61/0.99  fof(f38,plain,(
% 2.61/0.99    ! [X2,X1,X0] : (? [X3] : (r2_hidden(X2,X3) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X3,X0)) | (~r1_orders_2(X0,X2,X1) & ~r1_orders_2(X0,X1,X2)) | ~sP0(X2,X1,X0))),
% 2.61/0.99    inference(nnf_transformation,[],[f31])).
% 2.61/0.99  
% 2.61/0.99  fof(f39,plain,(
% 2.61/0.99    ! [X0,X1,X2] : (? [X3] : (r2_hidden(X0,X3) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) & v6_orders_2(X3,X2)) | (~r1_orders_2(X2,X0,X1) & ~r1_orders_2(X2,X1,X0)) | ~sP0(X0,X1,X2))),
% 2.61/0.99    inference(rectify,[],[f38])).
% 2.61/0.99  
% 2.61/0.99  fof(f40,plain,(
% 2.61/0.99    ! [X2,X1,X0] : (? [X3] : (r2_hidden(X0,X3) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) & v6_orders_2(X3,X2)) => (r2_hidden(X0,sK2(X0,X1,X2)) & r2_hidden(X1,sK2(X0,X1,X2)) & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) & v6_orders_2(sK2(X0,X1,X2),X2)))),
% 2.61/0.99    introduced(choice_axiom,[])).
% 2.61/0.99  
% 2.61/0.99  fof(f41,plain,(
% 2.61/0.99    ! [X0,X1,X2] : ((r2_hidden(X0,sK2(X0,X1,X2)) & r2_hidden(X1,sK2(X0,X1,X2)) & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) & v6_orders_2(sK2(X0,X1,X2),X2)) | (~r1_orders_2(X2,X0,X1) & ~r1_orders_2(X2,X1,X0)) | ~sP0(X0,X1,X2))),
% 2.61/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f39,f40])).
% 2.61/0.99  
% 2.61/0.99  fof(f63,plain,(
% 2.61/0.99    ( ! [X2,X0,X1] : (m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) | ~r1_orders_2(X2,X0,X1) | ~sP0(X0,X1,X2)) )),
% 2.61/0.99    inference(cnf_transformation,[],[f41])).
% 2.61/0.99  
% 2.61/0.99  fof(f10,axiom,(
% 2.61/0.99    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (~(! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X3,X0)) => ~(r2_hidden(X2,X3) & r2_hidden(X1,X3))) & (r1_orders_2(X0,X2,X1) | r1_orders_2(X0,X1,X2))) & ~(~r1_orders_2(X0,X2,X1) & ~r1_orders_2(X0,X1,X2) & ? [X3] : (r2_hidden(X2,X3) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X3,X0)))))))),
% 2.61/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.61/0.99  
% 2.61/0.99  fof(f14,plain,(
% 2.61/0.99    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (~(! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X3,X0)) => ~(r2_hidden(X2,X3) & r2_hidden(X1,X3))) & (r1_orders_2(X0,X2,X1) | r1_orders_2(X0,X1,X2))) & ~(~r1_orders_2(X0,X2,X1) & ~r1_orders_2(X0,X1,X2) & ? [X4] : (r2_hidden(X2,X4) & r2_hidden(X1,X4) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X4,X0)))))))),
% 2.61/0.99    inference(rectify,[],[f10])).
% 2.61/0.99  
% 2.61/0.99  fof(f25,plain,(
% 2.61/0.99    ! [X0] : (! [X1] : (! [X2] : (((? [X3] : ((r2_hidden(X2,X3) & r2_hidden(X1,X3)) & (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X3,X0))) | (~r1_orders_2(X0,X2,X1) & ~r1_orders_2(X0,X1,X2))) & (r1_orders_2(X0,X2,X1) | r1_orders_2(X0,X1,X2) | ! [X4] : (~r2_hidden(X2,X4) | ~r2_hidden(X1,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X4,X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v3_orders_2(X0)))),
% 2.61/0.99    inference(ennf_transformation,[],[f14])).
% 2.61/0.99  
% 2.61/0.99  fof(f26,plain,(
% 2.61/0.99    ! [X0] : (! [X1] : (! [X2] : (((? [X3] : (r2_hidden(X2,X3) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X3,X0)) | (~r1_orders_2(X0,X2,X1) & ~r1_orders_2(X0,X1,X2))) & (r1_orders_2(X0,X2,X1) | r1_orders_2(X0,X1,X2) | ! [X4] : (~r2_hidden(X2,X4) | ~r2_hidden(X1,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X4,X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_orders_2(X0))),
% 2.61/0.99    inference(flattening,[],[f25])).
% 2.61/0.99  
% 2.61/0.99  fof(f32,plain,(
% 2.61/0.99    ! [X0] : (! [X1] : (! [X2] : ((sP0(X2,X1,X0) & (r1_orders_2(X0,X2,X1) | r1_orders_2(X0,X1,X2) | ! [X4] : (~r2_hidden(X2,X4) | ~r2_hidden(X1,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X4,X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_orders_2(X0))),
% 2.61/0.99    inference(definition_folding,[],[f26,f31])).
% 2.61/0.99  
% 2.61/0.99  fof(f42,plain,(
% 2.61/0.99    ! [X0] : (! [X1] : (! [X2] : ((sP0(X2,X1,X0) & (r1_orders_2(X0,X2,X1) | r1_orders_2(X0,X1,X2) | ! [X3] : (~r2_hidden(X2,X3) | ~r2_hidden(X1,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X3,X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_orders_2(X0))),
% 2.61/0.99    inference(rectify,[],[f32])).
% 2.61/0.99  
% 2.61/0.99  fof(f69,plain,(
% 2.61/0.99    ( ! [X2,X0,X1] : (sP0(X2,X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0)) )),
% 2.61/0.99    inference(cnf_transformation,[],[f42])).
% 2.61/0.99  
% 2.61/0.99  fof(f64,plain,(
% 2.61/0.99    ( ! [X2,X0,X1] : (r2_hidden(X1,sK2(X0,X1,X2)) | ~r1_orders_2(X2,X1,X0) | ~sP0(X0,X1,X2)) )),
% 2.61/0.99    inference(cnf_transformation,[],[f41])).
% 2.61/0.99  
% 2.61/0.99  fof(f7,axiom,(
% 2.61/0.99    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 2.61/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.61/0.99  
% 2.61/0.99  fof(f20,plain,(
% 2.61/0.99    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.61/0.99    inference(ennf_transformation,[],[f7])).
% 2.61/0.99  
% 2.61/0.99  fof(f57,plain,(
% 2.61/0.99    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.61/0.99    inference(cnf_transformation,[],[f20])).
% 2.61/0.99  
% 2.61/0.99  fof(f4,axiom,(
% 2.61/0.99    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 2.61/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.61/0.99  
% 2.61/0.99  fof(f15,plain,(
% 2.61/0.99    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 2.61/0.99    inference(ennf_transformation,[],[f4])).
% 2.61/0.99  
% 2.61/0.99  fof(f54,plain,(
% 2.61/0.99    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 2.61/0.99    inference(cnf_transformation,[],[f15])).
% 2.61/0.99  
% 2.61/0.99  fof(f85,plain,(
% 2.61/0.99    ( ! [X0,X1] : (m1_subset_1(k1_enumset1(X0,X0,X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 2.61/0.99    inference(definition_unfolding,[],[f54,f78])).
% 2.61/0.99  
% 2.61/0.99  fof(f11,axiom,(
% 2.61/0.99    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(r2_hidden(X1,k1_orders_2(X0,X2)) & r2_hidden(X1,X2)))))),
% 2.61/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.61/0.99  
% 2.61/0.99  fof(f27,plain,(
% 2.61/0.99    ! [X0] : (! [X1] : (! [X2] : ((~r2_hidden(X1,k1_orders_2(X0,X2)) | ~r2_hidden(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.61/0.99    inference(ennf_transformation,[],[f11])).
% 2.61/0.99  
% 2.61/0.99  fof(f28,plain,(
% 2.61/0.99    ! [X0] : (! [X1] : (! [X2] : (~r2_hidden(X1,k1_orders_2(X0,X2)) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.61/0.99    inference(flattening,[],[f27])).
% 2.61/0.99  
% 2.61/0.99  fof(f70,plain,(
% 2.61/0.99    ( ! [X2,X0,X1] : (~r2_hidden(X1,k1_orders_2(X0,X2)) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.61/0.99    inference(cnf_transformation,[],[f28])).
% 2.61/0.99  
% 2.61/0.99  fof(f74,plain,(
% 2.61/0.99    v5_orders_2(sK3)),
% 2.61/0.99    inference(cnf_transformation,[],[f45])).
% 2.61/0.99  
% 2.61/0.99  fof(f73,plain,(
% 2.61/0.99    v4_orders_2(sK3)),
% 2.61/0.99    inference(cnf_transformation,[],[f45])).
% 2.61/0.99  
% 2.61/0.99  fof(f6,axiom,(
% 2.61/0.99    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 2.61/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.61/0.99  
% 2.61/0.99  fof(f18,plain,(
% 2.61/0.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 2.61/0.99    inference(ennf_transformation,[],[f6])).
% 2.61/0.99  
% 2.61/0.99  fof(f19,plain,(
% 2.61/0.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.61/0.99    inference(flattening,[],[f18])).
% 2.61/0.99  
% 2.61/0.99  fof(f56,plain,(
% 2.61/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.61/0.99    inference(cnf_transformation,[],[f19])).
% 2.61/0.99  
% 2.61/0.99  fof(f5,axiom,(
% 2.61/0.99    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.61/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.61/0.99  
% 2.61/0.99  fof(f16,plain,(
% 2.61/0.99    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.61/0.99    inference(ennf_transformation,[],[f5])).
% 2.61/0.99  
% 2.61/0.99  fof(f17,plain,(
% 2.61/0.99    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.61/0.99    inference(flattening,[],[f16])).
% 2.61/0.99  
% 2.61/0.99  fof(f55,plain,(
% 2.61/0.99    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 2.61/0.99    inference(cnf_transformation,[],[f17])).
% 2.61/0.99  
% 2.61/0.99  fof(f1,axiom,(
% 2.61/0.99    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 2.61/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.61/0.99  
% 2.61/0.99  fof(f33,plain,(
% 2.61/0.99    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 2.61/0.99    inference(nnf_transformation,[],[f1])).
% 2.61/0.99  
% 2.61/0.99  fof(f34,plain,(
% 2.61/0.99    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 2.61/0.99    inference(flattening,[],[f33])).
% 2.61/0.99  
% 2.61/0.99  fof(f35,plain,(
% 2.61/0.99    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 2.61/0.99    inference(rectify,[],[f34])).
% 2.61/0.99  
% 2.61/0.99  fof(f36,plain,(
% 2.61/0.99    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK1(X0,X1,X2) != X1 & sK1(X0,X1,X2) != X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (sK1(X0,X1,X2) = X1 | sK1(X0,X1,X2) = X0 | r2_hidden(sK1(X0,X1,X2),X2))))),
% 2.61/0.99    introduced(choice_axiom,[])).
% 2.61/0.99  
% 2.61/0.99  fof(f37,plain,(
% 2.61/0.99    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK1(X0,X1,X2) != X1 & sK1(X0,X1,X2) != X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (sK1(X0,X1,X2) = X1 | sK1(X0,X1,X2) = X0 | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 2.61/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f35,f36])).
% 2.61/0.99  
% 2.61/0.99  fof(f47,plain,(
% 2.61/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 2.61/0.99    inference(cnf_transformation,[],[f37])).
% 2.61/0.99  
% 2.61/0.99  fof(f83,plain,(
% 2.61/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k1_enumset1(X0,X0,X1) != X2) )),
% 2.61/0.99    inference(definition_unfolding,[],[f47,f53])).
% 2.61/0.99  
% 2.61/0.99  fof(f89,plain,(
% 2.61/0.99    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k1_enumset1(X4,X4,X1) != X2) )),
% 2.61/0.99    inference(equality_resolution,[],[f83])).
% 2.61/0.99  
% 2.61/0.99  fof(f90,plain,(
% 2.61/0.99    ( ! [X4,X1] : (r2_hidden(X4,k1_enumset1(X4,X4,X1))) )),
% 2.61/0.99    inference(equality_resolution,[],[f89])).
% 2.61/0.99  
% 2.61/0.99  cnf(c_23,negated_conjecture,
% 2.61/0.99      ( r2_hidden(sK4,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))) ),
% 2.61/0.99      inference(cnf_transformation,[],[f77]) ).
% 2.61/0.99  
% 2.61/0.99  cnf(c_1481,plain,
% 2.61/0.99      ( r2_hidden(sK4,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))) = iProver_top ),
% 2.61/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.61/0.99  
% 2.61/0.99  cnf(c_24,negated_conjecture,
% 2.61/0.99      ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 2.61/0.99      inference(cnf_transformation,[],[f76]) ).
% 2.61/0.99  
% 2.61/0.99  cnf(c_1480,plain,
% 2.61/0.99      ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
% 2.61/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.61/0.99  
% 2.61/0.99  cnf(c_10,plain,
% 2.61/0.99      ( ~ m1_subset_1(X0,X1)
% 2.61/0.99      | v1_xboole_0(X1)
% 2.61/0.99      | k1_enumset1(X0,X0,X0) = k6_domain_1(X1,X0) ),
% 2.61/0.99      inference(cnf_transformation,[],[f86]) ).
% 2.61/0.99  
% 2.61/0.99  cnf(c_1482,plain,
% 2.61/0.99      ( k1_enumset1(X0,X0,X0) = k6_domain_1(X1,X0)
% 2.61/0.99      | m1_subset_1(X0,X1) != iProver_top
% 2.61/0.99      | v1_xboole_0(X1) = iProver_top ),
% 2.61/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.61/0.99  
% 2.61/0.99  cnf(c_2596,plain,
% 2.61/0.99      ( k6_domain_1(u1_struct_0(sK3),sK4) = k1_enumset1(sK4,sK4,sK4)
% 2.61/0.99      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 2.61/0.99      inference(superposition,[status(thm)],[c_1480,c_1482]) ).
% 2.61/0.99  
% 2.61/0.99  cnf(c_35,plain,
% 2.61/0.99      ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
% 2.61/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.61/0.99  
% 2.61/0.99  cnf(c_11,plain,
% 2.61/0.99      ( r1_orders_2(X0,X1,X1)
% 2.61/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.61/0.99      | v2_struct_0(X0)
% 2.61/0.99      | ~ v3_orders_2(X0)
% 2.61/0.99      | ~ l1_orders_2(X0) ),
% 2.61/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.61/0.99  
% 2.61/0.99  cnf(c_29,negated_conjecture,
% 2.61/0.99      ( ~ v2_struct_0(sK3) ),
% 2.61/0.99      inference(cnf_transformation,[],[f71]) ).
% 2.61/0.99  
% 2.61/0.99  cnf(c_388,plain,
% 2.61/0.99      ( r1_orders_2(X0,X1,X1)
% 2.61/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.61/0.99      | ~ v3_orders_2(X0)
% 2.61/0.99      | ~ l1_orders_2(X0)
% 2.61/0.99      | sK3 != X0 ),
% 2.61/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_29]) ).
% 2.61/0.99  
% 2.61/0.99  cnf(c_389,plain,
% 2.61/0.99      ( r1_orders_2(sK3,X0,X0)
% 2.61/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.61/0.99      | ~ v3_orders_2(sK3)
% 2.61/0.99      | ~ l1_orders_2(sK3) ),
% 2.61/0.99      inference(unflattening,[status(thm)],[c_388]) ).
% 2.61/0.99  
% 2.61/0.99  cnf(c_28,negated_conjecture,
% 2.61/0.99      ( v3_orders_2(sK3) ),
% 2.61/0.99      inference(cnf_transformation,[],[f72]) ).
% 2.61/0.99  
% 2.61/0.99  cnf(c_25,negated_conjecture,
% 2.61/0.99      ( l1_orders_2(sK3) ),
% 2.61/0.99      inference(cnf_transformation,[],[f75]) ).
% 2.61/0.99  
% 2.61/0.99  cnf(c_393,plain,
% 2.61/0.99      ( r1_orders_2(sK3,X0,X0) | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 2.61/0.99      inference(global_propositional_subsumption,
% 2.61/0.99                [status(thm)],
% 2.61/0.99                [c_389,c_28,c_25]) ).
% 2.61/0.99  
% 2.61/0.99  cnf(c_1693,plain,
% 2.61/0.99      ( r1_orders_2(sK3,sK4,sK4) | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 2.61/0.99      inference(instantiation,[status(thm)],[c_393]) ).
% 2.61/0.99  
% 2.61/0.99  cnf(c_1694,plain,
% 2.61/0.99      ( r1_orders_2(sK3,sK4,sK4) = iProver_top
% 2.61/0.99      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
% 2.61/0.99      inference(predicate_to_equality,[status(thm)],[c_1693]) ).
% 2.61/0.99  
% 2.61/0.99  cnf(c_16,plain,
% 2.61/0.99      ( ~ sP0(X0,X1,X2)
% 2.61/0.99      | ~ r1_orders_2(X2,X0,X1)
% 2.61/0.99      | m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) ),
% 2.61/0.99      inference(cnf_transformation,[],[f63]) ).
% 2.61/0.99  
% 2.61/0.99  cnf(c_20,plain,
% 2.61/0.99      ( sP0(X0,X1,X2)
% 2.61/0.99      | ~ m1_subset_1(X1,u1_struct_0(X2))
% 2.61/0.99      | ~ m1_subset_1(X0,u1_struct_0(X2))
% 2.61/0.99      | ~ v3_orders_2(X2)
% 2.61/0.99      | ~ l1_orders_2(X2) ),
% 2.61/0.99      inference(cnf_transformation,[],[f69]) ).
% 2.61/0.99  
% 2.61/0.99  cnf(c_446,plain,
% 2.61/0.99      ( sP0(X0,X1,X2)
% 2.61/0.99      | ~ m1_subset_1(X1,u1_struct_0(X2))
% 2.61/0.99      | ~ m1_subset_1(X0,u1_struct_0(X2))
% 2.61/0.99      | ~ v3_orders_2(X2)
% 2.61/0.99      | sK3 != X2 ),
% 2.61/0.99      inference(resolution_lifted,[status(thm)],[c_20,c_25]) ).
% 2.61/0.99  
% 2.61/0.99  cnf(c_447,plain,
% 2.61/0.99      ( sP0(X0,X1,sK3)
% 2.61/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.61/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.61/0.99      | ~ v3_orders_2(sK3) ),
% 2.61/0.99      inference(unflattening,[status(thm)],[c_446]) ).
% 2.61/0.99  
% 2.61/0.99  cnf(c_451,plain,
% 2.61/0.99      ( ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.61/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.61/0.99      | sP0(X0,X1,sK3) ),
% 2.61/0.99      inference(global_propositional_subsumption,
% 2.61/0.99                [status(thm)],
% 2.61/0.99                [c_447,c_28]) ).
% 2.61/0.99  
% 2.61/0.99  cnf(c_452,plain,
% 2.61/0.99      ( sP0(X0,X1,sK3)
% 2.61/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.61/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3)) ),
% 2.61/0.99      inference(renaming,[status(thm)],[c_451]) ).
% 2.61/0.99  
% 2.61/0.99  cnf(c_592,plain,
% 2.61/0.99      ( ~ r1_orders_2(X0,X1,X2)
% 2.61/0.99      | ~ m1_subset_1(X3,u1_struct_0(sK3))
% 2.61/0.99      | ~ m1_subset_1(X4,u1_struct_0(sK3))
% 2.61/0.99      | m1_subset_1(sK2(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X0)))
% 2.61/0.99      | X4 != X2
% 2.61/0.99      | X3 != X1
% 2.61/0.99      | sK3 != X0 ),
% 2.61/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_452]) ).
% 2.61/0.99  
% 2.61/0.99  cnf(c_593,plain,
% 2.61/0.99      ( ~ r1_orders_2(sK3,X0,X1)
% 2.61/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.61/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.61/0.99      | m1_subset_1(sK2(X0,X1,sK3),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.61/0.99      inference(unflattening,[status(thm)],[c_592]) ).
% 2.61/0.99  
% 2.61/0.99  cnf(c_1711,plain,
% 2.61/0.99      ( ~ r1_orders_2(sK3,sK4,X0)
% 2.61/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.61/0.99      | m1_subset_1(sK2(sK4,X0,sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.61/0.99      | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 2.61/0.99      inference(instantiation,[status(thm)],[c_593]) ).
% 2.61/0.99  
% 2.61/0.99  cnf(c_1916,plain,
% 2.61/0.99      ( ~ r1_orders_2(sK3,sK4,sK4)
% 2.61/0.99      | m1_subset_1(sK2(sK4,sK4,sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.61/0.99      | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 2.61/0.99      inference(instantiation,[status(thm)],[c_1711]) ).
% 2.61/0.99  
% 2.61/0.99  cnf(c_1917,plain,
% 2.61/0.99      ( r1_orders_2(sK3,sK4,sK4) != iProver_top
% 2.61/0.99      | m1_subset_1(sK2(sK4,sK4,sK3),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 2.61/0.99      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
% 2.61/0.99      inference(predicate_to_equality,[status(thm)],[c_1916]) ).
% 2.61/0.99  
% 2.61/0.99  cnf(c_15,plain,
% 2.61/0.99      ( ~ sP0(X0,X1,X2)
% 2.61/0.99      | ~ r1_orders_2(X2,X1,X0)
% 2.61/0.99      | r2_hidden(X1,sK2(X0,X1,X2)) ),
% 2.61/0.99      inference(cnf_transformation,[],[f64]) ).
% 2.61/0.99  
% 2.61/0.99  cnf(c_608,plain,
% 2.61/0.99      ( ~ r1_orders_2(X0,X1,X2)
% 2.61/0.99      | ~ m1_subset_1(X3,u1_struct_0(sK3))
% 2.61/0.99      | ~ m1_subset_1(X4,u1_struct_0(sK3))
% 2.61/0.99      | r2_hidden(X1,sK2(X2,X1,X0))
% 2.61/0.99      | X4 != X1
% 2.61/0.99      | X3 != X2
% 2.61/0.99      | sK3 != X0 ),
% 2.61/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_452]) ).
% 2.61/0.99  
% 2.61/0.99  cnf(c_609,plain,
% 2.61/0.99      ( ~ r1_orders_2(sK3,X0,X1)
% 2.61/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.61/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.61/0.99      | r2_hidden(X0,sK2(X1,X0,sK3)) ),
% 2.61/0.99      inference(unflattening,[status(thm)],[c_608]) ).
% 2.61/0.99  
% 2.61/0.99  cnf(c_1716,plain,
% 2.61/0.99      ( ~ r1_orders_2(sK3,sK4,X0)
% 2.61/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.61/0.99      | ~ m1_subset_1(sK4,u1_struct_0(sK3))
% 2.61/0.99      | r2_hidden(sK4,sK2(X0,sK4,sK3)) ),
% 2.61/0.99      inference(instantiation,[status(thm)],[c_609]) ).
% 2.61/0.99  
% 2.61/0.99  cnf(c_1919,plain,
% 2.61/0.99      ( ~ r1_orders_2(sK3,sK4,sK4)
% 2.61/0.99      | ~ m1_subset_1(sK4,u1_struct_0(sK3))
% 2.61/0.99      | r2_hidden(sK4,sK2(sK4,sK4,sK3)) ),
% 2.61/0.99      inference(instantiation,[status(thm)],[c_1716]) ).
% 2.61/0.99  
% 2.61/0.99  cnf(c_1920,plain,
% 2.61/0.99      ( r1_orders_2(sK3,sK4,sK4) != iProver_top
% 2.61/0.99      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 2.61/0.99      | r2_hidden(sK4,sK2(sK4,sK4,sK3)) = iProver_top ),
% 2.61/0.99      inference(predicate_to_equality,[status(thm)],[c_1919]) ).
% 2.61/0.99  
% 2.61/0.99  cnf(c_9,plain,
% 2.61/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.61/0.99      | ~ r2_hidden(X2,X0)
% 2.61/0.99      | ~ v1_xboole_0(X1) ),
% 2.61/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.61/0.99  
% 2.61/0.99  cnf(c_1807,plain,
% 2.61/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.61/0.99      | ~ r2_hidden(X1,X0)
% 2.61/0.99      | ~ v1_xboole_0(u1_struct_0(sK3)) ),
% 2.61/0.99      inference(instantiation,[status(thm)],[c_9]) ).
% 2.61/0.99  
% 2.61/0.99  cnf(c_2138,plain,
% 2.61/0.99      ( ~ m1_subset_1(sK2(sK4,sK4,sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.61/0.99      | ~ r2_hidden(X0,sK2(sK4,sK4,sK3))
% 2.61/0.99      | ~ v1_xboole_0(u1_struct_0(sK3)) ),
% 2.61/0.99      inference(instantiation,[status(thm)],[c_1807]) ).
% 2.61/0.99  
% 2.61/0.99  cnf(c_2537,plain,
% 2.61/0.99      ( ~ m1_subset_1(sK2(sK4,sK4,sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.61/0.99      | ~ r2_hidden(sK4,sK2(sK4,sK4,sK3))
% 2.61/0.99      | ~ v1_xboole_0(u1_struct_0(sK3)) ),
% 2.61/0.99      inference(instantiation,[status(thm)],[c_2138]) ).
% 2.61/0.99  
% 2.61/0.99  cnf(c_2538,plain,
% 2.61/0.99      ( m1_subset_1(sK2(sK4,sK4,sK3),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.61/0.99      | r2_hidden(sK4,sK2(sK4,sK4,sK3)) != iProver_top
% 2.61/0.99      | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
% 2.61/0.99      inference(predicate_to_equality,[status(thm)],[c_2537]) ).
% 2.61/0.99  
% 2.61/0.99  cnf(c_3332,plain,
% 2.61/0.99      ( k6_domain_1(u1_struct_0(sK3),sK4) = k1_enumset1(sK4,sK4,sK4) ),
% 2.61/0.99      inference(global_propositional_subsumption,
% 2.61/0.99                [status(thm)],
% 2.61/0.99                [c_2596,c_35,c_1694,c_1917,c_1920,c_2538]) ).
% 2.61/0.99  
% 2.61/0.99  cnf(c_6,plain,
% 2.61/0.99      ( m1_subset_1(k1_enumset1(X0,X0,X0),k1_zfmisc_1(X1))
% 2.61/0.99      | ~ r2_hidden(X0,X1) ),
% 2.61/0.99      inference(cnf_transformation,[],[f85]) ).
% 2.61/0.99  
% 2.61/0.99  cnf(c_1486,plain,
% 2.61/0.99      ( m1_subset_1(k1_enumset1(X0,X0,X0),k1_zfmisc_1(X1)) = iProver_top
% 2.61/0.99      | r2_hidden(X0,X1) != iProver_top ),
% 2.61/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.61/0.99  
% 2.61/0.99  cnf(c_22,plain,
% 2.61/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.61/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.61/0.99      | ~ r2_hidden(X0,X2)
% 2.61/0.99      | ~ r2_hidden(X0,k1_orders_2(X1,X2))
% 2.61/0.99      | ~ v4_orders_2(X1)
% 2.61/0.99      | ~ v5_orders_2(X1)
% 2.61/0.99      | v2_struct_0(X1)
% 2.61/0.99      | ~ v3_orders_2(X1)
% 2.61/0.99      | ~ l1_orders_2(X1) ),
% 2.61/0.99      inference(cnf_transformation,[],[f70]) ).
% 2.61/0.99  
% 2.61/0.99  cnf(c_26,negated_conjecture,
% 2.61/0.99      ( v5_orders_2(sK3) ),
% 2.61/0.99      inference(cnf_transformation,[],[f74]) ).
% 2.61/0.99  
% 2.61/0.99  cnf(c_358,plain,
% 2.61/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.61/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.61/0.99      | ~ r2_hidden(X0,X2)
% 2.61/0.99      | ~ r2_hidden(X0,k1_orders_2(X1,X2))
% 2.61/0.99      | ~ v4_orders_2(X1)
% 2.61/0.99      | v2_struct_0(X1)
% 2.61/0.99      | ~ v3_orders_2(X1)
% 2.61/0.99      | ~ l1_orders_2(X1)
% 2.61/0.99      | sK3 != X1 ),
% 2.61/0.99      inference(resolution_lifted,[status(thm)],[c_22,c_26]) ).
% 2.61/0.99  
% 2.61/0.99  cnf(c_359,plain,
% 2.61/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.61/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.61/0.99      | ~ r2_hidden(X0,X1)
% 2.61/0.99      | ~ r2_hidden(X0,k1_orders_2(sK3,X1))
% 2.61/0.99      | ~ v4_orders_2(sK3)
% 2.61/0.99      | v2_struct_0(sK3)
% 2.61/0.99      | ~ v3_orders_2(sK3)
% 2.61/0.99      | ~ l1_orders_2(sK3) ),
% 2.61/0.99      inference(unflattening,[status(thm)],[c_358]) ).
% 2.61/0.99  
% 2.61/0.99  cnf(c_27,negated_conjecture,
% 2.61/0.99      ( v4_orders_2(sK3) ),
% 2.61/0.99      inference(cnf_transformation,[],[f73]) ).
% 2.61/0.99  
% 2.61/0.99  cnf(c_363,plain,
% 2.61/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.61/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.61/0.99      | ~ r2_hidden(X0,X1)
% 2.61/0.99      | ~ r2_hidden(X0,k1_orders_2(sK3,X1)) ),
% 2.61/0.99      inference(global_propositional_subsumption,
% 2.61/0.99                [status(thm)],
% 2.61/0.99                [c_359,c_29,c_28,c_27,c_25]) ).
% 2.61/0.99  
% 2.61/0.99  cnf(c_8,plain,
% 2.61/0.99      ( m1_subset_1(X0,X1)
% 2.61/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 2.61/0.99      | ~ r2_hidden(X0,X2) ),
% 2.61/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.61/0.99  
% 2.61/0.99  cnf(c_377,plain,
% 2.61/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.61/0.99      | ~ r2_hidden(X1,X0)
% 2.61/0.99      | ~ r2_hidden(X1,k1_orders_2(sK3,X0)) ),
% 2.61/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_363,c_8]) ).
% 2.61/0.99  
% 2.61/0.99  cnf(c_1479,plain,
% 2.61/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.61/0.99      | r2_hidden(X1,X0) != iProver_top
% 2.61/0.99      | r2_hidden(X1,k1_orders_2(sK3,X0)) != iProver_top ),
% 2.61/0.99      inference(predicate_to_equality,[status(thm)],[c_377]) ).
% 2.61/0.99  
% 2.61/0.99  cnf(c_1998,plain,
% 2.61/0.99      ( r2_hidden(X0,k1_enumset1(X1,X1,X1)) != iProver_top
% 2.61/0.99      | r2_hidden(X0,k1_orders_2(sK3,k1_enumset1(X1,X1,X1))) != iProver_top
% 2.61/0.99      | r2_hidden(X1,u1_struct_0(sK3)) != iProver_top ),
% 2.61/0.99      inference(superposition,[status(thm)],[c_1486,c_1479]) ).
% 2.61/0.99  
% 2.61/0.99  cnf(c_3339,plain,
% 2.61/0.99      ( r2_hidden(X0,k1_enumset1(sK4,sK4,sK4)) != iProver_top
% 2.61/0.99      | r2_hidden(X0,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))) != iProver_top
% 2.61/0.99      | r2_hidden(sK4,u1_struct_0(sK3)) != iProver_top ),
% 2.61/0.99      inference(superposition,[status(thm)],[c_3332,c_1998]) ).
% 2.61/0.99  
% 2.61/0.99  cnf(c_3340,plain,
% 2.61/0.99      ( r2_hidden(X0,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))) != iProver_top
% 2.61/0.99      | r2_hidden(X0,k6_domain_1(u1_struct_0(sK3),sK4)) != iProver_top
% 2.61/0.99      | r2_hidden(sK4,u1_struct_0(sK3)) != iProver_top ),
% 2.61/0.99      inference(light_normalisation,[status(thm)],[c_3339,c_3332]) ).
% 2.61/0.99  
% 2.61/0.99  cnf(c_7,plain,
% 2.61/0.99      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.61/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.61/0.99  
% 2.61/0.99  cnf(c_1485,plain,
% 2.61/0.99      ( m1_subset_1(X0,X1) != iProver_top
% 2.61/0.99      | r2_hidden(X0,X1) = iProver_top
% 2.61/0.99      | v1_xboole_0(X1) = iProver_top ),
% 2.61/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.61/0.99  
% 2.61/0.99  cnf(c_2037,plain,
% 2.61/0.99      ( r2_hidden(sK4,u1_struct_0(sK3)) = iProver_top
% 2.61/0.99      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 2.61/0.99      inference(superposition,[status(thm)],[c_1480,c_1485]) ).
% 2.61/0.99  
% 2.61/0.99  cnf(c_3818,plain,
% 2.61/0.99      ( r2_hidden(X0,k6_domain_1(u1_struct_0(sK3),sK4)) != iProver_top
% 2.61/0.99      | r2_hidden(X0,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))) != iProver_top ),
% 2.61/0.99      inference(global_propositional_subsumption,
% 2.61/0.99                [status(thm)],
% 2.61/0.99                [c_3340,c_35,c_1694,c_1917,c_1920,c_2037,c_2538]) ).
% 2.61/0.99  
% 2.61/0.99  cnf(c_3819,plain,
% 2.61/0.99      ( r2_hidden(X0,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))) != iProver_top
% 2.61/0.99      | r2_hidden(X0,k6_domain_1(u1_struct_0(sK3),sK4)) != iProver_top ),
% 2.61/0.99      inference(renaming,[status(thm)],[c_3818]) ).
% 2.61/0.99  
% 2.61/0.99  cnf(c_3826,plain,
% 2.61/0.99      ( r2_hidden(sK4,k6_domain_1(u1_struct_0(sK3),sK4)) != iProver_top ),
% 2.61/0.99      inference(superposition,[status(thm)],[c_1481,c_3819]) ).
% 2.61/0.99  
% 2.61/0.99  cnf(c_4,plain,
% 2.61/0.99      ( r2_hidden(X0,k1_enumset1(X0,X0,X1)) ),
% 2.61/0.99      inference(cnf_transformation,[],[f90]) ).
% 2.61/0.99  
% 2.61/0.99  cnf(c_1488,plain,
% 2.61/0.99      ( r2_hidden(X0,k1_enumset1(X0,X0,X1)) = iProver_top ),
% 2.61/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.61/0.99  
% 2.61/0.99  cnf(c_3335,plain,
% 2.61/0.99      ( r2_hidden(sK4,k6_domain_1(u1_struct_0(sK3),sK4)) = iProver_top ),
% 2.61/0.99      inference(superposition,[status(thm)],[c_3332,c_1488]) ).
% 2.61/0.99  
% 2.61/0.99  cnf(contradiction,plain,
% 2.61/0.99      ( $false ),
% 2.61/0.99      inference(minisat,[status(thm)],[c_3826,c_3335]) ).
% 2.61/0.99  
% 2.61/0.99  
% 2.61/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.61/0.99  
% 2.61/0.99  ------                               Statistics
% 2.61/0.99  
% 2.61/0.99  ------ General
% 2.61/0.99  
% 2.61/0.99  abstr_ref_over_cycles:                  0
% 2.61/0.99  abstr_ref_under_cycles:                 0
% 2.61/0.99  gc_basic_clause_elim:                   0
% 2.61/0.99  forced_gc_time:                         0
% 2.61/0.99  parsing_time:                           0.009
% 2.61/0.99  unif_index_cands_time:                  0.
% 2.61/0.99  unif_index_add_time:                    0.
% 2.61/0.99  orderings_time:                         0.
% 2.61/0.99  out_proof_time:                         0.011
% 2.61/0.99  total_time:                             0.146
% 2.61/0.99  num_of_symbols:                         51
% 2.61/0.99  num_of_terms:                           3925
% 2.61/0.99  
% 2.61/0.99  ------ Preprocessing
% 2.61/0.99  
% 2.61/0.99  num_of_splits:                          0
% 2.61/0.99  num_of_split_atoms:                     0
% 2.61/0.99  num_of_reused_defs:                     0
% 2.61/0.99  num_eq_ax_congr_red:                    39
% 2.61/0.99  num_of_sem_filtered_clauses:            1
% 2.61/0.99  num_of_subtypes:                        0
% 2.61/0.99  monotx_restored_types:                  0
% 2.61/0.99  sat_num_of_epr_types:                   0
% 2.61/0.99  sat_num_of_non_cyclic_types:            0
% 2.61/0.99  sat_guarded_non_collapsed_types:        0
% 2.61/0.99  num_pure_diseq_elim:                    0
% 2.61/0.99  simp_replaced_by:                       0
% 2.61/0.99  res_preprocessed:                       125
% 2.61/0.99  prep_upred:                             0
% 2.61/0.99  prep_unflattend:                        36
% 2.61/0.99  smt_new_axioms:                         0
% 2.61/0.99  pred_elim_cands:                        5
% 2.61/0.99  pred_elim:                              6
% 2.61/0.99  pred_elim_cl:                           6
% 2.61/0.99  pred_elim_cycles:                       11
% 2.61/0.99  merged_defs:                            0
% 2.61/0.99  merged_defs_ncl:                        0
% 2.61/0.99  bin_hyper_res:                          0
% 2.61/0.99  prep_cycles:                            4
% 2.61/0.99  pred_elim_time:                         0.012
% 2.61/0.99  splitting_time:                         0.
% 2.61/0.99  sem_filter_time:                        0.
% 2.61/0.99  monotx_time:                            0.
% 2.61/0.99  subtype_inf_time:                       0.
% 2.61/0.99  
% 2.61/0.99  ------ Problem properties
% 2.61/0.99  
% 2.61/0.99  clauses:                                24
% 2.61/0.99  conjectures:                            2
% 2.61/0.99  epr:                                    1
% 2.61/0.99  horn:                                   19
% 2.61/0.99  ground:                                 2
% 2.61/0.99  unary:                                  4
% 2.61/0.99  binary:                                 2
% 2.61/0.99  lits:                                   74
% 2.61/0.99  lits_eq:                                10
% 2.61/0.99  fd_pure:                                0
% 2.61/0.99  fd_pseudo:                              0
% 2.61/0.99  fd_cond:                                0
% 2.61/0.99  fd_pseudo_cond:                         3
% 2.61/0.99  ac_symbols:                             0
% 2.61/0.99  
% 2.61/0.99  ------ Propositional Solver
% 2.61/0.99  
% 2.61/0.99  prop_solver_calls:                      26
% 2.61/0.99  prop_fast_solver_calls:                 1003
% 2.61/0.99  smt_solver_calls:                       0
% 2.61/0.99  smt_fast_solver_calls:                  0
% 2.61/0.99  prop_num_of_clauses:                    1278
% 2.61/0.99  prop_preprocess_simplified:             5490
% 2.61/0.99  prop_fo_subsumed:                       14
% 2.61/0.99  prop_solver_time:                       0.
% 2.61/0.99  smt_solver_time:                        0.
% 2.61/0.99  smt_fast_solver_time:                   0.
% 2.61/0.99  prop_fast_solver_time:                  0.
% 2.61/0.99  prop_unsat_core_time:                   0.
% 2.61/0.99  
% 2.61/0.99  ------ QBF
% 2.61/0.99  
% 2.61/0.99  qbf_q_res:                              0
% 2.61/0.99  qbf_num_tautologies:                    0
% 2.61/0.99  qbf_prep_cycles:                        0
% 2.61/0.99  
% 2.61/0.99  ------ BMC1
% 2.61/0.99  
% 2.61/0.99  bmc1_current_bound:                     -1
% 2.61/0.99  bmc1_last_solved_bound:                 -1
% 2.61/0.99  bmc1_unsat_core_size:                   -1
% 2.61/0.99  bmc1_unsat_core_parents_size:           -1
% 2.61/0.99  bmc1_merge_next_fun:                    0
% 2.61/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.61/0.99  
% 2.61/0.99  ------ Instantiation
% 2.61/0.99  
% 2.61/0.99  inst_num_of_clauses:                    335
% 2.61/0.99  inst_num_in_passive:                    170
% 2.61/0.99  inst_num_in_active:                     146
% 2.61/0.99  inst_num_in_unprocessed:                19
% 2.61/0.99  inst_num_of_loops:                      160
% 2.61/0.99  inst_num_of_learning_restarts:          0
% 2.61/0.99  inst_num_moves_active_passive:          12
% 2.61/0.99  inst_lit_activity:                      0
% 2.61/0.99  inst_lit_activity_moves:                0
% 2.61/0.99  inst_num_tautologies:                   0
% 2.61/0.99  inst_num_prop_implied:                  0
% 2.61/0.99  inst_num_existing_simplified:           0
% 2.61/0.99  inst_num_eq_res_simplified:             0
% 2.61/0.99  inst_num_child_elim:                    0
% 2.61/0.99  inst_num_of_dismatching_blockings:      55
% 2.61/0.99  inst_num_of_non_proper_insts:           232
% 2.61/0.99  inst_num_of_duplicates:                 0
% 2.61/0.99  inst_inst_num_from_inst_to_res:         0
% 2.61/0.99  inst_dismatching_checking_time:         0.
% 2.61/0.99  
% 2.61/0.99  ------ Resolution
% 2.61/0.99  
% 2.61/0.99  res_num_of_clauses:                     0
% 2.61/0.99  res_num_in_passive:                     0
% 2.61/0.99  res_num_in_active:                      0
% 2.61/0.99  res_num_of_loops:                       129
% 2.61/0.99  res_forward_subset_subsumed:            47
% 2.61/0.99  res_backward_subset_subsumed:           0
% 2.61/0.99  res_forward_subsumed:                   0
% 2.61/0.99  res_backward_subsumed:                  0
% 2.61/0.99  res_forward_subsumption_resolution:     5
% 2.61/0.99  res_backward_subsumption_resolution:    0
% 2.61/0.99  res_clause_to_clause_subsumption:       288
% 2.61/0.99  res_orphan_elimination:                 0
% 2.61/0.99  res_tautology_del:                      19
% 2.61/0.99  res_num_eq_res_simplified:              0
% 2.61/0.99  res_num_sel_changes:                    0
% 2.61/0.99  res_moves_from_active_to_pass:          0
% 2.61/0.99  
% 2.61/0.99  ------ Superposition
% 2.61/0.99  
% 2.61/0.99  sup_time_total:                         0.
% 2.61/0.99  sup_time_generating:                    0.
% 2.61/0.99  sup_time_sim_full:                      0.
% 2.61/0.99  sup_time_sim_immed:                     0.
% 2.61/0.99  
% 2.61/0.99  sup_num_of_clauses:                     57
% 2.61/0.99  sup_num_in_active:                      31
% 2.61/0.99  sup_num_in_passive:                     26
% 2.61/0.99  sup_num_of_loops:                       30
% 2.61/0.99  sup_fw_superposition:                   20
% 2.61/0.99  sup_bw_superposition:                   16
% 2.61/0.99  sup_immediate_simplified:               1
% 2.61/0.99  sup_given_eliminated:                   0
% 2.61/0.99  comparisons_done:                       0
% 2.61/0.99  comparisons_avoided:                    0
% 2.61/0.99  
% 2.61/0.99  ------ Simplifications
% 2.61/0.99  
% 2.61/0.99  
% 2.61/0.99  sim_fw_subset_subsumed:                 0
% 2.61/0.99  sim_bw_subset_subsumed:                 0
% 2.61/0.99  sim_fw_subsumed:                        0
% 2.61/0.99  sim_bw_subsumed:                        0
% 2.61/0.99  sim_fw_subsumption_res:                 0
% 2.61/0.99  sim_bw_subsumption_res:                 0
% 2.61/0.99  sim_tautology_del:                      0
% 2.61/0.99  sim_eq_tautology_del:                   0
% 2.61/0.99  sim_eq_res_simp:                        0
% 2.61/0.99  sim_fw_demodulated:                     0
% 2.61/0.99  sim_bw_demodulated:                     0
% 2.61/0.99  sim_light_normalised:                   1
% 2.61/0.99  sim_joinable_taut:                      0
% 2.61/0.99  sim_joinable_simp:                      0
% 2.61/0.99  sim_ac_normalised:                      0
% 2.61/0.99  sim_smt_subsumption:                    0
% 2.61/0.99  
%------------------------------------------------------------------------------
