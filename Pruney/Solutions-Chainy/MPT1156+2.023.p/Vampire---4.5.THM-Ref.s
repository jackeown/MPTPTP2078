%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:01 EST 2020

% Result     : Theorem 1.44s
% Output     : Refutation 1.44s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 391 expanded)
%              Number of leaves         :   19 ( 122 expanded)
%              Depth                    :   17
%              Number of atoms          :  412 (2296 expanded)
%              Number of equality atoms :  101 ( 117 expanded)
%              Maximal formula depth    :   22 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f346,plain,(
    $false ),
    inference(subsumption_resolution,[],[f345,f198])).

fof(f198,plain,(
    m1_subset_1(k1_tarski(sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(backward_demodulation,[],[f91,f196])).

fof(f196,plain,(
    k6_domain_1(u1_struct_0(sK2),sK3) = k1_tarski(sK3) ),
    inference(resolution,[],[f135,f49])).

fof(f49,plain,(
    r2_hidden(sK3,k2_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK3))) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( r2_hidden(sK3,k2_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK3)))
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & l1_orders_2(sK2)
    & v5_orders_2(sK2)
    & v4_orders_2(sK2)
    & v3_orders_2(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f18,f33,f32])).

fof(f32,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( r2_hidden(X1,k2_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),X1)))
          & m1_subset_1(X1,u1_struct_0(sK2)) )
      & l1_orders_2(sK2)
      & v5_orders_2(sK2)
      & v4_orders_2(sK2)
      & v3_orders_2(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X1] :
        ( r2_hidden(X1,k2_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),X1)))
        & m1_subset_1(X1,u1_struct_0(sK2)) )
   => ( r2_hidden(sK3,k2_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK3)))
      & m1_subset_1(sK3,u1_struct_0(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ~ r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ~ r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_orders_2)).

fof(f135,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK3)))
      | k6_domain_1(u1_struct_0(sK2),sK3) = k1_tarski(sK3) ) ),
    inference(resolution,[],[f133,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | k6_domain_1(u1_struct_0(sK2),sK3) = k1_tarski(sK3)
      | ~ r2_hidden(X1,X0) ) ),
    inference(resolution,[],[f86,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f86,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | k6_domain_1(u1_struct_0(sK2),sK3) = k1_tarski(sK3) ),
    inference(resolution,[],[f54,f48])).

fof(f48,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f34])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f133,plain,(
    m1_subset_1(k2_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK3)),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(resolution,[],[f123,f91])).

fof(f123,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | m1_subset_1(k2_orders_2(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(subsumption_resolution,[],[f122,f43])).

fof(f43,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f122,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | m1_subset_1(k2_orders_2(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f121,f44])).

fof(f44,plain,(
    v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f121,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | m1_subset_1(k2_orders_2(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f120,f45])).

fof(f45,plain,(
    v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f120,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | m1_subset_1(k2_orders_2(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f119,f46])).

fof(f46,plain,(
    v5_orders_2(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f119,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | m1_subset_1(k2_orders_2(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v5_orders_2(sK2)
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f55,f47])).

fof(f47,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_orders_2)).

fof(f91,plain,(
    m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(resolution,[],[f90,f48])).

fof(f90,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
      | m1_subset_1(k6_domain_1(u1_struct_0(sK2),X0),k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(subsumption_resolution,[],[f89,f43])).

fof(f89,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
      | m1_subset_1(k6_domain_1(u1_struct_0(sK2),X0),k1_zfmisc_1(u1_struct_0(sK2)))
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f88,f44])).

fof(f88,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
      | m1_subset_1(k6_domain_1(u1_struct_0(sK2),X0),k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f52,f47])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_orders_2)).

fof(f345,plain,(
    ~ m1_subset_1(k1_tarski(sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(subsumption_resolution,[],[f344,f300])).

fof(f300,plain,(
    ! [X0] : r2_hidden(X0,k1_tarski(X0)) ),
    inference(resolution,[],[f299,f77])).

fof(f77,plain,(
    ! [X6,X4,X2,X8,X7,X5,X3,X1] : sP0(X1,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | ( X0 != X1
          & X0 != X2
          & X0 != X3
          & X0 != X4
          & X0 != X5
          & X0 != X6
          & X0 != X7
          & X0 != X8 ) )
      & ( X0 = X1
        | X0 = X2
        | X0 = X3
        | X0 = X4
        | X0 = X5
        | X0 = X6
        | X0 = X7
        | X0 = X8
        | ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
        | ( X7 != X9
          & X6 != X9
          & X5 != X9
          & X4 != X9
          & X3 != X9
          & X2 != X9
          & X1 != X9
          & X0 != X9 ) )
      & ( X7 = X9
        | X6 = X9
        | X5 = X9
        | X4 = X9
        | X3 = X9
        | X2 = X9
        | X1 = X9
        | X0 = X9
        | ~ sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
        | ( X7 != X9
          & X6 != X9
          & X5 != X9
          & X4 != X9
          & X3 != X9
          & X2 != X9
          & X1 != X9
          & X0 != X9 ) )
      & ( X7 = X9
        | X6 = X9
        | X5 = X9
        | X4 = X9
        | X3 = X9
        | X2 = X9
        | X1 = X9
        | X0 = X9
        | ~ sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
    <=> ( X7 = X9
        | X6 = X9
        | X5 = X9
        | X4 = X9
        | X3 = X9
        | X2 = X9
        | X1 = X9
        | X0 = X9 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f299,plain,(
    ! [X43,X42] :
      ( ~ sP0(X42,X43,X43,X43,X43,X43,X43,X43,X43)
      | r2_hidden(X42,k1_tarski(X43)) ) ),
    inference(resolution,[],[f63,f100])).

fof(f100,plain,(
    ! [X0] : sP1(X0,X0,X0,X0,X0,X0,X0,X0,k1_tarski(X0)) ),
    inference(superposition,[],[f99,f50])).

fof(f50,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f99,plain,(
    ! [X0,X1] : sP1(X0,X0,X0,X0,X0,X0,X0,X1,k2_tarski(X0,X1)) ),
    inference(superposition,[],[f98,f53])).

fof(f53,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f98,plain,(
    ! [X2,X0,X1] : sP1(X0,X0,X0,X0,X0,X0,X1,X2,k1_enumset1(X0,X1,X2)) ),
    inference(superposition,[],[f97,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f97,plain,(
    ! [X2,X0,X3,X1] : sP1(X0,X0,X0,X0,X0,X1,X2,X3,k2_enumset1(X0,X1,X2,X3)) ),
    inference(superposition,[],[f96,f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f96,plain,(
    ! [X4,X2,X0,X3,X1] : sP1(X0,X0,X0,X0,X1,X2,X3,X4,k3_enumset1(X0,X1,X2,X3,X4)) ),
    inference(superposition,[],[f95,f59])).

fof(f59,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f95,plain,(
    ! [X4,X2,X0,X5,X3,X1] : sP1(X0,X0,X0,X1,X2,X3,X4,X5,k4_enumset1(X0,X1,X2,X3,X4,X5)) ),
    inference(superposition,[],[f94,f60])).

fof(f60,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f94,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : sP1(X0,X0,X1,X2,X3,X4,X5,X6,k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) ),
    inference(superposition,[],[f85,f61])).

fof(f61,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f85,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
      | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) )
      & ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8 ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
    <=> sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ),
    inference(definition_folding,[],[f28,f30,f29])).

fof(f30,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
    <=> ! [X9] :
          ( r2_hidden(X9,X8)
        <=> sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f28,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
    <=> ! [X9] :
          ( r2_hidden(X9,X8)
        <=> ( X7 = X9
            | X6 = X9
            | X5 = X9
            | X4 = X9
            | X3 = X9
            | X2 = X9
            | X1 = X9
            | X0 = X9 ) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
    <=> ! [X9] :
          ( r2_hidden(X9,X8)
        <=> ~ ( X7 != X9
              & X6 != X9
              & X5 != X9
              & X4 != X9
              & X3 != X9
              & X2 != X9
              & X1 != X9
              & X0 != X9 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_enumset1)).

fof(f63,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1] :
      ( ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
      | ~ sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)
      | r2_hidden(X10,X8) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | ( ( ~ sP0(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0)
            | ~ r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) )
          & ( sP0(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0)
            | r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) ) ) )
      & ( ! [X10] :
            ( ( r2_hidden(X10,X8)
              | ~ sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) )
            & ( sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X10,X8) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f36,f37])).

fof(f37,plain,(
    ! [X8,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ? [X9] :
          ( ( ~ sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
            | ~ r2_hidden(X9,X8) )
          & ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
            | r2_hidden(X9,X8) ) )
     => ( ( ~ sP0(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0)
          | ~ r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) )
        & ( sP0(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0)
          | r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | ? [X9] :
            ( ( ~ sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X9,X8) )
            & ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
              | r2_hidden(X9,X8) ) ) )
      & ( ! [X10] :
            ( ( r2_hidden(X10,X8)
              | ~ sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) )
            & ( sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X10,X8) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ) ),
    inference(rectify,[],[f35])).

% (6578)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% (6558)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% (6558)Refutation not found, incomplete strategy% (6558)------------------------------
% (6558)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (6558)Termination reason: Refutation not found, incomplete strategy

% (6558)Memory used [KB]: 6268
% (6558)Time elapsed: 0.133 s
% (6558)------------------------------
% (6558)------------------------------
% (6555)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% (6562)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% (6554)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% (6582)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | ? [X9] :
            ( ( ~ sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X9,X8) )
            & ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
              | r2_hidden(X9,X8) ) ) )
      & ( ! [X9] :
            ( ( r2_hidden(X9,X8)
              | ~ sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) )
            & ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X9,X8) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f344,plain,
    ( ~ r2_hidden(sK3,k1_tarski(sK3))
    | ~ m1_subset_1(k1_tarski(sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(resolution,[],[f343,f197])).

fof(f197,plain,(
    r2_hidden(sK3,k2_orders_2(sK2,k1_tarski(sK3))) ),
    inference(backward_demodulation,[],[f49,f196])).

fof(f343,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3,k2_orders_2(sK2,X0))
      | ~ r2_hidden(sK3,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(resolution,[],[f312,f48])).

fof(f312,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k2_orders_2(sK2,X1)) ) ),
    inference(subsumption_resolution,[],[f311,f43])).

fof(f311,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ r2_hidden(X0,k2_orders_2(sK2,X1))
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f310,f44])).

fof(f310,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ r2_hidden(X0,k2_orders_2(sK2,X1))
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f309,f45])).

fof(f309,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ r2_hidden(X0,k2_orders_2(sK2,X1))
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f308,f46])).

fof(f308,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ r2_hidden(X0,k2_orders_2(sK2,X1))
      | ~ v5_orders_2(sK2)
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f51,f47])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ r2_hidden(X1,k2_orders_2(X0,X2))
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ r2_hidden(X1,k2_orders_2(X0,X2))
              | ~ r2_hidden(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ r2_hidden(X1,k2_orders_2(X0,X2))
              | ~ r2_hidden(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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
             => ~ ( r2_hidden(X1,k2_orders_2(X0,X2))
                  & r2_hidden(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_orders_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.33  % Computer   : n013.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 20:16:39 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.52  % (6561)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.53  % (6569)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.53  % (6577)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.54  % (6559)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.44/0.54  % (6561)Refutation found. Thanks to Tanya!
% 1.44/0.54  % SZS status Theorem for theBenchmark
% 1.44/0.54  % SZS output start Proof for theBenchmark
% 1.44/0.54  fof(f346,plain,(
% 1.44/0.54    $false),
% 1.44/0.54    inference(subsumption_resolution,[],[f345,f198])).
% 1.44/0.54  fof(f198,plain,(
% 1.44/0.54    m1_subset_1(k1_tarski(sK3),k1_zfmisc_1(u1_struct_0(sK2)))),
% 1.44/0.54    inference(backward_demodulation,[],[f91,f196])).
% 1.44/0.54  fof(f196,plain,(
% 1.44/0.54    k6_domain_1(u1_struct_0(sK2),sK3) = k1_tarski(sK3)),
% 1.44/0.54    inference(resolution,[],[f135,f49])).
% 1.44/0.54  fof(f49,plain,(
% 1.44/0.54    r2_hidden(sK3,k2_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK3)))),
% 1.44/0.54    inference(cnf_transformation,[],[f34])).
% 1.44/0.54  fof(f34,plain,(
% 1.44/0.54    (r2_hidden(sK3,k2_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK3))) & m1_subset_1(sK3,u1_struct_0(sK2))) & l1_orders_2(sK2) & v5_orders_2(sK2) & v4_orders_2(sK2) & v3_orders_2(sK2) & ~v2_struct_0(sK2)),
% 1.44/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f18,f33,f32])).
% 1.44/0.54  fof(f32,plain,(
% 1.44/0.54    ? [X0] : (? [X1] : (r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (r2_hidden(X1,k2_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),X1))) & m1_subset_1(X1,u1_struct_0(sK2))) & l1_orders_2(sK2) & v5_orders_2(sK2) & v4_orders_2(sK2) & v3_orders_2(sK2) & ~v2_struct_0(sK2))),
% 1.44/0.54    introduced(choice_axiom,[])).
% 1.44/0.54  fof(f33,plain,(
% 1.44/0.54    ? [X1] : (r2_hidden(X1,k2_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),X1))) & m1_subset_1(X1,u1_struct_0(sK2))) => (r2_hidden(sK3,k2_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK3))) & m1_subset_1(sK3,u1_struct_0(sK2)))),
% 1.44/0.54    introduced(choice_axiom,[])).
% 1.44/0.54  fof(f18,plain,(
% 1.44/0.54    ? [X0] : (? [X1] : (r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.44/0.54    inference(flattening,[],[f17])).
% 1.44/0.54  fof(f17,plain,(
% 1.44/0.54    ? [X0] : (? [X1] : (r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 1.44/0.54    inference(ennf_transformation,[],[f15])).
% 1.44/0.54  fof(f15,negated_conjecture,(
% 1.44/0.54    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ~r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))))),
% 1.44/0.54    inference(negated_conjecture,[],[f14])).
% 1.44/0.54  fof(f14,conjecture,(
% 1.44/0.54    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ~r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))))),
% 1.44/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_orders_2)).
% 1.44/0.54  fof(f135,plain,(
% 1.44/0.54    ( ! [X0] : (~r2_hidden(X0,k2_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK3))) | k6_domain_1(u1_struct_0(sK2),sK3) = k1_tarski(sK3)) )),
% 1.44/0.54    inference(resolution,[],[f133,f87])).
% 1.44/0.54  fof(f87,plain,(
% 1.44/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | k6_domain_1(u1_struct_0(sK2),sK3) = k1_tarski(sK3) | ~r2_hidden(X1,X0)) )),
% 1.44/0.54    inference(resolution,[],[f86,f57])).
% 1.44/0.54  fof(f57,plain,(
% 1.44/0.54    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.44/0.54    inference(cnf_transformation,[],[f27])).
% 1.44/0.54  fof(f27,plain,(
% 1.44/0.54    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.44/0.54    inference(ennf_transformation,[],[f9])).
% 1.44/0.54  fof(f9,axiom,(
% 1.44/0.54    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.44/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 1.44/0.54  fof(f86,plain,(
% 1.44/0.54    v1_xboole_0(u1_struct_0(sK2)) | k6_domain_1(u1_struct_0(sK2),sK3) = k1_tarski(sK3)),
% 1.44/0.54    inference(resolution,[],[f54,f48])).
% 1.44/0.54  fof(f48,plain,(
% 1.44/0.54    m1_subset_1(sK3,u1_struct_0(sK2))),
% 1.44/0.54    inference(cnf_transformation,[],[f34])).
% 1.44/0.54  fof(f54,plain,(
% 1.44/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k1_tarski(X1) | v1_xboole_0(X0)) )),
% 1.44/0.54    inference(cnf_transformation,[],[f24])).
% 1.44/0.54  fof(f24,plain,(
% 1.44/0.54    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.44/0.54    inference(flattening,[],[f23])).
% 1.44/0.54  fof(f23,plain,(
% 1.44/0.54    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.44/0.54    inference(ennf_transformation,[],[f11])).
% 1.44/0.54  fof(f11,axiom,(
% 1.44/0.54    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 1.44/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 1.44/0.54  fof(f133,plain,(
% 1.44/0.54    m1_subset_1(k2_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK3)),k1_zfmisc_1(u1_struct_0(sK2)))),
% 1.44/0.54    inference(resolution,[],[f123,f91])).
% 1.44/0.54  fof(f123,plain,(
% 1.44/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | m1_subset_1(k2_orders_2(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))) )),
% 1.44/0.54    inference(subsumption_resolution,[],[f122,f43])).
% 1.44/0.54  fof(f43,plain,(
% 1.44/0.54    ~v2_struct_0(sK2)),
% 1.44/0.54    inference(cnf_transformation,[],[f34])).
% 1.44/0.54  fof(f122,plain,(
% 1.44/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | m1_subset_1(k2_orders_2(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) | v2_struct_0(sK2)) )),
% 1.44/0.54    inference(subsumption_resolution,[],[f121,f44])).
% 1.44/0.54  fof(f44,plain,(
% 1.44/0.54    v3_orders_2(sK2)),
% 1.44/0.54    inference(cnf_transformation,[],[f34])).
% 1.44/0.54  fof(f121,plain,(
% 1.44/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | m1_subset_1(k2_orders_2(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) | ~v3_orders_2(sK2) | v2_struct_0(sK2)) )),
% 1.44/0.54    inference(subsumption_resolution,[],[f120,f45])).
% 1.44/0.54  fof(f45,plain,(
% 1.44/0.54    v4_orders_2(sK2)),
% 1.44/0.54    inference(cnf_transformation,[],[f34])).
% 1.44/0.54  fof(f120,plain,(
% 1.44/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | m1_subset_1(k2_orders_2(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | v2_struct_0(sK2)) )),
% 1.44/0.54    inference(subsumption_resolution,[],[f119,f46])).
% 1.44/0.54  fof(f46,plain,(
% 1.44/0.54    v5_orders_2(sK2)),
% 1.44/0.54    inference(cnf_transformation,[],[f34])).
% 1.44/0.54  fof(f119,plain,(
% 1.44/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | m1_subset_1(k2_orders_2(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) | ~v5_orders_2(sK2) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | v2_struct_0(sK2)) )),
% 1.44/0.54    inference(resolution,[],[f55,f47])).
% 1.44/0.54  fof(f47,plain,(
% 1.44/0.54    l1_orders_2(sK2)),
% 1.44/0.54    inference(cnf_transformation,[],[f34])).
% 1.44/0.54  fof(f55,plain,(
% 1.44/0.54    ( ! [X0,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.44/0.54    inference(cnf_transformation,[],[f26])).
% 1.44/0.54  fof(f26,plain,(
% 1.44/0.54    ! [X0,X1] : (m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.44/0.54    inference(flattening,[],[f25])).
% 1.44/0.54  fof(f25,plain,(
% 1.44/0.54    ! [X0,X1] : (m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.44/0.54    inference(ennf_transformation,[],[f10])).
% 1.44/0.54  fof(f10,axiom,(
% 1.44/0.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.44/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_orders_2)).
% 1.44/0.54  fof(f91,plain,(
% 1.44/0.54    m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2)))),
% 1.44/0.54    inference(resolution,[],[f90,f48])).
% 1.44/0.54  fof(f90,plain,(
% 1.44/0.54    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK2)) | m1_subset_1(k6_domain_1(u1_struct_0(sK2),X0),k1_zfmisc_1(u1_struct_0(sK2)))) )),
% 1.44/0.54    inference(subsumption_resolution,[],[f89,f43])).
% 1.44/0.54  fof(f89,plain,(
% 1.44/0.54    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK2)) | m1_subset_1(k6_domain_1(u1_struct_0(sK2),X0),k1_zfmisc_1(u1_struct_0(sK2))) | v2_struct_0(sK2)) )),
% 1.44/0.54    inference(subsumption_resolution,[],[f88,f44])).
% 1.44/0.54  fof(f88,plain,(
% 1.44/0.54    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK2)) | m1_subset_1(k6_domain_1(u1_struct_0(sK2),X0),k1_zfmisc_1(u1_struct_0(sK2))) | ~v3_orders_2(sK2) | v2_struct_0(sK2)) )),
% 1.44/0.54    inference(resolution,[],[f52,f47])).
% 1.44/0.54  fof(f52,plain,(
% 1.44/0.54    ( ! [X0,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.44/0.54    inference(cnf_transformation,[],[f22])).
% 1.44/0.54  fof(f22,plain,(
% 1.44/0.54    ! [X0] : (! [X1] : (m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.44/0.54    inference(flattening,[],[f21])).
% 1.44/0.54  fof(f21,plain,(
% 1.44/0.54    ! [X0] : (! [X1] : (m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.44/0.54    inference(ennf_transformation,[],[f16])).
% 1.44/0.54  fof(f16,plain,(
% 1.44/0.54    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.44/0.54    inference(pure_predicate_removal,[],[f12])).
% 1.44/0.54  fof(f12,axiom,(
% 1.44/0.54    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0))))),
% 1.44/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_orders_2)).
% 1.44/0.54  fof(f345,plain,(
% 1.44/0.54    ~m1_subset_1(k1_tarski(sK3),k1_zfmisc_1(u1_struct_0(sK2)))),
% 1.44/0.54    inference(subsumption_resolution,[],[f344,f300])).
% 1.44/0.54  fof(f300,plain,(
% 1.44/0.54    ( ! [X0] : (r2_hidden(X0,k1_tarski(X0))) )),
% 1.44/0.54    inference(resolution,[],[f299,f77])).
% 1.44/0.54  fof(f77,plain,(
% 1.44/0.54    ( ! [X6,X4,X2,X8,X7,X5,X3,X1] : (sP0(X1,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 1.44/0.54    inference(equality_resolution,[],[f74])).
% 1.44/0.54  fof(f74,plain,(
% 1.44/0.54    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) | X0 != X1) )),
% 1.44/0.54    inference(cnf_transformation,[],[f41])).
% 1.44/0.54  fof(f41,plain,(
% 1.44/0.54    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) | (X0 != X1 & X0 != X2 & X0 != X3 & X0 != X4 & X0 != X5 & X0 != X6 & X0 != X7 & X0 != X8)) & (X0 = X1 | X0 = X2 | X0 = X3 | X0 = X4 | X0 = X5 | X0 = X6 | X0 = X7 | X0 = X8 | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 1.44/0.54    inference(rectify,[],[f40])).
% 1.44/0.54  fof(f40,plain,(
% 1.44/0.54    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] : ((sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | (X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)) & (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9 | ~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 1.44/0.54    inference(flattening,[],[f39])).
% 1.44/0.54  fof(f39,plain,(
% 1.44/0.54    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] : ((sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | (X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)) & ((X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9) | ~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 1.44/0.54    inference(nnf_transformation,[],[f29])).
% 1.44/0.54  fof(f29,plain,(
% 1.44/0.54    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] : (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) <=> (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9))),
% 1.44/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.44/0.54  fof(f299,plain,(
% 1.44/0.54    ( ! [X43,X42] : (~sP0(X42,X43,X43,X43,X43,X43,X43,X43,X43) | r2_hidden(X42,k1_tarski(X43))) )),
% 1.44/0.54    inference(resolution,[],[f63,f100])).
% 1.44/0.54  fof(f100,plain,(
% 1.44/0.54    ( ! [X0] : (sP1(X0,X0,X0,X0,X0,X0,X0,X0,k1_tarski(X0))) )),
% 1.44/0.54    inference(superposition,[],[f99,f50])).
% 1.44/0.54  fof(f50,plain,(
% 1.44/0.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.44/0.54    inference(cnf_transformation,[],[f1])).
% 1.44/0.54  fof(f1,axiom,(
% 1.44/0.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.44/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.44/0.54  fof(f99,plain,(
% 1.44/0.54    ( ! [X0,X1] : (sP1(X0,X0,X0,X0,X0,X0,X0,X1,k2_tarski(X0,X1))) )),
% 1.44/0.54    inference(superposition,[],[f98,f53])).
% 1.44/0.54  fof(f53,plain,(
% 1.44/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.44/0.54    inference(cnf_transformation,[],[f2])).
% 1.44/0.54  fof(f2,axiom,(
% 1.44/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.44/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.44/0.54  fof(f98,plain,(
% 1.44/0.54    ( ! [X2,X0,X1] : (sP1(X0,X0,X0,X0,X0,X0,X1,X2,k1_enumset1(X0,X1,X2))) )),
% 1.44/0.54    inference(superposition,[],[f97,f56])).
% 1.44/0.54  fof(f56,plain,(
% 1.44/0.54    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.44/0.54    inference(cnf_transformation,[],[f3])).
% 1.44/0.54  fof(f3,axiom,(
% 1.44/0.54    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.44/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.44/0.54  fof(f97,plain,(
% 1.44/0.54    ( ! [X2,X0,X3,X1] : (sP1(X0,X0,X0,X0,X0,X1,X2,X3,k2_enumset1(X0,X1,X2,X3))) )),
% 1.44/0.54    inference(superposition,[],[f96,f58])).
% 1.44/0.54  fof(f58,plain,(
% 1.44/0.54    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.44/0.54    inference(cnf_transformation,[],[f4])).
% 1.44/0.54  fof(f4,axiom,(
% 1.44/0.54    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.44/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.44/0.54  fof(f96,plain,(
% 1.44/0.54    ( ! [X4,X2,X0,X3,X1] : (sP1(X0,X0,X0,X0,X1,X2,X3,X4,k3_enumset1(X0,X1,X2,X3,X4))) )),
% 1.44/0.54    inference(superposition,[],[f95,f59])).
% 1.44/0.54  fof(f59,plain,(
% 1.44/0.54    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.44/0.54    inference(cnf_transformation,[],[f5])).
% 1.44/0.54  fof(f5,axiom,(
% 1.44/0.54    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.44/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 1.44/0.54  fof(f95,plain,(
% 1.44/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (sP1(X0,X0,X0,X1,X2,X3,X4,X5,k4_enumset1(X0,X1,X2,X3,X4,X5))) )),
% 1.44/0.54    inference(superposition,[],[f94,f60])).
% 1.44/0.54  fof(f60,plain,(
% 1.44/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.44/0.54    inference(cnf_transformation,[],[f6])).
% 1.44/0.54  fof(f6,axiom,(
% 1.44/0.54    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.44/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 1.44/0.54  fof(f94,plain,(
% 1.44/0.54    ( ! [X6,X4,X2,X0,X5,X3,X1] : (sP1(X0,X0,X1,X2,X3,X4,X5,X6,k5_enumset1(X0,X1,X2,X3,X4,X5,X6))) )),
% 1.44/0.54    inference(superposition,[],[f85,f61])).
% 1.44/0.54  fof(f61,plain,(
% 1.44/0.54    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.44/0.54    inference(cnf_transformation,[],[f7])).
% 1.44/0.54  fof(f7,axiom,(
% 1.44/0.54    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.44/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 1.44/0.54  fof(f85,plain,(
% 1.44/0.54    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7))) )),
% 1.44/0.54    inference(equality_resolution,[],[f75])).
% 1.44/0.54  fof(f75,plain,(
% 1.44/0.54    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8) )),
% 1.44/0.54    inference(cnf_transformation,[],[f42])).
% 1.44/0.54  fof(f42,plain,(
% 1.44/0.54    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) & (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8))),
% 1.44/0.54    inference(nnf_transformation,[],[f31])).
% 1.44/0.54  fof(f31,plain,(
% 1.44/0.54    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8))),
% 1.44/0.54    inference(definition_folding,[],[f28,f30,f29])).
% 1.44/0.54  fof(f30,plain,(
% 1.44/0.54    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) <=> ! [X9] : (r2_hidden(X9,X8) <=> sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 1.44/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.44/0.54  fof(f28,plain,(
% 1.44/0.54    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> ! [X9] : (r2_hidden(X9,X8) <=> (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9)))),
% 1.44/0.54    inference(ennf_transformation,[],[f8])).
% 1.44/0.54  fof(f8,axiom,(
% 1.44/0.54    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> ! [X9] : (r2_hidden(X9,X8) <=> ~(X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)))),
% 1.44/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_enumset1)).
% 1.44/0.54  fof(f63,plain,(
% 1.44/0.54    ( ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1] : (~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | ~sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X10,X8)) )),
% 1.44/0.54    inference(cnf_transformation,[],[f38])).
% 1.44/0.54  fof(f38,plain,(
% 1.44/0.54    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | ((~sP0(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)) & (sP0(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)))) & (! [X10] : ((r2_hidden(X10,X8) | ~sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X10,X8))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 1.44/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f36,f37])).
% 1.44/0.54  fof(f37,plain,(
% 1.44/0.54    ! [X8,X7,X6,X5,X4,X3,X2,X1,X0] : (? [X9] : ((~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8)) & (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X9,X8))) => ((~sP0(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)) & (sP0(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8))))),
% 1.44/0.54    introduced(choice_axiom,[])).
% 1.44/0.54  fof(f36,plain,(
% 1.44/0.54    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | ? [X9] : ((~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8)) & (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X9,X8)))) & (! [X10] : ((r2_hidden(X10,X8) | ~sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X10,X8))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 1.44/0.54    inference(rectify,[],[f35])).
% 1.44/0.55  % (6578)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.44/0.55  % (6558)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.44/0.55  % (6558)Refutation not found, incomplete strategy% (6558)------------------------------
% 1.44/0.55  % (6558)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.55  % (6558)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.55  
% 1.44/0.55  % (6558)Memory used [KB]: 6268
% 1.44/0.55  % (6558)Time elapsed: 0.133 s
% 1.44/0.55  % (6558)------------------------------
% 1.44/0.55  % (6558)------------------------------
% 1.44/0.55  % (6555)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.44/0.55  % (6562)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.44/0.56  % (6554)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.44/0.56  % (6582)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.44/0.56  fof(f35,plain,(
% 1.44/0.56    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | ? [X9] : ((~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8)) & (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X9,X8)))) & (! [X9] : ((r2_hidden(X9,X8) | ~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 1.44/0.56    inference(nnf_transformation,[],[f30])).
% 1.44/0.56  fof(f344,plain,(
% 1.44/0.56    ~r2_hidden(sK3,k1_tarski(sK3)) | ~m1_subset_1(k1_tarski(sK3),k1_zfmisc_1(u1_struct_0(sK2)))),
% 1.44/0.56    inference(resolution,[],[f343,f197])).
% 1.44/0.56  fof(f197,plain,(
% 1.44/0.56    r2_hidden(sK3,k2_orders_2(sK2,k1_tarski(sK3)))),
% 1.44/0.56    inference(backward_demodulation,[],[f49,f196])).
% 1.44/0.56  fof(f343,plain,(
% 1.44/0.56    ( ! [X0] : (~r2_hidden(sK3,k2_orders_2(sK2,X0)) | ~r2_hidden(sK3,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))) )),
% 1.44/0.56    inference(resolution,[],[f312,f48])).
% 1.44/0.56  fof(f312,plain,(
% 1.44/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k2_orders_2(sK2,X1))) )),
% 1.44/0.56    inference(subsumption_resolution,[],[f311,f43])).
% 1.44/0.56  fof(f311,plain,(
% 1.44/0.56    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) | ~m1_subset_1(X0,u1_struct_0(sK2)) | ~r2_hidden(X0,k2_orders_2(sK2,X1)) | v2_struct_0(sK2)) )),
% 1.44/0.56    inference(subsumption_resolution,[],[f310,f44])).
% 1.44/0.56  fof(f310,plain,(
% 1.44/0.56    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) | ~m1_subset_1(X0,u1_struct_0(sK2)) | ~r2_hidden(X0,k2_orders_2(sK2,X1)) | ~v3_orders_2(sK2) | v2_struct_0(sK2)) )),
% 1.44/0.56    inference(subsumption_resolution,[],[f309,f45])).
% 1.44/0.56  fof(f309,plain,(
% 1.44/0.56    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) | ~m1_subset_1(X0,u1_struct_0(sK2)) | ~r2_hidden(X0,k2_orders_2(sK2,X1)) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | v2_struct_0(sK2)) )),
% 1.44/0.56    inference(subsumption_resolution,[],[f308,f46])).
% 1.44/0.56  fof(f308,plain,(
% 1.44/0.56    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) | ~m1_subset_1(X0,u1_struct_0(sK2)) | ~r2_hidden(X0,k2_orders_2(sK2,X1)) | ~v5_orders_2(sK2) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | v2_struct_0(sK2)) )),
% 1.44/0.56    inference(resolution,[],[f51,f47])).
% 1.44/0.56  fof(f51,plain,(
% 1.44/0.56    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r2_hidden(X1,k2_orders_2(X0,X2)) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f20])).
% 1.44/0.56  fof(f20,plain,(
% 1.44/0.56    ! [X0] : (! [X1] : (! [X2] : (~r2_hidden(X1,k2_orders_2(X0,X2)) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.44/0.56    inference(flattening,[],[f19])).
% 1.44/0.56  fof(f19,plain,(
% 1.44/0.56    ! [X0] : (! [X1] : (! [X2] : ((~r2_hidden(X1,k2_orders_2(X0,X2)) | ~r2_hidden(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.44/0.56    inference(ennf_transformation,[],[f13])).
% 1.44/0.56  fof(f13,axiom,(
% 1.44/0.56    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(r2_hidden(X1,k2_orders_2(X0,X2)) & r2_hidden(X1,X2)))))),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_orders_2)).
% 1.44/0.56  % SZS output end Proof for theBenchmark
% 1.44/0.56  % (6561)------------------------------
% 1.44/0.56  % (6561)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.56  % (6561)Termination reason: Refutation
% 1.44/0.56  
% 1.44/0.56  % (6561)Memory used [KB]: 6524
% 1.44/0.56  % (6561)Time elapsed: 0.126 s
% 1.44/0.56  % (6561)------------------------------
% 1.44/0.56  % (6561)------------------------------
% 1.44/0.56  % (6553)Success in time 0.208 s
%------------------------------------------------------------------------------
