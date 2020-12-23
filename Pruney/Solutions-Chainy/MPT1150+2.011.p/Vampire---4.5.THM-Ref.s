%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:44 EST 2020

% Result     : Theorem 1.58s
% Output     : Refutation 1.58s
% Verified   : 
% Statistics : Number of formulae       :  123 (1866 expanded)
%              Number of leaves         :   16 ( 468 expanded)
%              Depth                    :   30
%              Number of atoms          :  485 (9081 expanded)
%              Number of equality atoms :   53 (1219 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f331,plain,(
    $false ),
    inference(subsumption_resolution,[],[f328,f49])).

fof(f49,plain,(
    k1_xboole_0 != k1_orders_2(sK2,k2_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( k1_xboole_0 != k1_orders_2(sK2,k2_struct_0(sK2))
    & l1_orders_2(sK2)
    & v5_orders_2(sK2)
    & v4_orders_2(sK2)
    & v3_orders_2(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f13,f28])).

fof(f28,plain,
    ( ? [X0] :
        ( k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( k1_xboole_0 != k1_orders_2(sK2,k2_struct_0(sK2))
      & l1_orders_2(sK2)
      & v5_orders_2(sK2)
      & v4_orders_2(sK2)
      & v3_orders_2(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_orders_2)).

fof(f328,plain,(
    k1_xboole_0 = k1_orders_2(sK2,k2_struct_0(sK2)) ),
    inference(resolution,[],[f327,f55])).

fof(f55,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f327,plain,(
    r1_tarski(k1_orders_2(sK2,k2_struct_0(sK2)),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f326,f246])).

fof(f246,plain,
    ( m1_subset_1(sK3(k1_orders_2(sK2,k2_struct_0(sK2)),k1_xboole_0),k2_struct_0(sK2))
    | r1_tarski(k1_orders_2(sK2,k2_struct_0(sK2)),k1_xboole_0) ),
    inference(superposition,[],[f124,f245])).

fof(f245,plain,(
    sK3(k1_orders_2(sK2,k2_struct_0(sK2)),k1_xboole_0) = sK5(sK2,k2_struct_0(sK2),sK3(k1_orders_2(sK2,k2_struct_0(sK2)),k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f242,f49])).

fof(f242,plain,
    ( sK3(k1_orders_2(sK2,k2_struct_0(sK2)),k1_xboole_0) = sK5(sK2,k2_struct_0(sK2),sK3(k1_orders_2(sK2,k2_struct_0(sK2)),k1_xboole_0))
    | k1_xboole_0 = k1_orders_2(sK2,k2_struct_0(sK2)) ),
    inference(resolution,[],[f122,f55])).

fof(f122,plain,(
    ! [X4] :
      ( r1_tarski(k1_orders_2(sK2,k2_struct_0(sK2)),X4)
      | sK3(k1_orders_2(sK2,k2_struct_0(sK2)),X4) = sK5(sK2,k2_struct_0(sK2),sK3(k1_orders_2(sK2,k2_struct_0(sK2)),X4)) ) ),
    inference(forward_demodulation,[],[f116,f112])).

fof(f112,plain,(
    k1_orders_2(sK2,k2_struct_0(sK2)) = a_2_0_orders_2(sK2,k2_struct_0(sK2)) ),
    inference(resolution,[],[f111,f82])).

fof(f82,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(resolution,[],[f80,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f80,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f79])).

fof(f79,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f60,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f33,f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f111,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2)))
      | k1_orders_2(sK2,X0) = a_2_0_orders_2(sK2,X0) ) ),
    inference(forward_demodulation,[],[f110,f78])).

fof(f78,plain,(
    k2_struct_0(sK2) = u1_struct_0(sK2) ),
    inference(resolution,[],[f50,f77])).

fof(f77,plain,(
    l1_struct_0(sK2) ),
    inference(resolution,[],[f51,f48])).

fof(f48,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f51,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f50,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f110,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | k1_orders_2(sK2,X0) = a_2_0_orders_2(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f109,f44])).

fof(f44,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f109,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | k1_orders_2(sK2,X0) = a_2_0_orders_2(sK2,X0)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f108,f45])).

fof(f45,plain,(
    v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f108,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | k1_orders_2(sK2,X0) = a_2_0_orders_2(sK2,X0)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f107,f46])).

fof(f46,plain,(
    v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f107,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | k1_orders_2(sK2,X0) = a_2_0_orders_2(sK2,X0)
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f106,f48])).

fof(f106,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_orders_2(sK2)
      | k1_orders_2(sK2,X0) = a_2_0_orders_2(sK2,X0)
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f56,f47])).

fof(f47,plain,(
    v5_orders_2(sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_orders_2)).

fof(f116,plain,(
    ! [X4] :
      ( r1_tarski(k1_orders_2(sK2,k2_struct_0(sK2)),X4)
      | sK3(a_2_0_orders_2(sK2,k2_struct_0(sK2)),X4) = sK5(sK2,k2_struct_0(sK2),sK3(a_2_0_orders_2(sK2,k2_struct_0(sK2)),X4)) ) ),
    inference(backward_demodulation,[],[f101,f112])).

fof(f101,plain,(
    ! [X4] :
      ( r1_tarski(a_2_0_orders_2(sK2,k2_struct_0(sK2)),X4)
      | sK3(a_2_0_orders_2(sK2,k2_struct_0(sK2)),X4) = sK5(sK2,k2_struct_0(sK2),sK3(a_2_0_orders_2(sK2,k2_struct_0(sK2)),X4)) ) ),
    inference(resolution,[],[f97,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | sK5(X0,X1,X2) = X2 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3] :
            ( ( ~ r2_orders_2(X0,sK4(X0,X1,X3),X3)
              & r2_hidden(sK4(X0,X1,X3),X1)
              & m1_subset_1(sK4(X0,X1,X3),u1_struct_0(X0)) )
            | X2 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ( ! [X6] :
              ( r2_orders_2(X0,X6,sK5(X0,X1,X2))
              | ~ r2_hidden(X6,X1)
              | ~ m1_subset_1(X6,u1_struct_0(X0)) )
          & sK5(X0,X1,X2) = X2
          & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f40,f42,f41])).

fof(f41,plain,(
    ! [X3,X1,X0] :
      ( ? [X4] :
          ( ~ r2_orders_2(X0,X4,X3)
          & r2_hidden(X4,X1)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r2_orders_2(X0,sK4(X0,X1,X3),X3)
        & r2_hidden(sK4(X0,X1,X3),X1)
        & m1_subset_1(sK4(X0,X1,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r2_orders_2(X0,X6,X5)
              | ~ r2_hidden(X6,X1)
              | ~ m1_subset_1(X6,u1_struct_0(X0)) )
          & X2 = X5
          & m1_subset_1(X5,u1_struct_0(X0)) )
     => ( ! [X6] :
            ( r2_orders_2(X0,X6,sK5(X0,X1,X2))
            | ~ r2_hidden(X6,X1)
            | ~ m1_subset_1(X6,u1_struct_0(X0)) )
        & sK5(X0,X1,X2) = X2
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3] :
            ( ? [X4] :
                ( ~ r2_orders_2(X0,X4,X3)
                & r2_hidden(X4,X1)
                & m1_subset_1(X4,u1_struct_0(X0)) )
            | X2 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ? [X5] :
            ( ! [X6] :
                ( r2_orders_2(X0,X6,X5)
                | ~ r2_hidden(X6,X1)
                | ~ m1_subset_1(X6,u1_struct_0(X0)) )
            & X2 = X5
            & m1_subset_1(X5,u1_struct_0(X0)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X1,X2,X0] :
      ( ( sP0(X1,X2,X0)
        | ! [X3] :
            ( ? [X4] :
                ( ~ r2_orders_2(X1,X4,X3)
                & r2_hidden(X4,X2)
                & m1_subset_1(X4,u1_struct_0(X1)) )
            | X0 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ? [X3] :
            ( ! [X4] :
                ( r2_orders_2(X1,X4,X3)
                | ~ r2_hidden(X4,X2)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) )
        | ~ sP0(X1,X2,X0) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X1,X2,X0] :
      ( sP0(X1,X2,X0)
    <=> ? [X3] :
          ( ! [X4] :
              ( r2_orders_2(X1,X4,X3)
              | ~ r2_hidden(X4,X2)
              | ~ m1_subset_1(X4,u1_struct_0(X1)) )
          & X0 = X3
          & m1_subset_1(X3,u1_struct_0(X1)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f97,plain,(
    ! [X0] :
      ( sP0(sK2,k2_struct_0(sK2),sK3(a_2_0_orders_2(sK2,k2_struct_0(sK2)),X0))
      | r1_tarski(a_2_0_orders_2(sK2,k2_struct_0(sK2)),X0) ) ),
    inference(resolution,[],[f96,f59])).

fof(f96,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,a_2_0_orders_2(sK2,k2_struct_0(sK2)))
      | sP0(sK2,k2_struct_0(sK2),X1) ) ),
    inference(resolution,[],[f94,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ r2_hidden(X0,a_2_0_orders_2(X2,X1))
      | sP0(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_orders_2(X2,X1))
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | ~ r2_hidden(X0,a_2_0_orders_2(X2,X1)) ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X0,X2,X1] :
      ( ( ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
          | ~ sP0(X1,X2,X0) )
        & ( sP0(X1,X2,X0)
          | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2)) ) )
      | ~ sP1(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X2,X1] :
      ( ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
      <=> sP0(X1,X2,X0) )
      | ~ sP1(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f94,plain,(
    ! [X0] : sP1(X0,k2_struct_0(sK2),sK2) ),
    inference(resolution,[],[f93,f82])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2)))
      | sP1(X1,X0,sK2) ) ),
    inference(forward_demodulation,[],[f92,f78])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | sP1(X1,X0,sK2) ) ),
    inference(subsumption_resolution,[],[f91,f44])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | sP1(X1,X0,sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f90,f45])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | sP1(X1,X0,sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f89,f46])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | sP1(X1,X0,sK2)
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f88,f48])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_orders_2(sK2)
      | sP1(X1,X0,sK2)
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f71,f47])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | sP1(X0,X2,X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( sP1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(definition_folding,[],[f24,f26,f25])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( r2_orders_2(X1,X4,X3)
                | ~ r2_hidden(X4,X2)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( r2_orders_2(X1,X4,X3)
                | ~ r2_hidden(X4,X2)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & l1_orders_2(X1)
        & v5_orders_2(X1)
        & v4_orders_2(X1)
        & v3_orders_2(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r2_hidden(X4,X2)
                 => r2_orders_2(X1,X4,X3) ) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_0_orders_2)).

fof(f124,plain,(
    ! [X3] :
      ( m1_subset_1(sK5(sK2,k2_struct_0(sK2),sK3(k1_orders_2(sK2,k2_struct_0(sK2)),X3)),k2_struct_0(sK2))
      | r1_tarski(k1_orders_2(sK2,k2_struct_0(sK2)),X3) ) ),
    inference(forward_demodulation,[],[f118,f112])).

fof(f118,plain,(
    ! [X3] :
      ( r1_tarski(k1_orders_2(sK2,k2_struct_0(sK2)),X3)
      | m1_subset_1(sK5(sK2,k2_struct_0(sK2),sK3(a_2_0_orders_2(sK2,k2_struct_0(sK2)),X3)),k2_struct_0(sK2)) ) ),
    inference(backward_demodulation,[],[f103,f112])).

fof(f103,plain,(
    ! [X3] :
      ( m1_subset_1(sK5(sK2,k2_struct_0(sK2),sK3(a_2_0_orders_2(sK2,k2_struct_0(sK2)),X3)),k2_struct_0(sK2))
      | r1_tarski(a_2_0_orders_2(sK2,k2_struct_0(sK2)),X3) ) ),
    inference(forward_demodulation,[],[f100,f78])).

fof(f100,plain,(
    ! [X3] :
      ( r1_tarski(a_2_0_orders_2(sK2,k2_struct_0(sK2)),X3)
      | m1_subset_1(sK5(sK2,k2_struct_0(sK2),sK3(a_2_0_orders_2(sK2,k2_struct_0(sK2)),X3)),u1_struct_0(sK2)) ) ),
    inference(resolution,[],[f97,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f326,plain,
    ( ~ m1_subset_1(sK3(k1_orders_2(sK2,k2_struct_0(sK2)),k1_xboole_0),k2_struct_0(sK2))
    | r1_tarski(k1_orders_2(sK2,k2_struct_0(sK2)),k1_xboole_0) ),
    inference(forward_demodulation,[],[f325,f78])).

fof(f325,plain,
    ( r1_tarski(k1_orders_2(sK2,k2_struct_0(sK2)),k1_xboole_0)
    | ~ m1_subset_1(sK3(k1_orders_2(sK2,k2_struct_0(sK2)),k1_xboole_0),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f324,f48])).

fof(f324,plain,
    ( r1_tarski(k1_orders_2(sK2,k2_struct_0(sK2)),k1_xboole_0)
    | ~ m1_subset_1(sK3(k1_orders_2(sK2,k2_struct_0(sK2)),k1_xboole_0),u1_struct_0(sK2))
    | ~ l1_orders_2(sK2) ),
    inference(resolution,[],[f323,f76])).

fof(f76,plain,(
    ! [X2,X0] :
      ( ~ r2_orders_2(X0,X2,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f72])).

fof(f72,plain,(
    ! [X2,X0] :
      ( ~ r2_orders_2(X0,X2,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( X1 != X2
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_orders_2(X0,X1,X2)
                  | X1 = X2
                  | ~ r1_orders_2(X0,X1,X2) )
                & ( ( X1 != X2
                    & r1_orders_2(X0,X1,X2) )
                  | ~ r2_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_orders_2(X0,X1,X2)
                  | X1 = X2
                  | ~ r1_orders_2(X0,X1,X2) )
                & ( ( X1 != X2
                    & r1_orders_2(X0,X1,X2) )
                  | ~ r2_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_orders_2)).

fof(f323,plain,
    ( r2_orders_2(sK2,sK3(k1_orders_2(sK2,k2_struct_0(sK2)),k1_xboole_0),sK3(k1_orders_2(sK2,k2_struct_0(sK2)),k1_xboole_0))
    | r1_tarski(k1_orders_2(sK2,k2_struct_0(sK2)),k1_xboole_0) ),
    inference(duplicate_literal_removal,[],[f322])).

fof(f322,plain,
    ( r2_orders_2(sK2,sK3(k1_orders_2(sK2,k2_struct_0(sK2)),k1_xboole_0),sK3(k1_orders_2(sK2,k2_struct_0(sK2)),k1_xboole_0))
    | r1_tarski(k1_orders_2(sK2,k2_struct_0(sK2)),k1_xboole_0)
    | r1_tarski(k1_orders_2(sK2,k2_struct_0(sK2)),k1_xboole_0) ),
    inference(superposition,[],[f251,f245])).

fof(f251,plain,(
    ! [X2] :
      ( r2_orders_2(sK2,sK3(k1_orders_2(sK2,k2_struct_0(sK2)),k1_xboole_0),sK5(sK2,k2_struct_0(sK2),sK3(k1_orders_2(sK2,k2_struct_0(sK2)),X2)))
      | r1_tarski(k1_orders_2(sK2,k2_struct_0(sK2)),X2)
      | r1_tarski(k1_orders_2(sK2,k2_struct_0(sK2)),k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f250,f152])).

fof(f152,plain,(
    ! [X0] :
      ( r2_hidden(sK3(k1_orders_2(sK2,k2_struct_0(sK2)),X0),k2_struct_0(sK2))
      | r1_tarski(k1_orders_2(sK2,k2_struct_0(sK2)),X0) ) ),
    inference(resolution,[],[f147,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X2)
      | r2_hidden(sK3(X0,X1),X2)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f58,f59])).

fof(f58,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f147,plain,(
    r1_tarski(k1_orders_2(sK2,k2_struct_0(sK2)),k2_struct_0(sK2)) ),
    inference(resolution,[],[f143,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f143,plain,(
    m1_subset_1(k1_orders_2(sK2,k2_struct_0(sK2)),k1_zfmisc_1(k2_struct_0(sK2))) ),
    inference(resolution,[],[f142,f82])).

fof(f142,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2)))
      | m1_subset_1(k1_orders_2(sK2,X0),k1_zfmisc_1(k2_struct_0(sK2))) ) ),
    inference(forward_demodulation,[],[f141,f78])).

fof(f141,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2)))
      | m1_subset_1(k1_orders_2(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(forward_demodulation,[],[f140,f78])).

fof(f140,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | m1_subset_1(k1_orders_2(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(subsumption_resolution,[],[f139,f44])).

fof(f139,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | m1_subset_1(k1_orders_2(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f138,f45])).

fof(f138,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | m1_subset_1(k1_orders_2(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f137,f46])).

fof(f137,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | m1_subset_1(k1_orders_2(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f136,f48])).

fof(f136,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_orders_2(sK2)
      | m1_subset_1(k1_orders_2(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f57,f47])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_orders_2)).

fof(f250,plain,(
    ! [X2] :
      ( r1_tarski(k1_orders_2(sK2,k2_struct_0(sK2)),X2)
      | r2_orders_2(sK2,sK3(k1_orders_2(sK2,k2_struct_0(sK2)),k1_xboole_0),sK5(sK2,k2_struct_0(sK2),sK3(k1_orders_2(sK2,k2_struct_0(sK2)),X2)))
      | ~ r2_hidden(sK3(k1_orders_2(sK2,k2_struct_0(sK2)),k1_xboole_0),k2_struct_0(sK2))
      | r1_tarski(k1_orders_2(sK2,k2_struct_0(sK2)),k1_xboole_0) ) ),
    inference(resolution,[],[f123,f246])).

fof(f123,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k2_struct_0(sK2))
      | r1_tarski(k1_orders_2(sK2,k2_struct_0(sK2)),X1)
      | r2_orders_2(sK2,X2,sK5(sK2,k2_struct_0(sK2),sK3(k1_orders_2(sK2,k2_struct_0(sK2)),X1)))
      | ~ r2_hidden(X2,k2_struct_0(sK2)) ) ),
    inference(forward_demodulation,[],[f117,f112])).

fof(f117,plain,(
    ! [X2,X1] :
      ( r1_tarski(k1_orders_2(sK2,k2_struct_0(sK2)),X1)
      | ~ m1_subset_1(X2,k2_struct_0(sK2))
      | ~ r2_hidden(X2,k2_struct_0(sK2))
      | r2_orders_2(sK2,X2,sK5(sK2,k2_struct_0(sK2),sK3(a_2_0_orders_2(sK2,k2_struct_0(sK2)),X1))) ) ),
    inference(backward_demodulation,[],[f102,f112])).

fof(f102,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k2_struct_0(sK2))
      | r1_tarski(a_2_0_orders_2(sK2,k2_struct_0(sK2)),X1)
      | ~ r2_hidden(X2,k2_struct_0(sK2))
      | r2_orders_2(sK2,X2,sK5(sK2,k2_struct_0(sK2),sK3(a_2_0_orders_2(sK2,k2_struct_0(sK2)),X1))) ) ),
    inference(forward_demodulation,[],[f99,f78])).

fof(f99,plain,(
    ! [X2,X1] :
      ( r1_tarski(a_2_0_orders_2(sK2,k2_struct_0(sK2)),X1)
      | ~ r2_hidden(X2,k2_struct_0(sK2))
      | ~ m1_subset_1(X2,u1_struct_0(sK2))
      | r2_orders_2(sK2,X2,sK5(sK2,k2_struct_0(sK2),sK3(a_2_0_orders_2(sK2,k2_struct_0(sK2)),X1))) ) ),
    inference(resolution,[],[f97,f67])).

fof(f67,plain,(
    ! [X6,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X6,X1)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | r2_orders_2(X0,X6,sK5(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f43])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:53:56 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.50  % (14690)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.51  % (14687)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.51  % (14667)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (14682)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.51  % (14676)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.51  % (14676)Refutation not found, incomplete strategy% (14676)------------------------------
% 0.20/0.51  % (14676)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (14676)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (14676)Memory used [KB]: 10618
% 0.20/0.51  % (14676)Time elapsed: 0.102 s
% 0.20/0.51  % (14676)------------------------------
% 0.20/0.51  % (14676)------------------------------
% 0.20/0.51  % (14675)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.51  % (14679)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.52  % (14665)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  % (14682)Refutation not found, incomplete strategy% (14682)------------------------------
% 0.20/0.52  % (14682)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (14682)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (14682)Memory used [KB]: 10618
% 0.20/0.52  % (14682)Time elapsed: 0.114 s
% 0.20/0.52  % (14682)------------------------------
% 0.20/0.52  % (14682)------------------------------
% 0.20/0.52  % (14666)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.52  % (14674)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.52  % (14669)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.52  % (14680)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.52  % (14689)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.52  % (14669)Refutation not found, incomplete strategy% (14669)------------------------------
% 0.20/0.52  % (14669)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (14669)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (14669)Memory used [KB]: 6268
% 0.20/0.52  % (14669)Time elapsed: 0.127 s
% 0.20/0.52  % (14669)------------------------------
% 0.20/0.52  % (14669)------------------------------
% 0.20/0.53  % (14670)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.53  % (14671)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.53  % (14691)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.53  % (14665)Refutation not found, incomplete strategy% (14665)------------------------------
% 0.20/0.53  % (14665)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (14665)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (14665)Memory used [KB]: 1663
% 0.20/0.53  % (14665)Time elapsed: 0.123 s
% 0.20/0.53  % (14665)------------------------------
% 0.20/0.53  % (14665)------------------------------
% 0.20/0.53  % (14668)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (14692)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.53  % (14683)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.53  % (14685)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.54  % (14672)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.54  % (14675)Refutation not found, incomplete strategy% (14675)------------------------------
% 0.20/0.54  % (14675)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (14675)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (14675)Memory used [KB]: 10618
% 0.20/0.54  % (14675)Time elapsed: 0.134 s
% 0.20/0.54  % (14675)------------------------------
% 0.20/0.54  % (14675)------------------------------
% 1.45/0.54  % (14687)Refutation not found, incomplete strategy% (14687)------------------------------
% 1.45/0.54  % (14687)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.54  % (14687)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.54  
% 1.45/0.54  % (14687)Memory used [KB]: 10746
% 1.45/0.54  % (14687)Time elapsed: 0.090 s
% 1.45/0.54  % (14687)------------------------------
% 1.45/0.54  % (14687)------------------------------
% 1.45/0.54  % (14694)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.45/0.54  % (14684)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.45/0.54  % (14673)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.45/0.54  % (14681)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.45/0.54  % (14677)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.45/0.54  % (14686)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.45/0.54  % (14678)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.45/0.55  % (14686)Refutation not found, incomplete strategy% (14686)------------------------------
% 1.45/0.55  % (14686)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.55  % (14686)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.55  
% 1.45/0.55  % (14686)Memory used [KB]: 1663
% 1.45/0.55  % (14686)Time elapsed: 0.150 s
% 1.45/0.55  % (14686)------------------------------
% 1.45/0.55  % (14686)------------------------------
% 1.45/0.55  % (14674)Refutation not found, incomplete strategy% (14674)------------------------------
% 1.45/0.55  % (14674)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.55  % (14674)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.55  
% 1.45/0.55  % (14674)Memory used [KB]: 10746
% 1.45/0.55  % (14674)Time elapsed: 0.150 s
% 1.45/0.55  % (14674)------------------------------
% 1.45/0.55  % (14674)------------------------------
% 1.45/0.55  % (14688)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.45/0.55  % (14691)Refutation not found, incomplete strategy% (14691)------------------------------
% 1.45/0.55  % (14691)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.55  % (14691)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.55  
% 1.45/0.55  % (14691)Memory used [KB]: 10746
% 1.45/0.55  % (14691)Time elapsed: 0.132 s
% 1.45/0.55  % (14691)------------------------------
% 1.45/0.55  % (14691)------------------------------
% 1.45/0.55  % (14693)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.58/0.56  % (14685)Refutation not found, incomplete strategy% (14685)------------------------------
% 1.58/0.56  % (14685)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.56  % (14685)Termination reason: Refutation not found, incomplete strategy
% 1.58/0.56  
% 1.58/0.56  % (14685)Memory used [KB]: 10746
% 1.58/0.56  % (14685)Time elapsed: 0.158 s
% 1.58/0.56  % (14685)------------------------------
% 1.58/0.56  % (14685)------------------------------
% 1.58/0.56  % (14672)Refutation found. Thanks to Tanya!
% 1.58/0.56  % SZS status Theorem for theBenchmark
% 1.58/0.56  % SZS output start Proof for theBenchmark
% 1.58/0.56  fof(f331,plain,(
% 1.58/0.56    $false),
% 1.58/0.56    inference(subsumption_resolution,[],[f328,f49])).
% 1.58/0.56  fof(f49,plain,(
% 1.58/0.56    k1_xboole_0 != k1_orders_2(sK2,k2_struct_0(sK2))),
% 1.58/0.56    inference(cnf_transformation,[],[f29])).
% 1.58/0.56  fof(f29,plain,(
% 1.58/0.56    k1_xboole_0 != k1_orders_2(sK2,k2_struct_0(sK2)) & l1_orders_2(sK2) & v5_orders_2(sK2) & v4_orders_2(sK2) & v3_orders_2(sK2) & ~v2_struct_0(sK2)),
% 1.58/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f13,f28])).
% 1.58/0.56  fof(f28,plain,(
% 1.58/0.56    ? [X0] : (k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (k1_xboole_0 != k1_orders_2(sK2,k2_struct_0(sK2)) & l1_orders_2(sK2) & v5_orders_2(sK2) & v4_orders_2(sK2) & v3_orders_2(sK2) & ~v2_struct_0(sK2))),
% 1.58/0.56    introduced(choice_axiom,[])).
% 1.58/0.56  fof(f13,plain,(
% 1.58/0.56    ? [X0] : (k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.58/0.56    inference(flattening,[],[f12])).
% 1.58/0.56  fof(f12,plain,(
% 1.58/0.56    ? [X0] : (k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0)) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 1.58/0.56    inference(ennf_transformation,[],[f11])).
% 1.58/0.56  fof(f11,negated_conjecture,(
% 1.58/0.56    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)))),
% 1.58/0.56    inference(negated_conjecture,[],[f10])).
% 1.58/0.56  fof(f10,conjecture,(
% 1.58/0.56    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)))),
% 1.58/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_orders_2)).
% 1.58/0.56  fof(f328,plain,(
% 1.58/0.56    k1_xboole_0 = k1_orders_2(sK2,k2_struct_0(sK2))),
% 1.58/0.56    inference(resolution,[],[f327,f55])).
% 1.58/0.56  fof(f55,plain,(
% 1.58/0.56    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.58/0.56    inference(cnf_transformation,[],[f17])).
% 1.58/0.56  fof(f17,plain,(
% 1.58/0.56    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 1.58/0.56    inference(ennf_transformation,[],[f2])).
% 1.58/0.56  fof(f2,axiom,(
% 1.58/0.56    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 1.58/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 1.58/0.56  fof(f327,plain,(
% 1.58/0.56    r1_tarski(k1_orders_2(sK2,k2_struct_0(sK2)),k1_xboole_0)),
% 1.58/0.56    inference(subsumption_resolution,[],[f326,f246])).
% 1.58/0.56  fof(f246,plain,(
% 1.58/0.56    m1_subset_1(sK3(k1_orders_2(sK2,k2_struct_0(sK2)),k1_xboole_0),k2_struct_0(sK2)) | r1_tarski(k1_orders_2(sK2,k2_struct_0(sK2)),k1_xboole_0)),
% 1.58/0.56    inference(superposition,[],[f124,f245])).
% 1.58/0.56  fof(f245,plain,(
% 1.58/0.56    sK3(k1_orders_2(sK2,k2_struct_0(sK2)),k1_xboole_0) = sK5(sK2,k2_struct_0(sK2),sK3(k1_orders_2(sK2,k2_struct_0(sK2)),k1_xboole_0))),
% 1.58/0.56    inference(subsumption_resolution,[],[f242,f49])).
% 1.58/0.56  fof(f242,plain,(
% 1.58/0.56    sK3(k1_orders_2(sK2,k2_struct_0(sK2)),k1_xboole_0) = sK5(sK2,k2_struct_0(sK2),sK3(k1_orders_2(sK2,k2_struct_0(sK2)),k1_xboole_0)) | k1_xboole_0 = k1_orders_2(sK2,k2_struct_0(sK2))),
% 1.58/0.56    inference(resolution,[],[f122,f55])).
% 1.58/0.56  fof(f122,plain,(
% 1.58/0.56    ( ! [X4] : (r1_tarski(k1_orders_2(sK2,k2_struct_0(sK2)),X4) | sK3(k1_orders_2(sK2,k2_struct_0(sK2)),X4) = sK5(sK2,k2_struct_0(sK2),sK3(k1_orders_2(sK2,k2_struct_0(sK2)),X4))) )),
% 1.58/0.56    inference(forward_demodulation,[],[f116,f112])).
% 1.58/0.56  fof(f112,plain,(
% 1.58/0.56    k1_orders_2(sK2,k2_struct_0(sK2)) = a_2_0_orders_2(sK2,k2_struct_0(sK2))),
% 1.58/0.56    inference(resolution,[],[f111,f82])).
% 1.58/0.56  fof(f82,plain,(
% 1.58/0.56    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 1.58/0.56    inference(resolution,[],[f80,f62])).
% 1.58/0.56  fof(f62,plain,(
% 1.58/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.58/0.56    inference(cnf_transformation,[],[f36])).
% 1.58/0.56  fof(f36,plain,(
% 1.58/0.56    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.58/0.56    inference(nnf_transformation,[],[f3])).
% 1.58/0.57  fof(f3,axiom,(
% 1.58/0.57    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.58/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.58/0.57  fof(f80,plain,(
% 1.58/0.57    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 1.58/0.57    inference(duplicate_literal_removal,[],[f79])).
% 1.58/0.57  fof(f79,plain,(
% 1.58/0.57    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 1.58/0.57    inference(resolution,[],[f60,f59])).
% 1.58/0.57  fof(f59,plain,(
% 1.58/0.57    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.58/0.57    inference(cnf_transformation,[],[f35])).
% 1.58/0.57  fof(f35,plain,(
% 1.58/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.58/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f33,f34])).
% 1.58/0.57  fof(f34,plain,(
% 1.58/0.57    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 1.58/0.57    introduced(choice_axiom,[])).
% 1.58/0.57  fof(f33,plain,(
% 1.58/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.58/0.57    inference(rectify,[],[f32])).
% 1.58/0.57  fof(f32,plain,(
% 1.58/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.58/0.57    inference(nnf_transformation,[],[f22])).
% 1.58/0.57  fof(f22,plain,(
% 1.58/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.58/0.57    inference(ennf_transformation,[],[f1])).
% 1.58/0.57  fof(f1,axiom,(
% 1.58/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.58/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.58/0.57  fof(f60,plain,(
% 1.58/0.57    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.58/0.57    inference(cnf_transformation,[],[f35])).
% 1.58/0.57  fof(f111,plain,(
% 1.58/0.57    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) | k1_orders_2(sK2,X0) = a_2_0_orders_2(sK2,X0)) )),
% 1.58/0.57    inference(forward_demodulation,[],[f110,f78])).
% 1.58/0.57  fof(f78,plain,(
% 1.58/0.57    k2_struct_0(sK2) = u1_struct_0(sK2)),
% 1.58/0.57    inference(resolution,[],[f50,f77])).
% 1.58/0.57  fof(f77,plain,(
% 1.58/0.57    l1_struct_0(sK2)),
% 1.58/0.57    inference(resolution,[],[f51,f48])).
% 1.58/0.57  fof(f48,plain,(
% 1.58/0.57    l1_orders_2(sK2)),
% 1.58/0.57    inference(cnf_transformation,[],[f29])).
% 1.58/0.57  fof(f51,plain,(
% 1.58/0.57    ( ! [X0] : (~l1_orders_2(X0) | l1_struct_0(X0)) )),
% 1.58/0.57    inference(cnf_transformation,[],[f15])).
% 1.58/0.57  fof(f15,plain,(
% 1.58/0.57    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 1.58/0.57    inference(ennf_transformation,[],[f8])).
% 1.58/0.57  fof(f8,axiom,(
% 1.58/0.57    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 1.58/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 1.58/0.57  fof(f50,plain,(
% 1.58/0.57    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 1.58/0.57    inference(cnf_transformation,[],[f14])).
% 1.58/0.57  fof(f14,plain,(
% 1.58/0.57    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.58/0.57    inference(ennf_transformation,[],[f4])).
% 1.58/0.57  fof(f4,axiom,(
% 1.58/0.57    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.58/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 1.58/0.57  fof(f110,plain,(
% 1.58/0.57    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | k1_orders_2(sK2,X0) = a_2_0_orders_2(sK2,X0)) )),
% 1.58/0.57    inference(subsumption_resolution,[],[f109,f44])).
% 1.58/0.57  fof(f44,plain,(
% 1.58/0.57    ~v2_struct_0(sK2)),
% 1.58/0.57    inference(cnf_transformation,[],[f29])).
% 1.58/0.57  fof(f109,plain,(
% 1.58/0.57    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | k1_orders_2(sK2,X0) = a_2_0_orders_2(sK2,X0) | v2_struct_0(sK2)) )),
% 1.58/0.57    inference(subsumption_resolution,[],[f108,f45])).
% 1.58/0.57  fof(f45,plain,(
% 1.58/0.57    v3_orders_2(sK2)),
% 1.58/0.57    inference(cnf_transformation,[],[f29])).
% 1.58/0.57  fof(f108,plain,(
% 1.58/0.57    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | k1_orders_2(sK2,X0) = a_2_0_orders_2(sK2,X0) | ~v3_orders_2(sK2) | v2_struct_0(sK2)) )),
% 1.58/0.57    inference(subsumption_resolution,[],[f107,f46])).
% 1.58/0.57  fof(f46,plain,(
% 1.58/0.57    v4_orders_2(sK2)),
% 1.58/0.57    inference(cnf_transformation,[],[f29])).
% 1.58/0.57  fof(f107,plain,(
% 1.58/0.57    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | k1_orders_2(sK2,X0) = a_2_0_orders_2(sK2,X0) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | v2_struct_0(sK2)) )),
% 1.58/0.57    inference(subsumption_resolution,[],[f106,f48])).
% 1.58/0.57  fof(f106,plain,(
% 1.58/0.57    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_orders_2(sK2) | k1_orders_2(sK2,X0) = a_2_0_orders_2(sK2,X0) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | v2_struct_0(sK2)) )),
% 1.58/0.57    inference(resolution,[],[f56,f47])).
% 1.58/0.57  fof(f47,plain,(
% 1.58/0.57    v5_orders_2(sK2)),
% 1.58/0.57    inference(cnf_transformation,[],[f29])).
% 1.58/0.57  fof(f56,plain,(
% 1.58/0.57    ( ! [X0,X1] : (~v5_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.58/0.57    inference(cnf_transformation,[],[f19])).
% 1.58/0.57  fof(f19,plain,(
% 1.58/0.57    ! [X0] : (! [X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.58/0.57    inference(flattening,[],[f18])).
% 1.58/0.57  fof(f18,plain,(
% 1.58/0.57    ! [X0] : (! [X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.58/0.57    inference(ennf_transformation,[],[f6])).
% 1.58/0.57  fof(f6,axiom,(
% 1.58/0.57    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)))),
% 1.58/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_orders_2)).
% 1.58/0.57  fof(f116,plain,(
% 1.58/0.57    ( ! [X4] : (r1_tarski(k1_orders_2(sK2,k2_struct_0(sK2)),X4) | sK3(a_2_0_orders_2(sK2,k2_struct_0(sK2)),X4) = sK5(sK2,k2_struct_0(sK2),sK3(a_2_0_orders_2(sK2,k2_struct_0(sK2)),X4))) )),
% 1.58/0.57    inference(backward_demodulation,[],[f101,f112])).
% 1.58/0.57  fof(f101,plain,(
% 1.58/0.57    ( ! [X4] : (r1_tarski(a_2_0_orders_2(sK2,k2_struct_0(sK2)),X4) | sK3(a_2_0_orders_2(sK2,k2_struct_0(sK2)),X4) = sK5(sK2,k2_struct_0(sK2),sK3(a_2_0_orders_2(sK2,k2_struct_0(sK2)),X4))) )),
% 1.58/0.57    inference(resolution,[],[f97,f66])).
% 1.58/0.57  fof(f66,plain,(
% 1.58/0.57    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | sK5(X0,X1,X2) = X2) )),
% 1.58/0.57    inference(cnf_transformation,[],[f43])).
% 1.58/0.57  fof(f43,plain,(
% 1.58/0.57    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3] : ((~r2_orders_2(X0,sK4(X0,X1,X3),X3) & r2_hidden(sK4(X0,X1,X3),X1) & m1_subset_1(sK4(X0,X1,X3),u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)))) & ((! [X6] : (r2_orders_2(X0,X6,sK5(X0,X1,X2)) | ~r2_hidden(X6,X1) | ~m1_subset_1(X6,u1_struct_0(X0))) & sK5(X0,X1,X2) = X2 & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))) | ~sP0(X0,X1,X2)))),
% 1.58/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f40,f42,f41])).
% 1.58/0.57  fof(f41,plain,(
% 1.58/0.57    ! [X3,X1,X0] : (? [X4] : (~r2_orders_2(X0,X4,X3) & r2_hidden(X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) => (~r2_orders_2(X0,sK4(X0,X1,X3),X3) & r2_hidden(sK4(X0,X1,X3),X1) & m1_subset_1(sK4(X0,X1,X3),u1_struct_0(X0))))),
% 1.58/0.57    introduced(choice_axiom,[])).
% 1.58/0.57  fof(f42,plain,(
% 1.58/0.57    ! [X2,X1,X0] : (? [X5] : (! [X6] : (r2_orders_2(X0,X6,X5) | ~r2_hidden(X6,X1) | ~m1_subset_1(X6,u1_struct_0(X0))) & X2 = X5 & m1_subset_1(X5,u1_struct_0(X0))) => (! [X6] : (r2_orders_2(X0,X6,sK5(X0,X1,X2)) | ~r2_hidden(X6,X1) | ~m1_subset_1(X6,u1_struct_0(X0))) & sK5(X0,X1,X2) = X2 & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))))),
% 1.58/0.57    introduced(choice_axiom,[])).
% 1.58/0.57  fof(f40,plain,(
% 1.58/0.57    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3] : (? [X4] : (~r2_orders_2(X0,X4,X3) & r2_hidden(X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)))) & (? [X5] : (! [X6] : (r2_orders_2(X0,X6,X5) | ~r2_hidden(X6,X1) | ~m1_subset_1(X6,u1_struct_0(X0))) & X2 = X5 & m1_subset_1(X5,u1_struct_0(X0))) | ~sP0(X0,X1,X2)))),
% 1.58/0.57    inference(rectify,[],[f39])).
% 1.58/0.57  fof(f39,plain,(
% 1.58/0.57    ! [X1,X2,X0] : ((sP0(X1,X2,X0) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X4,X3) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (! [X4] : (r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~sP0(X1,X2,X0)))),
% 1.58/0.57    inference(nnf_transformation,[],[f25])).
% 1.58/0.57  fof(f25,plain,(
% 1.58/0.57    ! [X1,X2,X0] : (sP0(X1,X2,X0) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))))),
% 1.58/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.58/0.57  fof(f97,plain,(
% 1.58/0.57    ( ! [X0] : (sP0(sK2,k2_struct_0(sK2),sK3(a_2_0_orders_2(sK2,k2_struct_0(sK2)),X0)) | r1_tarski(a_2_0_orders_2(sK2,k2_struct_0(sK2)),X0)) )),
% 1.58/0.57    inference(resolution,[],[f96,f59])).
% 1.58/0.57  fof(f96,plain,(
% 1.58/0.57    ( ! [X1] : (~r2_hidden(X1,a_2_0_orders_2(sK2,k2_struct_0(sK2))) | sP0(sK2,k2_struct_0(sK2),X1)) )),
% 1.58/0.57    inference(resolution,[],[f94,f63])).
% 1.58/0.57  fof(f63,plain,(
% 1.58/0.57    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | ~r2_hidden(X0,a_2_0_orders_2(X2,X1)) | sP0(X2,X1,X0)) )),
% 1.58/0.57    inference(cnf_transformation,[],[f38])).
% 1.58/0.57  fof(f38,plain,(
% 1.58/0.57    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_0_orders_2(X2,X1)) | ~sP0(X2,X1,X0)) & (sP0(X2,X1,X0) | ~r2_hidden(X0,a_2_0_orders_2(X2,X1)))) | ~sP1(X0,X1,X2))),
% 1.58/0.57    inference(rectify,[],[f37])).
% 1.58/0.57  fof(f37,plain,(
% 1.58/0.57    ! [X0,X2,X1] : (((r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ~sP0(X1,X2,X0)) & (sP0(X1,X2,X0) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)))) | ~sP1(X0,X2,X1))),
% 1.58/0.57    inference(nnf_transformation,[],[f26])).
% 1.58/0.57  fof(f26,plain,(
% 1.58/0.57    ! [X0,X2,X1] : ((r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> sP0(X1,X2,X0)) | ~sP1(X0,X2,X1))),
% 1.58/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.58/0.57  fof(f94,plain,(
% 1.58/0.57    ( ! [X0] : (sP1(X0,k2_struct_0(sK2),sK2)) )),
% 1.58/0.57    inference(resolution,[],[f93,f82])).
% 1.58/0.57  fof(f93,plain,(
% 1.58/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) | sP1(X1,X0,sK2)) )),
% 1.58/0.57    inference(forward_demodulation,[],[f92,f78])).
% 1.58/0.57  fof(f92,plain,(
% 1.58/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | sP1(X1,X0,sK2)) )),
% 1.58/0.57    inference(subsumption_resolution,[],[f91,f44])).
% 1.58/0.57  fof(f91,plain,(
% 1.58/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | sP1(X1,X0,sK2) | v2_struct_0(sK2)) )),
% 1.58/0.57    inference(subsumption_resolution,[],[f90,f45])).
% 1.58/0.57  fof(f90,plain,(
% 1.58/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | sP1(X1,X0,sK2) | ~v3_orders_2(sK2) | v2_struct_0(sK2)) )),
% 1.58/0.57    inference(subsumption_resolution,[],[f89,f46])).
% 1.58/0.57  fof(f89,plain,(
% 1.58/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | sP1(X1,X0,sK2) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | v2_struct_0(sK2)) )),
% 1.58/0.57    inference(subsumption_resolution,[],[f88,f48])).
% 1.58/0.57  fof(f88,plain,(
% 1.58/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_orders_2(sK2) | sP1(X1,X0,sK2) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | v2_struct_0(sK2)) )),
% 1.58/0.57    inference(resolution,[],[f71,f47])).
% 1.58/0.57  fof(f71,plain,(
% 1.58/0.57    ( ! [X2,X0,X1] : (~v5_orders_2(X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | sP1(X0,X2,X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 1.58/0.57    inference(cnf_transformation,[],[f27])).
% 1.58/0.57  fof(f27,plain,(
% 1.58/0.57    ! [X0,X1,X2] : (sP1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 1.58/0.57    inference(definition_folding,[],[f24,f26,f25])).
% 1.58/0.57  fof(f24,plain,(
% 1.58/0.57    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 1.58/0.57    inference(flattening,[],[f23])).
% 1.58/0.57  fof(f23,plain,(
% 1.58/0.57    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : ((r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)))),
% 1.58/0.57    inference(ennf_transformation,[],[f9])).
% 1.58/0.57  fof(f9,axiom,(
% 1.58/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) & l1_orders_2(X1) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r2_hidden(X4,X2) => r2_orders_2(X1,X4,X3))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 1.58/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_0_orders_2)).
% 1.58/0.57  fof(f124,plain,(
% 1.58/0.57    ( ! [X3] : (m1_subset_1(sK5(sK2,k2_struct_0(sK2),sK3(k1_orders_2(sK2,k2_struct_0(sK2)),X3)),k2_struct_0(sK2)) | r1_tarski(k1_orders_2(sK2,k2_struct_0(sK2)),X3)) )),
% 1.58/0.57    inference(forward_demodulation,[],[f118,f112])).
% 1.58/0.57  fof(f118,plain,(
% 1.58/0.57    ( ! [X3] : (r1_tarski(k1_orders_2(sK2,k2_struct_0(sK2)),X3) | m1_subset_1(sK5(sK2,k2_struct_0(sK2),sK3(a_2_0_orders_2(sK2,k2_struct_0(sK2)),X3)),k2_struct_0(sK2))) )),
% 1.58/0.57    inference(backward_demodulation,[],[f103,f112])).
% 1.58/0.57  fof(f103,plain,(
% 1.58/0.57    ( ! [X3] : (m1_subset_1(sK5(sK2,k2_struct_0(sK2),sK3(a_2_0_orders_2(sK2,k2_struct_0(sK2)),X3)),k2_struct_0(sK2)) | r1_tarski(a_2_0_orders_2(sK2,k2_struct_0(sK2)),X3)) )),
% 1.58/0.57    inference(forward_demodulation,[],[f100,f78])).
% 1.58/0.57  fof(f100,plain,(
% 1.58/0.57    ( ! [X3] : (r1_tarski(a_2_0_orders_2(sK2,k2_struct_0(sK2)),X3) | m1_subset_1(sK5(sK2,k2_struct_0(sK2),sK3(a_2_0_orders_2(sK2,k2_struct_0(sK2)),X3)),u1_struct_0(sK2))) )),
% 1.58/0.57    inference(resolution,[],[f97,f65])).
% 1.58/0.57  fof(f65,plain,(
% 1.58/0.57    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))) )),
% 1.58/0.57    inference(cnf_transformation,[],[f43])).
% 1.58/0.57  fof(f326,plain,(
% 1.58/0.57    ~m1_subset_1(sK3(k1_orders_2(sK2,k2_struct_0(sK2)),k1_xboole_0),k2_struct_0(sK2)) | r1_tarski(k1_orders_2(sK2,k2_struct_0(sK2)),k1_xboole_0)),
% 1.58/0.57    inference(forward_demodulation,[],[f325,f78])).
% 1.58/0.57  fof(f325,plain,(
% 1.58/0.57    r1_tarski(k1_orders_2(sK2,k2_struct_0(sK2)),k1_xboole_0) | ~m1_subset_1(sK3(k1_orders_2(sK2,k2_struct_0(sK2)),k1_xboole_0),u1_struct_0(sK2))),
% 1.58/0.57    inference(subsumption_resolution,[],[f324,f48])).
% 1.58/0.57  fof(f324,plain,(
% 1.58/0.57    r1_tarski(k1_orders_2(sK2,k2_struct_0(sK2)),k1_xboole_0) | ~m1_subset_1(sK3(k1_orders_2(sK2,k2_struct_0(sK2)),k1_xboole_0),u1_struct_0(sK2)) | ~l1_orders_2(sK2)),
% 1.58/0.57    inference(resolution,[],[f323,f76])).
% 1.58/0.57  fof(f76,plain,(
% 1.58/0.57    ( ! [X2,X0] : (~r2_orders_2(X0,X2,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.58/0.57    inference(duplicate_literal_removal,[],[f72])).
% 1.58/0.57  fof(f72,plain,(
% 1.58/0.57    ( ! [X2,X0] : (~r2_orders_2(X0,X2,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.58/0.57    inference(equality_resolution,[],[f53])).
% 1.58/0.57  fof(f53,plain,(
% 1.58/0.57    ( ! [X2,X0,X1] : (X1 != X2 | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.58/0.57    inference(cnf_transformation,[],[f31])).
% 1.58/0.57  fof(f31,plain,(
% 1.58/0.57    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | X1 = X2 | ~r1_orders_2(X0,X1,X2)) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.58/0.57    inference(flattening,[],[f30])).
% 1.58/0.57  fof(f30,plain,(
% 1.58/0.57    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | (X1 = X2 | ~r1_orders_2(X0,X1,X2))) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.58/0.57    inference(nnf_transformation,[],[f16])).
% 1.58/0.57  fof(f16,plain,(
% 1.58/0.57    ! [X0] : (! [X1] : (! [X2] : ((r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.58/0.57    inference(ennf_transformation,[],[f5])).
% 1.58/0.57  fof(f5,axiom,(
% 1.58/0.57    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))))))),
% 1.58/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_orders_2)).
% 1.58/0.57  fof(f323,plain,(
% 1.58/0.57    r2_orders_2(sK2,sK3(k1_orders_2(sK2,k2_struct_0(sK2)),k1_xboole_0),sK3(k1_orders_2(sK2,k2_struct_0(sK2)),k1_xboole_0)) | r1_tarski(k1_orders_2(sK2,k2_struct_0(sK2)),k1_xboole_0)),
% 1.58/0.57    inference(duplicate_literal_removal,[],[f322])).
% 1.58/0.57  fof(f322,plain,(
% 1.58/0.57    r2_orders_2(sK2,sK3(k1_orders_2(sK2,k2_struct_0(sK2)),k1_xboole_0),sK3(k1_orders_2(sK2,k2_struct_0(sK2)),k1_xboole_0)) | r1_tarski(k1_orders_2(sK2,k2_struct_0(sK2)),k1_xboole_0) | r1_tarski(k1_orders_2(sK2,k2_struct_0(sK2)),k1_xboole_0)),
% 1.58/0.57    inference(superposition,[],[f251,f245])).
% 1.58/0.57  fof(f251,plain,(
% 1.58/0.57    ( ! [X2] : (r2_orders_2(sK2,sK3(k1_orders_2(sK2,k2_struct_0(sK2)),k1_xboole_0),sK5(sK2,k2_struct_0(sK2),sK3(k1_orders_2(sK2,k2_struct_0(sK2)),X2))) | r1_tarski(k1_orders_2(sK2,k2_struct_0(sK2)),X2) | r1_tarski(k1_orders_2(sK2,k2_struct_0(sK2)),k1_xboole_0)) )),
% 1.58/0.57    inference(subsumption_resolution,[],[f250,f152])).
% 1.58/0.57  fof(f152,plain,(
% 1.58/0.57    ( ! [X0] : (r2_hidden(sK3(k1_orders_2(sK2,k2_struct_0(sK2)),X0),k2_struct_0(sK2)) | r1_tarski(k1_orders_2(sK2,k2_struct_0(sK2)),X0)) )),
% 1.58/0.57    inference(resolution,[],[f147,f84])).
% 1.58/0.57  fof(f84,plain,(
% 1.58/0.57    ( ! [X2,X0,X1] : (~r1_tarski(X0,X2) | r2_hidden(sK3(X0,X1),X2) | r1_tarski(X0,X1)) )),
% 1.58/0.57    inference(resolution,[],[f58,f59])).
% 1.58/0.57  fof(f58,plain,(
% 1.58/0.57    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 1.58/0.57    inference(cnf_transformation,[],[f35])).
% 1.58/0.57  fof(f147,plain,(
% 1.58/0.57    r1_tarski(k1_orders_2(sK2,k2_struct_0(sK2)),k2_struct_0(sK2))),
% 1.58/0.57    inference(resolution,[],[f143,f61])).
% 1.58/0.57  fof(f61,plain,(
% 1.58/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.58/0.57    inference(cnf_transformation,[],[f36])).
% 1.58/0.57  fof(f143,plain,(
% 1.58/0.57    m1_subset_1(k1_orders_2(sK2,k2_struct_0(sK2)),k1_zfmisc_1(k2_struct_0(sK2)))),
% 1.58/0.57    inference(resolution,[],[f142,f82])).
% 1.58/0.57  fof(f142,plain,(
% 1.58/0.57    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) | m1_subset_1(k1_orders_2(sK2,X0),k1_zfmisc_1(k2_struct_0(sK2)))) )),
% 1.58/0.57    inference(forward_demodulation,[],[f141,f78])).
% 1.58/0.57  fof(f141,plain,(
% 1.58/0.57    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) | m1_subset_1(k1_orders_2(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))) )),
% 1.58/0.57    inference(forward_demodulation,[],[f140,f78])).
% 1.58/0.57  fof(f140,plain,(
% 1.58/0.57    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | m1_subset_1(k1_orders_2(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))) )),
% 1.58/0.57    inference(subsumption_resolution,[],[f139,f44])).
% 1.58/0.57  fof(f139,plain,(
% 1.58/0.57    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | m1_subset_1(k1_orders_2(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) | v2_struct_0(sK2)) )),
% 1.58/0.57    inference(subsumption_resolution,[],[f138,f45])).
% 1.58/0.57  fof(f138,plain,(
% 1.58/0.57    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | m1_subset_1(k1_orders_2(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) | ~v3_orders_2(sK2) | v2_struct_0(sK2)) )),
% 1.58/0.57    inference(subsumption_resolution,[],[f137,f46])).
% 1.58/0.57  fof(f137,plain,(
% 1.58/0.57    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | m1_subset_1(k1_orders_2(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | v2_struct_0(sK2)) )),
% 1.58/0.57    inference(subsumption_resolution,[],[f136,f48])).
% 1.58/0.57  fof(f136,plain,(
% 1.58/0.57    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_orders_2(sK2) | m1_subset_1(k1_orders_2(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | v2_struct_0(sK2)) )),
% 1.58/0.57    inference(resolution,[],[f57,f47])).
% 1.58/0.57  fof(f57,plain,(
% 1.58/0.57    ( ! [X0,X1] : (~v5_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.58/0.57    inference(cnf_transformation,[],[f21])).
% 1.58/0.57  fof(f21,plain,(
% 1.58/0.57    ! [X0,X1] : (m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.58/0.57    inference(flattening,[],[f20])).
% 1.58/0.57  fof(f20,plain,(
% 1.58/0.57    ! [X0,X1] : (m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.58/0.57    inference(ennf_transformation,[],[f7])).
% 1.58/0.57  fof(f7,axiom,(
% 1.58/0.57    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.58/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_orders_2)).
% 1.58/0.57  fof(f250,plain,(
% 1.58/0.57    ( ! [X2] : (r1_tarski(k1_orders_2(sK2,k2_struct_0(sK2)),X2) | r2_orders_2(sK2,sK3(k1_orders_2(sK2,k2_struct_0(sK2)),k1_xboole_0),sK5(sK2,k2_struct_0(sK2),sK3(k1_orders_2(sK2,k2_struct_0(sK2)),X2))) | ~r2_hidden(sK3(k1_orders_2(sK2,k2_struct_0(sK2)),k1_xboole_0),k2_struct_0(sK2)) | r1_tarski(k1_orders_2(sK2,k2_struct_0(sK2)),k1_xboole_0)) )),
% 1.58/0.57    inference(resolution,[],[f123,f246])).
% 1.58/0.57  fof(f123,plain,(
% 1.58/0.57    ( ! [X2,X1] : (~m1_subset_1(X2,k2_struct_0(sK2)) | r1_tarski(k1_orders_2(sK2,k2_struct_0(sK2)),X1) | r2_orders_2(sK2,X2,sK5(sK2,k2_struct_0(sK2),sK3(k1_orders_2(sK2,k2_struct_0(sK2)),X1))) | ~r2_hidden(X2,k2_struct_0(sK2))) )),
% 1.58/0.57    inference(forward_demodulation,[],[f117,f112])).
% 1.58/0.57  fof(f117,plain,(
% 1.58/0.57    ( ! [X2,X1] : (r1_tarski(k1_orders_2(sK2,k2_struct_0(sK2)),X1) | ~m1_subset_1(X2,k2_struct_0(sK2)) | ~r2_hidden(X2,k2_struct_0(sK2)) | r2_orders_2(sK2,X2,sK5(sK2,k2_struct_0(sK2),sK3(a_2_0_orders_2(sK2,k2_struct_0(sK2)),X1)))) )),
% 1.58/0.57    inference(backward_demodulation,[],[f102,f112])).
% 1.58/0.57  fof(f102,plain,(
% 1.58/0.57    ( ! [X2,X1] : (~m1_subset_1(X2,k2_struct_0(sK2)) | r1_tarski(a_2_0_orders_2(sK2,k2_struct_0(sK2)),X1) | ~r2_hidden(X2,k2_struct_0(sK2)) | r2_orders_2(sK2,X2,sK5(sK2,k2_struct_0(sK2),sK3(a_2_0_orders_2(sK2,k2_struct_0(sK2)),X1)))) )),
% 1.58/0.57    inference(forward_demodulation,[],[f99,f78])).
% 1.58/0.57  fof(f99,plain,(
% 1.58/0.57    ( ! [X2,X1] : (r1_tarski(a_2_0_orders_2(sK2,k2_struct_0(sK2)),X1) | ~r2_hidden(X2,k2_struct_0(sK2)) | ~m1_subset_1(X2,u1_struct_0(sK2)) | r2_orders_2(sK2,X2,sK5(sK2,k2_struct_0(sK2),sK3(a_2_0_orders_2(sK2,k2_struct_0(sK2)),X1)))) )),
% 1.58/0.57    inference(resolution,[],[f97,f67])).
% 1.58/0.57  fof(f67,plain,(
% 1.58/0.57    ( ! [X6,X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X6,X1) | ~m1_subset_1(X6,u1_struct_0(X0)) | r2_orders_2(X0,X6,sK5(X0,X1,X2))) )),
% 1.58/0.57    inference(cnf_transformation,[],[f43])).
% 1.58/0.57  % SZS output end Proof for theBenchmark
% 1.58/0.57  % (14672)------------------------------
% 1.58/0.57  % (14672)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.57  % (14672)Termination reason: Refutation
% 1.58/0.57  
% 1.58/0.57  % (14672)Memory used [KB]: 6652
% 1.58/0.57  % (14672)Time elapsed: 0.171 s
% 1.58/0.57  % (14672)------------------------------
% 1.58/0.57  % (14672)------------------------------
% 1.58/0.59  % (14664)Success in time 0.23 s
%------------------------------------------------------------------------------
