%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:45 EST 2020

% Result     : Theorem 1.49s
% Output     : Refutation 1.49s
% Verified   : 
% Statistics : Number of formulae       :  130 (2285 expanded)
%              Number of leaves         :   17 ( 576 expanded)
%              Depth                    :   26
%              Number of atoms          :  491 (11111 expanded)
%              Number of equality atoms :   62 (1547 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f236,plain,(
    $false ),
    inference(subsumption_resolution,[],[f235,f143])).

fof(f143,plain,(
    m1_subset_1(sK3(k1_orders_2(sK2,k2_struct_0(sK2))),k2_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f142,f137])).

fof(f137,plain,(
    sK3(k1_orders_2(sK2,k2_struct_0(sK2))) = sK6(sK2,k2_struct_0(sK2),sK3(k1_orders_2(sK2,k2_struct_0(sK2)))) ),
    inference(forward_demodulation,[],[f136,f119])).

fof(f119,plain,(
    k1_orders_2(sK2,k2_struct_0(sK2)) = a_2_0_orders_2(sK2,k2_struct_0(sK2)) ),
    inference(resolution,[],[f118,f83])).

fof(f83,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(resolution,[],[f82,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f82,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f81])).

fof(f81,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f62,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f35,f36])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f118,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2)))
      | k1_orders_2(sK2,X0) = a_2_0_orders_2(sK2,X0) ) ),
    inference(forward_demodulation,[],[f117,f80])).

fof(f80,plain,(
    k2_struct_0(sK2) = u1_struct_0(sK2) ),
    inference(resolution,[],[f52,f79])).

fof(f79,plain,(
    l1_struct_0(sK2) ),
    inference(resolution,[],[f53,f50])).

fof(f50,plain,(
    l1_orders_2(sK2) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_orders_2)).

fof(f53,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f52,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f117,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | k1_orders_2(sK2,X0) = a_2_0_orders_2(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f116,f46])).

fof(f46,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f116,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | k1_orders_2(sK2,X0) = a_2_0_orders_2(sK2,X0)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f115,f47])).

fof(f47,plain,(
    v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f115,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | k1_orders_2(sK2,X0) = a_2_0_orders_2(sK2,X0)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f114,f48])).

fof(f48,plain,(
    v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f114,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | k1_orders_2(sK2,X0) = a_2_0_orders_2(sK2,X0)
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f113,f50])).

fof(f113,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_orders_2(sK2)
      | k1_orders_2(sK2,X0) = a_2_0_orders_2(sK2,X0)
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f57,f49])).

fof(f49,plain,(
    v5_orders_2(sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_orders_2)).

fof(f136,plain,(
    sK3(a_2_0_orders_2(sK2,k2_struct_0(sK2))) = sK6(sK2,k2_struct_0(sK2),sK3(a_2_0_orders_2(sK2,k2_struct_0(sK2)))) ),
    inference(subsumption_resolution,[],[f125,f51])).

fof(f51,plain,(
    k1_xboole_0 != k1_orders_2(sK2,k2_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f29])).

fof(f125,plain,
    ( k1_xboole_0 = k1_orders_2(sK2,k2_struct_0(sK2))
    | sK3(a_2_0_orders_2(sK2,k2_struct_0(sK2))) = sK6(sK2,k2_struct_0(sK2),sK3(a_2_0_orders_2(sK2,k2_struct_0(sK2)))) ),
    inference(backward_demodulation,[],[f102,f119])).

fof(f102,plain,
    ( sK3(a_2_0_orders_2(sK2,k2_struct_0(sK2))) = sK6(sK2,k2_struct_0(sK2),sK3(a_2_0_orders_2(sK2,k2_struct_0(sK2))))
    | k1_xboole_0 = a_2_0_orders_2(sK2,k2_struct_0(sK2)) ),
    inference(resolution,[],[f96,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | sK6(X0,X1,X2) = X2 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3] :
            ( ( ~ r2_orders_2(X0,sK5(X0,X1,X3),X3)
              & r2_hidden(sK5(X0,X1,X3),X1)
              & m1_subset_1(sK5(X0,X1,X3),u1_struct_0(X0)) )
            | X2 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ( ! [X6] :
              ( r2_orders_2(X0,X6,sK6(X0,X1,X2))
              | ~ r2_hidden(X6,X1)
              | ~ m1_subset_1(X6,u1_struct_0(X0)) )
          & sK6(X0,X1,X2) = X2
          & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f42,f44,f43])).

fof(f43,plain,(
    ! [X3,X1,X0] :
      ( ? [X4] :
          ( ~ r2_orders_2(X0,X4,X3)
          & r2_hidden(X4,X1)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r2_orders_2(X0,sK5(X0,X1,X3),X3)
        & r2_hidden(sK5(X0,X1,X3),X1)
        & m1_subset_1(sK5(X0,X1,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r2_orders_2(X0,X6,X5)
              | ~ r2_hidden(X6,X1)
              | ~ m1_subset_1(X6,u1_struct_0(X0)) )
          & X2 = X5
          & m1_subset_1(X5,u1_struct_0(X0)) )
     => ( ! [X6] :
            ( r2_orders_2(X0,X6,sK6(X0,X1,X2))
            | ~ r2_hidden(X6,X1)
            | ~ m1_subset_1(X6,u1_struct_0(X0)) )
        & sK6(X0,X1,X2) = X2
        & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
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
    inference(rectify,[],[f41])).

fof(f41,plain,(
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

fof(f96,plain,
    ( sP0(sK2,k2_struct_0(sK2),sK3(a_2_0_orders_2(sK2,k2_struct_0(sK2))))
    | k1_xboole_0 = a_2_0_orders_2(sK2,k2_struct_0(sK2)) ),
    inference(resolution,[],[f95,f58])).

fof(f58,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f32])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f95,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,a_2_0_orders_2(sK2,k2_struct_0(sK2)))
      | sP0(sK2,k2_struct_0(sK2),X1) ) ),
    inference(resolution,[],[f93,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ r2_hidden(X0,a_2_0_orders_2(X2,X1))
      | sP0(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_orders_2(X2,X1))
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | ~ r2_hidden(X0,a_2_0_orders_2(X2,X1)) ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
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

fof(f93,plain,(
    ! [X0] : sP1(X0,k2_struct_0(sK2),sK2) ),
    inference(resolution,[],[f92,f83])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2)))
      | sP1(X1,X0,sK2) ) ),
    inference(forward_demodulation,[],[f91,f80])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | sP1(X1,X0,sK2) ) ),
    inference(subsumption_resolution,[],[f90,f46])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | sP1(X1,X0,sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f89,f47])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | sP1(X1,X0,sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f88,f48])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | sP1(X1,X0,sK2)
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f87,f50])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_orders_2(sK2)
      | sP1(X1,X0,sK2)
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f73,f49])).

fof(f73,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_0_orders_2)).

fof(f142,plain,(
    m1_subset_1(sK6(sK2,k2_struct_0(sK2),sK3(k1_orders_2(sK2,k2_struct_0(sK2)))),k2_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f141,f119])).

fof(f141,plain,(
    m1_subset_1(sK6(sK2,k2_struct_0(sK2),sK3(a_2_0_orders_2(sK2,k2_struct_0(sK2)))),k2_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f127,f51])).

fof(f127,plain,
    ( k1_xboole_0 = k1_orders_2(sK2,k2_struct_0(sK2))
    | m1_subset_1(sK6(sK2,k2_struct_0(sK2),sK3(a_2_0_orders_2(sK2,k2_struct_0(sK2)))),k2_struct_0(sK2)) ),
    inference(backward_demodulation,[],[f104,f119])).

fof(f104,plain,
    ( m1_subset_1(sK6(sK2,k2_struct_0(sK2),sK3(a_2_0_orders_2(sK2,k2_struct_0(sK2)))),k2_struct_0(sK2))
    | k1_xboole_0 = a_2_0_orders_2(sK2,k2_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f101,f80])).

fof(f101,plain,
    ( k1_xboole_0 = a_2_0_orders_2(sK2,k2_struct_0(sK2))
    | m1_subset_1(sK6(sK2,k2_struct_0(sK2),sK3(a_2_0_orders_2(sK2,k2_struct_0(sK2)))),u1_struct_0(sK2)) ),
    inference(resolution,[],[f96,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f235,plain,(
    ~ m1_subset_1(sK3(k1_orders_2(sK2,k2_struct_0(sK2))),k2_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f234,f80])).

fof(f234,plain,(
    ~ m1_subset_1(sK3(k1_orders_2(sK2,k2_struct_0(sK2))),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f233,f50])).

fof(f233,plain,
    ( ~ m1_subset_1(sK3(k1_orders_2(sK2,k2_struct_0(sK2))),u1_struct_0(sK2))
    | ~ l1_orders_2(sK2) ),
    inference(subsumption_resolution,[],[f232,f189])).

fof(f189,plain,(
    r2_hidden(sK3(k1_orders_2(sK2,k2_struct_0(sK2))),k2_struct_0(sK2)) ),
    inference(resolution,[],[f177,f163])).

fof(f163,plain,(
    r2_hidden(sK3(k1_orders_2(sK2,k2_struct_0(sK2))),k1_orders_2(sK2,k2_struct_0(sK2))) ),
    inference(resolution,[],[f120,f133])).

fof(f133,plain,(
    sP0(sK2,k2_struct_0(sK2),sK3(k1_orders_2(sK2,k2_struct_0(sK2)))) ),
    inference(subsumption_resolution,[],[f132,f51])).

fof(f132,plain,
    ( k1_xboole_0 = k1_orders_2(sK2,k2_struct_0(sK2))
    | sP0(sK2,k2_struct_0(sK2),sK3(k1_orders_2(sK2,k2_struct_0(sK2)))) ),
    inference(forward_demodulation,[],[f122,f119])).

fof(f122,plain,
    ( sP0(sK2,k2_struct_0(sK2),sK3(k1_orders_2(sK2,k2_struct_0(sK2))))
    | k1_xboole_0 = a_2_0_orders_2(sK2,k2_struct_0(sK2)) ),
    inference(backward_demodulation,[],[f96,f119])).

fof(f120,plain,(
    ! [X0] :
      ( ~ sP0(sK2,k2_struct_0(sK2),X0)
      | r2_hidden(X0,k1_orders_2(sK2,k2_struct_0(sK2))) ) ),
    inference(backward_demodulation,[],[f94,f119])).

fof(f94,plain,(
    ! [X0] :
      ( ~ sP0(sK2,k2_struct_0(sK2),X0)
      | r2_hidden(X0,a_2_0_orders_2(sK2,k2_struct_0(sK2))) ) ),
    inference(resolution,[],[f93,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ sP0(X2,X1,X0)
      | r2_hidden(X0,a_2_0_orders_2(X2,X1)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f177,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_orders_2(sK2,k2_struct_0(sK2)))
      | r2_hidden(X0,k2_struct_0(sK2)) ) ),
    inference(resolution,[],[f172,f60])).

fof(f60,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f172,plain,(
    r1_tarski(k1_orders_2(sK2,k2_struct_0(sK2)),k2_struct_0(sK2)) ),
    inference(resolution,[],[f168,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f168,plain,(
    m1_subset_1(k1_orders_2(sK2,k2_struct_0(sK2)),k1_zfmisc_1(k2_struct_0(sK2))) ),
    inference(resolution,[],[f155,f83])).

fof(f155,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2)))
      | m1_subset_1(k1_orders_2(sK2,X0),k1_zfmisc_1(k2_struct_0(sK2))) ) ),
    inference(forward_demodulation,[],[f154,f80])).

fof(f154,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2)))
      | m1_subset_1(k1_orders_2(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(forward_demodulation,[],[f153,f80])).

fof(f153,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | m1_subset_1(k1_orders_2(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(subsumption_resolution,[],[f152,f46])).

fof(f152,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | m1_subset_1(k1_orders_2(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f151,f47])).

fof(f151,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | m1_subset_1(k1_orders_2(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f150,f48])).

fof(f150,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | m1_subset_1(k1_orders_2(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f149,f50])).

fof(f149,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_orders_2(sK2)
      | m1_subset_1(k1_orders_2(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f59,f49])).

fof(f59,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_orders_2)).

fof(f232,plain,
    ( ~ r2_hidden(sK3(k1_orders_2(sK2,k2_struct_0(sK2))),k2_struct_0(sK2))
    | ~ m1_subset_1(sK3(k1_orders_2(sK2,k2_struct_0(sK2))),u1_struct_0(sK2))
    | ~ l1_orders_2(sK2) ),
    inference(subsumption_resolution,[],[f230,f143])).

fof(f230,plain,
    ( ~ m1_subset_1(sK3(k1_orders_2(sK2,k2_struct_0(sK2))),k2_struct_0(sK2))
    | ~ r2_hidden(sK3(k1_orders_2(sK2,k2_struct_0(sK2))),k2_struct_0(sK2))
    | ~ m1_subset_1(sK3(k1_orders_2(sK2,k2_struct_0(sK2))),u1_struct_0(sK2))
    | ~ l1_orders_2(sK2) ),
    inference(resolution,[],[f140,f78])).

fof(f78,plain,(
    ! [X2,X0] :
      ( ~ r2_orders_2(X0,X2,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f74])).

fof(f74,plain,(
    ! [X2,X0] :
      ( ~ r2_orders_2(X0,X2,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_orders_2)).

fof(f140,plain,(
    ! [X0] :
      ( r2_orders_2(sK2,X0,sK3(k1_orders_2(sK2,k2_struct_0(sK2))))
      | ~ m1_subset_1(X0,k2_struct_0(sK2))
      | ~ r2_hidden(X0,k2_struct_0(sK2)) ) ),
    inference(forward_demodulation,[],[f139,f137])).

fof(f139,plain,(
    ! [X0] :
      ( r2_orders_2(sK2,X0,sK6(sK2,k2_struct_0(sK2),sK3(k1_orders_2(sK2,k2_struct_0(sK2)))))
      | ~ m1_subset_1(X0,k2_struct_0(sK2))
      | ~ r2_hidden(X0,k2_struct_0(sK2)) ) ),
    inference(forward_demodulation,[],[f138,f119])).

fof(f138,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k2_struct_0(sK2))
      | ~ r2_hidden(X0,k2_struct_0(sK2))
      | r2_orders_2(sK2,X0,sK6(sK2,k2_struct_0(sK2),sK3(a_2_0_orders_2(sK2,k2_struct_0(sK2))))) ) ),
    inference(subsumption_resolution,[],[f126,f51])).

fof(f126,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_orders_2(sK2,k2_struct_0(sK2))
      | ~ m1_subset_1(X0,k2_struct_0(sK2))
      | ~ r2_hidden(X0,k2_struct_0(sK2))
      | r2_orders_2(sK2,X0,sK6(sK2,k2_struct_0(sK2),sK3(a_2_0_orders_2(sK2,k2_struct_0(sK2))))) ) ),
    inference(backward_demodulation,[],[f103,f119])).

fof(f103,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k2_struct_0(sK2))
      | k1_xboole_0 = a_2_0_orders_2(sK2,k2_struct_0(sK2))
      | ~ r2_hidden(X0,k2_struct_0(sK2))
      | r2_orders_2(sK2,X0,sK6(sK2,k2_struct_0(sK2),sK3(a_2_0_orders_2(sK2,k2_struct_0(sK2))))) ) ),
    inference(forward_demodulation,[],[f100,f80])).

fof(f100,plain,(
    ! [X0] :
      ( k1_xboole_0 = a_2_0_orders_2(sK2,k2_struct_0(sK2))
      | ~ r2_hidden(X0,k2_struct_0(sK2))
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | r2_orders_2(sK2,X0,sK6(sK2,k2_struct_0(sK2),sK3(a_2_0_orders_2(sK2,k2_struct_0(sK2))))) ) ),
    inference(resolution,[],[f96,f69])).

fof(f69,plain,(
    ! [X6,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X6,X1)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | r2_orders_2(X0,X6,sK6(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f45])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:06:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (14559)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.52  % (14554)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.52  % (14555)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.53  % (14575)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.53  % (14561)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.53  % (14552)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.53  % (14561)Refutation not found, incomplete strategy% (14561)------------------------------
% 0.22/0.53  % (14561)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (14579)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.54  % (14577)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.54  % (14558)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.54  % (14551)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (14577)Refutation not found, incomplete strategy% (14577)------------------------------
% 0.22/0.54  % (14577)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (14574)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.54  % (14561)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (14561)Memory used [KB]: 10618
% 0.22/0.54  % (14561)Time elapsed: 0.105 s
% 0.22/0.54  % (14561)------------------------------
% 0.22/0.54  % (14561)------------------------------
% 0.22/0.54  % (14551)Refutation not found, incomplete strategy% (14551)------------------------------
% 0.22/0.54  % (14551)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (14551)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (14551)Memory used [KB]: 1663
% 0.22/0.54  % (14551)Time elapsed: 0.123 s
% 0.22/0.54  % (14551)------------------------------
% 0.22/0.54  % (14551)------------------------------
% 0.22/0.54  % (14560)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.54  % (14580)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.54  % (14563)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (14570)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.55  % (14566)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.55  % (14572)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.55  % (14578)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.55  % (14577)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (14577)Memory used [KB]: 10746
% 0.22/0.55  % (14577)Time elapsed: 0.121 s
% 0.22/0.55  % (14577)------------------------------
% 0.22/0.55  % (14577)------------------------------
% 0.22/0.55  % (14557)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.49/0.55  % (14567)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.49/0.55  % (14558)Refutation found. Thanks to Tanya!
% 1.49/0.55  % SZS status Theorem for theBenchmark
% 1.49/0.55  % SZS output start Proof for theBenchmark
% 1.49/0.55  fof(f236,plain,(
% 1.49/0.55    $false),
% 1.49/0.55    inference(subsumption_resolution,[],[f235,f143])).
% 1.49/0.55  fof(f143,plain,(
% 1.49/0.55    m1_subset_1(sK3(k1_orders_2(sK2,k2_struct_0(sK2))),k2_struct_0(sK2))),
% 1.49/0.55    inference(forward_demodulation,[],[f142,f137])).
% 1.49/0.55  fof(f137,plain,(
% 1.49/0.55    sK3(k1_orders_2(sK2,k2_struct_0(sK2))) = sK6(sK2,k2_struct_0(sK2),sK3(k1_orders_2(sK2,k2_struct_0(sK2))))),
% 1.49/0.55    inference(forward_demodulation,[],[f136,f119])).
% 1.49/0.55  fof(f119,plain,(
% 1.49/0.55    k1_orders_2(sK2,k2_struct_0(sK2)) = a_2_0_orders_2(sK2,k2_struct_0(sK2))),
% 1.49/0.55    inference(resolution,[],[f118,f83])).
% 1.49/0.55  fof(f83,plain,(
% 1.49/0.55    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 1.49/0.55    inference(resolution,[],[f82,f64])).
% 1.49/0.55  fof(f64,plain,(
% 1.49/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.49/0.55    inference(cnf_transformation,[],[f38])).
% 1.49/0.55  fof(f38,plain,(
% 1.49/0.55    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.49/0.55    inference(nnf_transformation,[],[f3])).
% 1.49/0.55  fof(f3,axiom,(
% 1.49/0.55    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.49/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.49/0.55  fof(f82,plain,(
% 1.49/0.55    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 1.49/0.55    inference(duplicate_literal_removal,[],[f81])).
% 1.49/0.55  fof(f81,plain,(
% 1.49/0.55    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 1.49/0.55    inference(resolution,[],[f62,f61])).
% 1.49/0.55  fof(f61,plain,(
% 1.49/0.55    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f37])).
% 1.49/0.55  fof(f37,plain,(
% 1.49/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.49/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f35,f36])).
% 1.49/0.55  fof(f36,plain,(
% 1.49/0.55    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 1.49/0.55    introduced(choice_axiom,[])).
% 1.49/0.55  fof(f35,plain,(
% 1.49/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.49/0.55    inference(rectify,[],[f34])).
% 1.49/0.55  fof(f34,plain,(
% 1.49/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.49/0.55    inference(nnf_transformation,[],[f22])).
% 1.49/0.55  fof(f22,plain,(
% 1.49/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.49/0.55    inference(ennf_transformation,[],[f1])).
% 1.49/0.55  fof(f1,axiom,(
% 1.49/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.49/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.49/0.55  fof(f62,plain,(
% 1.49/0.55    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f37])).
% 1.49/0.55  fof(f118,plain,(
% 1.49/0.55    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) | k1_orders_2(sK2,X0) = a_2_0_orders_2(sK2,X0)) )),
% 1.49/0.55    inference(forward_demodulation,[],[f117,f80])).
% 1.49/0.55  fof(f80,plain,(
% 1.49/0.55    k2_struct_0(sK2) = u1_struct_0(sK2)),
% 1.49/0.55    inference(resolution,[],[f52,f79])).
% 1.49/0.55  fof(f79,plain,(
% 1.49/0.55    l1_struct_0(sK2)),
% 1.49/0.55    inference(resolution,[],[f53,f50])).
% 1.49/0.55  fof(f50,plain,(
% 1.49/0.55    l1_orders_2(sK2)),
% 1.49/0.55    inference(cnf_transformation,[],[f29])).
% 1.49/0.55  fof(f29,plain,(
% 1.49/0.55    k1_xboole_0 != k1_orders_2(sK2,k2_struct_0(sK2)) & l1_orders_2(sK2) & v5_orders_2(sK2) & v4_orders_2(sK2) & v3_orders_2(sK2) & ~v2_struct_0(sK2)),
% 1.49/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f13,f28])).
% 1.49/0.55  fof(f28,plain,(
% 1.49/0.55    ? [X0] : (k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (k1_xboole_0 != k1_orders_2(sK2,k2_struct_0(sK2)) & l1_orders_2(sK2) & v5_orders_2(sK2) & v4_orders_2(sK2) & v3_orders_2(sK2) & ~v2_struct_0(sK2))),
% 1.49/0.55    introduced(choice_axiom,[])).
% 1.49/0.55  fof(f13,plain,(
% 1.49/0.55    ? [X0] : (k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.49/0.55    inference(flattening,[],[f12])).
% 1.49/0.55  fof(f12,plain,(
% 1.49/0.55    ? [X0] : (k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0)) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 1.49/0.55    inference(ennf_transformation,[],[f11])).
% 1.49/0.55  fof(f11,negated_conjecture,(
% 1.49/0.55    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)))),
% 1.49/0.55    inference(negated_conjecture,[],[f10])).
% 1.49/0.55  fof(f10,conjecture,(
% 1.49/0.55    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)))),
% 1.49/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_orders_2)).
% 1.49/0.55  fof(f53,plain,(
% 1.49/0.55    ( ! [X0] : (~l1_orders_2(X0) | l1_struct_0(X0)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f15])).
% 1.49/0.55  fof(f15,plain,(
% 1.49/0.55    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 1.49/0.55    inference(ennf_transformation,[],[f8])).
% 1.49/0.55  fof(f8,axiom,(
% 1.49/0.55    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 1.49/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 1.49/0.55  fof(f52,plain,(
% 1.49/0.55    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f14])).
% 1.49/0.55  fof(f14,plain,(
% 1.49/0.55    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.49/0.55    inference(ennf_transformation,[],[f4])).
% 1.49/0.55  fof(f4,axiom,(
% 1.49/0.55    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.49/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 1.49/0.55  fof(f117,plain,(
% 1.49/0.55    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | k1_orders_2(sK2,X0) = a_2_0_orders_2(sK2,X0)) )),
% 1.49/0.55    inference(subsumption_resolution,[],[f116,f46])).
% 1.49/0.55  fof(f46,plain,(
% 1.49/0.55    ~v2_struct_0(sK2)),
% 1.49/0.55    inference(cnf_transformation,[],[f29])).
% 1.49/0.55  fof(f116,plain,(
% 1.49/0.55    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | k1_orders_2(sK2,X0) = a_2_0_orders_2(sK2,X0) | v2_struct_0(sK2)) )),
% 1.49/0.55    inference(subsumption_resolution,[],[f115,f47])).
% 1.49/0.55  fof(f47,plain,(
% 1.49/0.55    v3_orders_2(sK2)),
% 1.49/0.55    inference(cnf_transformation,[],[f29])).
% 1.49/0.55  fof(f115,plain,(
% 1.49/0.55    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | k1_orders_2(sK2,X0) = a_2_0_orders_2(sK2,X0) | ~v3_orders_2(sK2) | v2_struct_0(sK2)) )),
% 1.49/0.55    inference(subsumption_resolution,[],[f114,f48])).
% 1.49/0.55  fof(f48,plain,(
% 1.49/0.55    v4_orders_2(sK2)),
% 1.49/0.55    inference(cnf_transformation,[],[f29])).
% 1.49/0.55  fof(f114,plain,(
% 1.49/0.55    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | k1_orders_2(sK2,X0) = a_2_0_orders_2(sK2,X0) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | v2_struct_0(sK2)) )),
% 1.49/0.55    inference(subsumption_resolution,[],[f113,f50])).
% 1.49/0.55  fof(f113,plain,(
% 1.49/0.55    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_orders_2(sK2) | k1_orders_2(sK2,X0) = a_2_0_orders_2(sK2,X0) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | v2_struct_0(sK2)) )),
% 1.49/0.55    inference(resolution,[],[f57,f49])).
% 1.49/0.55  fof(f49,plain,(
% 1.49/0.55    v5_orders_2(sK2)),
% 1.49/0.55    inference(cnf_transformation,[],[f29])).
% 1.49/0.55  fof(f57,plain,(
% 1.49/0.55    ( ! [X0,X1] : (~v5_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f18])).
% 1.49/0.55  fof(f18,plain,(
% 1.49/0.55    ! [X0] : (! [X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.49/0.55    inference(flattening,[],[f17])).
% 1.49/0.55  fof(f17,plain,(
% 1.49/0.55    ! [X0] : (! [X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.49/0.55    inference(ennf_transformation,[],[f6])).
% 1.49/0.55  fof(f6,axiom,(
% 1.49/0.55    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)))),
% 1.49/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_orders_2)).
% 1.49/0.55  fof(f136,plain,(
% 1.49/0.55    sK3(a_2_0_orders_2(sK2,k2_struct_0(sK2))) = sK6(sK2,k2_struct_0(sK2),sK3(a_2_0_orders_2(sK2,k2_struct_0(sK2))))),
% 1.49/0.55    inference(subsumption_resolution,[],[f125,f51])).
% 1.49/0.55  fof(f51,plain,(
% 1.49/0.55    k1_xboole_0 != k1_orders_2(sK2,k2_struct_0(sK2))),
% 1.49/0.55    inference(cnf_transformation,[],[f29])).
% 1.49/0.55  fof(f125,plain,(
% 1.49/0.55    k1_xboole_0 = k1_orders_2(sK2,k2_struct_0(sK2)) | sK3(a_2_0_orders_2(sK2,k2_struct_0(sK2))) = sK6(sK2,k2_struct_0(sK2),sK3(a_2_0_orders_2(sK2,k2_struct_0(sK2))))),
% 1.49/0.55    inference(backward_demodulation,[],[f102,f119])).
% 1.49/0.55  fof(f102,plain,(
% 1.49/0.55    sK3(a_2_0_orders_2(sK2,k2_struct_0(sK2))) = sK6(sK2,k2_struct_0(sK2),sK3(a_2_0_orders_2(sK2,k2_struct_0(sK2)))) | k1_xboole_0 = a_2_0_orders_2(sK2,k2_struct_0(sK2))),
% 1.49/0.55    inference(resolution,[],[f96,f68])).
% 1.49/0.55  fof(f68,plain,(
% 1.49/0.55    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | sK6(X0,X1,X2) = X2) )),
% 1.49/0.55    inference(cnf_transformation,[],[f45])).
% 1.49/0.55  fof(f45,plain,(
% 1.49/0.55    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3] : ((~r2_orders_2(X0,sK5(X0,X1,X3),X3) & r2_hidden(sK5(X0,X1,X3),X1) & m1_subset_1(sK5(X0,X1,X3),u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)))) & ((! [X6] : (r2_orders_2(X0,X6,sK6(X0,X1,X2)) | ~r2_hidden(X6,X1) | ~m1_subset_1(X6,u1_struct_0(X0))) & sK6(X0,X1,X2) = X2 & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))) | ~sP0(X0,X1,X2)))),
% 1.49/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f42,f44,f43])).
% 1.49/0.55  fof(f43,plain,(
% 1.49/0.55    ! [X3,X1,X0] : (? [X4] : (~r2_orders_2(X0,X4,X3) & r2_hidden(X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) => (~r2_orders_2(X0,sK5(X0,X1,X3),X3) & r2_hidden(sK5(X0,X1,X3),X1) & m1_subset_1(sK5(X0,X1,X3),u1_struct_0(X0))))),
% 1.49/0.55    introduced(choice_axiom,[])).
% 1.49/0.55  fof(f44,plain,(
% 1.49/0.55    ! [X2,X1,X0] : (? [X5] : (! [X6] : (r2_orders_2(X0,X6,X5) | ~r2_hidden(X6,X1) | ~m1_subset_1(X6,u1_struct_0(X0))) & X2 = X5 & m1_subset_1(X5,u1_struct_0(X0))) => (! [X6] : (r2_orders_2(X0,X6,sK6(X0,X1,X2)) | ~r2_hidden(X6,X1) | ~m1_subset_1(X6,u1_struct_0(X0))) & sK6(X0,X1,X2) = X2 & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))))),
% 1.49/0.55    introduced(choice_axiom,[])).
% 1.49/0.55  fof(f42,plain,(
% 1.49/0.55    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3] : (? [X4] : (~r2_orders_2(X0,X4,X3) & r2_hidden(X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)))) & (? [X5] : (! [X6] : (r2_orders_2(X0,X6,X5) | ~r2_hidden(X6,X1) | ~m1_subset_1(X6,u1_struct_0(X0))) & X2 = X5 & m1_subset_1(X5,u1_struct_0(X0))) | ~sP0(X0,X1,X2)))),
% 1.49/0.55    inference(rectify,[],[f41])).
% 1.49/0.55  fof(f41,plain,(
% 1.49/0.55    ! [X1,X2,X0] : ((sP0(X1,X2,X0) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X4,X3) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (! [X4] : (r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~sP0(X1,X2,X0)))),
% 1.49/0.55    inference(nnf_transformation,[],[f25])).
% 1.49/0.55  fof(f25,plain,(
% 1.49/0.55    ! [X1,X2,X0] : (sP0(X1,X2,X0) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))))),
% 1.49/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.49/0.55  fof(f96,plain,(
% 1.49/0.55    sP0(sK2,k2_struct_0(sK2),sK3(a_2_0_orders_2(sK2,k2_struct_0(sK2)))) | k1_xboole_0 = a_2_0_orders_2(sK2,k2_struct_0(sK2))),
% 1.49/0.55    inference(resolution,[],[f95,f58])).
% 1.49/0.55  fof(f58,plain,(
% 1.49/0.55    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 1.49/0.55    inference(cnf_transformation,[],[f33])).
% 1.49/0.56  fof(f33,plain,(
% 1.49/0.56    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 1.49/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f32])).
% 1.49/0.56  fof(f32,plain,(
% 1.49/0.56    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 1.49/0.56    introduced(choice_axiom,[])).
% 1.49/0.56  fof(f19,plain,(
% 1.49/0.56    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.49/0.56    inference(ennf_transformation,[],[f2])).
% 1.49/0.56  fof(f2,axiom,(
% 1.49/0.56    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.49/0.56  fof(f95,plain,(
% 1.49/0.56    ( ! [X1] : (~r2_hidden(X1,a_2_0_orders_2(sK2,k2_struct_0(sK2))) | sP0(sK2,k2_struct_0(sK2),X1)) )),
% 1.49/0.56    inference(resolution,[],[f93,f65])).
% 1.49/0.56  fof(f65,plain,(
% 1.49/0.56    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | ~r2_hidden(X0,a_2_0_orders_2(X2,X1)) | sP0(X2,X1,X0)) )),
% 1.49/0.56    inference(cnf_transformation,[],[f40])).
% 1.49/0.56  fof(f40,plain,(
% 1.49/0.56    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_0_orders_2(X2,X1)) | ~sP0(X2,X1,X0)) & (sP0(X2,X1,X0) | ~r2_hidden(X0,a_2_0_orders_2(X2,X1)))) | ~sP1(X0,X1,X2))),
% 1.49/0.56    inference(rectify,[],[f39])).
% 1.49/0.56  fof(f39,plain,(
% 1.49/0.56    ! [X0,X2,X1] : (((r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ~sP0(X1,X2,X0)) & (sP0(X1,X2,X0) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)))) | ~sP1(X0,X2,X1))),
% 1.49/0.56    inference(nnf_transformation,[],[f26])).
% 1.49/0.56  fof(f26,plain,(
% 1.49/0.56    ! [X0,X2,X1] : ((r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> sP0(X1,X2,X0)) | ~sP1(X0,X2,X1))),
% 1.49/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.49/0.56  fof(f93,plain,(
% 1.49/0.56    ( ! [X0] : (sP1(X0,k2_struct_0(sK2),sK2)) )),
% 1.49/0.56    inference(resolution,[],[f92,f83])).
% 1.49/0.56  fof(f92,plain,(
% 1.49/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) | sP1(X1,X0,sK2)) )),
% 1.49/0.56    inference(forward_demodulation,[],[f91,f80])).
% 1.49/0.56  fof(f91,plain,(
% 1.49/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | sP1(X1,X0,sK2)) )),
% 1.49/0.56    inference(subsumption_resolution,[],[f90,f46])).
% 1.49/0.56  fof(f90,plain,(
% 1.49/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | sP1(X1,X0,sK2) | v2_struct_0(sK2)) )),
% 1.49/0.56    inference(subsumption_resolution,[],[f89,f47])).
% 1.49/0.56  fof(f89,plain,(
% 1.49/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | sP1(X1,X0,sK2) | ~v3_orders_2(sK2) | v2_struct_0(sK2)) )),
% 1.49/0.56    inference(subsumption_resolution,[],[f88,f48])).
% 1.49/0.56  fof(f88,plain,(
% 1.49/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | sP1(X1,X0,sK2) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | v2_struct_0(sK2)) )),
% 1.49/0.56    inference(subsumption_resolution,[],[f87,f50])).
% 1.49/0.56  fof(f87,plain,(
% 1.49/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_orders_2(sK2) | sP1(X1,X0,sK2) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | v2_struct_0(sK2)) )),
% 1.49/0.56    inference(resolution,[],[f73,f49])).
% 1.49/0.56  fof(f73,plain,(
% 1.49/0.56    ( ! [X2,X0,X1] : (~v5_orders_2(X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | sP1(X0,X2,X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 1.49/0.56    inference(cnf_transformation,[],[f27])).
% 1.49/0.56  fof(f27,plain,(
% 1.49/0.56    ! [X0,X1,X2] : (sP1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 1.49/0.56    inference(definition_folding,[],[f24,f26,f25])).
% 1.49/0.56  fof(f24,plain,(
% 1.49/0.56    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 1.49/0.56    inference(flattening,[],[f23])).
% 1.49/0.56  fof(f23,plain,(
% 1.49/0.56    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : ((r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)))),
% 1.49/0.56    inference(ennf_transformation,[],[f9])).
% 1.49/0.56  fof(f9,axiom,(
% 1.49/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) & l1_orders_2(X1) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r2_hidden(X4,X2) => r2_orders_2(X1,X4,X3))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_0_orders_2)).
% 1.49/0.56  fof(f142,plain,(
% 1.49/0.56    m1_subset_1(sK6(sK2,k2_struct_0(sK2),sK3(k1_orders_2(sK2,k2_struct_0(sK2)))),k2_struct_0(sK2))),
% 1.49/0.56    inference(forward_demodulation,[],[f141,f119])).
% 1.49/0.56  fof(f141,plain,(
% 1.49/0.56    m1_subset_1(sK6(sK2,k2_struct_0(sK2),sK3(a_2_0_orders_2(sK2,k2_struct_0(sK2)))),k2_struct_0(sK2))),
% 1.49/0.56    inference(subsumption_resolution,[],[f127,f51])).
% 1.49/0.56  fof(f127,plain,(
% 1.49/0.56    k1_xboole_0 = k1_orders_2(sK2,k2_struct_0(sK2)) | m1_subset_1(sK6(sK2,k2_struct_0(sK2),sK3(a_2_0_orders_2(sK2,k2_struct_0(sK2)))),k2_struct_0(sK2))),
% 1.49/0.56    inference(backward_demodulation,[],[f104,f119])).
% 1.49/0.56  fof(f104,plain,(
% 1.49/0.56    m1_subset_1(sK6(sK2,k2_struct_0(sK2),sK3(a_2_0_orders_2(sK2,k2_struct_0(sK2)))),k2_struct_0(sK2)) | k1_xboole_0 = a_2_0_orders_2(sK2,k2_struct_0(sK2))),
% 1.49/0.56    inference(forward_demodulation,[],[f101,f80])).
% 1.49/0.56  fof(f101,plain,(
% 1.49/0.56    k1_xboole_0 = a_2_0_orders_2(sK2,k2_struct_0(sK2)) | m1_subset_1(sK6(sK2,k2_struct_0(sK2),sK3(a_2_0_orders_2(sK2,k2_struct_0(sK2)))),u1_struct_0(sK2))),
% 1.49/0.56    inference(resolution,[],[f96,f67])).
% 1.49/0.56  fof(f67,plain,(
% 1.49/0.56    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))) )),
% 1.49/0.56    inference(cnf_transformation,[],[f45])).
% 1.49/0.56  fof(f235,plain,(
% 1.49/0.56    ~m1_subset_1(sK3(k1_orders_2(sK2,k2_struct_0(sK2))),k2_struct_0(sK2))),
% 1.49/0.56    inference(forward_demodulation,[],[f234,f80])).
% 1.49/0.56  fof(f234,plain,(
% 1.49/0.56    ~m1_subset_1(sK3(k1_orders_2(sK2,k2_struct_0(sK2))),u1_struct_0(sK2))),
% 1.49/0.56    inference(subsumption_resolution,[],[f233,f50])).
% 1.49/0.56  fof(f233,plain,(
% 1.49/0.56    ~m1_subset_1(sK3(k1_orders_2(sK2,k2_struct_0(sK2))),u1_struct_0(sK2)) | ~l1_orders_2(sK2)),
% 1.49/0.56    inference(subsumption_resolution,[],[f232,f189])).
% 1.49/0.56  fof(f189,plain,(
% 1.49/0.56    r2_hidden(sK3(k1_orders_2(sK2,k2_struct_0(sK2))),k2_struct_0(sK2))),
% 1.49/0.56    inference(resolution,[],[f177,f163])).
% 1.49/0.56  fof(f163,plain,(
% 1.49/0.56    r2_hidden(sK3(k1_orders_2(sK2,k2_struct_0(sK2))),k1_orders_2(sK2,k2_struct_0(sK2)))),
% 1.49/0.56    inference(resolution,[],[f120,f133])).
% 1.49/0.56  fof(f133,plain,(
% 1.49/0.56    sP0(sK2,k2_struct_0(sK2),sK3(k1_orders_2(sK2,k2_struct_0(sK2))))),
% 1.49/0.56    inference(subsumption_resolution,[],[f132,f51])).
% 1.49/0.56  fof(f132,plain,(
% 1.49/0.56    k1_xboole_0 = k1_orders_2(sK2,k2_struct_0(sK2)) | sP0(sK2,k2_struct_0(sK2),sK3(k1_orders_2(sK2,k2_struct_0(sK2))))),
% 1.49/0.56    inference(forward_demodulation,[],[f122,f119])).
% 1.49/0.56  fof(f122,plain,(
% 1.49/0.56    sP0(sK2,k2_struct_0(sK2),sK3(k1_orders_2(sK2,k2_struct_0(sK2)))) | k1_xboole_0 = a_2_0_orders_2(sK2,k2_struct_0(sK2))),
% 1.49/0.56    inference(backward_demodulation,[],[f96,f119])).
% 1.49/0.56  fof(f120,plain,(
% 1.49/0.56    ( ! [X0] : (~sP0(sK2,k2_struct_0(sK2),X0) | r2_hidden(X0,k1_orders_2(sK2,k2_struct_0(sK2)))) )),
% 1.49/0.56    inference(backward_demodulation,[],[f94,f119])).
% 1.49/0.56  fof(f94,plain,(
% 1.49/0.56    ( ! [X0] : (~sP0(sK2,k2_struct_0(sK2),X0) | r2_hidden(X0,a_2_0_orders_2(sK2,k2_struct_0(sK2)))) )),
% 1.49/0.56    inference(resolution,[],[f93,f66])).
% 1.49/0.56  fof(f66,plain,(
% 1.49/0.56    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | ~sP0(X2,X1,X0) | r2_hidden(X0,a_2_0_orders_2(X2,X1))) )),
% 1.49/0.56    inference(cnf_transformation,[],[f40])).
% 1.49/0.56  fof(f177,plain,(
% 1.49/0.56    ( ! [X0] : (~r2_hidden(X0,k1_orders_2(sK2,k2_struct_0(sK2))) | r2_hidden(X0,k2_struct_0(sK2))) )),
% 1.49/0.56    inference(resolution,[],[f172,f60])).
% 1.49/0.56  fof(f60,plain,(
% 1.49/0.56    ( ! [X0,X3,X1] : (~r1_tarski(X0,X1) | ~r2_hidden(X3,X0) | r2_hidden(X3,X1)) )),
% 1.49/0.56    inference(cnf_transformation,[],[f37])).
% 1.49/0.56  fof(f172,plain,(
% 1.49/0.56    r1_tarski(k1_orders_2(sK2,k2_struct_0(sK2)),k2_struct_0(sK2))),
% 1.49/0.56    inference(resolution,[],[f168,f63])).
% 1.49/0.56  fof(f63,plain,(
% 1.49/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.49/0.56    inference(cnf_transformation,[],[f38])).
% 1.49/0.56  fof(f168,plain,(
% 1.49/0.56    m1_subset_1(k1_orders_2(sK2,k2_struct_0(sK2)),k1_zfmisc_1(k2_struct_0(sK2)))),
% 1.49/0.56    inference(resolution,[],[f155,f83])).
% 1.49/0.56  fof(f155,plain,(
% 1.49/0.56    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) | m1_subset_1(k1_orders_2(sK2,X0),k1_zfmisc_1(k2_struct_0(sK2)))) )),
% 1.49/0.56    inference(forward_demodulation,[],[f154,f80])).
% 1.49/0.56  fof(f154,plain,(
% 1.49/0.56    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) | m1_subset_1(k1_orders_2(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))) )),
% 1.49/0.56    inference(forward_demodulation,[],[f153,f80])).
% 1.49/0.56  fof(f153,plain,(
% 1.49/0.56    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | m1_subset_1(k1_orders_2(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))) )),
% 1.49/0.56    inference(subsumption_resolution,[],[f152,f46])).
% 1.49/0.56  fof(f152,plain,(
% 1.49/0.56    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | m1_subset_1(k1_orders_2(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) | v2_struct_0(sK2)) )),
% 1.49/0.56    inference(subsumption_resolution,[],[f151,f47])).
% 1.49/0.56  fof(f151,plain,(
% 1.49/0.56    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | m1_subset_1(k1_orders_2(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) | ~v3_orders_2(sK2) | v2_struct_0(sK2)) )),
% 1.49/0.56    inference(subsumption_resolution,[],[f150,f48])).
% 1.49/0.56  fof(f150,plain,(
% 1.49/0.56    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | m1_subset_1(k1_orders_2(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | v2_struct_0(sK2)) )),
% 1.49/0.56    inference(subsumption_resolution,[],[f149,f50])).
% 1.49/0.56  fof(f149,plain,(
% 1.49/0.56    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_orders_2(sK2) | m1_subset_1(k1_orders_2(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | v2_struct_0(sK2)) )),
% 1.49/0.56    inference(resolution,[],[f59,f49])).
% 1.49/0.56  fof(f59,plain,(
% 1.49/0.56    ( ! [X0,X1] : (~v5_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.49/0.56    inference(cnf_transformation,[],[f21])).
% 1.49/0.56  fof(f21,plain,(
% 1.49/0.56    ! [X0,X1] : (m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.49/0.56    inference(flattening,[],[f20])).
% 1.49/0.56  fof(f20,plain,(
% 1.49/0.56    ! [X0,X1] : (m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.49/0.56    inference(ennf_transformation,[],[f7])).
% 1.49/0.56  fof(f7,axiom,(
% 1.49/0.56    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_orders_2)).
% 1.49/0.56  fof(f232,plain,(
% 1.49/0.56    ~r2_hidden(sK3(k1_orders_2(sK2,k2_struct_0(sK2))),k2_struct_0(sK2)) | ~m1_subset_1(sK3(k1_orders_2(sK2,k2_struct_0(sK2))),u1_struct_0(sK2)) | ~l1_orders_2(sK2)),
% 1.49/0.56    inference(subsumption_resolution,[],[f230,f143])).
% 1.49/0.56  fof(f230,plain,(
% 1.49/0.56    ~m1_subset_1(sK3(k1_orders_2(sK2,k2_struct_0(sK2))),k2_struct_0(sK2)) | ~r2_hidden(sK3(k1_orders_2(sK2,k2_struct_0(sK2))),k2_struct_0(sK2)) | ~m1_subset_1(sK3(k1_orders_2(sK2,k2_struct_0(sK2))),u1_struct_0(sK2)) | ~l1_orders_2(sK2)),
% 1.49/0.56    inference(resolution,[],[f140,f78])).
% 1.49/0.56  fof(f78,plain,(
% 1.49/0.56    ( ! [X2,X0] : (~r2_orders_2(X0,X2,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.49/0.56    inference(duplicate_literal_removal,[],[f74])).
% 1.49/0.56  fof(f74,plain,(
% 1.49/0.56    ( ! [X2,X0] : (~r2_orders_2(X0,X2,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.49/0.56    inference(equality_resolution,[],[f55])).
% 1.49/0.56  fof(f55,plain,(
% 1.49/0.56    ( ! [X2,X0,X1] : (X1 != X2 | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.49/0.56    inference(cnf_transformation,[],[f31])).
% 1.49/0.56  fof(f31,plain,(
% 1.49/0.56    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | X1 = X2 | ~r1_orders_2(X0,X1,X2)) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.49/0.56    inference(flattening,[],[f30])).
% 1.49/0.56  fof(f30,plain,(
% 1.49/0.56    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | (X1 = X2 | ~r1_orders_2(X0,X1,X2))) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.49/0.56    inference(nnf_transformation,[],[f16])).
% 1.49/0.56  fof(f16,plain,(
% 1.49/0.56    ! [X0] : (! [X1] : (! [X2] : ((r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.49/0.56    inference(ennf_transformation,[],[f5])).
% 1.49/0.56  fof(f5,axiom,(
% 1.49/0.56    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))))))),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_orders_2)).
% 1.49/0.56  fof(f140,plain,(
% 1.49/0.56    ( ! [X0] : (r2_orders_2(sK2,X0,sK3(k1_orders_2(sK2,k2_struct_0(sK2)))) | ~m1_subset_1(X0,k2_struct_0(sK2)) | ~r2_hidden(X0,k2_struct_0(sK2))) )),
% 1.49/0.56    inference(forward_demodulation,[],[f139,f137])).
% 1.49/0.56  fof(f139,plain,(
% 1.49/0.56    ( ! [X0] : (r2_orders_2(sK2,X0,sK6(sK2,k2_struct_0(sK2),sK3(k1_orders_2(sK2,k2_struct_0(sK2))))) | ~m1_subset_1(X0,k2_struct_0(sK2)) | ~r2_hidden(X0,k2_struct_0(sK2))) )),
% 1.49/0.56    inference(forward_demodulation,[],[f138,f119])).
% 1.49/0.56  fof(f138,plain,(
% 1.49/0.56    ( ! [X0] : (~m1_subset_1(X0,k2_struct_0(sK2)) | ~r2_hidden(X0,k2_struct_0(sK2)) | r2_orders_2(sK2,X0,sK6(sK2,k2_struct_0(sK2),sK3(a_2_0_orders_2(sK2,k2_struct_0(sK2)))))) )),
% 1.49/0.56    inference(subsumption_resolution,[],[f126,f51])).
% 1.49/0.56  fof(f126,plain,(
% 1.49/0.56    ( ! [X0] : (k1_xboole_0 = k1_orders_2(sK2,k2_struct_0(sK2)) | ~m1_subset_1(X0,k2_struct_0(sK2)) | ~r2_hidden(X0,k2_struct_0(sK2)) | r2_orders_2(sK2,X0,sK6(sK2,k2_struct_0(sK2),sK3(a_2_0_orders_2(sK2,k2_struct_0(sK2)))))) )),
% 1.49/0.56    inference(backward_demodulation,[],[f103,f119])).
% 1.49/0.56  fof(f103,plain,(
% 1.49/0.56    ( ! [X0] : (~m1_subset_1(X0,k2_struct_0(sK2)) | k1_xboole_0 = a_2_0_orders_2(sK2,k2_struct_0(sK2)) | ~r2_hidden(X0,k2_struct_0(sK2)) | r2_orders_2(sK2,X0,sK6(sK2,k2_struct_0(sK2),sK3(a_2_0_orders_2(sK2,k2_struct_0(sK2)))))) )),
% 1.49/0.56    inference(forward_demodulation,[],[f100,f80])).
% 1.49/0.56  fof(f100,plain,(
% 1.49/0.56    ( ! [X0] : (k1_xboole_0 = a_2_0_orders_2(sK2,k2_struct_0(sK2)) | ~r2_hidden(X0,k2_struct_0(sK2)) | ~m1_subset_1(X0,u1_struct_0(sK2)) | r2_orders_2(sK2,X0,sK6(sK2,k2_struct_0(sK2),sK3(a_2_0_orders_2(sK2,k2_struct_0(sK2)))))) )),
% 1.49/0.56    inference(resolution,[],[f96,f69])).
% 1.49/0.56  fof(f69,plain,(
% 1.49/0.56    ( ! [X6,X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X6,X1) | ~m1_subset_1(X6,u1_struct_0(X0)) | r2_orders_2(X0,X6,sK6(X0,X1,X2))) )),
% 1.49/0.56    inference(cnf_transformation,[],[f45])).
% 1.49/0.56  % SZS output end Proof for theBenchmark
% 1.49/0.56  % (14558)------------------------------
% 1.49/0.56  % (14558)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.56  % (14558)Termination reason: Refutation
% 1.49/0.56  
% 1.49/0.56  % (14558)Memory used [KB]: 6396
% 1.49/0.56  % (14558)Time elapsed: 0.117 s
% 1.49/0.56  % (14558)------------------------------
% 1.49/0.56  % (14558)------------------------------
% 1.49/0.56  % (14573)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.49/0.56  % (14556)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.49/0.56  % (14550)Success in time 0.193 s
%------------------------------------------------------------------------------
