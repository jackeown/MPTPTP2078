%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:43 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  131 (2284 expanded)
%              Number of leaves         :   20 ( 574 expanded)
%              Depth                    :   31
%              Number of atoms          :  478 (11501 expanded)
%              Number of equality atoms :   80 (1970 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f301,plain,(
    $false ),
    inference(subsumption_resolution,[],[f300,f237])).

fof(f237,plain,(
    m1_subset_1(sK3(k1_orders_2(sK2,k2_struct_0(sK2))),k2_struct_0(sK2)) ),
    inference(backward_demodulation,[],[f236,f234])).

fof(f234,plain,(
    sK3(k1_orders_2(sK2,k2_struct_0(sK2))) = sK5(sK2,k2_struct_0(sK2),sK3(k1_orders_2(sK2,k2_struct_0(sK2)))) ),
    inference(resolution,[],[f231,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | sK5(X0,X1,X2) = X2 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f48,f50,f49])).

fof(f49,plain,(
    ! [X3,X1,X0] :
      ( ? [X4] :
          ( ~ r2_orders_2(X0,X4,X3)
          & r2_hidden(X4,X1)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r2_orders_2(X0,sK4(X0,X1,X3),X3)
        & r2_hidden(sK4(X0,X1,X3),X1)
        & m1_subset_1(sK4(X0,X1,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
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

fof(f48,plain,(
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
    inference(rectify,[],[f47])).

fof(f47,plain,(
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
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
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

fof(f231,plain,(
    sP0(sK2,k2_struct_0(sK2),sK3(k1_orders_2(sK2,k2_struct_0(sK2)))) ),
    inference(forward_demodulation,[],[f230,f223])).

fof(f223,plain,(
    k1_orders_2(sK2,k2_struct_0(sK2)) = a_2_0_orders_2(sK2,k2_struct_0(sK2)) ),
    inference(resolution,[],[f202,f88])).

fof(f88,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f202,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_struct_0(sK2))
      | k1_orders_2(sK2,X0) = a_2_0_orders_2(sK2,X0) ) ),
    inference(resolution,[],[f200,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f200,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2)))
      | k1_orders_2(sK2,X0) = a_2_0_orders_2(sK2,X0) ) ),
    inference(forward_demodulation,[],[f199,f96])).

fof(f96,plain,(
    k2_struct_0(sK2) = u1_struct_0(sK2) ),
    inference(resolution,[],[f61,f94])).

fof(f94,plain,(
    l1_struct_0(sK2) ),
    inference(resolution,[],[f62,f56])).

fof(f56,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( k1_xboole_0 != k1_orders_2(sK2,k2_struct_0(sK2))
    & l1_orders_2(sK2)
    & v5_orders_2(sK2)
    & v4_orders_2(sK2)
    & v3_orders_2(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f36])).

fof(f36,plain,
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

fof(f18,plain,(
    ? [X0] :
      ( k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_orders_2)).

fof(f62,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f61,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f199,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | k1_orders_2(sK2,X0) = a_2_0_orders_2(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f198,f52])).

fof(f52,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f198,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | k1_orders_2(sK2,X0) = a_2_0_orders_2(sK2,X0)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f197,f53])).

fof(f53,plain,(
    v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f197,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | k1_orders_2(sK2,X0) = a_2_0_orders_2(sK2,X0)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f196,f54])).

fof(f54,plain,(
    v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f196,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | k1_orders_2(sK2,X0) = a_2_0_orders_2(sK2,X0)
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f195,f56])).

fof(f195,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_orders_2(sK2)
      | k1_orders_2(sK2,X0) = a_2_0_orders_2(sK2,X0)
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f67,f55])).

fof(f55,plain,(
    v5_orders_2(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f230,plain,(
    sP0(sK2,k2_struct_0(sK2),sK3(a_2_0_orders_2(sK2,k2_struct_0(sK2)))) ),
    inference(subsumption_resolution,[],[f227,f57])).

fof(f57,plain,(
    k1_xboole_0 != k1_orders_2(sK2,k2_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f37])).

fof(f227,plain,
    ( k1_xboole_0 = k1_orders_2(sK2,k2_struct_0(sK2))
    | sP0(sK2,k2_struct_0(sK2),sK3(a_2_0_orders_2(sK2,k2_struct_0(sK2)))) ),
    inference(backward_demodulation,[],[f188,f223])).

fof(f188,plain,
    ( sP0(sK2,k2_struct_0(sK2),sK3(a_2_0_orders_2(sK2,k2_struct_0(sK2))))
    | k1_xboole_0 = a_2_0_orders_2(sK2,k2_struct_0(sK2)) ),
    inference(resolution,[],[f186,f68])).

fof(f68,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ( ! [X2,X3] :
            ( k4_tarski(X2,X3) != sK3(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK3(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f40])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] :
            ( k4_tarski(X2,X3) != sK3(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK3(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3] :
                  ~ ( k4_tarski(X2,X3) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

fof(f186,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,a_2_0_orders_2(sK2,k2_struct_0(sK2)))
      | sP0(sK2,k2_struct_0(sK2),X1) ) ),
    inference(resolution,[],[f182,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ r2_hidden(X0,a_2_0_orders_2(X2,X1))
      | sP0(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_orders_2(X2,X1))
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | ~ r2_hidden(X0,a_2_0_orders_2(X2,X1)) ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X0,X2,X1] :
      ( ( ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
          | ~ sP0(X1,X2,X0) )
        & ( sP0(X1,X2,X0)
          | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2)) ) )
      | ~ sP1(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X2,X1] :
      ( ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
      <=> sP0(X1,X2,X0) )
      | ~ sP1(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f182,plain,(
    ! [X1] : sP1(X1,k2_struct_0(sK2),sK2) ),
    inference(resolution,[],[f177,f88])).

fof(f177,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X2,k2_struct_0(sK2))
      | sP1(X1,X2,sK2) ) ),
    inference(resolution,[],[f175,f75])).

fof(f175,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2)))
      | sP1(X1,X0,sK2) ) ),
    inference(forward_demodulation,[],[f174,f96])).

fof(f174,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | sP1(X1,X0,sK2) ) ),
    inference(subsumption_resolution,[],[f173,f52])).

fof(f173,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | sP1(X1,X0,sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f172,f53])).

fof(f172,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | sP1(X1,X0,sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f171,f54])).

fof(f171,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | sP1(X1,X0,sK2)
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f170,f56])).

fof(f170,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_orders_2(sK2)
      | sP1(X1,X0,sK2)
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f85,f55])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | sP1(X0,X2,X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( sP1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(definition_folding,[],[f30,f34,f33])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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

fof(f236,plain,(
    m1_subset_1(sK5(sK2,k2_struct_0(sK2),sK3(k1_orders_2(sK2,k2_struct_0(sK2)))),k2_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f233,f96])).

fof(f233,plain,(
    m1_subset_1(sK5(sK2,k2_struct_0(sK2),sK3(k1_orders_2(sK2,k2_struct_0(sK2)))),u1_struct_0(sK2)) ),
    inference(resolution,[],[f231,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f300,plain,(
    ~ m1_subset_1(sK3(k1_orders_2(sK2,k2_struct_0(sK2))),k2_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f299,f96])).

fof(f299,plain,(
    ~ m1_subset_1(sK3(k1_orders_2(sK2,k2_struct_0(sK2))),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f298,f56])).

fof(f298,plain,
    ( ~ m1_subset_1(sK3(k1_orders_2(sK2,k2_struct_0(sK2))),u1_struct_0(sK2))
    | ~ l1_orders_2(sK2) ),
    inference(resolution,[],[f295,f93])).

fof(f93,plain,(
    ! [X2,X0] :
      ( ~ r2_orders_2(X0,X2,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f87])).

fof(f87,plain,(
    ! [X2,X0] :
      ( ~ r2_orders_2(X0,X2,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( X1 != X2
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f295,plain,(
    r2_orders_2(sK2,sK3(k1_orders_2(sK2,k2_struct_0(sK2))),sK3(k1_orders_2(sK2,k2_struct_0(sK2)))) ),
    inference(subsumption_resolution,[],[f291,f237])).

fof(f291,plain,
    ( ~ m1_subset_1(sK3(k1_orders_2(sK2,k2_struct_0(sK2))),k2_struct_0(sK2))
    | r2_orders_2(sK2,sK3(k1_orders_2(sK2,k2_struct_0(sK2))),sK3(k1_orders_2(sK2,k2_struct_0(sK2)))) ),
    inference(resolution,[],[f283,f238])).

fof(f238,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_struct_0(sK2))
      | ~ m1_subset_1(X0,k2_struct_0(sK2))
      | r2_orders_2(sK2,X0,sK3(k1_orders_2(sK2,k2_struct_0(sK2)))) ) ),
    inference(backward_demodulation,[],[f235,f234])).

fof(f235,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k2_struct_0(sK2))
      | ~ r2_hidden(X0,k2_struct_0(sK2))
      | r2_orders_2(sK2,X0,sK5(sK2,k2_struct_0(sK2),sK3(k1_orders_2(sK2,k2_struct_0(sK2))))) ) ),
    inference(forward_demodulation,[],[f232,f96])).

fof(f232,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_struct_0(sK2))
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | r2_orders_2(sK2,X0,sK5(sK2,k2_struct_0(sK2),sK3(k1_orders_2(sK2,k2_struct_0(sK2))))) ) ),
    inference(resolution,[],[f231,f81])).

fof(f81,plain,(
    ! [X6,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X6,X1)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | r2_orders_2(X0,X6,sK5(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f283,plain,(
    r2_hidden(sK3(k1_orders_2(sK2,k2_struct_0(sK2))),k2_struct_0(sK2)) ),
    inference(resolution,[],[f282,f205])).

fof(f205,plain,(
    ! [X0] :
      ( ~ sP0(sK2,k1_xboole_0,X0)
      | r2_hidden(X0,k2_struct_0(sK2)) ) ),
    inference(backward_demodulation,[],[f179,f204])).

fof(f204,plain,(
    k2_struct_0(sK2) = a_2_0_orders_2(sK2,k1_xboole_0) ),
    inference(forward_demodulation,[],[f201,f145])).

fof(f145,plain,(
    k2_struct_0(sK2) = k1_orders_2(sK2,k1_xboole_0) ),
    inference(forward_demodulation,[],[f144,f96])).

fof(f144,plain,(
    u1_struct_0(sK2) = k1_orders_2(sK2,k1_xboole_0) ),
    inference(forward_demodulation,[],[f143,f95])).

fof(f95,plain,(
    k1_xboole_0 = k1_struct_0(sK2) ),
    inference(resolution,[],[f60,f94])).

fof(f60,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k1_xboole_0 = k1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k1_xboole_0 = k1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_struct_0)).

fof(f143,plain,(
    u1_struct_0(sK2) = k1_orders_2(sK2,k1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f142,f52])).

fof(f142,plain,
    ( u1_struct_0(sK2) = k1_orders_2(sK2,k1_struct_0(sK2))
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f141,f53])).

fof(f141,plain,
    ( u1_struct_0(sK2) = k1_orders_2(sK2,k1_struct_0(sK2))
    | ~ v3_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f140,f54])).

fof(f140,plain,
    ( u1_struct_0(sK2) = k1_orders_2(sK2,k1_struct_0(sK2))
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f139,f56])).

fof(f139,plain,
    ( ~ l1_orders_2(sK2)
    | u1_struct_0(sK2) = k1_orders_2(sK2,k1_struct_0(sK2))
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f66,f55])).

fof(f66,plain,(
    ! [X0] :
      ( ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | u1_struct_0(X0) = k1_orders_2(X0,k1_struct_0(X0))
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k1_orders_2(X0,k1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k1_orders_2(X0,k1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => u1_struct_0(X0) = k1_orders_2(X0,k1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_orders_2)).

fof(f201,plain,(
    k1_orders_2(sK2,k1_xboole_0) = a_2_0_orders_2(sK2,k1_xboole_0) ),
    inference(resolution,[],[f200,f59])).

fof(f59,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f179,plain,(
    ! [X0] :
      ( ~ sP0(sK2,k1_xboole_0,X0)
      | r2_hidden(X0,a_2_0_orders_2(sK2,k1_xboole_0)) ) ),
    inference(resolution,[],[f176,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ sP0(X2,X1,X0)
      | r2_hidden(X0,a_2_0_orders_2(X2,X1)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f176,plain,(
    ! [X0] : sP1(X0,k1_xboole_0,sK2) ),
    inference(resolution,[],[f175,f59])).

fof(f282,plain,(
    sP0(sK2,k1_xboole_0,sK3(k1_orders_2(sK2,k2_struct_0(sK2)))) ),
    inference(resolution,[],[f273,f58])).

fof(f58,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f273,plain,(
    ! [X2] :
      ( ~ r1_tarski(X2,sK4(sK2,X2,sK3(k1_orders_2(sK2,k2_struct_0(sK2)))))
      | sP0(sK2,X2,sK3(k1_orders_2(sK2,k2_struct_0(sK2)))) ) ),
    inference(resolution,[],[f239,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f239,plain,(
    ! [X0] :
      ( r2_hidden(sK4(sK2,X0,sK3(k1_orders_2(sK2,k2_struct_0(sK2)))),X0)
      | sP0(sK2,X0,sK3(k1_orders_2(sK2,k2_struct_0(sK2)))) ) ),
    inference(resolution,[],[f237,f132])).

fof(f132,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k2_struct_0(sK2))
      | r2_hidden(sK4(sK2,X1,X0),X1)
      | sP0(sK2,X1,X0) ) ),
    inference(superposition,[],[f91,f96])).

fof(f91,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,u1_struct_0(X0))
      | r2_hidden(sK4(X0,X1,X3),X1)
      | sP0(X0,X1,X3) ) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2)
      | r2_hidden(sK4(X0,X1,X3),X1)
      | X2 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f51])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:09:30 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.49  % (28416)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.50  % (28416)Refutation not found, incomplete strategy% (28416)------------------------------
% 0.22/0.50  % (28416)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (28416)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (28416)Memory used [KB]: 6140
% 0.22/0.50  % (28416)Time elapsed: 0.085 s
% 0.22/0.50  % (28416)------------------------------
% 0.22/0.50  % (28416)------------------------------
% 0.22/0.50  % (28429)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.50  % (28417)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.51  % (28421)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.51  % (28414)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.51  % (28412)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  % (28422)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.51  % (28425)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.52  % (28422)Refutation not found, incomplete strategy% (28422)------------------------------
% 0.22/0.52  % (28422)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (28422)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (28422)Memory used [KB]: 10490
% 0.22/0.52  % (28422)Time elapsed: 0.103 s
% 0.22/0.52  % (28422)------------------------------
% 0.22/0.52  % (28422)------------------------------
% 0.22/0.52  % (28430)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.52  % (28433)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.52  % (28419)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.52  % (28434)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.52  % (28428)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.53  % (28431)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.53  % (28417)Refutation not found, incomplete strategy% (28417)------------------------------
% 0.22/0.53  % (28417)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (28417)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (28417)Memory used [KB]: 10618
% 0.22/0.53  % (28417)Time elapsed: 0.098 s
% 0.22/0.53  % (28417)------------------------------
% 0.22/0.53  % (28417)------------------------------
% 0.22/0.53  % (28415)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.53  % (28424)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.53  % (28424)Refutation not found, incomplete strategy% (28424)------------------------------
% 0.22/0.53  % (28424)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (28424)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (28424)Memory used [KB]: 6140
% 0.22/0.53  % (28424)Time elapsed: 0.129 s
% 0.22/0.53  % (28424)------------------------------
% 0.22/0.53  % (28424)------------------------------
% 0.22/0.53  % (28418)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.53  % (28414)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f301,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(subsumption_resolution,[],[f300,f237])).
% 0.22/0.53  fof(f237,plain,(
% 0.22/0.53    m1_subset_1(sK3(k1_orders_2(sK2,k2_struct_0(sK2))),k2_struct_0(sK2))),
% 0.22/0.53    inference(backward_demodulation,[],[f236,f234])).
% 0.22/0.53  fof(f234,plain,(
% 0.22/0.53    sK3(k1_orders_2(sK2,k2_struct_0(sK2))) = sK5(sK2,k2_struct_0(sK2),sK3(k1_orders_2(sK2,k2_struct_0(sK2))))),
% 0.22/0.53    inference(resolution,[],[f231,f80])).
% 0.22/0.53  fof(f80,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | sK5(X0,X1,X2) = X2) )),
% 0.22/0.53    inference(cnf_transformation,[],[f51])).
% 0.22/0.53  fof(f51,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3] : ((~r2_orders_2(X0,sK4(X0,X1,X3),X3) & r2_hidden(sK4(X0,X1,X3),X1) & m1_subset_1(sK4(X0,X1,X3),u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)))) & ((! [X6] : (r2_orders_2(X0,X6,sK5(X0,X1,X2)) | ~r2_hidden(X6,X1) | ~m1_subset_1(X6,u1_struct_0(X0))) & sK5(X0,X1,X2) = X2 & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))) | ~sP0(X0,X1,X2)))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f48,f50,f49])).
% 0.22/0.53  fof(f49,plain,(
% 0.22/0.53    ! [X3,X1,X0] : (? [X4] : (~r2_orders_2(X0,X4,X3) & r2_hidden(X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) => (~r2_orders_2(X0,sK4(X0,X1,X3),X3) & r2_hidden(sK4(X0,X1,X3),X1) & m1_subset_1(sK4(X0,X1,X3),u1_struct_0(X0))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f50,plain,(
% 0.22/0.53    ! [X2,X1,X0] : (? [X5] : (! [X6] : (r2_orders_2(X0,X6,X5) | ~r2_hidden(X6,X1) | ~m1_subset_1(X6,u1_struct_0(X0))) & X2 = X5 & m1_subset_1(X5,u1_struct_0(X0))) => (! [X6] : (r2_orders_2(X0,X6,sK5(X0,X1,X2)) | ~r2_hidden(X6,X1) | ~m1_subset_1(X6,u1_struct_0(X0))) & sK5(X0,X1,X2) = X2 & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f48,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3] : (? [X4] : (~r2_orders_2(X0,X4,X3) & r2_hidden(X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)))) & (? [X5] : (! [X6] : (r2_orders_2(X0,X6,X5) | ~r2_hidden(X6,X1) | ~m1_subset_1(X6,u1_struct_0(X0))) & X2 = X5 & m1_subset_1(X5,u1_struct_0(X0))) | ~sP0(X0,X1,X2)))),
% 0.22/0.53    inference(rectify,[],[f47])).
% 0.22/0.53  fof(f47,plain,(
% 0.22/0.53    ! [X1,X2,X0] : ((sP0(X1,X2,X0) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X4,X3) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (! [X4] : (r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~sP0(X1,X2,X0)))),
% 0.22/0.53    inference(nnf_transformation,[],[f33])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    ! [X1,X2,X0] : (sP0(X1,X2,X0) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))))),
% 0.22/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.53  fof(f231,plain,(
% 0.22/0.53    sP0(sK2,k2_struct_0(sK2),sK3(k1_orders_2(sK2,k2_struct_0(sK2))))),
% 0.22/0.53    inference(forward_demodulation,[],[f230,f223])).
% 0.22/0.53  fof(f223,plain,(
% 0.22/0.53    k1_orders_2(sK2,k2_struct_0(sK2)) = a_2_0_orders_2(sK2,k2_struct_0(sK2))),
% 0.22/0.53    inference(resolution,[],[f202,f88])).
% 0.22/0.53  fof(f88,plain,(
% 0.22/0.53    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.53    inference(equality_resolution,[],[f72])).
% 0.22/0.53  fof(f72,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f43])).
% 0.22/0.53  fof(f43,plain,(
% 0.22/0.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.53    inference(flattening,[],[f42])).
% 0.22/0.53  fof(f42,plain,(
% 0.22/0.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.53    inference(nnf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.53  fof(f202,plain,(
% 0.22/0.53    ( ! [X0] : (~r1_tarski(X0,k2_struct_0(sK2)) | k1_orders_2(sK2,X0) = a_2_0_orders_2(sK2,X0)) )),
% 0.22/0.53    inference(resolution,[],[f200,f75])).
% 0.22/0.53  fof(f75,plain,(
% 0.22/0.53    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f44])).
% 0.22/0.53  fof(f44,plain,(
% 0.22/0.53    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.53    inference(nnf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.53  fof(f200,plain,(
% 0.22/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) | k1_orders_2(sK2,X0) = a_2_0_orders_2(sK2,X0)) )),
% 0.22/0.53    inference(forward_demodulation,[],[f199,f96])).
% 0.22/0.53  fof(f96,plain,(
% 0.22/0.53    k2_struct_0(sK2) = u1_struct_0(sK2)),
% 0.22/0.53    inference(resolution,[],[f61,f94])).
% 0.22/0.53  fof(f94,plain,(
% 0.22/0.53    l1_struct_0(sK2)),
% 0.22/0.53    inference(resolution,[],[f62,f56])).
% 0.22/0.53  fof(f56,plain,(
% 0.22/0.53    l1_orders_2(sK2)),
% 0.22/0.53    inference(cnf_transformation,[],[f37])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    k1_xboole_0 != k1_orders_2(sK2,k2_struct_0(sK2)) & l1_orders_2(sK2) & v5_orders_2(sK2) & v4_orders_2(sK2) & v3_orders_2(sK2) & ~v2_struct_0(sK2)),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f36])).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    ? [X0] : (k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (k1_xboole_0 != k1_orders_2(sK2,k2_struct_0(sK2)) & l1_orders_2(sK2) & v5_orders_2(sK2) & v4_orders_2(sK2) & v3_orders_2(sK2) & ~v2_struct_0(sK2))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ? [X0] : (k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f17])).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    ? [X0] : (k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0)) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f16])).
% 0.22/0.53  fof(f16,negated_conjecture,(
% 0.22/0.53    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)))),
% 0.22/0.53    inference(negated_conjecture,[],[f15])).
% 0.22/0.53  fof(f15,conjecture,(
% 0.22/0.53    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_orders_2)).
% 0.22/0.53  fof(f62,plain,(
% 0.22/0.53    ( ! [X0] : (~l1_orders_2(X0) | l1_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f21])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f12])).
% 0.22/0.53  fof(f12,axiom,(
% 0.22/0.53    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 0.22/0.53  fof(f61,plain,(
% 0.22/0.53    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f20])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f9])).
% 0.22/0.53  fof(f9,axiom,(
% 0.22/0.53    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.22/0.53  fof(f199,plain,(
% 0.22/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | k1_orders_2(sK2,X0) = a_2_0_orders_2(sK2,X0)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f198,f52])).
% 0.22/0.53  fof(f52,plain,(
% 0.22/0.53    ~v2_struct_0(sK2)),
% 0.22/0.53    inference(cnf_transformation,[],[f37])).
% 0.22/0.53  fof(f198,plain,(
% 0.22/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | k1_orders_2(sK2,X0) = a_2_0_orders_2(sK2,X0) | v2_struct_0(sK2)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f197,f53])).
% 0.22/0.53  fof(f53,plain,(
% 0.22/0.53    v3_orders_2(sK2)),
% 0.22/0.53    inference(cnf_transformation,[],[f37])).
% 0.22/0.53  fof(f197,plain,(
% 0.22/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | k1_orders_2(sK2,X0) = a_2_0_orders_2(sK2,X0) | ~v3_orders_2(sK2) | v2_struct_0(sK2)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f196,f54])).
% 0.22/0.53  fof(f54,plain,(
% 0.22/0.53    v4_orders_2(sK2)),
% 0.22/0.53    inference(cnf_transformation,[],[f37])).
% 0.22/0.53  fof(f196,plain,(
% 0.22/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | k1_orders_2(sK2,X0) = a_2_0_orders_2(sK2,X0) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | v2_struct_0(sK2)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f195,f56])).
% 0.22/0.53  fof(f195,plain,(
% 0.22/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_orders_2(sK2) | k1_orders_2(sK2,X0) = a_2_0_orders_2(sK2,X0) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | v2_struct_0(sK2)) )),
% 0.22/0.53    inference(resolution,[],[f67,f55])).
% 0.22/0.53  fof(f55,plain,(
% 0.22/0.53    v5_orders_2(sK2)),
% 0.22/0.53    inference(cnf_transformation,[],[f37])).
% 0.22/0.53  fof(f67,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v5_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f26])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f25])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f11])).
% 0.22/0.53  fof(f11,axiom,(
% 0.22/0.53    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_orders_2)).
% 0.22/0.53  fof(f230,plain,(
% 0.22/0.53    sP0(sK2,k2_struct_0(sK2),sK3(a_2_0_orders_2(sK2,k2_struct_0(sK2))))),
% 0.22/0.53    inference(subsumption_resolution,[],[f227,f57])).
% 0.22/0.53  fof(f57,plain,(
% 0.22/0.53    k1_xboole_0 != k1_orders_2(sK2,k2_struct_0(sK2))),
% 0.22/0.53    inference(cnf_transformation,[],[f37])).
% 0.22/0.53  fof(f227,plain,(
% 0.22/0.53    k1_xboole_0 = k1_orders_2(sK2,k2_struct_0(sK2)) | sP0(sK2,k2_struct_0(sK2),sK3(a_2_0_orders_2(sK2,k2_struct_0(sK2))))),
% 0.22/0.53    inference(backward_demodulation,[],[f188,f223])).
% 0.22/0.53  fof(f188,plain,(
% 0.22/0.53    sP0(sK2,k2_struct_0(sK2),sK3(a_2_0_orders_2(sK2,k2_struct_0(sK2)))) | k1_xboole_0 = a_2_0_orders_2(sK2,k2_struct_0(sK2))),
% 0.22/0.53    inference(resolution,[],[f186,f68])).
% 0.22/0.53  fof(f68,plain,(
% 0.22/0.53    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f41])).
% 0.22/0.53  fof(f41,plain,(
% 0.22/0.53    ! [X0] : ((! [X2,X3] : (k4_tarski(X2,X3) != sK3(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK3(X0),X0)) | k1_xboole_0 = X0)),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f40])).
% 0.22/0.53  fof(f40,plain,(
% 0.22/0.53    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X3,X2] : (k4_tarski(X2,X3) != sK3(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK3(X0),X0)))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.22/0.53    inference(ennf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,axiom,(
% 0.22/0.53    ! [X0] : ~(! [X1] : ~(! [X2,X3] : ~(k4_tarski(X2,X3) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).
% 0.22/0.53  fof(f186,plain,(
% 0.22/0.53    ( ! [X1] : (~r2_hidden(X1,a_2_0_orders_2(sK2,k2_struct_0(sK2))) | sP0(sK2,k2_struct_0(sK2),X1)) )),
% 0.22/0.53    inference(resolution,[],[f182,f77])).
% 0.22/0.53  fof(f77,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | ~r2_hidden(X0,a_2_0_orders_2(X2,X1)) | sP0(X2,X1,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f46])).
% 0.22/0.53  fof(f46,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_0_orders_2(X2,X1)) | ~sP0(X2,X1,X0)) & (sP0(X2,X1,X0) | ~r2_hidden(X0,a_2_0_orders_2(X2,X1)))) | ~sP1(X0,X1,X2))),
% 0.22/0.53    inference(rectify,[],[f45])).
% 0.22/0.53  fof(f45,plain,(
% 0.22/0.53    ! [X0,X2,X1] : (((r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ~sP0(X1,X2,X0)) & (sP0(X1,X2,X0) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)))) | ~sP1(X0,X2,X1))),
% 0.22/0.53    inference(nnf_transformation,[],[f34])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    ! [X0,X2,X1] : ((r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> sP0(X1,X2,X0)) | ~sP1(X0,X2,X1))),
% 0.22/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.22/0.53  fof(f182,plain,(
% 0.22/0.53    ( ! [X1] : (sP1(X1,k2_struct_0(sK2),sK2)) )),
% 0.22/0.53    inference(resolution,[],[f177,f88])).
% 0.22/0.53  fof(f177,plain,(
% 0.22/0.53    ( ! [X2,X1] : (~r1_tarski(X2,k2_struct_0(sK2)) | sP1(X1,X2,sK2)) )),
% 0.22/0.53    inference(resolution,[],[f175,f75])).
% 0.22/0.53  fof(f175,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) | sP1(X1,X0,sK2)) )),
% 0.22/0.53    inference(forward_demodulation,[],[f174,f96])).
% 0.22/0.53  fof(f174,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | sP1(X1,X0,sK2)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f173,f52])).
% 0.22/0.53  fof(f173,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | sP1(X1,X0,sK2) | v2_struct_0(sK2)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f172,f53])).
% 0.22/0.53  fof(f172,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | sP1(X1,X0,sK2) | ~v3_orders_2(sK2) | v2_struct_0(sK2)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f171,f54])).
% 0.22/0.53  fof(f171,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | sP1(X1,X0,sK2) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | v2_struct_0(sK2)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f170,f56])).
% 0.22/0.53  fof(f170,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_orders_2(sK2) | sP1(X1,X0,sK2) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | v2_struct_0(sK2)) )),
% 0.22/0.53    inference(resolution,[],[f85,f55])).
% 0.22/0.53  fof(f85,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~v5_orders_2(X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | sP1(X0,X2,X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f35])).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (sP1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 0.22/0.53    inference(definition_folding,[],[f30,f34,f33])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 0.22/0.53    inference(flattening,[],[f29])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : ((r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)))),
% 0.22/0.53    inference(ennf_transformation,[],[f13])).
% 0.22/0.53  fof(f13,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) & l1_orders_2(X1) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r2_hidden(X4,X2) => r2_orders_2(X1,X4,X3))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_0_orders_2)).
% 0.22/0.53  fof(f236,plain,(
% 0.22/0.53    m1_subset_1(sK5(sK2,k2_struct_0(sK2),sK3(k1_orders_2(sK2,k2_struct_0(sK2)))),k2_struct_0(sK2))),
% 0.22/0.53    inference(forward_demodulation,[],[f233,f96])).
% 0.22/0.53  fof(f233,plain,(
% 0.22/0.53    m1_subset_1(sK5(sK2,k2_struct_0(sK2),sK3(k1_orders_2(sK2,k2_struct_0(sK2)))),u1_struct_0(sK2))),
% 0.22/0.53    inference(resolution,[],[f231,f79])).
% 0.22/0.53  fof(f79,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f51])).
% 0.22/0.53  fof(f300,plain,(
% 0.22/0.53    ~m1_subset_1(sK3(k1_orders_2(sK2,k2_struct_0(sK2))),k2_struct_0(sK2))),
% 0.22/0.53    inference(forward_demodulation,[],[f299,f96])).
% 0.22/0.53  fof(f299,plain,(
% 0.22/0.53    ~m1_subset_1(sK3(k1_orders_2(sK2,k2_struct_0(sK2))),u1_struct_0(sK2))),
% 0.22/0.53    inference(subsumption_resolution,[],[f298,f56])).
% 0.22/0.53  fof(f298,plain,(
% 0.22/0.53    ~m1_subset_1(sK3(k1_orders_2(sK2,k2_struct_0(sK2))),u1_struct_0(sK2)) | ~l1_orders_2(sK2)),
% 0.22/0.53    inference(resolution,[],[f295,f93])).
% 0.22/0.53  fof(f93,plain,(
% 0.22/0.53    ( ! [X2,X0] : (~r2_orders_2(X0,X2,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f87])).
% 0.22/0.53  fof(f87,plain,(
% 0.22/0.53    ( ! [X2,X0] : (~r2_orders_2(X0,X2,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.22/0.53    inference(equality_resolution,[],[f64])).
% 0.22/0.53  fof(f64,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (X1 != X2 | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f39])).
% 0.22/0.53  fof(f39,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | X1 = X2 | ~r1_orders_2(X0,X1,X2)) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.53    inference(flattening,[],[f38])).
% 0.22/0.53  fof(f38,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | (X1 = X2 | ~r1_orders_2(X0,X1,X2))) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.53    inference(nnf_transformation,[],[f22])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : ((r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f10])).
% 0.22/0.53  fof(f10,axiom,(
% 0.22/0.53    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_orders_2)).
% 0.22/0.53  fof(f295,plain,(
% 0.22/0.53    r2_orders_2(sK2,sK3(k1_orders_2(sK2,k2_struct_0(sK2))),sK3(k1_orders_2(sK2,k2_struct_0(sK2))))),
% 0.22/0.53    inference(subsumption_resolution,[],[f291,f237])).
% 0.22/0.53  fof(f291,plain,(
% 0.22/0.53    ~m1_subset_1(sK3(k1_orders_2(sK2,k2_struct_0(sK2))),k2_struct_0(sK2)) | r2_orders_2(sK2,sK3(k1_orders_2(sK2,k2_struct_0(sK2))),sK3(k1_orders_2(sK2,k2_struct_0(sK2))))),
% 0.22/0.53    inference(resolution,[],[f283,f238])).
% 0.22/0.53  fof(f238,plain,(
% 0.22/0.53    ( ! [X0] : (~r2_hidden(X0,k2_struct_0(sK2)) | ~m1_subset_1(X0,k2_struct_0(sK2)) | r2_orders_2(sK2,X0,sK3(k1_orders_2(sK2,k2_struct_0(sK2))))) )),
% 0.22/0.53    inference(backward_demodulation,[],[f235,f234])).
% 0.22/0.53  fof(f235,plain,(
% 0.22/0.53    ( ! [X0] : (~m1_subset_1(X0,k2_struct_0(sK2)) | ~r2_hidden(X0,k2_struct_0(sK2)) | r2_orders_2(sK2,X0,sK5(sK2,k2_struct_0(sK2),sK3(k1_orders_2(sK2,k2_struct_0(sK2)))))) )),
% 0.22/0.53    inference(forward_demodulation,[],[f232,f96])).
% 0.22/0.53  fof(f232,plain,(
% 0.22/0.53    ( ! [X0] : (~r2_hidden(X0,k2_struct_0(sK2)) | ~m1_subset_1(X0,u1_struct_0(sK2)) | r2_orders_2(sK2,X0,sK5(sK2,k2_struct_0(sK2),sK3(k1_orders_2(sK2,k2_struct_0(sK2)))))) )),
% 0.22/0.53    inference(resolution,[],[f231,f81])).
% 0.22/0.53  fof(f81,plain,(
% 0.22/0.53    ( ! [X6,X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X6,X1) | ~m1_subset_1(X6,u1_struct_0(X0)) | r2_orders_2(X0,X6,sK5(X0,X1,X2))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f51])).
% 0.22/0.53  fof(f283,plain,(
% 0.22/0.53    r2_hidden(sK3(k1_orders_2(sK2,k2_struct_0(sK2))),k2_struct_0(sK2))),
% 0.22/0.53    inference(resolution,[],[f282,f205])).
% 0.22/0.53  fof(f205,plain,(
% 0.22/0.53    ( ! [X0] : (~sP0(sK2,k1_xboole_0,X0) | r2_hidden(X0,k2_struct_0(sK2))) )),
% 0.22/0.53    inference(backward_demodulation,[],[f179,f204])).
% 0.22/0.53  fof(f204,plain,(
% 0.22/0.53    k2_struct_0(sK2) = a_2_0_orders_2(sK2,k1_xboole_0)),
% 0.22/0.53    inference(forward_demodulation,[],[f201,f145])).
% 0.22/0.53  fof(f145,plain,(
% 0.22/0.53    k2_struct_0(sK2) = k1_orders_2(sK2,k1_xboole_0)),
% 0.22/0.53    inference(forward_demodulation,[],[f144,f96])).
% 0.22/0.53  fof(f144,plain,(
% 0.22/0.53    u1_struct_0(sK2) = k1_orders_2(sK2,k1_xboole_0)),
% 0.22/0.53    inference(forward_demodulation,[],[f143,f95])).
% 0.22/0.53  fof(f95,plain,(
% 0.22/0.53    k1_xboole_0 = k1_struct_0(sK2)),
% 0.22/0.53    inference(resolution,[],[f60,f94])).
% 0.22/0.53  fof(f60,plain,(
% 0.22/0.53    ( ! [X0] : (~l1_struct_0(X0) | k1_xboole_0 = k1_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f19])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ! [X0] : (k1_xboole_0 = k1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f8])).
% 0.22/0.53  fof(f8,axiom,(
% 0.22/0.53    ! [X0] : (l1_struct_0(X0) => k1_xboole_0 = k1_struct_0(X0))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_struct_0)).
% 0.22/0.53  fof(f143,plain,(
% 0.22/0.53    u1_struct_0(sK2) = k1_orders_2(sK2,k1_struct_0(sK2))),
% 0.22/0.53    inference(subsumption_resolution,[],[f142,f52])).
% 0.22/0.53  fof(f142,plain,(
% 0.22/0.53    u1_struct_0(sK2) = k1_orders_2(sK2,k1_struct_0(sK2)) | v2_struct_0(sK2)),
% 0.22/0.53    inference(subsumption_resolution,[],[f141,f53])).
% 0.22/0.53  fof(f141,plain,(
% 0.22/0.53    u1_struct_0(sK2) = k1_orders_2(sK2,k1_struct_0(sK2)) | ~v3_orders_2(sK2) | v2_struct_0(sK2)),
% 0.22/0.53    inference(subsumption_resolution,[],[f140,f54])).
% 0.22/0.53  fof(f140,plain,(
% 0.22/0.53    u1_struct_0(sK2) = k1_orders_2(sK2,k1_struct_0(sK2)) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | v2_struct_0(sK2)),
% 0.22/0.53    inference(subsumption_resolution,[],[f139,f56])).
% 0.22/0.53  fof(f139,plain,(
% 0.22/0.53    ~l1_orders_2(sK2) | u1_struct_0(sK2) = k1_orders_2(sK2,k1_struct_0(sK2)) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | v2_struct_0(sK2)),
% 0.22/0.53    inference(resolution,[],[f66,f55])).
% 0.22/0.53  fof(f66,plain,(
% 0.22/0.53    ( ! [X0] : (~v5_orders_2(X0) | ~l1_orders_2(X0) | u1_struct_0(X0) = k1_orders_2(X0,k1_struct_0(X0)) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f24])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    ! [X0] : (u1_struct_0(X0) = k1_orders_2(X0,k1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f23])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ! [X0] : (u1_struct_0(X0) = k1_orders_2(X0,k1_struct_0(X0)) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f14])).
% 0.22/0.53  fof(f14,axiom,(
% 0.22/0.53    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => u1_struct_0(X0) = k1_orders_2(X0,k1_struct_0(X0)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_orders_2)).
% 0.22/0.53  fof(f201,plain,(
% 0.22/0.53    k1_orders_2(sK2,k1_xboole_0) = a_2_0_orders_2(sK2,k1_xboole_0)),
% 0.22/0.53    inference(resolution,[],[f200,f59])).
% 0.22/0.53  fof(f59,plain,(
% 0.22/0.53    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.22/0.53  fof(f179,plain,(
% 0.22/0.53    ( ! [X0] : (~sP0(sK2,k1_xboole_0,X0) | r2_hidden(X0,a_2_0_orders_2(sK2,k1_xboole_0))) )),
% 0.22/0.53    inference(resolution,[],[f176,f78])).
% 0.22/0.53  fof(f78,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | ~sP0(X2,X1,X0) | r2_hidden(X0,a_2_0_orders_2(X2,X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f46])).
% 0.22/0.53  fof(f176,plain,(
% 0.22/0.53    ( ! [X0] : (sP1(X0,k1_xboole_0,sK2)) )),
% 0.22/0.53    inference(resolution,[],[f175,f59])).
% 0.22/0.53  fof(f282,plain,(
% 0.22/0.53    sP0(sK2,k1_xboole_0,sK3(k1_orders_2(sK2,k2_struct_0(sK2))))),
% 0.22/0.53    inference(resolution,[],[f273,f58])).
% 0.22/0.53  fof(f58,plain,(
% 0.22/0.53    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.53  fof(f273,plain,(
% 0.22/0.53    ( ! [X2] : (~r1_tarski(X2,sK4(sK2,X2,sK3(k1_orders_2(sK2,k2_struct_0(sK2))))) | sP0(sK2,X2,sK3(k1_orders_2(sK2,k2_struct_0(sK2))))) )),
% 0.22/0.53    inference(resolution,[],[f239,f76])).
% 0.22/0.53  fof(f76,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f28])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.22/0.53  fof(f239,plain,(
% 0.22/0.53    ( ! [X0] : (r2_hidden(sK4(sK2,X0,sK3(k1_orders_2(sK2,k2_struct_0(sK2)))),X0) | sP0(sK2,X0,sK3(k1_orders_2(sK2,k2_struct_0(sK2))))) )),
% 0.22/0.53    inference(resolution,[],[f237,f132])).
% 0.22/0.53  fof(f132,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,k2_struct_0(sK2)) | r2_hidden(sK4(sK2,X1,X0),X1) | sP0(sK2,X1,X0)) )),
% 0.22/0.53    inference(superposition,[],[f91,f96])).
% 0.22/0.53  fof(f91,plain,(
% 0.22/0.53    ( ! [X0,X3,X1] : (~m1_subset_1(X3,u1_struct_0(X0)) | r2_hidden(sK4(X0,X1,X3),X1) | sP0(X0,X1,X3)) )),
% 0.22/0.53    inference(equality_resolution,[],[f83])).
% 0.22/0.53  fof(f83,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (sP0(X0,X1,X2) | r2_hidden(sK4(X0,X1,X3),X1) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f51])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (28414)------------------------------
% 0.22/0.53  % (28414)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (28414)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (28414)Memory used [KB]: 6396
% 0.22/0.53  % (28414)Time elapsed: 0.112 s
% 0.22/0.53  % (28414)------------------------------
% 0.22/0.53  % (28414)------------------------------
% 0.22/0.54  % (28410)Success in time 0.173 s
%------------------------------------------------------------------------------
