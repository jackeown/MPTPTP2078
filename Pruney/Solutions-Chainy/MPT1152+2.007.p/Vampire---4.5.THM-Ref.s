%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:48 EST 2020

% Result     : Theorem 1.66s
% Output     : Refutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :  118 (1807 expanded)
%              Number of leaves         :   19 ( 456 expanded)
%              Depth                    :   26
%              Number of atoms          :  457 (8825 expanded)
%              Number of equality atoms :   56 (1247 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f347,plain,(
    $false ),
    inference(subsumption_resolution,[],[f346,f315])).

fof(f315,plain,(
    m1_subset_1(sK3(k2_orders_2(sK2,k2_struct_0(sK2))),k2_struct_0(sK2)) ),
    inference(backward_demodulation,[],[f314,f311])).

fof(f311,plain,(
    sK3(k2_orders_2(sK2,k2_struct_0(sK2))) = sK6(sK2,k2_struct_0(sK2),sK3(k2_orders_2(sK2,k2_struct_0(sK2)))) ),
    inference(resolution,[],[f297,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | sK6(X0,X1,X2) = X2 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3] :
            ( ( ~ r2_orders_2(X0,X3,sK5(X0,X1,X3))
              & r2_hidden(sK5(X0,X1,X3),X1)
              & m1_subset_1(sK5(X0,X1,X3),u1_struct_0(X0)) )
            | X2 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ( ! [X6] :
              ( r2_orders_2(X0,sK6(X0,X1,X2),X6)
              | ~ r2_hidden(X6,X1)
              | ~ m1_subset_1(X6,u1_struct_0(X0)) )
          & sK6(X0,X1,X2) = X2
          & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f48,f50,f49])).

fof(f49,plain,(
    ! [X3,X1,X0] :
      ( ? [X4] :
          ( ~ r2_orders_2(X0,X3,X4)
          & r2_hidden(X4,X1)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r2_orders_2(X0,X3,sK5(X0,X1,X3))
        & r2_hidden(sK5(X0,X1,X3),X1)
        & m1_subset_1(sK5(X0,X1,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r2_orders_2(X0,X5,X6)
              | ~ r2_hidden(X6,X1)
              | ~ m1_subset_1(X6,u1_struct_0(X0)) )
          & X2 = X5
          & m1_subset_1(X5,u1_struct_0(X0)) )
     => ( ! [X6] :
            ( r2_orders_2(X0,sK6(X0,X1,X2),X6)
            | ~ r2_hidden(X6,X1)
            | ~ m1_subset_1(X6,u1_struct_0(X0)) )
        & sK6(X0,X1,X2) = X2
        & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3] :
            ( ? [X4] :
                ( ~ r2_orders_2(X0,X3,X4)
                & r2_hidden(X4,X1)
                & m1_subset_1(X4,u1_struct_0(X0)) )
            | X2 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ? [X5] :
            ( ! [X6] :
                ( r2_orders_2(X0,X5,X6)
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
                ( ~ r2_orders_2(X1,X3,X4)
                & r2_hidden(X4,X2)
                & m1_subset_1(X4,u1_struct_0(X1)) )
            | X0 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ? [X3] :
            ( ! [X4] :
                ( r2_orders_2(X1,X3,X4)
                | ~ r2_hidden(X4,X2)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) )
        | ~ sP0(X1,X2,X0) ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X1,X2,X0] :
      ( sP0(X1,X2,X0)
    <=> ? [X3] :
          ( ! [X4] :
              ( r2_orders_2(X1,X3,X4)
              | ~ r2_hidden(X4,X2)
              | ~ m1_subset_1(X4,u1_struct_0(X1)) )
          & X0 = X3
          & m1_subset_1(X3,u1_struct_0(X1)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f297,plain,(
    sP0(sK2,k2_struct_0(sK2),sK3(k2_orders_2(sK2,k2_struct_0(sK2)))) ),
    inference(subsumption_resolution,[],[f296,f57])).

fof(f57,plain,(
    k1_xboole_0 != k2_orders_2(sK2,k2_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( k1_xboole_0 != k2_orders_2(sK2,k2_struct_0(sK2))
    & l1_orders_2(sK2)
    & v5_orders_2(sK2)
    & v4_orders_2(sK2)
    & v3_orders_2(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f34])).

fof(f34,plain,
    ( ? [X0] :
        ( k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( k1_xboole_0 != k2_orders_2(sK2,k2_struct_0(sK2))
      & l1_orders_2(sK2)
      & v5_orders_2(sK2)
      & v4_orders_2(sK2)
      & v3_orders_2(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_orders_2)).

fof(f296,plain,
    ( k1_xboole_0 = k2_orders_2(sK2,k2_struct_0(sK2))
    | sP0(sK2,k2_struct_0(sK2),sK3(k2_orders_2(sK2,k2_struct_0(sK2)))) ),
    inference(forward_demodulation,[],[f288,f278])).

fof(f278,plain,(
    k2_orders_2(sK2,k2_struct_0(sK2)) = a_2_1_orders_2(sK2,k2_struct_0(sK2)) ),
    inference(resolution,[],[f258,f96])).

fof(f96,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(resolution,[],[f95,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
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

fof(f95,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f94])).

fof(f94,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f71,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f41,f42])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
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

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f258,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2)))
      | k2_orders_2(sK2,X0) = a_2_1_orders_2(sK2,X0) ) ),
    inference(forward_demodulation,[],[f257,f90])).

fof(f90,plain,(
    k2_struct_0(sK2) = u1_struct_0(sK2) ),
    inference(resolution,[],[f58,f89])).

fof(f89,plain,(
    l1_struct_0(sK2) ),
    inference(resolution,[],[f59,f56])).

fof(f56,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f59,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f58,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f257,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | k2_orders_2(sK2,X0) = a_2_1_orders_2(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f256,f52])).

fof(f52,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f256,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | k2_orders_2(sK2,X0) = a_2_1_orders_2(sK2,X0)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f255,f53])).

fof(f53,plain,(
    v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f255,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | k2_orders_2(sK2,X0) = a_2_1_orders_2(sK2,X0)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f254,f54])).

fof(f54,plain,(
    v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f254,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | k2_orders_2(sK2,X0) = a_2_1_orders_2(sK2,X0)
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f253,f56])).

fof(f253,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_orders_2(sK2)
      | k2_orders_2(sK2,X0) = a_2_1_orders_2(sK2,X0)
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f63,f55])).

fof(f55,plain,(
    v5_orders_2(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_orders_2)).

fof(f288,plain,
    ( sP0(sK2,k2_struct_0(sK2),sK3(k2_orders_2(sK2,k2_struct_0(sK2))))
    | k1_xboole_0 = a_2_1_orders_2(sK2,k2_struct_0(sK2)) ),
    inference(backward_demodulation,[],[f270,f278])).

fof(f270,plain,
    ( sP0(sK2,k2_struct_0(sK2),sK3(a_2_1_orders_2(sK2,k2_struct_0(sK2))))
    | k1_xboole_0 = a_2_1_orders_2(sK2,k2_struct_0(sK2)) ),
    inference(resolution,[],[f260,f65])).

fof(f65,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4] :
            ( k3_mcart_1(X2,X3,X4) != sK3(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK3(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f23,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X4,X3,X2] :
            ( k3_mcart_1(X2,X3,X4) != sK3(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK3(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4] :
                  ~ ( k3_mcart_1(X2,X3,X4) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).

fof(f260,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,a_2_1_orders_2(sK2,k2_struct_0(sK2)))
      | sP0(sK2,k2_struct_0(sK2),X1) ) ),
    inference(resolution,[],[f245,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ r2_hidden(X0,a_2_1_orders_2(X2,X1))
      | sP0(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_orders_2(X2,X1))
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | ~ r2_hidden(X0,a_2_1_orders_2(X2,X1)) ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X0,X2,X1] :
      ( ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
          | ~ sP0(X1,X2,X0) )
        & ( sP0(X1,X2,X0)
          | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2)) ) )
      | ~ sP1(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X2,X1] :
      ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      <=> sP0(X1,X2,X0) )
      | ~ sP1(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f245,plain,(
    ! [X0] : sP1(X0,k2_struct_0(sK2),sK2) ),
    inference(resolution,[],[f244,f96])).

fof(f244,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2)))
      | sP1(X1,X0,sK2) ) ),
    inference(forward_demodulation,[],[f243,f90])).

fof(f243,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | sP1(X1,X0,sK2) ) ),
    inference(subsumption_resolution,[],[f242,f52])).

fof(f242,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | sP1(X1,X0,sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f241,f53])).

fof(f241,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | sP1(X1,X0,sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f240,f54])).

fof(f240,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | sP1(X1,X0,sK2)
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f239,f56])).

fof(f239,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_orders_2(sK2)
      | sP1(X1,X0,sK2)
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f82,f55])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | sP1(X0,X2,X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( sP1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(definition_folding,[],[f28,f32,f31])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( r2_orders_2(X1,X3,X4)
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
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( r2_orders_2(X1,X3,X4)
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & l1_orders_2(X1)
        & v5_orders_2(X1)
        & v4_orders_2(X1)
        & v3_orders_2(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r2_hidden(X4,X2)
                 => r2_orders_2(X1,X3,X4) ) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_1_orders_2)).

fof(f314,plain,(
    m1_subset_1(sK6(sK2,k2_struct_0(sK2),sK3(k2_orders_2(sK2,k2_struct_0(sK2)))),k2_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f310,f90])).

fof(f310,plain,(
    m1_subset_1(sK6(sK2,k2_struct_0(sK2),sK3(k2_orders_2(sK2,k2_struct_0(sK2)))),u1_struct_0(sK2)) ),
    inference(resolution,[],[f297,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f346,plain,(
    ~ m1_subset_1(sK3(k2_orders_2(sK2,k2_struct_0(sK2))),k2_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f345,f90])).

fof(f345,plain,(
    ~ m1_subset_1(sK3(k2_orders_2(sK2,k2_struct_0(sK2))),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f344,f56])).

fof(f344,plain,
    ( ~ m1_subset_1(sK3(k2_orders_2(sK2,k2_struct_0(sK2))),u1_struct_0(sK2))
    | ~ l1_orders_2(sK2) ),
    inference(subsumption_resolution,[],[f342,f320])).

fof(f320,plain,(
    r2_hidden(sK3(k2_orders_2(sK2,k2_struct_0(sK2))),k2_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f319,f93])).

fof(f93,plain,(
    ~ v1_xboole_0(k2_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f92,f52])).

fof(f92,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK2))
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f91,f89])).

fof(f91,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK2))
    | ~ l1_struct_0(sK2)
    | v2_struct_0(sK2) ),
    inference(superposition,[],[f64,f90])).

fof(f64,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f319,plain,
    ( v1_xboole_0(k2_struct_0(sK2))
    | r2_hidden(sK3(k2_orders_2(sK2,k2_struct_0(sK2))),k2_struct_0(sK2)) ),
    inference(resolution,[],[f315,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f342,plain,
    ( ~ r2_hidden(sK3(k2_orders_2(sK2,k2_struct_0(sK2))),k2_struct_0(sK2))
    | ~ m1_subset_1(sK3(k2_orders_2(sK2,k2_struct_0(sK2))),u1_struct_0(sK2))
    | ~ l1_orders_2(sK2) ),
    inference(resolution,[],[f316,f88])).

fof(f88,plain,(
    ! [X2,X0] :
      ( ~ r2_orders_2(X0,X2,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f84])).

fof(f84,plain,(
    ! [X2,X0] :
      ( ~ r2_orders_2(X0,X2,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( X1 != X2
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f316,plain,(
    ! [X0] :
      ( r2_orders_2(sK2,sK3(k2_orders_2(sK2,k2_struct_0(sK2))),X0)
      | ~ r2_hidden(X0,k2_struct_0(sK2)) ) ),
    inference(backward_demodulation,[],[f313,f311])).

fof(f313,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_struct_0(sK2))
      | r2_orders_2(sK2,sK6(sK2,k2_struct_0(sK2),sK3(k2_orders_2(sK2,k2_struct_0(sK2)))),X0) ) ),
    inference(subsumption_resolution,[],[f312,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f83,f96])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f312,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k2_struct_0(sK2))
      | ~ r2_hidden(X0,k2_struct_0(sK2))
      | r2_orders_2(sK2,sK6(sK2,k2_struct_0(sK2),sK3(k2_orders_2(sK2,k2_struct_0(sK2)))),X0) ) ),
    inference(forward_demodulation,[],[f309,f90])).

fof(f309,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_struct_0(sK2))
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | r2_orders_2(sK2,sK6(sK2,k2_struct_0(sK2),sK3(k2_orders_2(sK2,k2_struct_0(sK2)))),X0) ) ),
    inference(resolution,[],[f297,f78])).

fof(f78,plain,(
    ! [X6,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X6,X1)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | r2_orders_2(X0,sK6(X0,X1,X2),X6) ) ),
    inference(cnf_transformation,[],[f51])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:32:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (28029)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.53  % (28020)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.53  % (28042)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.54  % (28025)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.54  % (28034)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.54  % (28021)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (28023)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (28042)Refutation not found, incomplete strategy% (28042)------------------------------
% 0.22/0.54  % (28042)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (28042)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (28042)Memory used [KB]: 10746
% 0.22/0.54  % (28042)Time elapsed: 0.090 s
% 0.22/0.54  % (28042)------------------------------
% 0.22/0.54  % (28042)------------------------------
% 0.22/0.54  % (28026)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.54  % (28022)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (28041)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.54  % (28030)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.55  % (28024)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.55  % (28030)Refutation not found, incomplete strategy% (28030)------------------------------
% 0.22/0.55  % (28030)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (28030)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (28030)Memory used [KB]: 10618
% 0.22/0.55  % (28030)Time elapsed: 0.124 s
% 0.22/0.55  % (28030)------------------------------
% 0.22/0.55  % (28030)------------------------------
% 0.22/0.55  % (28041)Refutation not found, incomplete strategy% (28041)------------------------------
% 0.22/0.55  % (28041)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (28041)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (28041)Memory used [KB]: 1791
% 0.22/0.55  % (28041)Time elapsed: 0.129 s
% 0.22/0.55  % (28041)------------------------------
% 0.22/0.55  % (28041)------------------------------
% 0.22/0.55  % (28024)Refutation not found, incomplete strategy% (28024)------------------------------
% 0.22/0.55  % (28024)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (28024)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (28024)Memory used [KB]: 6268
% 0.22/0.55  % (28024)Time elapsed: 0.123 s
% 0.22/0.55  % (28024)------------------------------
% 0.22/0.55  % (28024)------------------------------
% 0.22/0.55  % (28039)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.55  % (28049)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.55  % (28040)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.56  % (28028)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.56  % (28033)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.56  % (28043)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.56  % (28031)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.56  % (28046)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.47/0.56  % (28048)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.47/0.56  % (28031)Refutation not found, incomplete strategy% (28031)------------------------------
% 1.47/0.56  % (28031)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.56  % (28031)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.56  
% 1.47/0.56  % (28031)Memory used [KB]: 10618
% 1.47/0.56  % (28031)Time elapsed: 0.139 s
% 1.47/0.56  % (28031)------------------------------
% 1.47/0.56  % (28031)------------------------------
% 1.47/0.56  % (28047)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.47/0.56  % (28046)Refutation not found, incomplete strategy% (28046)------------------------------
% 1.47/0.56  % (28046)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.56  % (28046)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.56  
% 1.47/0.56  % (28046)Memory used [KB]: 10746
% 1.47/0.56  % (28046)Time elapsed: 0.140 s
% 1.47/0.56  % (28046)------------------------------
% 1.47/0.56  % (28046)------------------------------
% 1.47/0.56  % (28035)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.47/0.56  % (28032)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.47/0.57  % (28027)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.47/0.57  % (28038)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.47/0.57  % (28036)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.47/0.57  % (28044)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.47/0.58  % (28037)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.47/0.58  % (28040)Refutation not found, incomplete strategy% (28040)------------------------------
% 1.47/0.58  % (28040)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.58  % (28040)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.58  
% 1.47/0.58  % (28040)Memory used [KB]: 10746
% 1.47/0.58  % (28040)Time elapsed: 0.140 s
% 1.47/0.58  % (28040)------------------------------
% 1.47/0.58  % (28040)------------------------------
% 1.47/0.58  % (28037)Refutation not found, incomplete strategy% (28037)------------------------------
% 1.47/0.58  % (28037)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.58  % (28045)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.66/0.58  % (28037)Termination reason: Refutation not found, incomplete strategy
% 1.66/0.58  
% 1.66/0.58  % (28037)Memory used [KB]: 10618
% 1.66/0.58  % (28037)Time elapsed: 0.148 s
% 1.66/0.58  % (28037)------------------------------
% 1.66/0.58  % (28037)------------------------------
% 1.66/0.59  % (28027)Refutation found. Thanks to Tanya!
% 1.66/0.59  % SZS status Theorem for theBenchmark
% 1.66/0.61  % SZS output start Proof for theBenchmark
% 1.66/0.61  fof(f347,plain,(
% 1.66/0.61    $false),
% 1.66/0.61    inference(subsumption_resolution,[],[f346,f315])).
% 1.66/0.61  fof(f315,plain,(
% 1.66/0.61    m1_subset_1(sK3(k2_orders_2(sK2,k2_struct_0(sK2))),k2_struct_0(sK2))),
% 1.66/0.61    inference(backward_demodulation,[],[f314,f311])).
% 1.66/0.61  fof(f311,plain,(
% 1.66/0.61    sK3(k2_orders_2(sK2,k2_struct_0(sK2))) = sK6(sK2,k2_struct_0(sK2),sK3(k2_orders_2(sK2,k2_struct_0(sK2))))),
% 1.66/0.61    inference(resolution,[],[f297,f77])).
% 1.66/0.61  fof(f77,plain,(
% 1.66/0.61    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | sK6(X0,X1,X2) = X2) )),
% 1.66/0.61    inference(cnf_transformation,[],[f51])).
% 1.66/0.61  fof(f51,plain,(
% 1.66/0.61    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3] : ((~r2_orders_2(X0,X3,sK5(X0,X1,X3)) & r2_hidden(sK5(X0,X1,X3),X1) & m1_subset_1(sK5(X0,X1,X3),u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)))) & ((! [X6] : (r2_orders_2(X0,sK6(X0,X1,X2),X6) | ~r2_hidden(X6,X1) | ~m1_subset_1(X6,u1_struct_0(X0))) & sK6(X0,X1,X2) = X2 & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))) | ~sP0(X0,X1,X2)))),
% 1.66/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f48,f50,f49])).
% 1.66/0.61  fof(f49,plain,(
% 1.66/0.61    ! [X3,X1,X0] : (? [X4] : (~r2_orders_2(X0,X3,X4) & r2_hidden(X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) => (~r2_orders_2(X0,X3,sK5(X0,X1,X3)) & r2_hidden(sK5(X0,X1,X3),X1) & m1_subset_1(sK5(X0,X1,X3),u1_struct_0(X0))))),
% 1.66/0.61    introduced(choice_axiom,[])).
% 1.66/0.61  fof(f50,plain,(
% 1.66/0.61    ! [X2,X1,X0] : (? [X5] : (! [X6] : (r2_orders_2(X0,X5,X6) | ~r2_hidden(X6,X1) | ~m1_subset_1(X6,u1_struct_0(X0))) & X2 = X5 & m1_subset_1(X5,u1_struct_0(X0))) => (! [X6] : (r2_orders_2(X0,sK6(X0,X1,X2),X6) | ~r2_hidden(X6,X1) | ~m1_subset_1(X6,u1_struct_0(X0))) & sK6(X0,X1,X2) = X2 & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))))),
% 1.66/0.61    introduced(choice_axiom,[])).
% 1.66/0.61  fof(f48,plain,(
% 1.66/0.61    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3] : (? [X4] : (~r2_orders_2(X0,X3,X4) & r2_hidden(X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)))) & (? [X5] : (! [X6] : (r2_orders_2(X0,X5,X6) | ~r2_hidden(X6,X1) | ~m1_subset_1(X6,u1_struct_0(X0))) & X2 = X5 & m1_subset_1(X5,u1_struct_0(X0))) | ~sP0(X0,X1,X2)))),
% 1.66/0.61    inference(rectify,[],[f47])).
% 1.66/0.61  fof(f47,plain,(
% 1.66/0.61    ! [X1,X2,X0] : ((sP0(X1,X2,X0) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~sP0(X1,X2,X0)))),
% 1.66/0.61    inference(nnf_transformation,[],[f31])).
% 1.66/0.61  fof(f31,plain,(
% 1.66/0.61    ! [X1,X2,X0] : (sP0(X1,X2,X0) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))))),
% 1.66/0.61    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.66/0.61  fof(f297,plain,(
% 1.66/0.61    sP0(sK2,k2_struct_0(sK2),sK3(k2_orders_2(sK2,k2_struct_0(sK2))))),
% 1.66/0.61    inference(subsumption_resolution,[],[f296,f57])).
% 1.66/0.61  fof(f57,plain,(
% 1.66/0.61    k1_xboole_0 != k2_orders_2(sK2,k2_struct_0(sK2))),
% 1.66/0.61    inference(cnf_transformation,[],[f35])).
% 1.66/0.61  fof(f35,plain,(
% 1.66/0.61    k1_xboole_0 != k2_orders_2(sK2,k2_struct_0(sK2)) & l1_orders_2(sK2) & v5_orders_2(sK2) & v4_orders_2(sK2) & v3_orders_2(sK2) & ~v2_struct_0(sK2)),
% 1.66/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f34])).
% 1.66/0.61  fof(f34,plain,(
% 1.66/0.61    ? [X0] : (k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (k1_xboole_0 != k2_orders_2(sK2,k2_struct_0(sK2)) & l1_orders_2(sK2) & v5_orders_2(sK2) & v4_orders_2(sK2) & v3_orders_2(sK2) & ~v2_struct_0(sK2))),
% 1.66/0.61    introduced(choice_axiom,[])).
% 1.66/0.61  fof(f15,plain,(
% 1.66/0.61    ? [X0] : (k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.66/0.61    inference(flattening,[],[f14])).
% 1.66/0.61  fof(f14,plain,(
% 1.66/0.61    ? [X0] : (k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0)) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 1.66/0.61    inference(ennf_transformation,[],[f13])).
% 1.66/0.61  fof(f13,negated_conjecture,(
% 1.66/0.61    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)))),
% 1.66/0.61    inference(negated_conjecture,[],[f12])).
% 1.66/0.61  fof(f12,conjecture,(
% 1.66/0.61    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)))),
% 1.66/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_orders_2)).
% 1.66/0.61  fof(f296,plain,(
% 1.66/0.61    k1_xboole_0 = k2_orders_2(sK2,k2_struct_0(sK2)) | sP0(sK2,k2_struct_0(sK2),sK3(k2_orders_2(sK2,k2_struct_0(sK2))))),
% 1.66/0.61    inference(forward_demodulation,[],[f288,f278])).
% 1.66/0.61  fof(f278,plain,(
% 1.66/0.61    k2_orders_2(sK2,k2_struct_0(sK2)) = a_2_1_orders_2(sK2,k2_struct_0(sK2))),
% 1.66/0.61    inference(resolution,[],[f258,f96])).
% 1.66/0.61  fof(f96,plain,(
% 1.66/0.61    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 1.66/0.61    inference(resolution,[],[f95,f73])).
% 1.66/0.61  fof(f73,plain,(
% 1.66/0.61    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.66/0.61    inference(cnf_transformation,[],[f44])).
% 1.66/0.61  fof(f44,plain,(
% 1.66/0.61    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.66/0.61    inference(nnf_transformation,[],[f3])).
% 1.66/0.61  fof(f3,axiom,(
% 1.66/0.61    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.66/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.66/0.61  fof(f95,plain,(
% 1.66/0.61    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 1.66/0.61    inference(duplicate_literal_removal,[],[f94])).
% 1.66/0.61  fof(f94,plain,(
% 1.66/0.61    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 1.66/0.61    inference(resolution,[],[f71,f70])).
% 1.66/0.61  fof(f70,plain,(
% 1.66/0.61    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.66/0.61    inference(cnf_transformation,[],[f43])).
% 1.66/0.61  fof(f43,plain,(
% 1.66/0.61    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.66/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f41,f42])).
% 1.66/0.61  fof(f42,plain,(
% 1.66/0.61    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 1.66/0.61    introduced(choice_axiom,[])).
% 1.66/0.61  fof(f41,plain,(
% 1.66/0.61    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.66/0.61    inference(rectify,[],[f40])).
% 1.66/0.61  fof(f40,plain,(
% 1.66/0.61    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.66/0.61    inference(nnf_transformation,[],[f26])).
% 1.66/0.61  fof(f26,plain,(
% 1.66/0.61    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.66/0.61    inference(ennf_transformation,[],[f1])).
% 1.66/0.61  fof(f1,axiom,(
% 1.66/0.61    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.66/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.66/0.61  fof(f71,plain,(
% 1.66/0.61    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.66/0.61    inference(cnf_transformation,[],[f43])).
% 1.66/0.61  fof(f258,plain,(
% 1.66/0.61    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) | k2_orders_2(sK2,X0) = a_2_1_orders_2(sK2,X0)) )),
% 1.66/0.61    inference(forward_demodulation,[],[f257,f90])).
% 1.66/0.61  fof(f90,plain,(
% 1.66/0.61    k2_struct_0(sK2) = u1_struct_0(sK2)),
% 1.66/0.61    inference(resolution,[],[f58,f89])).
% 1.66/0.61  fof(f89,plain,(
% 1.66/0.61    l1_struct_0(sK2)),
% 1.66/0.61    inference(resolution,[],[f59,f56])).
% 1.66/0.61  fof(f56,plain,(
% 1.66/0.61    l1_orders_2(sK2)),
% 1.66/0.61    inference(cnf_transformation,[],[f35])).
% 1.66/0.61  fof(f59,plain,(
% 1.66/0.61    ( ! [X0] : (~l1_orders_2(X0) | l1_struct_0(X0)) )),
% 1.66/0.61    inference(cnf_transformation,[],[f17])).
% 1.66/0.61  fof(f17,plain,(
% 1.66/0.61    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 1.66/0.61    inference(ennf_transformation,[],[f10])).
% 1.66/0.61  fof(f10,axiom,(
% 1.66/0.61    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 1.66/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 1.66/0.61  fof(f58,plain,(
% 1.66/0.61    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 1.66/0.61    inference(cnf_transformation,[],[f16])).
% 1.66/0.61  fof(f16,plain,(
% 1.66/0.61    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.66/0.61    inference(ennf_transformation,[],[f6])).
% 1.66/0.61  fof(f6,axiom,(
% 1.66/0.61    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.66/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 1.66/0.61  fof(f257,plain,(
% 1.66/0.61    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | k2_orders_2(sK2,X0) = a_2_1_orders_2(sK2,X0)) )),
% 1.66/0.61    inference(subsumption_resolution,[],[f256,f52])).
% 1.66/0.61  fof(f52,plain,(
% 1.66/0.61    ~v2_struct_0(sK2)),
% 1.66/0.61    inference(cnf_transformation,[],[f35])).
% 1.66/0.61  fof(f256,plain,(
% 1.66/0.61    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | k2_orders_2(sK2,X0) = a_2_1_orders_2(sK2,X0) | v2_struct_0(sK2)) )),
% 1.66/0.61    inference(subsumption_resolution,[],[f255,f53])).
% 1.66/0.61  fof(f53,plain,(
% 1.66/0.61    v3_orders_2(sK2)),
% 1.66/0.61    inference(cnf_transformation,[],[f35])).
% 1.66/0.61  fof(f255,plain,(
% 1.66/0.61    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | k2_orders_2(sK2,X0) = a_2_1_orders_2(sK2,X0) | ~v3_orders_2(sK2) | v2_struct_0(sK2)) )),
% 1.66/0.61    inference(subsumption_resolution,[],[f254,f54])).
% 1.66/0.61  fof(f54,plain,(
% 1.66/0.61    v4_orders_2(sK2)),
% 1.66/0.61    inference(cnf_transformation,[],[f35])).
% 1.66/0.61  fof(f254,plain,(
% 1.66/0.61    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | k2_orders_2(sK2,X0) = a_2_1_orders_2(sK2,X0) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | v2_struct_0(sK2)) )),
% 1.66/0.61    inference(subsumption_resolution,[],[f253,f56])).
% 1.66/0.61  fof(f253,plain,(
% 1.66/0.61    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_orders_2(sK2) | k2_orders_2(sK2,X0) = a_2_1_orders_2(sK2,X0) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | v2_struct_0(sK2)) )),
% 1.66/0.61    inference(resolution,[],[f63,f55])).
% 1.66/0.61  fof(f55,plain,(
% 1.66/0.61    v5_orders_2(sK2)),
% 1.66/0.61    inference(cnf_transformation,[],[f35])).
% 1.66/0.61  fof(f63,plain,(
% 1.66/0.61    ( ! [X0,X1] : (~v5_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.66/0.61    inference(cnf_transformation,[],[f20])).
% 1.66/0.61  fof(f20,plain,(
% 1.66/0.61    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.66/0.61    inference(flattening,[],[f19])).
% 1.66/0.61  fof(f19,plain,(
% 1.66/0.61    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.66/0.61    inference(ennf_transformation,[],[f9])).
% 1.66/0.61  fof(f9,axiom,(
% 1.66/0.61    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)))),
% 1.66/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_orders_2)).
% 1.66/0.61  fof(f288,plain,(
% 1.66/0.61    sP0(sK2,k2_struct_0(sK2),sK3(k2_orders_2(sK2,k2_struct_0(sK2)))) | k1_xboole_0 = a_2_1_orders_2(sK2,k2_struct_0(sK2))),
% 1.66/0.61    inference(backward_demodulation,[],[f270,f278])).
% 1.66/0.61  fof(f270,plain,(
% 1.66/0.61    sP0(sK2,k2_struct_0(sK2),sK3(a_2_1_orders_2(sK2,k2_struct_0(sK2)))) | k1_xboole_0 = a_2_1_orders_2(sK2,k2_struct_0(sK2))),
% 1.66/0.61    inference(resolution,[],[f260,f65])).
% 1.66/0.61  fof(f65,plain,(
% 1.66/0.61    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 1.66/0.61    inference(cnf_transformation,[],[f39])).
% 1.66/0.61  fof(f39,plain,(
% 1.66/0.61    ! [X0] : ((! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != sK3(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK3(X0),X0)) | k1_xboole_0 = X0)),
% 1.66/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f23,f38])).
% 1.66/0.61  fof(f38,plain,(
% 1.66/0.61    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X4,X3,X2] : (k3_mcart_1(X2,X3,X4) != sK3(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK3(X0),X0)))),
% 1.66/0.61    introduced(choice_axiom,[])).
% 1.66/0.61  fof(f23,plain,(
% 1.66/0.61    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 1.66/0.61    inference(ennf_transformation,[],[f5])).
% 1.66/0.61  fof(f5,axiom,(
% 1.66/0.61    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4] : ~(k3_mcart_1(X2,X3,X4) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 1.66/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).
% 1.66/0.61  fof(f260,plain,(
% 1.66/0.61    ( ! [X1] : (~r2_hidden(X1,a_2_1_orders_2(sK2,k2_struct_0(sK2))) | sP0(sK2,k2_struct_0(sK2),X1)) )),
% 1.66/0.61    inference(resolution,[],[f245,f74])).
% 1.66/0.61  fof(f74,plain,(
% 1.66/0.61    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | ~r2_hidden(X0,a_2_1_orders_2(X2,X1)) | sP0(X2,X1,X0)) )),
% 1.66/0.61    inference(cnf_transformation,[],[f46])).
% 1.66/0.61  fof(f46,plain,(
% 1.66/0.61    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X2,X1)) | ~sP0(X2,X1,X0)) & (sP0(X2,X1,X0) | ~r2_hidden(X0,a_2_1_orders_2(X2,X1)))) | ~sP1(X0,X1,X2))),
% 1.66/0.61    inference(rectify,[],[f45])).
% 1.66/0.61  fof(f45,plain,(
% 1.66/0.61    ! [X0,X2,X1] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ~sP0(X1,X2,X0)) & (sP0(X1,X2,X0) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~sP1(X0,X2,X1))),
% 1.66/0.61    inference(nnf_transformation,[],[f32])).
% 1.66/0.61  fof(f32,plain,(
% 1.66/0.61    ! [X0,X2,X1] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> sP0(X1,X2,X0)) | ~sP1(X0,X2,X1))),
% 1.66/0.61    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.66/0.61  fof(f245,plain,(
% 1.66/0.61    ( ! [X0] : (sP1(X0,k2_struct_0(sK2),sK2)) )),
% 1.66/0.61    inference(resolution,[],[f244,f96])).
% 1.66/0.61  fof(f244,plain,(
% 1.66/0.61    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) | sP1(X1,X0,sK2)) )),
% 1.66/0.61    inference(forward_demodulation,[],[f243,f90])).
% 1.66/0.61  fof(f243,plain,(
% 1.66/0.61    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | sP1(X1,X0,sK2)) )),
% 1.66/0.61    inference(subsumption_resolution,[],[f242,f52])).
% 1.66/0.61  fof(f242,plain,(
% 1.66/0.61    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | sP1(X1,X0,sK2) | v2_struct_0(sK2)) )),
% 1.66/0.61    inference(subsumption_resolution,[],[f241,f53])).
% 1.66/0.61  fof(f241,plain,(
% 1.66/0.61    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | sP1(X1,X0,sK2) | ~v3_orders_2(sK2) | v2_struct_0(sK2)) )),
% 1.66/0.61    inference(subsumption_resolution,[],[f240,f54])).
% 1.66/0.61  fof(f240,plain,(
% 1.66/0.61    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | sP1(X1,X0,sK2) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | v2_struct_0(sK2)) )),
% 1.66/0.61    inference(subsumption_resolution,[],[f239,f56])).
% 1.66/0.61  fof(f239,plain,(
% 1.66/0.61    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_orders_2(sK2) | sP1(X1,X0,sK2) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | v2_struct_0(sK2)) )),
% 1.66/0.61    inference(resolution,[],[f82,f55])).
% 1.66/0.61  fof(f82,plain,(
% 1.66/0.61    ( ! [X2,X0,X1] : (~v5_orders_2(X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | sP1(X0,X2,X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 1.66/0.61    inference(cnf_transformation,[],[f33])).
% 1.66/0.61  fof(f33,plain,(
% 1.66/0.61    ! [X0,X1,X2] : (sP1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 1.66/0.61    inference(definition_folding,[],[f28,f32,f31])).
% 1.66/0.61  fof(f28,plain,(
% 1.66/0.61    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 1.66/0.61    inference(flattening,[],[f27])).
% 1.66/0.61  fof(f27,plain,(
% 1.66/0.61    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : ((r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)))),
% 1.66/0.61    inference(ennf_transformation,[],[f11])).
% 1.66/0.61  fof(f11,axiom,(
% 1.66/0.61    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) & l1_orders_2(X1) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r2_hidden(X4,X2) => r2_orders_2(X1,X3,X4))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 1.66/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_1_orders_2)).
% 1.66/0.61  fof(f314,plain,(
% 1.66/0.61    m1_subset_1(sK6(sK2,k2_struct_0(sK2),sK3(k2_orders_2(sK2,k2_struct_0(sK2)))),k2_struct_0(sK2))),
% 1.66/0.61    inference(forward_demodulation,[],[f310,f90])).
% 1.66/0.61  fof(f310,plain,(
% 1.66/0.61    m1_subset_1(sK6(sK2,k2_struct_0(sK2),sK3(k2_orders_2(sK2,k2_struct_0(sK2)))),u1_struct_0(sK2))),
% 1.66/0.61    inference(resolution,[],[f297,f76])).
% 1.66/0.61  fof(f76,plain,(
% 1.66/0.61    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))) )),
% 1.66/0.61    inference(cnf_transformation,[],[f51])).
% 1.66/0.61  fof(f346,plain,(
% 1.66/0.61    ~m1_subset_1(sK3(k2_orders_2(sK2,k2_struct_0(sK2))),k2_struct_0(sK2))),
% 1.66/0.61    inference(forward_demodulation,[],[f345,f90])).
% 1.66/0.61  fof(f345,plain,(
% 1.66/0.61    ~m1_subset_1(sK3(k2_orders_2(sK2,k2_struct_0(sK2))),u1_struct_0(sK2))),
% 1.66/0.61    inference(subsumption_resolution,[],[f344,f56])).
% 1.66/0.61  fof(f344,plain,(
% 1.66/0.61    ~m1_subset_1(sK3(k2_orders_2(sK2,k2_struct_0(sK2))),u1_struct_0(sK2)) | ~l1_orders_2(sK2)),
% 1.66/0.61    inference(subsumption_resolution,[],[f342,f320])).
% 1.66/0.61  fof(f320,plain,(
% 1.66/0.61    r2_hidden(sK3(k2_orders_2(sK2,k2_struct_0(sK2))),k2_struct_0(sK2))),
% 1.66/0.61    inference(subsumption_resolution,[],[f319,f93])).
% 1.66/0.61  fof(f93,plain,(
% 1.66/0.61    ~v1_xboole_0(k2_struct_0(sK2))),
% 1.66/0.61    inference(subsumption_resolution,[],[f92,f52])).
% 1.66/0.61  fof(f92,plain,(
% 1.66/0.61    ~v1_xboole_0(k2_struct_0(sK2)) | v2_struct_0(sK2)),
% 1.66/0.61    inference(subsumption_resolution,[],[f91,f89])).
% 1.66/0.61  fof(f91,plain,(
% 1.66/0.61    ~v1_xboole_0(k2_struct_0(sK2)) | ~l1_struct_0(sK2) | v2_struct_0(sK2)),
% 1.66/0.61    inference(superposition,[],[f64,f90])).
% 1.66/0.61  fof(f64,plain,(
% 1.66/0.61    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.66/0.61    inference(cnf_transformation,[],[f22])).
% 1.66/0.61  fof(f22,plain,(
% 1.66/0.61    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.66/0.61    inference(flattening,[],[f21])).
% 1.66/0.61  fof(f21,plain,(
% 1.66/0.61    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.66/0.61    inference(ennf_transformation,[],[f7])).
% 1.66/0.61  fof(f7,axiom,(
% 1.66/0.61    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.66/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 1.66/0.61  fof(f319,plain,(
% 1.66/0.61    v1_xboole_0(k2_struct_0(sK2)) | r2_hidden(sK3(k2_orders_2(sK2,k2_struct_0(sK2))),k2_struct_0(sK2))),
% 1.66/0.61    inference(resolution,[],[f315,f68])).
% 1.66/0.61  fof(f68,plain,(
% 1.66/0.61    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 1.66/0.61    inference(cnf_transformation,[],[f25])).
% 1.66/0.61  fof(f25,plain,(
% 1.66/0.61    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.66/0.61    inference(flattening,[],[f24])).
% 1.66/0.61  fof(f24,plain,(
% 1.66/0.61    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.66/0.61    inference(ennf_transformation,[],[f2])).
% 1.66/0.61  fof(f2,axiom,(
% 1.66/0.61    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.66/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 1.66/0.61  fof(f342,plain,(
% 1.66/0.61    ~r2_hidden(sK3(k2_orders_2(sK2,k2_struct_0(sK2))),k2_struct_0(sK2)) | ~m1_subset_1(sK3(k2_orders_2(sK2,k2_struct_0(sK2))),u1_struct_0(sK2)) | ~l1_orders_2(sK2)),
% 1.66/0.61    inference(resolution,[],[f316,f88])).
% 1.66/0.61  fof(f88,plain,(
% 1.66/0.61    ( ! [X2,X0] : (~r2_orders_2(X0,X2,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.66/0.61    inference(duplicate_literal_removal,[],[f84])).
% 1.66/0.61  fof(f84,plain,(
% 1.66/0.61    ( ! [X2,X0] : (~r2_orders_2(X0,X2,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.66/0.61    inference(equality_resolution,[],[f61])).
% 1.66/0.61  fof(f61,plain,(
% 1.66/0.61    ( ! [X2,X0,X1] : (X1 != X2 | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.66/0.61    inference(cnf_transformation,[],[f37])).
% 1.66/0.61  fof(f37,plain,(
% 1.66/0.61    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | X1 = X2 | ~r1_orders_2(X0,X1,X2)) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.66/0.61    inference(flattening,[],[f36])).
% 1.66/0.61  fof(f36,plain,(
% 1.66/0.61    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | (X1 = X2 | ~r1_orders_2(X0,X1,X2))) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.66/0.61    inference(nnf_transformation,[],[f18])).
% 1.66/0.61  fof(f18,plain,(
% 1.66/0.61    ! [X0] : (! [X1] : (! [X2] : ((r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.66/0.61    inference(ennf_transformation,[],[f8])).
% 1.66/0.61  fof(f8,axiom,(
% 1.66/0.61    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))))))),
% 1.66/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_orders_2)).
% 1.66/0.61  fof(f316,plain,(
% 1.66/0.61    ( ! [X0] : (r2_orders_2(sK2,sK3(k2_orders_2(sK2,k2_struct_0(sK2))),X0) | ~r2_hidden(X0,k2_struct_0(sK2))) )),
% 1.66/0.61    inference(backward_demodulation,[],[f313,f311])).
% 1.66/0.61  fof(f313,plain,(
% 1.66/0.61    ( ! [X0] : (~r2_hidden(X0,k2_struct_0(sK2)) | r2_orders_2(sK2,sK6(sK2,k2_struct_0(sK2),sK3(k2_orders_2(sK2,k2_struct_0(sK2)))),X0)) )),
% 1.66/0.61    inference(subsumption_resolution,[],[f312,f100])).
% 1.66/0.61  fof(f100,plain,(
% 1.66/0.61    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 1.66/0.61    inference(resolution,[],[f83,f96])).
% 1.66/0.61  fof(f83,plain,(
% 1.66/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 1.66/0.61    inference(cnf_transformation,[],[f30])).
% 1.66/0.61  fof(f30,plain,(
% 1.66/0.61    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.66/0.61    inference(flattening,[],[f29])).
% 1.66/0.61  fof(f29,plain,(
% 1.66/0.61    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 1.66/0.61    inference(ennf_transformation,[],[f4])).
% 1.66/0.61  fof(f4,axiom,(
% 1.66/0.61    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 1.66/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 1.66/0.61  fof(f312,plain,(
% 1.66/0.61    ( ! [X0] : (~m1_subset_1(X0,k2_struct_0(sK2)) | ~r2_hidden(X0,k2_struct_0(sK2)) | r2_orders_2(sK2,sK6(sK2,k2_struct_0(sK2),sK3(k2_orders_2(sK2,k2_struct_0(sK2)))),X0)) )),
% 1.66/0.61    inference(forward_demodulation,[],[f309,f90])).
% 1.66/0.61  fof(f309,plain,(
% 1.66/0.61    ( ! [X0] : (~r2_hidden(X0,k2_struct_0(sK2)) | ~m1_subset_1(X0,u1_struct_0(sK2)) | r2_orders_2(sK2,sK6(sK2,k2_struct_0(sK2),sK3(k2_orders_2(sK2,k2_struct_0(sK2)))),X0)) )),
% 1.66/0.61    inference(resolution,[],[f297,f78])).
% 1.66/0.61  fof(f78,plain,(
% 1.66/0.61    ( ! [X6,X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X6,X1) | ~m1_subset_1(X6,u1_struct_0(X0)) | r2_orders_2(X0,sK6(X0,X1,X2),X6)) )),
% 1.66/0.61    inference(cnf_transformation,[],[f51])).
% 1.66/0.61  % SZS output end Proof for theBenchmark
% 1.66/0.61  % (28027)------------------------------
% 1.66/0.61  % (28027)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.61  % (28027)Termination reason: Refutation
% 1.66/0.61  
% 1.66/0.61  % (28027)Memory used [KB]: 6652
% 1.66/0.61  % (28027)Time elapsed: 0.169 s
% 1.66/0.61  % (28027)------------------------------
% 1.66/0.61  % (28027)------------------------------
% 1.66/0.61  % (28019)Success in time 0.241 s
%------------------------------------------------------------------------------
