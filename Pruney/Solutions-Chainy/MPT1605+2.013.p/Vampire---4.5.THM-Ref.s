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
% DateTime   : Thu Dec  3 13:16:35 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 267 expanded)
%              Number of leaves         :   23 (  70 expanded)
%              Depth                    :   23
%              Number of atoms          :  559 ( 945 expanded)
%              Number of equality atoms :   16 (  73 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f548,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f521,f475,f112])).

fof(f112,plain,(
    ! [X0] :
      ( ~ sP0(k2_yellow_1(X0))
      | v1_yellow_0(k2_yellow_1(X0)) ) ),
    inference(resolution,[],[f83,f109])).

fof(f109,plain,(
    ! [X0] : sP1(k2_yellow_1(X0)) ),
    inference(resolution,[],[f87,f75])).

fof(f75,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

fof(f87,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | sP1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f28,f40,f39])).

fof(f39,plain,(
    ! [X0] :
      ( sP0(X0)
    <=> ? [X1] :
          ( r1_lattice3(X0,u1_struct_0(X0),X1)
          & m1_subset_1(X1,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f40,plain,(
    ! [X0] :
      ( ( v1_yellow_0(X0)
      <=> sP0(X0) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f28,plain,(
    ! [X0] :
      ( ( v1_yellow_0(X0)
      <=> ? [X1] :
            ( r1_lattice3(X0,u1_struct_0(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_yellow_0(X0)
      <=> ? [X1] :
            ( r1_lattice3(X0,u1_struct_0(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_yellow_0)).

fof(f83,plain,(
    ! [X0] :
      ( ~ sP1(X0)
      | ~ sP0(X0)
      | v1_yellow_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ( ( v1_yellow_0(X0)
          | ~ sP0(X0) )
        & ( sP0(X0)
          | ~ v1_yellow_0(X0) ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f475,plain,(
    sP0(k2_yellow_1(sK4)) ),
    inference(resolution,[],[f463,f115])).

fof(f115,plain,(
    m1_subset_1(k1_xboole_0,sK4) ),
    inference(resolution,[],[f103,f70])).

fof(f70,plain,(
    r2_hidden(k1_xboole_0,sK4) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,
    ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK4))
    & r2_hidden(k1_xboole_0,sK4)
    & ~ v1_xboole_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f45])).

fof(f45,plain,
    ( ? [X0] :
        ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0))
        & r2_hidden(k1_xboole_0,X0)
        & ~ v1_xboole_0(X0) )
   => ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK4))
      & r2_hidden(k1_xboole_0,sK4)
      & ~ v1_xboole_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0] :
      ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0))
      & r2_hidden(k1_xboole_0,X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0))
      & r2_hidden(k1_xboole_0,X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ( r2_hidden(k1_xboole_0,X0)
         => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( r2_hidden(k1_xboole_0,X0)
       => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_yellow_1)).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f463,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,X0)
      | sP0(k2_yellow_1(X0)) ) ),
    inference(subsumption_resolution,[],[f462,f299])).

fof(f299,plain,(
    ! [X3] :
      ( sP0(k2_yellow_1(X3))
      | ~ v1_xboole_0(X3) ) ),
    inference(subsumption_resolution,[],[f298,f118])).

fof(f118,plain,(
    ! [X0] : m1_subset_1(k3_yellow_0(k2_yellow_1(X0)),X0) ),
    inference(subsumption_resolution,[],[f117,f75])).

fof(f117,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(k2_yellow_1(X0)),X0)
      | ~ l1_orders_2(k2_yellow_1(X0)) ) ),
    inference(superposition,[],[f81,f76])).

fof(f76,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0)
      & u1_struct_0(k2_yellow_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).

fof(f81,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_yellow_0)).

fof(f298,plain,(
    ! [X3] :
      ( ~ v1_xboole_0(X3)
      | sP0(k2_yellow_1(X3))
      | ~ m1_subset_1(k3_yellow_0(k2_yellow_1(X3)),X3) ) ),
    inference(subsumption_resolution,[],[f295,f75])).

fof(f295,plain,(
    ! [X3] :
      ( ~ l1_orders_2(k2_yellow_1(X3))
      | ~ v1_xboole_0(X3)
      | sP0(k2_yellow_1(X3))
      | ~ m1_subset_1(k3_yellow_0(k2_yellow_1(X3)),X3) ) ),
    inference(resolution,[],[f288,f163])).

fof(f163,plain,(
    ! [X0,X1] :
      ( ~ r1_lattice3(k2_yellow_1(X0),X0,X1)
      | sP0(k2_yellow_1(X0))
      | ~ m1_subset_1(X1,X0) ) ),
    inference(superposition,[],[f86,f76])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ r1_lattice3(X0,u1_struct_0(X0),X1)
      | sP0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ! [X1] :
            ( ~ r1_lattice3(X0,u1_struct_0(X0),X1)
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      & ( ( r1_lattice3(X0,u1_struct_0(X0),sK5(X0))
          & m1_subset_1(sK5(X0),u1_struct_0(X0)) )
        | ~ sP0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f50,f51])).

fof(f51,plain,(
    ! [X0] :
      ( ? [X2] :
          ( r1_lattice3(X0,u1_struct_0(X0),X2)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( r1_lattice3(X0,u1_struct_0(X0),sK5(X0))
        & m1_subset_1(sK5(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ! [X1] :
            ( ~ r1_lattice3(X0,u1_struct_0(X0),X1)
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      & ( ? [X2] :
            ( r1_lattice3(X0,u1_struct_0(X0),X2)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        | ~ sP0(X0) ) ) ),
    inference(rectify,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ! [X1] :
            ( ~ r1_lattice3(X0,u1_struct_0(X0),X1)
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      & ( ? [X1] :
            ( r1_lattice3(X0,u1_struct_0(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) )
        | ~ sP0(X0) ) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f288,plain,(
    ! [X2,X3] :
      ( r1_lattice3(X2,X3,k3_yellow_0(X2))
      | ~ l1_orders_2(X2)
      | ~ v1_xboole_0(X3) ) ),
    inference(resolution,[],[f204,f145])).

fof(f145,plain,(
    ! [X4,X5,X3] :
      ( sP2(X3,X4,X5)
      | ~ v1_xboole_0(X5) ) ),
    inference(resolution,[],[f92,f97])).

fof(f97,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK7(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f60,f61])).

fof(f61,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK7(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK6(X0,X1,X2),X2)
      | sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ( ~ r1_orders_2(X1,X0,sK6(X0,X1,X2))
          & r2_hidden(sK6(X0,X1,X2),X2)
          & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_orders_2(X1,X0,X4)
            | ~ r2_hidden(X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f56,f57])).

fof(f57,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X1,X0,X3)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_orders_2(X1,X0,sK6(X0,X1,X2))
        & r2_hidden(sK6(X0,X1,X2),X2)
        & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ? [X3] :
            ( ~ r1_orders_2(X1,X0,X3)
            & r2_hidden(X3,X2)
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_orders_2(X1,X0,X4)
            | ~ r2_hidden(X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(rectify,[],[f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ( sP2(X2,X0,X1)
        | ? [X3] :
            ( ~ r1_orders_2(X0,X2,X3)
            & r2_hidden(X3,X1)
            & m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ! [X3] :
            ( r1_orders_2(X0,X2,X3)
            | ~ r2_hidden(X3,X1)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        | ~ sP2(X2,X0,X1) ) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( sP2(X2,X0,X1)
    <=> ! [X3] :
          ( r1_orders_2(X0,X2,X3)
          | ~ r2_hidden(X3,X1)
          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f204,plain,(
    ! [X0,X1] :
      ( ~ sP2(k3_yellow_0(X0),X0,X1)
      | ~ l1_orders_2(X0)
      | r1_lattice3(X0,X1,k3_yellow_0(X0)) ) ),
    inference(resolution,[],[f157,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ sP3(X0,X1,X2)
      | ~ sP2(X2,X1,X0)
      | r1_lattice3(X1,X0,X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( ( r1_lattice3(X1,X0,X2)
          | ~ sP2(X2,X1,X0) )
        & ( sP2(X2,X1,X0)
          | ~ r1_lattice3(X1,X0,X2) ) )
      | ~ sP3(X0,X1,X2) ) ),
    inference(rectify,[],[f53])).

fof(f53,plain,(
    ! [X1,X0,X2] :
      ( ( ( r1_lattice3(X0,X1,X2)
          | ~ sP2(X2,X0,X1) )
        & ( sP2(X2,X0,X1)
          | ~ r1_lattice3(X0,X1,X2) ) )
      | ~ sP3(X1,X0,X2) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X1,X0,X2] :
      ( ( r1_lattice3(X0,X1,X2)
      <=> sP2(X2,X0,X1) )
      | ~ sP3(X1,X0,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

% (5359)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
fof(f157,plain,(
    ! [X4,X3] :
      ( sP3(X3,X4,k3_yellow_0(X4))
      | ~ l1_orders_2(X4) ) ),
    inference(duplicate_literal_removal,[],[f152])).

fof(f152,plain,(
    ! [X4,X3] :
      ( sP3(X3,X4,k3_yellow_0(X4))
      | ~ l1_orders_2(X4)
      | ~ l1_orders_2(X4) ) ),
    inference(resolution,[],[f94,f81])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | sP3(X1,X0,X2)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( sP3(X1,X0,X2)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f30,f43,f42])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_lattice3)).

fof(f462,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,X0)
      | v1_xboole_0(X0)
      | sP0(k2_yellow_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f456])).

fof(f456,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,X0)
      | v1_xboole_0(X0)
      | sP0(k2_yellow_1(X0))
      | ~ m1_subset_1(k1_xboole_0,X0) ) ),
    inference(resolution,[],[f412,f163])).

fof(f412,plain,(
    ! [X0,X1] :
      ( r1_lattice3(k2_yellow_1(X0),X1,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,X0)
      | v1_xboole_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f408])).

fof(f408,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(k1_xboole_0,X0)
      | ~ m1_subset_1(k1_xboole_0,X0)
      | r1_lattice3(k2_yellow_1(X0),X1,k1_xboole_0) ) ),
    inference(resolution,[],[f378,f221])).

fof(f221,plain,(
    ! [X2,X0,X1] :
      ( ~ sP2(X0,k2_yellow_1(X1),X2)
      | ~ m1_subset_1(X0,X1)
      | r1_lattice3(k2_yellow_1(X1),X2,X0) ) ),
    inference(resolution,[],[f158,f89])).

fof(f158,plain,(
    ! [X2,X0,X1] :
      ( sP3(X2,k2_yellow_1(X0),X1)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(subsumption_resolution,[],[f156,f75])).

fof(f156,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | sP3(X2,k2_yellow_1(X0),X1)
      | ~ l1_orders_2(k2_yellow_1(X0)) ) ),
    inference(superposition,[],[f94,f76])).

fof(f378,plain,(
    ! [X0,X1] :
      ( sP2(k1_xboole_0,k2_yellow_1(X0),X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(k1_xboole_0,X0) ) ),
    inference(resolution,[],[f269,f72])).

fof(f72,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f269,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,sK6(X0,k2_yellow_1(X1),X2))
      | ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | sP2(X0,k2_yellow_1(X1),X2) ) ),
    inference(subsumption_resolution,[],[f267,f167])).

fof(f167,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK6(X1,k2_yellow_1(X0),X2),X0)
      | sP2(X1,k2_yellow_1(X0),X2) ) ),
    inference(superposition,[],[f91,f76])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1))
      | sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f267,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK6(X0,k2_yellow_1(X1),X2),X1)
      | ~ m1_subset_1(X0,X1)
      | ~ r1_tarski(X0,sK6(X0,k2_yellow_1(X1),X2))
      | v1_xboole_0(X1)
      | sP2(X0,k2_yellow_1(X1),X2) ) ),
    inference(resolution,[],[f196,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X1,X0,sK6(X0,X1,X2))
      | sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f196,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | ~ r1_tarski(X1,X2)
      | v1_xboole_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f195])).

fof(f195,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | ~ m1_subset_1(X2,X0)
      | r1_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X1,X0)
      | ~ r1_tarski(X1,X2)
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f194,f76])).

fof(f194,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,X0)
      | r1_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,X0)
      | ~ r1_tarski(X1,X2)
      | v1_xboole_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f193])).

fof(f193,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,X0)
      | r1_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | ~ r1_tarski(X1,X2)
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f192,f76])).

fof(f192,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | ~ r1_tarski(X1,X2)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f191,f78])).

fof(f78,plain,(
    ! [X0] :
      ( ~ v2_struct_0(k2_yellow_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v2_struct_0(k2_yellow_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ~ v2_struct_0(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_orders_2(k2_yellow_1(X0))
        & ~ v2_struct_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_yellow_1)).

fof(f191,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v2_struct_0(k2_yellow_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | ~ r1_tarski(X1,X2)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f190,f73])).

fof(f73,plain,(
    ! [X0] : v3_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v4_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow_1)).

fof(f190,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | ~ v3_orders_2(k2_yellow_1(X0))
      | v2_struct_0(k2_yellow_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | ~ r1_tarski(X1,X2)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f189,f75])).

fof(f189,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | ~ l1_orders_2(k2_yellow_1(X0))
      | ~ v3_orders_2(k2_yellow_1(X0))
      | v2_struct_0(k2_yellow_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | ~ r1_tarski(X1,X2)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f107,f185])).

fof(f185,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | ~ r1_tarski(X1,X2)
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f184,f76])).

fof(f184,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,X0)
      | r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f80,f76])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_orders_2(k2_yellow_1(X0),X1,X2)
                  | ~ r1_tarski(X1,X2) )
                & ( r1_tarski(X1,X2)
                  | ~ r3_orders_2(k2_yellow_1(X0),X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) )
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
             => ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_yellow_1)).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_orders_2(X0,X1,X2)
      | r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_orders_2(X0,X1,X2)
          | ~ r1_orders_2(X0,X1,X2) )
        & ( r1_orders_2(X0,X1,X2)
          | ~ r3_orders_2(X0,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

% (5370)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% (5373)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% (5363)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% (5362)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% (5361)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% (5352)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% (5362)Refutation not found, incomplete strategy% (5362)------------------------------
% (5362)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (5362)Termination reason: Refutation not found, incomplete strategy

% (5362)Memory used [KB]: 10618
% (5362)Time elapsed: 0.133 s
% (5362)------------------------------
% (5362)------------------------------
% (5357)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% (5355)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% (5355)Refutation not found, incomplete strategy% (5355)------------------------------
% (5355)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (5371)Refutation not found, incomplete strategy% (5371)------------------------------
% (5371)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (5371)Termination reason: Refutation not found, incomplete strategy

% (5371)Memory used [KB]: 10746
% (5371)Time elapsed: 0.151 s
% (5371)------------------------------
% (5371)------------------------------
fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(f521,plain,(
    ~ v1_yellow_0(k2_yellow_1(sK4)) ),
    inference(subsumption_resolution,[],[f520,f69])).

fof(f69,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f46])).

fof(f520,plain,
    ( v1_xboole_0(sK4)
    | ~ v1_yellow_0(k2_yellow_1(sK4)) ),
    inference(subsumption_resolution,[],[f514,f115])).

fof(f514,plain,
    ( ~ m1_subset_1(k1_xboole_0,sK4)
    | v1_xboole_0(sK4)
    | ~ v1_yellow_0(k2_yellow_1(sK4)) ),
    inference(trivial_inequality_removal,[],[f498])).

fof(f498,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ m1_subset_1(k1_xboole_0,sK4)
    | v1_xboole_0(sK4)
    | ~ v1_yellow_0(k2_yellow_1(sK4)) ),
    inference(superposition,[],[f71,f323])).

fof(f323,plain,(
    ! [X0] :
      ( k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))
      | ~ m1_subset_1(k1_xboole_0,X0)
      | v1_xboole_0(X0)
      | ~ v1_yellow_0(k2_yellow_1(X0)) ) ),
    inference(resolution,[],[f282,f95])).

fof(f95,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f282,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_yellow_0(k2_yellow_1(X1)),X0)
      | ~ v1_yellow_0(k2_yellow_1(X1))
      | ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1) ) ),
    inference(duplicate_literal_removal,[],[f281])).

fof(f281,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | ~ v1_yellow_0(k2_yellow_1(X1))
      | ~ m1_subset_1(X0,X1)
      | r1_tarski(k3_yellow_0(k2_yellow_1(X1)),X0)
      | v1_xboole_0(X1) ) ),
    inference(forward_demodulation,[],[f280,f76])).

fof(f280,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
      | ~ v1_yellow_0(k2_yellow_1(X1))
      | ~ m1_subset_1(X0,X1)
      | r1_tarski(k3_yellow_0(k2_yellow_1(X1)),X0)
      | v1_xboole_0(X1) ) ),
    inference(subsumption_resolution,[],[f279,f78])).

fof(f279,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
      | v2_struct_0(k2_yellow_1(X1))
      | ~ v1_yellow_0(k2_yellow_1(X1))
      | ~ m1_subset_1(X0,X1)
      | r1_tarski(k3_yellow_0(k2_yellow_1(X1)),X0)
      | v1_xboole_0(X1) ) ),
    inference(subsumption_resolution,[],[f278,f118])).

fof(f278,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
      | v2_struct_0(k2_yellow_1(X1))
      | ~ v1_yellow_0(k2_yellow_1(X1))
      | ~ m1_subset_1(X0,X1)
      | r1_tarski(k3_yellow_0(k2_yellow_1(X1)),X0)
      | ~ m1_subset_1(k3_yellow_0(k2_yellow_1(X1)),X1)
      | v1_xboole_0(X1) ) ),
    inference(subsumption_resolution,[],[f277,f74])).

fof(f74,plain,(
    ! [X0] : v5_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f277,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
      | v2_struct_0(k2_yellow_1(X1))
      | ~ v1_yellow_0(k2_yellow_1(X1))
      | ~ v5_orders_2(k2_yellow_1(X1))
      | ~ m1_subset_1(X0,X1)
      | r1_tarski(k3_yellow_0(k2_yellow_1(X1)),X0)
      | ~ m1_subset_1(k3_yellow_0(k2_yellow_1(X1)),X1)
      | v1_xboole_0(X1) ) ),
    inference(subsumption_resolution,[],[f276,f73])).

fof(f276,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
      | ~ v3_orders_2(k2_yellow_1(X1))
      | v2_struct_0(k2_yellow_1(X1))
      | ~ v1_yellow_0(k2_yellow_1(X1))
      | ~ v5_orders_2(k2_yellow_1(X1))
      | ~ m1_subset_1(X0,X1)
      | r1_tarski(k3_yellow_0(k2_yellow_1(X1)),X0)
      | ~ m1_subset_1(k3_yellow_0(k2_yellow_1(X1)),X1)
      | v1_xboole_0(X1) ) ),
    inference(subsumption_resolution,[],[f273,f75])).

fof(f273,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
      | ~ l1_orders_2(k2_yellow_1(X1))
      | ~ v3_orders_2(k2_yellow_1(X1))
      | v2_struct_0(k2_yellow_1(X1))
      | ~ v1_yellow_0(k2_yellow_1(X1))
      | ~ v5_orders_2(k2_yellow_1(X1))
      | ~ m1_subset_1(X0,X1)
      | r1_tarski(k3_yellow_0(k2_yellow_1(X1)),X0)
      | ~ m1_subset_1(k3_yellow_0(k2_yellow_1(X1)),X1)
      | v1_xboole_0(X1) ) ),
    inference(resolution,[],[f203,f179])).

fof(f179,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,X0)
      | r1_tarski(X1,X2)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f178,f76])).

fof(f178,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,X0)
      | r1_tarski(X1,X2)
      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f79,f76])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f203,plain,(
    ! [X0,X1] :
      ( r3_orders_2(X0,k3_yellow_0(X0),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f202,f81])).

fof(f202,plain,(
    ! [X0,X1] :
      ( r3_orders_2(X0,k3_yellow_0(X0),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f201])).

fof(f201,plain,(
    ! [X0,X1] :
      ( r3_orders_2(X0,k3_yellow_0(X0),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f108,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( r1_orders_2(X0,k3_yellow_0(X0),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,k3_yellow_0(X0),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,k3_yellow_0(X0),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r1_orders_2(X0,k3_yellow_0(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_yellow_0)).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X1,X2)
      | r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f71,plain,(
    k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK4)) ),
    inference(cnf_transformation,[],[f46])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:44:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (5358)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.51  % (5354)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.51  % (5366)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.51  % (5350)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.51  % (5353)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.51  % (5353)Refutation not found, incomplete strategy% (5353)------------------------------
% 0.20/0.51  % (5353)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (5353)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (5353)Memory used [KB]: 10618
% 0.20/0.51  % (5353)Time elapsed: 0.104 s
% 0.20/0.51  % (5353)------------------------------
% 0.20/0.51  % (5353)------------------------------
% 0.20/0.51  % (5349)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.52  % (5348)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.52  % (5374)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.52  % (5349)Refutation not found, incomplete strategy% (5349)------------------------------
% 0.20/0.52  % (5349)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (5349)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (5349)Memory used [KB]: 6268
% 0.20/0.52  % (5349)Time elapsed: 0.108 s
% 0.20/0.52  % (5349)------------------------------
% 0.20/0.52  % (5349)------------------------------
% 0.20/0.52  % (5351)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.52  % (5356)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.52  % (5346)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.52  % (5345)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.53  % (5367)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.53  % (5347)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (5367)Refutation not found, incomplete strategy% (5367)------------------------------
% 0.20/0.53  % (5367)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (5367)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (5367)Memory used [KB]: 10746
% 0.20/0.53  % (5367)Time elapsed: 0.083 s
% 0.20/0.53  % (5367)------------------------------
% 0.20/0.53  % (5367)------------------------------
% 0.20/0.53  % (5364)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.53  % (5347)Refutation not found, incomplete strategy% (5347)------------------------------
% 0.20/0.53  % (5347)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (5347)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (5347)Memory used [KB]: 10746
% 0.20/0.53  % (5347)Time elapsed: 0.125 s
% 0.20/0.53  % (5347)------------------------------
% 0.20/0.53  % (5347)------------------------------
% 0.20/0.53  % (5365)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.53  % (5368)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.53  % (5372)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.53  % (5360)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.54  % (5371)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.54  % (5369)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.54  % (5374)Refutation found. Thanks to Tanya!
% 0.20/0.54  % SZS status Theorem for theBenchmark
% 0.20/0.54  % SZS output start Proof for theBenchmark
% 0.20/0.54  fof(f548,plain,(
% 0.20/0.54    $false),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f521,f475,f112])).
% 0.20/0.54  fof(f112,plain,(
% 0.20/0.54    ( ! [X0] : (~sP0(k2_yellow_1(X0)) | v1_yellow_0(k2_yellow_1(X0))) )),
% 0.20/0.54    inference(resolution,[],[f83,f109])).
% 0.20/0.54  fof(f109,plain,(
% 0.20/0.54    ( ! [X0] : (sP1(k2_yellow_1(X0))) )),
% 0.20/0.54    inference(resolution,[],[f87,f75])).
% 0.20/0.54  fof(f75,plain,(
% 0.20/0.54    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f21])).
% 0.20/0.54  fof(f21,plain,(
% 0.20/0.54    ! [X0] : l1_orders_2(k2_yellow_1(X0))),
% 0.20/0.54    inference(pure_predicate_removal,[],[f12])).
% 0.20/0.54  fof(f12,axiom,(
% 0.20/0.54    ! [X0] : (l1_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).
% 0.20/0.54  fof(f87,plain,(
% 0.20/0.54    ( ! [X0] : (~l1_orders_2(X0) | sP1(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f41])).
% 0.20/0.54  fof(f41,plain,(
% 0.20/0.54    ! [X0] : (sP1(X0) | ~l1_orders_2(X0))),
% 0.20/0.54    inference(definition_folding,[],[f28,f40,f39])).
% 0.20/0.54  fof(f39,plain,(
% 0.20/0.54    ! [X0] : (sP0(X0) <=> ? [X1] : (r1_lattice3(X0,u1_struct_0(X0),X1) & m1_subset_1(X1,u1_struct_0(X0))))),
% 0.20/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.54  fof(f40,plain,(
% 0.20/0.54    ! [X0] : ((v1_yellow_0(X0) <=> sP0(X0)) | ~sP1(X0))),
% 0.20/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.20/0.54  fof(f28,plain,(
% 0.20/0.54    ! [X0] : ((v1_yellow_0(X0) <=> ? [X1] : (r1_lattice3(X0,u1_struct_0(X0),X1) & m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.20/0.54    inference(ennf_transformation,[],[f9])).
% 0.20/0.54  fof(f9,axiom,(
% 0.20/0.54    ! [X0] : (l1_orders_2(X0) => (v1_yellow_0(X0) <=> ? [X1] : (r1_lattice3(X0,u1_struct_0(X0),X1) & m1_subset_1(X1,u1_struct_0(X0)))))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_yellow_0)).
% 0.20/0.54  fof(f83,plain,(
% 0.20/0.54    ( ! [X0] : (~sP1(X0) | ~sP0(X0) | v1_yellow_0(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f48])).
% 0.20/0.54  fof(f48,plain,(
% 0.20/0.54    ! [X0] : (((v1_yellow_0(X0) | ~sP0(X0)) & (sP0(X0) | ~v1_yellow_0(X0))) | ~sP1(X0))),
% 0.20/0.54    inference(nnf_transformation,[],[f40])).
% 0.20/0.54  fof(f475,plain,(
% 0.20/0.54    sP0(k2_yellow_1(sK4))),
% 0.20/0.54    inference(resolution,[],[f463,f115])).
% 0.20/0.54  fof(f115,plain,(
% 0.20/0.54    m1_subset_1(k1_xboole_0,sK4)),
% 0.20/0.54    inference(resolution,[],[f103,f70])).
% 0.20/0.54  fof(f70,plain,(
% 0.20/0.54    r2_hidden(k1_xboole_0,sK4)),
% 0.20/0.54    inference(cnf_transformation,[],[f46])).
% 0.20/0.54  fof(f46,plain,(
% 0.20/0.54    k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK4)) & r2_hidden(k1_xboole_0,sK4) & ~v1_xboole_0(sK4)),
% 0.20/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f45])).
% 0.20/0.54  fof(f45,plain,(
% 0.20/0.54    ? [X0] : (k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0)) & r2_hidden(k1_xboole_0,X0) & ~v1_xboole_0(X0)) => (k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK4)) & r2_hidden(k1_xboole_0,sK4) & ~v1_xboole_0(sK4))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f24,plain,(
% 0.20/0.54    ? [X0] : (k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0)) & r2_hidden(k1_xboole_0,X0) & ~v1_xboole_0(X0))),
% 0.20/0.54    inference(flattening,[],[f23])).
% 0.20/0.54  fof(f23,plain,(
% 0.20/0.54    ? [X0] : ((k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0)) & r2_hidden(k1_xboole_0,X0)) & ~v1_xboole_0(X0))),
% 0.20/0.54    inference(ennf_transformation,[],[f18])).
% 0.20/0.54  fof(f18,negated_conjecture,(
% 0.20/0.54    ~! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k1_xboole_0,X0) => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))))),
% 0.20/0.54    inference(negated_conjecture,[],[f17])).
% 0.20/0.54  fof(f17,conjecture,(
% 0.20/0.54    ! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k1_xboole_0,X0) => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_yellow_1)).
% 0.20/0.54  fof(f103,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f35])).
% 0.20/0.54  fof(f35,plain,(
% 0.20/0.54    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.20/0.54    inference(ennf_transformation,[],[f6])).
% 0.20/0.54  fof(f6,axiom,(
% 0.20/0.54    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 0.20/0.54  fof(f463,plain,(
% 0.20/0.54    ( ! [X0] : (~m1_subset_1(k1_xboole_0,X0) | sP0(k2_yellow_1(X0))) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f462,f299])).
% 0.20/0.54  fof(f299,plain,(
% 0.20/0.54    ( ! [X3] : (sP0(k2_yellow_1(X3)) | ~v1_xboole_0(X3)) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f298,f118])).
% 0.20/0.54  fof(f118,plain,(
% 0.20/0.54    ( ! [X0] : (m1_subset_1(k3_yellow_0(k2_yellow_1(X0)),X0)) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f117,f75])).
% 0.20/0.54  fof(f117,plain,(
% 0.20/0.54    ( ! [X0] : (m1_subset_1(k3_yellow_0(k2_yellow_1(X0)),X0) | ~l1_orders_2(k2_yellow_1(X0))) )),
% 0.20/0.54    inference(superposition,[],[f81,f76])).
% 0.20/0.54  fof(f76,plain,(
% 0.20/0.54    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = X0) )),
% 0.20/0.54    inference(cnf_transformation,[],[f15])).
% 0.20/0.54  fof(f15,axiom,(
% 0.20/0.54    ! [X0] : (u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0) & u1_struct_0(k2_yellow_1(X0)) = X0)),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).
% 0.20/0.54  fof(f81,plain,(
% 0.20/0.54    ( ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f27])).
% 0.20/0.54  fof(f27,plain,(
% 0.20/0.54    ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 0.20/0.54    inference(ennf_transformation,[],[f10])).
% 0.20/0.54  fof(f10,axiom,(
% 0.20/0.54    ! [X0] : (l1_orders_2(X0) => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_yellow_0)).
% 0.20/0.54  fof(f298,plain,(
% 0.20/0.54    ( ! [X3] : (~v1_xboole_0(X3) | sP0(k2_yellow_1(X3)) | ~m1_subset_1(k3_yellow_0(k2_yellow_1(X3)),X3)) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f295,f75])).
% 0.20/0.54  fof(f295,plain,(
% 0.20/0.54    ( ! [X3] : (~l1_orders_2(k2_yellow_1(X3)) | ~v1_xboole_0(X3) | sP0(k2_yellow_1(X3)) | ~m1_subset_1(k3_yellow_0(k2_yellow_1(X3)),X3)) )),
% 0.20/0.54    inference(resolution,[],[f288,f163])).
% 0.20/0.54  fof(f163,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~r1_lattice3(k2_yellow_1(X0),X0,X1) | sP0(k2_yellow_1(X0)) | ~m1_subset_1(X1,X0)) )),
% 0.20/0.54    inference(superposition,[],[f86,f76])).
% 0.20/0.54  fof(f86,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~r1_lattice3(X0,u1_struct_0(X0),X1) | sP0(X0) | ~m1_subset_1(X1,u1_struct_0(X0))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f52])).
% 0.20/0.54  fof(f52,plain,(
% 0.20/0.54    ! [X0] : ((sP0(X0) | ! [X1] : (~r1_lattice3(X0,u1_struct_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0)))) & ((r1_lattice3(X0,u1_struct_0(X0),sK5(X0)) & m1_subset_1(sK5(X0),u1_struct_0(X0))) | ~sP0(X0)))),
% 0.20/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f50,f51])).
% 0.20/0.54  fof(f51,plain,(
% 0.20/0.54    ! [X0] : (? [X2] : (r1_lattice3(X0,u1_struct_0(X0),X2) & m1_subset_1(X2,u1_struct_0(X0))) => (r1_lattice3(X0,u1_struct_0(X0),sK5(X0)) & m1_subset_1(sK5(X0),u1_struct_0(X0))))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f50,plain,(
% 0.20/0.54    ! [X0] : ((sP0(X0) | ! [X1] : (~r1_lattice3(X0,u1_struct_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0)))) & (? [X2] : (r1_lattice3(X0,u1_struct_0(X0),X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~sP0(X0)))),
% 0.20/0.54    inference(rectify,[],[f49])).
% 0.20/0.54  fof(f49,plain,(
% 0.20/0.54    ! [X0] : ((sP0(X0) | ! [X1] : (~r1_lattice3(X0,u1_struct_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0)))) & (? [X1] : (r1_lattice3(X0,u1_struct_0(X0),X1) & m1_subset_1(X1,u1_struct_0(X0))) | ~sP0(X0)))),
% 0.20/0.54    inference(nnf_transformation,[],[f39])).
% 0.20/0.54  fof(f288,plain,(
% 0.20/0.54    ( ! [X2,X3] : (r1_lattice3(X2,X3,k3_yellow_0(X2)) | ~l1_orders_2(X2) | ~v1_xboole_0(X3)) )),
% 0.20/0.54    inference(resolution,[],[f204,f145])).
% 0.20/0.54  fof(f145,plain,(
% 0.20/0.54    ( ! [X4,X5,X3] : (sP2(X3,X4,X5) | ~v1_xboole_0(X5)) )),
% 0.20/0.54    inference(resolution,[],[f92,f97])).
% 0.20/0.54  fof(f97,plain,(
% 0.20/0.54    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f62])).
% 0.20/0.54  fof(f62,plain,(
% 0.20/0.54    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK7(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f60,f61])).
% 0.20/0.54  fof(f61,plain,(
% 0.20/0.54    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK7(X0),X0))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f60,plain,(
% 0.20/0.54    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.54    inference(rectify,[],[f59])).
% 0.20/0.54  fof(f59,plain,(
% 0.20/0.54    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.54    inference(nnf_transformation,[],[f1])).
% 0.20/0.54  fof(f1,axiom,(
% 0.20/0.54    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.54  fof(f92,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (r2_hidden(sK6(X0,X1,X2),X2) | sP2(X0,X1,X2)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f58])).
% 0.20/0.54  fof(f58,plain,(
% 0.20/0.54    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | (~r1_orders_2(X1,X0,sK6(X0,X1,X2)) & r2_hidden(sK6(X0,X1,X2),X2) & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1)))) & (! [X4] : (r1_orders_2(X1,X0,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP2(X0,X1,X2)))),
% 0.20/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f56,f57])).
% 0.20/0.54  fof(f57,plain,(
% 0.20/0.54    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X1,X0,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X1))) => (~r1_orders_2(X1,X0,sK6(X0,X1,X2)) & r2_hidden(sK6(X0,X1,X2),X2) & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1))))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f56,plain,(
% 0.20/0.54    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ? [X3] : (~r1_orders_2(X1,X0,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X4] : (r1_orders_2(X1,X0,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP2(X0,X1,X2)))),
% 0.20/0.54    inference(rectify,[],[f55])).
% 0.20/0.54  fof(f55,plain,(
% 0.20/0.54    ! [X2,X0,X1] : ((sP2(X2,X0,X1) | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~sP2(X2,X0,X1)))),
% 0.20/0.54    inference(nnf_transformation,[],[f42])).
% 0.20/0.54  fof(f42,plain,(
% 0.20/0.54    ! [X2,X0,X1] : (sP2(X2,X0,X1) <=> ! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))))),
% 0.20/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.20/0.54  fof(f204,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~sP2(k3_yellow_0(X0),X0,X1) | ~l1_orders_2(X0) | r1_lattice3(X0,X1,k3_yellow_0(X0))) )),
% 0.20/0.54    inference(resolution,[],[f157,f89])).
% 0.20/0.54  fof(f89,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~sP3(X0,X1,X2) | ~sP2(X2,X1,X0) | r1_lattice3(X1,X0,X2)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f54])).
% 0.20/0.54  fof(f54,plain,(
% 0.20/0.54    ! [X0,X1,X2] : (((r1_lattice3(X1,X0,X2) | ~sP2(X2,X1,X0)) & (sP2(X2,X1,X0) | ~r1_lattice3(X1,X0,X2))) | ~sP3(X0,X1,X2))),
% 0.20/0.54    inference(rectify,[],[f53])).
% 0.20/0.54  fof(f53,plain,(
% 0.20/0.54    ! [X1,X0,X2] : (((r1_lattice3(X0,X1,X2) | ~sP2(X2,X0,X1)) & (sP2(X2,X0,X1) | ~r1_lattice3(X0,X1,X2))) | ~sP3(X1,X0,X2))),
% 0.20/0.54    inference(nnf_transformation,[],[f43])).
% 0.20/0.54  fof(f43,plain,(
% 0.20/0.54    ! [X1,X0,X2] : ((r1_lattice3(X0,X1,X2) <=> sP2(X2,X0,X1)) | ~sP3(X1,X0,X2))),
% 0.20/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.20/0.54  % (5359)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.54  fof(f157,plain,(
% 0.20/0.54    ( ! [X4,X3] : (sP3(X3,X4,k3_yellow_0(X4)) | ~l1_orders_2(X4)) )),
% 0.20/0.54    inference(duplicate_literal_removal,[],[f152])).
% 0.20/0.54  fof(f152,plain,(
% 0.20/0.54    ( ! [X4,X3] : (sP3(X3,X4,k3_yellow_0(X4)) | ~l1_orders_2(X4) | ~l1_orders_2(X4)) )),
% 0.20/0.54    inference(resolution,[],[f94,f81])).
% 0.20/0.54  fof(f94,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(X0)) | sP3(X1,X0,X2) | ~l1_orders_2(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f44])).
% 0.20/0.54  fof(f44,plain,(
% 0.20/0.54    ! [X0] : (! [X1,X2] : (sP3(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.20/0.54    inference(definition_folding,[],[f30,f43,f42])).
% 0.20/0.54  fof(f30,plain,(
% 0.20/0.54    ! [X0] : (! [X1,X2] : ((r1_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.20/0.54    inference(flattening,[],[f29])).
% 0.20/0.54  fof(f29,plain,(
% 0.20/0.54    ! [X0] : (! [X1,X2] : ((r1_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.20/0.54    inference(ennf_transformation,[],[f8])).
% 0.20/0.54  fof(f8,axiom,(
% 0.20/0.54    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X2,X3))))))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_lattice3)).
% 0.20/0.54  fof(f462,plain,(
% 0.20/0.54    ( ! [X0] : (~m1_subset_1(k1_xboole_0,X0) | v1_xboole_0(X0) | sP0(k2_yellow_1(X0))) )),
% 0.20/0.54    inference(duplicate_literal_removal,[],[f456])).
% 0.20/0.54  fof(f456,plain,(
% 0.20/0.54    ( ! [X0] : (~m1_subset_1(k1_xboole_0,X0) | v1_xboole_0(X0) | sP0(k2_yellow_1(X0)) | ~m1_subset_1(k1_xboole_0,X0)) )),
% 0.20/0.54    inference(resolution,[],[f412,f163])).
% 0.20/0.54  fof(f412,plain,(
% 0.20/0.54    ( ! [X0,X1] : (r1_lattice3(k2_yellow_1(X0),X1,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,X0) | v1_xboole_0(X0)) )),
% 0.20/0.54    inference(duplicate_literal_removal,[],[f408])).
% 0.20/0.54  fof(f408,plain,(
% 0.20/0.54    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(k1_xboole_0,X0) | ~m1_subset_1(k1_xboole_0,X0) | r1_lattice3(k2_yellow_1(X0),X1,k1_xboole_0)) )),
% 0.20/0.54    inference(resolution,[],[f378,f221])).
% 0.20/0.54  fof(f221,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~sP2(X0,k2_yellow_1(X1),X2) | ~m1_subset_1(X0,X1) | r1_lattice3(k2_yellow_1(X1),X2,X0)) )),
% 0.20/0.54    inference(resolution,[],[f158,f89])).
% 0.20/0.54  fof(f158,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (sP3(X2,k2_yellow_1(X0),X1) | ~m1_subset_1(X1,X0)) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f156,f75])).
% 0.20/0.54  fof(f156,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X1,X0) | sP3(X2,k2_yellow_1(X0),X1) | ~l1_orders_2(k2_yellow_1(X0))) )),
% 0.20/0.54    inference(superposition,[],[f94,f76])).
% 0.20/0.54  fof(f378,plain,(
% 0.20/0.54    ( ! [X0,X1] : (sP2(k1_xboole_0,k2_yellow_1(X0),X1) | v1_xboole_0(X0) | ~m1_subset_1(k1_xboole_0,X0)) )),
% 0.20/0.54    inference(resolution,[],[f269,f72])).
% 0.20/0.54  fof(f72,plain,(
% 0.20/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f3])).
% 0.20/0.54  fof(f3,axiom,(
% 0.20/0.54    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.54  fof(f269,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X0,sK6(X0,k2_yellow_1(X1),X2)) | ~m1_subset_1(X0,X1) | v1_xboole_0(X1) | sP2(X0,k2_yellow_1(X1),X2)) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f267,f167])).
% 0.20/0.54  fof(f167,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (m1_subset_1(sK6(X1,k2_yellow_1(X0),X2),X0) | sP2(X1,k2_yellow_1(X0),X2)) )),
% 0.20/0.54    inference(superposition,[],[f91,f76])).
% 0.20/0.54  fof(f91,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1)) | sP2(X0,X1,X2)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f58])).
% 0.20/0.54  fof(f267,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(sK6(X0,k2_yellow_1(X1),X2),X1) | ~m1_subset_1(X0,X1) | ~r1_tarski(X0,sK6(X0,k2_yellow_1(X1),X2)) | v1_xboole_0(X1) | sP2(X0,k2_yellow_1(X1),X2)) )),
% 0.20/0.54    inference(resolution,[],[f196,f93])).
% 0.20/0.54  fof(f93,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~r1_orders_2(X1,X0,sK6(X0,X1,X2)) | sP2(X0,X1,X2)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f58])).
% 0.20/0.54  fof(f196,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (r1_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | ~r1_tarski(X1,X2) | v1_xboole_0(X0)) )),
% 0.20/0.54    inference(duplicate_literal_removal,[],[f195])).
% 0.20/0.54  fof(f195,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X1,X0) | ~m1_subset_1(X2,X0) | r1_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X1,X0) | ~r1_tarski(X1,X2) | v1_xboole_0(X0)) )),
% 0.20/0.54    inference(forward_demodulation,[],[f194,f76])).
% 0.20/0.54  fof(f194,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,X0) | r1_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,X0) | ~r1_tarski(X1,X2) | v1_xboole_0(X0)) )),
% 0.20/0.54    inference(duplicate_literal_removal,[],[f193])).
% 0.20/0.54  fof(f193,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,X0) | r1_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | ~r1_tarski(X1,X2) | v1_xboole_0(X0)) )),
% 0.20/0.54    inference(forward_demodulation,[],[f192,f76])).
% 0.20/0.54  fof(f192,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (r1_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | ~r1_tarski(X1,X2) | v1_xboole_0(X0)) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f191,f78])).
% 0.20/0.54  fof(f78,plain,(
% 0.20/0.54    ( ! [X0] : (~v2_struct_0(k2_yellow_1(X0)) | v1_xboole_0(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f25])).
% 0.20/0.54  fof(f25,plain,(
% 0.20/0.54    ! [X0] : (~v2_struct_0(k2_yellow_1(X0)) | v1_xboole_0(X0))),
% 0.20/0.54    inference(ennf_transformation,[],[f20])).
% 0.20/0.54  fof(f20,plain,(
% 0.20/0.54    ! [X0] : (~v1_xboole_0(X0) => ~v2_struct_0(k2_yellow_1(X0)))),
% 0.20/0.54    inference(pure_predicate_removal,[],[f14])).
% 0.20/0.54  fof(f14,axiom,(
% 0.20/0.54    ! [X0] : (~v1_xboole_0(X0) => (v1_orders_2(k2_yellow_1(X0)) & ~v2_struct_0(k2_yellow_1(X0))))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_yellow_1)).
% 0.20/0.54  fof(f191,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (r1_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v2_struct_0(k2_yellow_1(X0)) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | ~r1_tarski(X1,X2) | v1_xboole_0(X0)) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f190,f73])).
% 0.20/0.54  fof(f73,plain,(
% 0.20/0.54    ( ! [X0] : (v3_orders_2(k2_yellow_1(X0))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f22])).
% 0.20/0.54  fof(f22,plain,(
% 0.20/0.54    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)))),
% 0.20/0.54    inference(pure_predicate_removal,[],[f19])).
% 0.20/0.54  fof(f19,plain,(
% 0.20/0.54    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.20/0.54    inference(pure_predicate_removal,[],[f13])).
% 0.20/0.54  fof(f13,axiom,(
% 0.20/0.54    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v4_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow_1)).
% 0.20/0.54  fof(f190,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (r1_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | ~v3_orders_2(k2_yellow_1(X0)) | v2_struct_0(k2_yellow_1(X0)) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | ~r1_tarski(X1,X2) | v1_xboole_0(X0)) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f189,f75])).
% 0.20/0.54  fof(f189,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (r1_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | ~l1_orders_2(k2_yellow_1(X0)) | ~v3_orders_2(k2_yellow_1(X0)) | v2_struct_0(k2_yellow_1(X0)) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | ~r1_tarski(X1,X2) | v1_xboole_0(X0)) )),
% 0.20/0.54    inference(resolution,[],[f107,f185])).
% 0.20/0.54  fof(f185,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | ~r1_tarski(X1,X2) | v1_xboole_0(X0)) )),
% 0.20/0.54    inference(forward_demodulation,[],[f184,f76])).
% 0.20/0.54  fof(f184,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,X0) | r3_orders_2(k2_yellow_1(X0),X1,X2) | ~r1_tarski(X1,X2) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 0.20/0.54    inference(forward_demodulation,[],[f80,f76])).
% 0.20/0.54  fof(f80,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (r3_orders_2(k2_yellow_1(X0),X1,X2) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f47])).
% 0.20/0.54  fof(f47,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : (! [X2] : (((r3_orders_2(k2_yellow_1(X0),X1,X2) | ~r1_tarski(X1,X2)) & (r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 0.20/0.54    inference(nnf_transformation,[],[f26])).
% 0.20/0.54  fof(f26,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : (! [X2] : ((r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 0.20/0.54    inference(ennf_transformation,[],[f16])).
% 0.20/0.54  fof(f16,axiom,(
% 0.20/0.54    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => (r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)))))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_yellow_1)).
% 0.20/0.54  fof(f107,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~r3_orders_2(X0,X1,X2) | r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f68])).
% 0.20/0.54  fof(f68,plain,(
% 0.20/0.54    ! [X0,X1,X2] : (((r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.54    inference(nnf_transformation,[],[f38])).
% 0.20/0.54  fof(f38,plain,(
% 0.20/0.54    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.54    inference(flattening,[],[f37])).
% 0.20/0.54  % (5370)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.54  % (5373)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.54  % (5363)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.54  % (5362)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.54  % (5361)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.54  % (5352)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.55  % (5362)Refutation not found, incomplete strategy% (5362)------------------------------
% 0.20/0.55  % (5362)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (5362)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (5362)Memory used [KB]: 10618
% 0.20/0.55  % (5362)Time elapsed: 0.133 s
% 0.20/0.55  % (5362)------------------------------
% 0.20/0.55  % (5362)------------------------------
% 0.20/0.55  % (5357)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.55  % (5355)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.55  % (5355)Refutation not found, incomplete strategy% (5355)------------------------------
% 0.20/0.55  % (5355)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (5371)Refutation not found, incomplete strategy% (5371)------------------------------
% 0.20/0.55  % (5371)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (5371)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (5371)Memory used [KB]: 10746
% 0.20/0.55  % (5371)Time elapsed: 0.151 s
% 0.20/0.55  % (5371)------------------------------
% 0.20/0.55  % (5371)------------------------------
% 0.20/0.55  fof(f37,plain,(
% 0.20/0.55    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.55    inference(ennf_transformation,[],[f7])).
% 0.20/0.55  fof(f7,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).
% 0.20/0.55  fof(f521,plain,(
% 0.20/0.55    ~v1_yellow_0(k2_yellow_1(sK4))),
% 0.20/0.55    inference(subsumption_resolution,[],[f520,f69])).
% 0.20/0.55  fof(f69,plain,(
% 0.20/0.55    ~v1_xboole_0(sK4)),
% 0.20/0.55    inference(cnf_transformation,[],[f46])).
% 0.20/0.55  fof(f520,plain,(
% 0.20/0.55    v1_xboole_0(sK4) | ~v1_yellow_0(k2_yellow_1(sK4))),
% 0.20/0.55    inference(subsumption_resolution,[],[f514,f115])).
% 0.20/0.55  fof(f514,plain,(
% 0.20/0.55    ~m1_subset_1(k1_xboole_0,sK4) | v1_xboole_0(sK4) | ~v1_yellow_0(k2_yellow_1(sK4))),
% 0.20/0.55    inference(trivial_inequality_removal,[],[f498])).
% 0.20/0.55  fof(f498,plain,(
% 0.20/0.55    k1_xboole_0 != k1_xboole_0 | ~m1_subset_1(k1_xboole_0,sK4) | v1_xboole_0(sK4) | ~v1_yellow_0(k2_yellow_1(sK4))),
% 0.20/0.55    inference(superposition,[],[f71,f323])).
% 0.20/0.55  fof(f323,plain,(
% 0.20/0.55    ( ! [X0] : (k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) | ~m1_subset_1(k1_xboole_0,X0) | v1_xboole_0(X0) | ~v1_yellow_0(k2_yellow_1(X0))) )),
% 0.20/0.55    inference(resolution,[],[f282,f95])).
% 0.20/0.55  fof(f95,plain,(
% 0.20/0.55    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.20/0.55    inference(cnf_transformation,[],[f31])).
% 0.20/0.55  fof(f31,plain,(
% 0.20/0.55    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.20/0.55    inference(ennf_transformation,[],[f4])).
% 0.20/0.55  fof(f4,axiom,(
% 0.20/0.55    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.20/0.55  fof(f282,plain,(
% 0.20/0.55    ( ! [X0,X1] : (r1_tarski(k3_yellow_0(k2_yellow_1(X1)),X0) | ~v1_yellow_0(k2_yellow_1(X1)) | ~m1_subset_1(X0,X1) | v1_xboole_0(X1)) )),
% 0.20/0.55    inference(duplicate_literal_removal,[],[f281])).
% 0.20/0.55  fof(f281,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | ~v1_yellow_0(k2_yellow_1(X1)) | ~m1_subset_1(X0,X1) | r1_tarski(k3_yellow_0(k2_yellow_1(X1)),X0) | v1_xboole_0(X1)) )),
% 0.20/0.55    inference(forward_demodulation,[],[f280,f76])).
% 0.20/0.55  fof(f280,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1))) | ~v1_yellow_0(k2_yellow_1(X1)) | ~m1_subset_1(X0,X1) | r1_tarski(k3_yellow_0(k2_yellow_1(X1)),X0) | v1_xboole_0(X1)) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f279,f78])).
% 0.20/0.55  fof(f279,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1))) | v2_struct_0(k2_yellow_1(X1)) | ~v1_yellow_0(k2_yellow_1(X1)) | ~m1_subset_1(X0,X1) | r1_tarski(k3_yellow_0(k2_yellow_1(X1)),X0) | v1_xboole_0(X1)) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f278,f118])).
% 0.20/0.55  fof(f278,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1))) | v2_struct_0(k2_yellow_1(X1)) | ~v1_yellow_0(k2_yellow_1(X1)) | ~m1_subset_1(X0,X1) | r1_tarski(k3_yellow_0(k2_yellow_1(X1)),X0) | ~m1_subset_1(k3_yellow_0(k2_yellow_1(X1)),X1) | v1_xboole_0(X1)) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f277,f74])).
% 0.20/0.55  fof(f74,plain,(
% 0.20/0.55    ( ! [X0] : (v5_orders_2(k2_yellow_1(X0))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f22])).
% 0.20/0.55  fof(f277,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1))) | v2_struct_0(k2_yellow_1(X1)) | ~v1_yellow_0(k2_yellow_1(X1)) | ~v5_orders_2(k2_yellow_1(X1)) | ~m1_subset_1(X0,X1) | r1_tarski(k3_yellow_0(k2_yellow_1(X1)),X0) | ~m1_subset_1(k3_yellow_0(k2_yellow_1(X1)),X1) | v1_xboole_0(X1)) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f276,f73])).
% 0.20/0.55  fof(f276,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1))) | ~v3_orders_2(k2_yellow_1(X1)) | v2_struct_0(k2_yellow_1(X1)) | ~v1_yellow_0(k2_yellow_1(X1)) | ~v5_orders_2(k2_yellow_1(X1)) | ~m1_subset_1(X0,X1) | r1_tarski(k3_yellow_0(k2_yellow_1(X1)),X0) | ~m1_subset_1(k3_yellow_0(k2_yellow_1(X1)),X1) | v1_xboole_0(X1)) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f273,f75])).
% 0.20/0.55  fof(f273,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1))) | ~l1_orders_2(k2_yellow_1(X1)) | ~v3_orders_2(k2_yellow_1(X1)) | v2_struct_0(k2_yellow_1(X1)) | ~v1_yellow_0(k2_yellow_1(X1)) | ~v5_orders_2(k2_yellow_1(X1)) | ~m1_subset_1(X0,X1) | r1_tarski(k3_yellow_0(k2_yellow_1(X1)),X0) | ~m1_subset_1(k3_yellow_0(k2_yellow_1(X1)),X1) | v1_xboole_0(X1)) )),
% 0.20/0.55    inference(resolution,[],[f203,f179])).
% 0.20/0.55  fof(f179,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,X0) | r1_tarski(X1,X2) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.55    inference(forward_demodulation,[],[f178,f76])).
% 0.20/0.55  fof(f178,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,X0) | r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 0.20/0.55    inference(forward_demodulation,[],[f79,f76])).
% 0.20/0.55  fof(f79,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f47])).
% 0.20/0.55  fof(f203,plain,(
% 0.20/0.55    ( ! [X0,X1] : (r3_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0)) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f202,f81])).
% 0.20/0.55  fof(f202,plain,(
% 0.20/0.55    ( ! [X0,X1] : (r3_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0)) )),
% 0.20/0.55    inference(duplicate_literal_removal,[],[f201])).
% 0.20/0.55  fof(f201,plain,(
% 0.20/0.55    ( ! [X0,X1] : (r3_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.55    inference(resolution,[],[f108,f96])).
% 0.20/0.55  fof(f96,plain,(
% 0.20/0.55    ( ! [X0,X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f33])).
% 0.20/0.55  fof(f33,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.55    inference(flattening,[],[f32])).
% 0.20/0.55  fof(f32,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.55    inference(ennf_transformation,[],[f11])).
% 0.20/0.55  fof(f11,axiom,(
% 0.20/0.55    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r1_orders_2(X0,k3_yellow_0(X0),X1)))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_yellow_0)).
% 0.20/0.55  fof(f108,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~r1_orders_2(X0,X1,X2) | r3_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f68])).
% 0.20/0.55  fof(f71,plain,(
% 0.20/0.55    k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK4))),
% 0.20/0.55    inference(cnf_transformation,[],[f46])).
% 0.20/0.55  % SZS output end Proof for theBenchmark
% 0.20/0.55  % (5374)------------------------------
% 0.20/0.55  % (5374)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (5374)Termination reason: Refutation
% 0.20/0.55  
% 0.20/0.55  % (5374)Memory used [KB]: 1918
% 0.20/0.55  % (5374)Time elapsed: 0.141 s
% 0.20/0.55  % (5374)------------------------------
% 0.20/0.55  % (5374)------------------------------
% 0.20/0.56  % (5344)Success in time 0.196 s
%------------------------------------------------------------------------------
