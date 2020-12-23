%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1564+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:06 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  159 ( 360 expanded)
%              Number of leaves         :   28 ( 101 expanded)
%              Depth                    :   28
%              Number of atoms          :  663 (1730 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f514,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f124,f249,f513])).

fof(f513,plain,(
    spl17_2 ),
    inference(avatar_contradiction_clause,[],[f512])).

fof(f512,plain,
    ( $false
    | spl17_2 ),
    inference(subsumption_resolution,[],[f511,f71])).

fof(f71,plain,(
    ~ v2_struct_0(sK10) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( ( ~ r2_yellow_0(sK10,u1_struct_0(sK10))
      | ~ r1_yellow_0(sK10,k1_xboole_0) )
    & l1_orders_2(sK10)
    & v1_yellow_0(sK10)
    & v5_orders_2(sK10)
    & ~ v2_struct_0(sK10) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f12,f40])).

fof(f40,plain,
    ( ? [X0] :
        ( ( ~ r2_yellow_0(X0,u1_struct_0(X0))
          | ~ r1_yellow_0(X0,k1_xboole_0) )
        & l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ( ~ r2_yellow_0(sK10,u1_struct_0(sK10))
        | ~ r1_yellow_0(sK10,k1_xboole_0) )
      & l1_orders_2(sK10)
      & v1_yellow_0(sK10)
      & v5_orders_2(sK10)
      & ~ v2_struct_0(sK10) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ( ~ r2_yellow_0(X0,u1_struct_0(X0))
        | ~ r1_yellow_0(X0,k1_xboole_0) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ( ~ r2_yellow_0(X0,u1_struct_0(X0))
        | ~ r1_yellow_0(X0,k1_xboole_0) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_yellow_0(X0)
          & v5_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ( r2_yellow_0(X0,u1_struct_0(X0))
          & r1_yellow_0(X0,k1_xboole_0) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r2_yellow_0(X0,u1_struct_0(X0))
        & r1_yellow_0(X0,k1_xboole_0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_yellow_0)).

fof(f511,plain,
    ( v2_struct_0(sK10)
    | spl17_2 ),
    inference(subsumption_resolution,[],[f510,f125])).

fof(f125,plain,(
    l1_struct_0(sK10) ),
    inference(resolution,[],[f76,f74])).

fof(f74,plain,(
    l1_orders_2(sK10) ),
    inference(cnf_transformation,[],[f41])).

fof(f76,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f510,plain,
    ( ~ l1_struct_0(sK10)
    | v2_struct_0(sK10)
    | spl17_2 ),
    inference(resolution,[],[f509,f92])).

fof(f92,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

% (5296)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
fof(f18,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f509,plain,
    ( v1_xboole_0(u1_struct_0(sK10))
    | spl17_2 ),
    inference(subsumption_resolution,[],[f508,f133])).

fof(f133,plain,(
    sP9(sK10) ),
    inference(subsumption_resolution,[],[f132,f74])).

fof(f132,plain,
    ( ~ l1_orders_2(sK10)
    | sP9(sK10) ),
    inference(resolution,[],[f114,f72])).

fof(f72,plain,(
    v5_orders_2(sK10) ),
    inference(cnf_transformation,[],[f41])).

fof(f114,plain,(
    ! [X0] :
      ( ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | sP9(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( sP9(X0)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(definition_folding,[],[f23,f38,f37,f36])).

% (5284)dis+1002_8:1_awrs=converge:awrsf=256:anc=all_dependent:br=off:fsr=off:fde=none:gs=on:gsaa=from_current:gsem=on:irw=on:nm=64:nwc=1:sas=z3:s2a=on:sp=frequency:thf=on:uwa=interpreted_only:urr=on_7 on theBenchmark
fof(f36,plain,(
    ! [X2,X0,X1] :
      ( sP7(X2,X0,X1)
    <=> ! [X3] :
          ( r1_orders_2(X0,X3,X2)
          | ~ r1_lattice3(X0,X1,X3)
          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP7])])).

fof(f37,plain,(
    ! [X1,X0] :
      ( sP8(X1,X0)
    <=> ? [X2] :
          ( sP7(X2,X0,X1)
          & r1_lattice3(X0,X1,X2)
          & m1_subset_1(X2,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP8])])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_yellow_0(X0,X1)
        <=> sP8(X1,X0) )
      | ~ sP9(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP9])])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r1_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r1_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( r2_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r1_lattice3(X0,X1,X3)
                   => r1_orders_2(X0,X3,X2) ) )
              & r1_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_yellow_0)).

fof(f508,plain,
    ( v1_xboole_0(u1_struct_0(sK10))
    | ~ sP9(sK10)
    | spl17_2 ),
    inference(subsumption_resolution,[],[f507,f128])).

fof(f128,plain,(
    sP0(sK10) ),
    inference(subsumption_resolution,[],[f127,f73])).

fof(f73,plain,(
    v1_yellow_0(sK10) ),
    inference(cnf_transformation,[],[f41])).

fof(f127,plain,
    ( ~ v1_yellow_0(sK10)
    | sP0(sK10) ),
    inference(resolution,[],[f77,f126])).

fof(f126,plain,(
    sP1(sK10) ),
    inference(resolution,[],[f82,f74])).

fof(f82,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | sP1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f14,f27,f26])).

fof(f26,plain,(
    ! [X0] :
      ( sP0(X0)
    <=> ? [X1] :
          ( r1_lattice3(X0,u1_struct_0(X0),X1)
          & m1_subset_1(X1,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_yellow_0(X0)
      <=> sP0(X0) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f14,plain,(
    ! [X0] :
      ( ( v1_yellow_0(X0)
      <=> ? [X1] :
            ( r1_lattice3(X0,u1_struct_0(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_yellow_0(X0)
      <=> ? [X1] :
            ( r1_lattice3(X0,u1_struct_0(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_yellow_0)).

fof(f77,plain,(
    ! [X0] :
      ( ~ sP1(X0)
      | ~ v1_yellow_0(X0)
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ( ( v1_yellow_0(X0)
          | ~ sP0(X0) )
        & ( sP0(X0)
          | ~ v1_yellow_0(X0) ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f507,plain,
    ( v1_xboole_0(u1_struct_0(sK10))
    | ~ sP0(sK10)
    | ~ sP9(sK10)
    | spl17_2 ),
    inference(subsumption_resolution,[],[f504,f74])).

fof(f504,plain,
    ( ~ l1_orders_2(sK10)
    | v1_xboole_0(u1_struct_0(sK10))
    | ~ sP0(sK10)
    | ~ sP9(sK10)
    | spl17_2 ),
    inference(resolution,[],[f502,f123])).

fof(f123,plain,
    ( ~ r2_yellow_0(sK10,u1_struct_0(sK10))
    | spl17_2 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl17_2
  <=> r2_yellow_0(sK10,u1_struct_0(sK10)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_2])])).

fof(f502,plain,(
    ! [X2] :
      ( r2_yellow_0(X2,u1_struct_0(X2))
      | ~ l1_orders_2(X2)
      | v1_xboole_0(u1_struct_0(X2))
      | ~ sP0(X2)
      | ~ sP9(X2) ) ),
    inference(resolution,[],[f499,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( ~ sP8(X1,X0)
      | r2_yellow_0(X0,X1)
      | ~ sP9(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_yellow_0(X0,X1)
            | ~ sP8(X1,X0) )
          & ( sP8(X1,X0)
            | ~ r2_yellow_0(X0,X1) ) )
      | ~ sP9(X0) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f499,plain,(
    ! [X0] :
      ( sP8(u1_struct_0(X0),X0)
      | ~ sP0(X0)
      | ~ l1_orders_2(X0)
      | v1_xboole_0(u1_struct_0(X0)) ) ),
    inference(duplicate_literal_removal,[],[f498])).

fof(f498,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | sP8(u1_struct_0(X0),X0)
      | ~ l1_orders_2(X0)
      | v1_xboole_0(u1_struct_0(X0))
      | ~ sP0(X0) ) ),
    inference(resolution,[],[f497,f134])).

fof(f134,plain,(
    ! [X0] :
      ( r2_hidden(sK11(X0),u1_struct_0(X0))
      | v1_xboole_0(u1_struct_0(X0))
      | ~ sP0(X0) ) ),
    inference(resolution,[],[f115,f79])).

fof(f79,plain,(
    ! [X0] :
      ( m1_subset_1(sK11(X0),u1_struct_0(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ! [X1] :
            ( ~ r1_lattice3(X0,u1_struct_0(X0),X1)
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      & ( ( r1_lattice3(X0,u1_struct_0(X0),sK11(X0))
          & m1_subset_1(sK11(X0),u1_struct_0(X0)) )
        | ~ sP0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f44,f45])).

fof(f45,plain,(
    ! [X0] :
      ( ? [X2] :
          ( r1_lattice3(X0,u1_struct_0(X0),X2)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( r1_lattice3(X0,u1_struct_0(X0),sK11(X0))
        & m1_subset_1(sK11(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ! [X1] :
            ( ~ r1_lattice3(X0,u1_struct_0(X0),X1)
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      & ( ? [X2] :
            ( r1_lattice3(X0,u1_struct_0(X0),X2)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        | ~ sP0(X0) ) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ! [X1] :
            ( ~ r1_lattice3(X0,u1_struct_0(X0),X1)
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      & ( ? [X1] :
            ( r1_lattice3(X0,u1_struct_0(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) )
        | ~ sP0(X0) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f115,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f497,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK11(X0),u1_struct_0(X0))
      | ~ sP0(X0)
      | sP8(u1_struct_0(X0),X0)
      | ~ l1_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f492])).

fof(f492,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK11(X0),u1_struct_0(X0))
      | ~ sP0(X0)
      | sP8(u1_struct_0(X0),X0)
      | ~ l1_orders_2(X0)
      | ~ sP0(X0) ) ),
    inference(resolution,[],[f485,f80])).

fof(f80,plain,(
    ! [X0] :
      ( r1_lattice3(X0,u1_struct_0(X0),sK11(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f485,plain,(
    ! [X4,X3] :
      ( ~ r1_lattice3(X3,X4,sK11(X3))
      | ~ r2_hidden(sK11(X3),X4)
      | ~ sP0(X3)
      | sP8(X4,X3)
      | ~ l1_orders_2(X3) ) ),
    inference(subsumption_resolution,[],[f484,f79])).

fof(f484,plain,(
    ! [X4,X3] :
      ( ~ l1_orders_2(X3)
      | ~ r2_hidden(sK11(X3),X4)
      | ~ sP0(X3)
      | sP8(X4,X3)
      | ~ r1_lattice3(X3,X4,sK11(X3))
      | ~ m1_subset_1(sK11(X3),u1_struct_0(X3)) ) ),
    inference(resolution,[],[f477,f109])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( ~ sP7(X2,X1,X0)
      | sP8(X0,X1)
      | ~ r1_lattice3(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ( sP8(X0,X1)
        | ! [X2] :
            ( ~ sP7(X2,X1,X0)
            | ~ r1_lattice3(X1,X0,X2)
            | ~ m1_subset_1(X2,u1_struct_0(X1)) ) )
      & ( ( sP7(sK15(X0,X1),X1,X0)
          & r1_lattice3(X1,X0,sK15(X0,X1))
          & m1_subset_1(sK15(X0,X1),u1_struct_0(X1)) )
        | ~ sP8(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15])],[f64,f65])).

fof(f65,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( sP7(X3,X1,X0)
          & r1_lattice3(X1,X0,X3)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( sP7(sK15(X0,X1),X1,X0)
        & r1_lattice3(X1,X0,sK15(X0,X1))
        & m1_subset_1(sK15(X0,X1),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( sP8(X0,X1)
        | ! [X2] :
            ( ~ sP7(X2,X1,X0)
            | ~ r1_lattice3(X1,X0,X2)
            | ~ m1_subset_1(X2,u1_struct_0(X1)) ) )
      & ( ? [X3] :
            ( sP7(X3,X1,X0)
            & r1_lattice3(X1,X0,X3)
            & m1_subset_1(X3,u1_struct_0(X1)) )
        | ~ sP8(X0,X1) ) ) ),
    inference(rectify,[],[f63])).

fof(f63,plain,(
    ! [X1,X0] :
      ( ( sP8(X1,X0)
        | ! [X2] :
            ( ~ sP7(X2,X0,X1)
            | ~ r1_lattice3(X0,X1,X2)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
      & ( ? [X2] :
            ( sP7(X2,X0,X1)
            & r1_lattice3(X0,X1,X2)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        | ~ sP8(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f477,plain,(
    ! [X0,X1] :
      ( sP7(sK11(X0),X0,X1)
      | ~ l1_orders_2(X0)
      | ~ r2_hidden(sK11(X0),X1)
      | ~ sP0(X0) ) ),
    inference(resolution,[],[f474,f79])).

fof(f474,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ r2_hidden(X1,X2)
      | ~ l1_orders_2(X0)
      | sP7(X1,X0,X2) ) ),
    inference(duplicate_literal_removal,[],[f471])).

fof(f471,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | sP7(X1,X0,X2)
      | sP7(X1,X0,X2) ) ),
    inference(resolution,[],[f415,f113])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X1,sK16(X0,X1,X2),X0)
      | sP7(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1,X2] :
      ( ( sP7(X0,X1,X2)
        | ( ~ r1_orders_2(X1,sK16(X0,X1,X2),X0)
          & r1_lattice3(X1,X2,sK16(X0,X1,X2))
          & m1_subset_1(sK16(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_orders_2(X1,X4,X0)
            | ~ r1_lattice3(X1,X2,X4)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP7(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK16])],[f68,f69])).

fof(f69,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X1,X3,X0)
          & r1_lattice3(X1,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_orders_2(X1,sK16(X0,X1,X2),X0)
        & r1_lattice3(X1,X2,sK16(X0,X1,X2))
        & m1_subset_1(sK16(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f68,plain,(
    ! [X0,X1,X2] :
      ( ( sP7(X0,X1,X2)
        | ? [X3] :
            ( ~ r1_orders_2(X1,X3,X0)
            & r1_lattice3(X1,X2,X3)
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_orders_2(X1,X4,X0)
            | ~ r1_lattice3(X1,X2,X4)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP7(X0,X1,X2) ) ) ),
    inference(rectify,[],[f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ( sP7(X2,X0,X1)
        | ? [X3] :
            ( ~ r1_orders_2(X0,X3,X2)
            & r1_lattice3(X0,X1,X3)
            & m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ! [X3] :
            ( r1_orders_2(X0,X3,X2)
            | ~ r1_lattice3(X0,X1,X3)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        | ~ sP7(X2,X0,X1) ) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f415,plain,(
    ! [X6,X4,X5,X3] :
      ( r1_orders_2(X4,sK16(X3,X4,X5),X6)
      | ~ l1_orders_2(X4)
      | ~ r2_hidden(X6,X5)
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | sP7(X3,X4,X5) ) ),
    inference(resolution,[],[f410,f87])).

fof(f87,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | r1_orders_2(X1,X0,X4) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ( ~ r1_orders_2(X1,X0,sK12(X0,X1,X2))
          & r2_hidden(sK12(X0,X1,X2),X2)
          & m1_subset_1(sK12(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_orders_2(X1,X0,X4)
            | ~ r2_hidden(X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f50,f51])).

fof(f51,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X1,X0,X3)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_orders_2(X1,X0,sK12(X0,X1,X2))
        & r2_hidden(sK12(X0,X1,X2),X2)
        & m1_subset_1(sK12(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
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
    inference(rectify,[],[f49])).

fof(f49,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( sP2(X2,X0,X1)
    <=> ! [X3] :
          ( r1_orders_2(X0,X2,X3)
          | ~ r2_hidden(X3,X1)
          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f410,plain,(
    ! [X2,X0,X1] :
      ( sP2(sK16(X1,X0,X2),X0,X2)
      | sP7(X1,X0,X2)
      | ~ l1_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f407])).

fof(f407,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | sP7(X1,X0,X2)
      | sP2(sK16(X1,X0,X2),X0,X2)
      | sP7(X1,X0,X2) ) ),
    inference(resolution,[],[f174,f112])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X1,X2,sK16(X0,X1,X2))
      | sP7(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f174,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_lattice3(X5,X7,sK16(X4,X5,X6))
      | ~ l1_orders_2(X5)
      | sP7(X4,X5,X6)
      | sP2(sK16(X4,X5,X6),X5,X7) ) ),
    inference(resolution,[],[f157,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ sP3(X0,X1,X2)
      | ~ r1_lattice3(X1,X0,X2)
      | sP2(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( ( r1_lattice3(X1,X0,X2)
          | ~ sP2(X2,X1,X0) )
        & ( sP2(X2,X1,X0)
          | ~ r1_lattice3(X1,X0,X2) ) )
      | ~ sP3(X0,X1,X2) ) ),
    inference(rectify,[],[f47])).

fof(f47,plain,(
    ! [X1,X0,X2] :
      ( ( ( r1_lattice3(X0,X1,X2)
          | ~ sP2(X2,X0,X1) )
        & ( sP2(X2,X0,X1)
          | ~ r1_lattice3(X0,X1,X2) ) )
      | ~ sP3(X1,X0,X2) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X1,X0,X2] :
      ( ( r1_lattice3(X0,X1,X2)
      <=> sP2(X2,X0,X1) )
      | ~ sP3(X1,X0,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f157,plain,(
    ! [X2,X0,X3,X1] :
      ( sP3(X3,X1,sK16(X0,X1,X2))
      | sP7(X0,X1,X2)
      | ~ l1_orders_2(X1) ) ),
    inference(resolution,[],[f111,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | sP3(X1,X0,X2)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( sP3(X1,X0,X2)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f17,f30,f29])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_lattice3)).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK16(X0,X1,X2),u1_struct_0(X1))
      | sP7(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f249,plain,(
    spl17_1 ),
    inference(avatar_contradiction_clause,[],[f248])).

fof(f248,plain,
    ( $false
    | spl17_1 ),
    inference(subsumption_resolution,[],[f247,f131])).

fof(f131,plain,(
    sP6(sK10) ),
    inference(subsumption_resolution,[],[f130,f74])).

fof(f130,plain,
    ( ~ l1_orders_2(sK10)
    | sP6(sK10) ),
    inference(resolution,[],[f103,f72])).

fof(f103,plain,(
    ! [X0] :
      ( ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | sP6(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( sP6(X0)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(definition_folding,[],[f21,f34,f33,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( sP4(X2,X0,X1)
    <=> ! [X3] :
          ( r1_orders_2(X0,X2,X3)
          | ~ r2_lattice3(X0,X1,X3)
          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f33,plain,(
    ! [X1,X0] :
      ( sP5(X1,X0)
    <=> ? [X2] :
          ( sP4(X2,X0,X1)
          & r2_lattice3(X0,X1,X2)
          & m1_subset_1(X2,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> sP5(X1,X0) )
      | ~ sP6(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP6])])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r2_lattice3(X0,X1,X3)
                   => r1_orders_2(X0,X2,X3) ) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_yellow_0)).

fof(f247,plain,
    ( ~ sP6(sK10)
    | spl17_1 ),
    inference(subsumption_resolution,[],[f246,f74])).

fof(f246,plain,
    ( ~ l1_orders_2(sK10)
    | ~ sP6(sK10)
    | spl17_1 ),
    inference(subsumption_resolution,[],[f245,f71])).

fof(f245,plain,
    ( v2_struct_0(sK10)
    | ~ l1_orders_2(sK10)
    | ~ sP6(sK10)
    | spl17_1 ),
    inference(subsumption_resolution,[],[f242,f128])).

fof(f242,plain,
    ( ~ sP0(sK10)
    | v2_struct_0(sK10)
    | ~ l1_orders_2(sK10)
    | ~ sP6(sK10)
    | spl17_1 ),
    inference(resolution,[],[f241,f119])).

fof(f119,plain,
    ( ~ r1_yellow_0(sK10,k1_xboole_0)
    | spl17_1 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl17_1
  <=> r1_yellow_0(sK10,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_1])])).

fof(f241,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ sP0(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | ~ sP6(X0) ) ),
    inference(resolution,[],[f240,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ sP5(X1,X0)
      | r1_yellow_0(X0,X1)
      | ~ sP6(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_yellow_0(X0,X1)
            | ~ sP5(X1,X0) )
          & ( sP5(X1,X0)
            | ~ r1_yellow_0(X0,X1) ) )
      | ~ sP6(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f240,plain,(
    ! [X0] :
      ( sP5(k1_xboole_0,X0)
      | ~ l1_orders_2(X0)
      | ~ sP0(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f239,f76])).

fof(f239,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | sP5(k1_xboole_0,X0)
      | ~ sP0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f238,f92])).

fof(f238,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | sP5(k1_xboole_0,X0)
      | ~ sP0(X0) ) ),
    inference(duplicate_literal_removal,[],[f237])).

fof(f237,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | v1_xboole_0(u1_struct_0(X0))
      | sP5(k1_xboole_0,X0)
      | ~ sP0(X0)
      | ~ l1_orders_2(X0)
      | ~ sP0(X0) ) ),
    inference(resolution,[],[f236,f137])).

fof(f137,plain,(
    ! [X0] :
      ( r2_lattice3(X0,k1_xboole_0,sK11(X0))
      | ~ l1_orders_2(X0)
      | ~ sP0(X0) ) ),
    inference(resolution,[],[f83,f79])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | r2_lattice3(X0,k1_xboole_0,X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_lattice3(X0,k1_xboole_0,X1)
            & r2_lattice3(X0,k1_xboole_0,X1) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( r1_lattice3(X0,k1_xboole_0,X1)
            & r2_lattice3(X0,k1_xboole_0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_yellow_0)).

fof(f236,plain,(
    ! [X4,X3] :
      ( ~ r2_lattice3(X3,X4,sK11(X3))
      | ~ l1_orders_2(X3)
      | v1_xboole_0(u1_struct_0(X3))
      | sP5(X4,X3)
      | ~ sP0(X3) ) ),
    inference(subsumption_resolution,[],[f235,f79])).

fof(f235,plain,(
    ! [X4,X3] :
      ( ~ sP0(X3)
      | ~ l1_orders_2(X3)
      | v1_xboole_0(u1_struct_0(X3))
      | sP5(X4,X3)
      | ~ r2_lattice3(X3,X4,sK11(X3))
      | ~ m1_subset_1(sK11(X3),u1_struct_0(X3)) ) ),
    inference(resolution,[],[f233,f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ sP4(X2,X1,X0)
      | sP5(X0,X1)
      | ~ r2_lattice3(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( sP5(X0,X1)
        | ! [X2] :
            ( ~ sP4(X2,X1,X0)
            | ~ r2_lattice3(X1,X0,X2)
            | ~ m1_subset_1(X2,u1_struct_0(X1)) ) )
      & ( ( sP4(sK13(X0,X1),X1,X0)
          & r2_lattice3(X1,X0,sK13(X0,X1))
          & m1_subset_1(sK13(X0,X1),u1_struct_0(X1)) )
        | ~ sP5(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13])],[f55,f56])).

fof(f56,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( sP4(X3,X1,X0)
          & r2_lattice3(X1,X0,X3)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( sP4(sK13(X0,X1),X1,X0)
        & r2_lattice3(X1,X0,sK13(X0,X1))
        & m1_subset_1(sK13(X0,X1),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( sP5(X0,X1)
        | ! [X2] :
            ( ~ sP4(X2,X1,X0)
            | ~ r2_lattice3(X1,X0,X2)
            | ~ m1_subset_1(X2,u1_struct_0(X1)) ) )
      & ( ? [X3] :
            ( sP4(X3,X1,X0)
            & r2_lattice3(X1,X0,X3)
            & m1_subset_1(X3,u1_struct_0(X1)) )
        | ~ sP5(X0,X1) ) ) ),
    inference(rectify,[],[f54])).

fof(f54,plain,(
    ! [X1,X0] :
      ( ( sP5(X1,X0)
        | ! [X2] :
            ( ~ sP4(X2,X0,X1)
            | ~ r2_lattice3(X0,X1,X2)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
      & ( ? [X2] :
            ( sP4(X2,X0,X1)
            & r2_lattice3(X0,X1,X2)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        | ~ sP5(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f233,plain,(
    ! [X0,X1] :
      ( sP4(sK11(X0),X0,X1)
      | ~ sP0(X0)
      | ~ l1_orders_2(X0)
      | v1_xboole_0(u1_struct_0(X0)) ) ),
    inference(duplicate_literal_removal,[],[f232])).

fof(f232,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ sP0(X0)
      | sP4(sK11(X0),X0,X1)
      | v1_xboole_0(u1_struct_0(X0))
      | sP4(sK11(X0),X0,X1) ) ),
    inference(resolution,[],[f221,f156])).

fof(f156,plain,(
    ! [X12,X10,X11] :
      ( r2_hidden(sK14(X10,X11,X12),u1_struct_0(X11))
      | v1_xboole_0(u1_struct_0(X11))
      | sP4(X10,X11,X12) ) ),
    inference(resolution,[],[f100,f115])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK14(X0,X1,X2),u1_struct_0(X1))
      | sP4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( ( sP4(X0,X1,X2)
        | ( ~ r1_orders_2(X1,X0,sK14(X0,X1,X2))
          & r2_lattice3(X1,X2,sK14(X0,X1,X2))
          & m1_subset_1(sK14(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_orders_2(X1,X0,X4)
            | ~ r2_lattice3(X1,X2,X4)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP4(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14])],[f59,f60])).

fof(f60,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X1,X0,X3)
          & r2_lattice3(X1,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_orders_2(X1,X0,sK14(X0,X1,X2))
        & r2_lattice3(X1,X2,sK14(X0,X1,X2))
        & m1_subset_1(sK14(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( ( sP4(X0,X1,X2)
        | ? [X3] :
            ( ~ r1_orders_2(X1,X0,X3)
            & r2_lattice3(X1,X2,X3)
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_orders_2(X1,X0,X4)
            | ~ r2_lattice3(X1,X2,X4)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP4(X0,X1,X2) ) ) ),
    inference(rectify,[],[f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ( sP4(X2,X0,X1)
        | ? [X3] :
            ( ~ r1_orders_2(X0,X2,X3)
            & r2_lattice3(X0,X1,X3)
            & m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ! [X3] :
            ( r1_orders_2(X0,X2,X3)
            | ~ r2_lattice3(X0,X1,X3)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        | ~ sP4(X2,X0,X1) ) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f221,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(sK14(sK11(X2),X2,X3),u1_struct_0(X2))
      | ~ l1_orders_2(X2)
      | ~ sP0(X2)
      | sP4(sK11(X2),X2,X3) ) ),
    inference(subsumption_resolution,[],[f219,f100])).

fof(f219,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(sK14(sK11(X2),X2,X3),u1_struct_0(X2))
      | ~ r2_hidden(sK14(sK11(X2),X2,X3),u1_struct_0(X2))
      | ~ l1_orders_2(X2)
      | ~ sP0(X2)
      | sP4(sK11(X2),X2,X3) ) ),
    inference(resolution,[],[f184,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X1,X0,sK14(X0,X1,X2))
      | sP4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f184,plain,(
    ! [X2,X3] :
      ( r1_orders_2(X3,sK11(X3),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X3))
      | ~ r2_hidden(X2,u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | ~ sP0(X3) ) ),
    inference(resolution,[],[f87,f178])).

fof(f178,plain,(
    ! [X0] :
      ( sP2(sK11(X0),X0,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ sP0(X0) ) ),
    inference(duplicate_literal_removal,[],[f175])).

fof(f175,plain,(
    ! [X0] :
      ( sP2(sK11(X0),X0,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ sP0(X0)
      | ~ sP0(X0) ) ),
    inference(resolution,[],[f163,f80])).

fof(f163,plain,(
    ! [X0,X1] :
      ( ~ r1_lattice3(X0,X1,sK11(X0))
      | sP2(sK11(X0),X0,X1)
      | ~ l1_orders_2(X0)
      | ~ sP0(X0) ) ),
    inference(resolution,[],[f85,f143])).

fof(f143,plain,(
    ! [X0,X1] :
      ( sP3(X0,X1,sK11(X1))
      | ~ l1_orders_2(X1)
      | ~ sP0(X1) ) ),
    inference(resolution,[],[f91,f79])).

fof(f124,plain,
    ( ~ spl17_1
    | ~ spl17_2 ),
    inference(avatar_split_clause,[],[f75,f121,f117])).

fof(f75,plain,
    ( ~ r2_yellow_0(sK10,u1_struct_0(sK10))
    | ~ r1_yellow_0(sK10,k1_xboole_0) ),
    inference(cnf_transformation,[],[f41])).

%------------------------------------------------------------------------------
