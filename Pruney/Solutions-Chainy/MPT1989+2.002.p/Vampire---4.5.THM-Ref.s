%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:59 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  180 ( 867 expanded)
%              Number of leaves         :   24 ( 275 expanded)
%              Depth                    :   23
%              Number of atoms          :  977 (6641 expanded)
%              Number of equality atoms :   39 (  62 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (23251)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
fof(f2486,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f315,f469,f503,f581,f1464,f1472,f1480,f1921,f2485])).

fof(f2485,plain,
    ( spl5_13
    | ~ spl5_41
    | ~ spl5_43
    | spl5_44 ),
    inference(avatar_contradiction_clause,[],[f2484])).

fof(f2484,plain,
    ( $false
    | spl5_13
    | ~ spl5_41
    | ~ spl5_43
    | spl5_44 ),
    inference(subsumption_resolution,[],[f2482,f1471])).

fof(f1471,plain,
    ( r2_lattice3(sK0,k5_waybel_0(sK0,sK1),sK3(sK0,sK1,k5_waybel_0(sK0,sK1)))
    | ~ spl5_43 ),
    inference(avatar_component_clause,[],[f1469])).

fof(f1469,plain,
    ( spl5_43
  <=> r2_lattice3(sK0,k5_waybel_0(sK0,sK1),sK3(sK0,sK1,k5_waybel_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).

fof(f2482,plain,
    ( ~ r2_lattice3(sK0,k5_waybel_0(sK0,sK1),sK3(sK0,sK1,k5_waybel_0(sK0,sK1)))
    | spl5_13
    | ~ spl5_41
    | spl5_44 ),
    inference(resolution,[],[f1679,f586])).

fof(f586,plain,
    ( r2_hidden(sK1,k5_waybel_0(sK0,sK1))
    | spl5_13 ),
    inference(subsumption_resolution,[],[f585,f154])).

fof(f154,plain,
    ( ~ v2_struct_0(sK0)
    | spl5_13 ),
    inference(avatar_component_clause,[],[f153])).

fof(f153,plain,
    ( spl5_13
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f585,plain,
    ( r2_hidden(sK1,k5_waybel_0(sK0,sK1))
    | v2_struct_0(sK0)
    | spl5_13 ),
    inference(subsumption_resolution,[],[f584,f57])).

fof(f57,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( ~ v4_waybel_7(sK1,sK0)
    & v5_waybel_6(sK1,sK0)
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v2_lattice3(sK0)
    & v1_lattice3(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f39,f38])).

fof(f38,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v4_waybel_7(X1,X0)
            & v5_waybel_6(X1,X0)
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
   => ( ? [X1] :
          ( ~ v4_waybel_7(X1,sK0)
          & v5_waybel_6(X1,sK0)
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & v2_lattice3(sK0)
      & v1_lattice3(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X1] :
        ( ~ v4_waybel_7(X1,sK0)
        & v5_waybel_6(X1,sK0)
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ~ v4_waybel_7(sK1,sK0)
      & v5_waybel_6(sK1,sK0)
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v4_waybel_7(X1,X0)
          & v5_waybel_6(X1,X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v4_waybel_7(X1,X0)
          & v5_waybel_6(X1,X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( v5_waybel_6(X1,X0)
             => v4_waybel_7(X1,X0) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v5_waybel_6(X1,X0)
           => v4_waybel_7(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_waybel_7)).

fof(f584,plain,
    ( r2_hidden(sK1,k5_waybel_0(sK0,sK1))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl5_13 ),
    inference(subsumption_resolution,[],[f583,f58])).

fof(f58,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f40])).

fof(f583,plain,
    ( r2_hidden(sK1,k5_waybel_0(sK0,sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl5_13 ),
    inference(duplicate_literal_removal,[],[f582])).

fof(f582,plain,
    ( r2_hidden(sK1,k5_waybel_0(sK0,sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl5_13 ),
    inference(resolution,[],[f541,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k5_waybel_0(X0,X1))
      | ~ r1_orders_2(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k5_waybel_0(X0,X1))
                  | ~ r1_orders_2(X0,X2,X1) )
                & ( r1_orders_2(X0,X2,X1)
                  | ~ r2_hidden(X2,k5_waybel_0(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k5_waybel_0(X0,X1))
              <=> r1_orders_2(X0,X2,X1) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k5_waybel_0(X0,X1))
              <=> r1_orders_2(X0,X2,X1) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k5_waybel_0(X0,X1))
              <=> r1_orders_2(X0,X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_waybel_0)).

fof(f541,plain,
    ( r1_orders_2(sK0,sK1,sK1)
    | spl5_13 ),
    inference(subsumption_resolution,[],[f540,f154])).

fof(f540,plain,
    ( r1_orders_2(sK0,sK1,sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f539,f52])).

fof(f52,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f539,plain,
    ( r1_orders_2(sK0,sK1,sK1)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f511,f57])).

fof(f511,plain,
    ( r1_orders_2(sK0,sK1,sK1)
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f58,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,X1,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,X1,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r1_orders_2(X0,X1,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_orders_2)).

fof(f1679,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK1,X0)
        | ~ r2_lattice3(sK0,X0,sK3(sK0,sK1,k5_waybel_0(sK0,sK1))) )
    | ~ spl5_41
    | spl5_44 ),
    inference(subsumption_resolution,[],[f1678,f57])).

fof(f1678,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK1,X0)
        | ~ r2_lattice3(sK0,X0,sK3(sK0,sK1,k5_waybel_0(sK0,sK1)))
        | ~ l1_orders_2(sK0) )
    | ~ spl5_41
    | spl5_44 ),
    inference(subsumption_resolution,[],[f1677,f1459])).

fof(f1459,plain,
    ( m1_subset_1(sK3(sK0,sK1,k5_waybel_0(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl5_41 ),
    inference(avatar_component_clause,[],[f1457])).

fof(f1457,plain,
    ( spl5_41
  <=> m1_subset_1(sK3(sK0,sK1,k5_waybel_0(sK0,sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).

fof(f1677,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK1,X0)
        | ~ r2_lattice3(sK0,X0,sK3(sK0,sK1,k5_waybel_0(sK0,sK1)))
        | ~ m1_subset_1(sK3(sK0,sK1,k5_waybel_0(sK0,sK1)),u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | spl5_44 ),
    inference(subsumption_resolution,[],[f1675,f58])).

fof(f1675,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK1,X0)
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X0,sK3(sK0,sK1,k5_waybel_0(sK0,sK1)))
        | ~ m1_subset_1(sK3(sK0,sK1,k5_waybel_0(sK0,sK1)),u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | spl5_44 ),
    inference(resolution,[],[f1479,f86])).

fof(f86,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,sK4(X0,X1,X2),X2)
                & r2_hidden(sK4(X0,X1,X2),X1)
                & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f49,f50])).

fof(f50,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK4(X0,X1,X2),X2)
        & r2_hidden(sK4(X0,X1,X2),X1)
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X3,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattice3)).

fof(f1479,plain,
    ( ~ r1_orders_2(sK0,sK1,sK3(sK0,sK1,k5_waybel_0(sK0,sK1)))
    | spl5_44 ),
    inference(avatar_component_clause,[],[f1477])).

fof(f1477,plain,
    ( spl5_44
  <=> r1_orders_2(sK0,sK1,sK3(sK0,sK1,k5_waybel_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).

fof(f1921,plain,
    ( spl5_13
    | ~ spl5_31
    | ~ spl5_42 ),
    inference(avatar_contradiction_clause,[],[f1920])).

fof(f1920,plain,
    ( $false
    | spl5_13
    | ~ spl5_31
    | ~ spl5_42 ),
    inference(subsumption_resolution,[],[f1919,f52])).

fof(f1919,plain,
    ( ~ v3_orders_2(sK0)
    | spl5_13
    | ~ spl5_31
    | ~ spl5_42 ),
    inference(subsumption_resolution,[],[f1918,f53])).

fof(f53,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f1918,plain,
    ( ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | spl5_13
    | ~ spl5_31
    | ~ spl5_42 ),
    inference(subsumption_resolution,[],[f1917,f54])).

fof(f54,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f1917,plain,
    ( ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | spl5_13
    | ~ spl5_31
    | ~ spl5_42 ),
    inference(subsumption_resolution,[],[f1916,f55])).

fof(f55,plain,(
    v1_lattice3(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f1916,plain,
    ( ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | spl5_13
    | ~ spl5_31
    | ~ spl5_42 ),
    inference(subsumption_resolution,[],[f1915,f56])).

fof(f56,plain,(
    v2_lattice3(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f1915,plain,
    ( ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | spl5_13
    | ~ spl5_31
    | ~ spl5_42 ),
    inference(subsumption_resolution,[],[f1914,f57])).

fof(f1914,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | spl5_13
    | ~ spl5_31
    | ~ spl5_42 ),
    inference(subsumption_resolution,[],[f1913,f559])).

fof(f559,plain,
    ( ~ v1_xboole_0(k5_waybel_0(sK0,sK1))
    | spl5_13 ),
    inference(subsumption_resolution,[],[f558,f154])).

fof(f558,plain,
    ( ~ v1_xboole_0(k5_waybel_0(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f557,f52])).

fof(f557,plain,
    ( ~ v1_xboole_0(k5_waybel_0(sK0,sK1))
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f519,f57])).

fof(f519,plain,
    ( ~ v1_xboole_0(k5_waybel_0(sK0,sK1))
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f58,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k5_waybel_0(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v1_waybel_0(k5_waybel_0(X0,X1),X0)
        & ~ v1_xboole_0(k5_waybel_0(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v1_waybel_0(k5_waybel_0(X0,X1),X0)
        & ~ v1_xboole_0(k5_waybel_0(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_waybel_0(k5_waybel_0(X0,X1),X0)
        & ~ v1_xboole_0(k5_waybel_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_waybel_0)).

fof(f1913,plain,
    ( v1_xboole_0(k5_waybel_0(sK0,sK1))
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | spl5_13
    | ~ spl5_31
    | ~ spl5_42 ),
    inference(subsumption_resolution,[],[f1912,f562])).

fof(f562,plain,
    ( v1_waybel_0(k5_waybel_0(sK0,sK1),sK0)
    | spl5_13 ),
    inference(subsumption_resolution,[],[f561,f154])).

fof(f561,plain,
    ( v1_waybel_0(k5_waybel_0(sK0,sK1),sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f560,f52])).

fof(f560,plain,
    ( v1_waybel_0(k5_waybel_0(sK0,sK1),sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f520,f57])).

fof(f520,plain,
    ( v1_waybel_0(k5_waybel_0(sK0,sK1),sK0)
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f58,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( v1_waybel_0(k5_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f1912,plain,
    ( ~ v1_waybel_0(k5_waybel_0(sK0,sK1),sK0)
    | v1_xboole_0(k5_waybel_0(sK0,sK1))
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | spl5_13
    | ~ spl5_31
    | ~ spl5_42 ),
    inference(subsumption_resolution,[],[f1911,f556])).

fof(f556,plain,
    ( v12_waybel_0(k5_waybel_0(sK0,sK1),sK0)
    | spl5_13 ),
    inference(subsumption_resolution,[],[f555,f154])).

fof(f555,plain,
    ( v12_waybel_0(k5_waybel_0(sK0,sK1),sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f554,f53])).

fof(f554,plain,
    ( v12_waybel_0(k5_waybel_0(sK0,sK1),sK0)
    | ~ v4_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f518,f57])).

fof(f518,plain,
    ( v12_waybel_0(k5_waybel_0(sK0,sK1),sK0)
    | ~ l1_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f58,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( v12_waybel_0(k5_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v12_waybel_0(k5_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( v12_waybel_0(k5_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v4_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => v12_waybel_0(k5_waybel_0(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc12_waybel_0)).

fof(f1911,plain,
    ( ~ v12_waybel_0(k5_waybel_0(sK0,sK1),sK0)
    | ~ v1_waybel_0(k5_waybel_0(sK0,sK1),sK0)
    | v1_xboole_0(k5_waybel_0(sK0,sK1))
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | spl5_13
    | ~ spl5_31
    | ~ spl5_42 ),
    inference(subsumption_resolution,[],[f1910,f502])).

fof(f502,plain,
    ( v1_waybel_7(k5_waybel_0(sK0,sK1),sK0)
    | ~ spl5_31 ),
    inference(avatar_component_clause,[],[f500])).

fof(f500,plain,
    ( spl5_31
  <=> v1_waybel_7(k5_waybel_0(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f1910,plain,
    ( ~ v1_waybel_7(k5_waybel_0(sK0,sK1),sK0)
    | ~ v12_waybel_0(k5_waybel_0(sK0,sK1),sK0)
    | ~ v1_waybel_0(k5_waybel_0(sK0,sK1),sK0)
    | v1_xboole_0(k5_waybel_0(sK0,sK1))
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | spl5_13
    | ~ spl5_42 ),
    inference(subsumption_resolution,[],[f1909,f564])).

fof(f564,plain,
    ( m1_subset_1(k5_waybel_0(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_13 ),
    inference(subsumption_resolution,[],[f563,f154])).

fof(f563,plain,
    ( m1_subset_1(k5_waybel_0(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f521,f57])).

fof(f521,plain,
    ( m1_subset_1(k5_waybel_0(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f58,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_waybel_0)).

fof(f1909,plain,
    ( ~ m1_subset_1(k5_waybel_0(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_waybel_7(k5_waybel_0(sK0,sK1),sK0)
    | ~ v12_waybel_0(k5_waybel_0(sK0,sK1),sK0)
    | ~ v1_waybel_0(k5_waybel_0(sK0,sK1),sK0)
    | v1_xboole_0(k5_waybel_0(sK0,sK1))
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl5_42 ),
    inference(subsumption_resolution,[],[f1908,f60])).

fof(f60,plain,(
    ~ v4_waybel_7(sK1,sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f1908,plain,
    ( v4_waybel_7(sK1,sK0)
    | ~ m1_subset_1(k5_waybel_0(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_waybel_7(k5_waybel_0(sK0,sK1),sK0)
    | ~ v12_waybel_0(k5_waybel_0(sK0,sK1),sK0)
    | ~ v1_waybel_0(k5_waybel_0(sK0,sK1),sK0)
    | v1_xboole_0(k5_waybel_0(sK0,sK1))
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl5_42 ),
    inference(subsumption_resolution,[],[f1875,f58])).

fof(f1875,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v4_waybel_7(sK1,sK0)
    | ~ m1_subset_1(k5_waybel_0(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_waybel_7(k5_waybel_0(sK0,sK1),sK0)
    | ~ v12_waybel_0(k5_waybel_0(sK0,sK1),sK0)
    | ~ v1_waybel_0(k5_waybel_0(sK0,sK1),sK0)
    | v1_xboole_0(k5_waybel_0(sK0,sK1))
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl5_42 ),
    inference(superposition,[],[f90,f1463])).

fof(f1463,plain,
    ( sK1 = k1_yellow_0(sK0,k5_waybel_0(sK0,sK1))
    | ~ spl5_42 ),
    inference(avatar_component_clause,[],[f1461])).

fof(f1461,plain,
    ( spl5_42
  <=> sK1 = k1_yellow_0(sK0,k5_waybel_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).

fof(f90,plain,(
    ! [X2,X0] :
      ( v4_waybel_7(k1_yellow_0(X0,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_waybel_7(X2,X0)
      | ~ v12_waybel_0(X2,X0)
      | ~ v1_waybel_0(X2,X0)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(k1_yellow_0(X0,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v4_waybel_7(X1,X0)
      | k1_yellow_0(X0,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_waybel_7(X2,X0)
      | ~ v12_waybel_0(X2,X0)
      | ~ v1_waybel_0(X2,X0)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_waybel_7(X1,X0)
              | ! [X2] :
                  ( k1_yellow_0(X0,X2) != X1
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                  | ~ v1_waybel_7(X2,X0)
                  | ~ v12_waybel_0(X2,X0)
                  | ~ v1_waybel_0(X2,X0)
                  | v1_xboole_0(X2) ) )
            & ( ( k1_yellow_0(X0,sK2(X0,X1)) = X1
                & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
                & v1_waybel_7(sK2(X0,X1),X0)
                & v12_waybel_0(sK2(X0,X1),X0)
                & v1_waybel_0(sK2(X0,X1),X0)
                & ~ v1_xboole_0(sK2(X0,X1)) )
              | ~ v4_waybel_7(X1,X0) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f42,f43])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( k1_yellow_0(X0,X3) = X1
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_waybel_7(X3,X0)
          & v12_waybel_0(X3,X0)
          & v1_waybel_0(X3,X0)
          & ~ v1_xboole_0(X3) )
     => ( k1_yellow_0(X0,sK2(X0,X1)) = X1
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
        & v1_waybel_7(sK2(X0,X1),X0)
        & v12_waybel_0(sK2(X0,X1),X0)
        & v1_waybel_0(sK2(X0,X1),X0)
        & ~ v1_xboole_0(sK2(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_waybel_7(X1,X0)
              | ! [X2] :
                  ( k1_yellow_0(X0,X2) != X1
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                  | ~ v1_waybel_7(X2,X0)
                  | ~ v12_waybel_0(X2,X0)
                  | ~ v1_waybel_0(X2,X0)
                  | v1_xboole_0(X2) ) )
            & ( ? [X3] :
                  ( k1_yellow_0(X0,X3) = X1
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  & v1_waybel_7(X3,X0)
                  & v12_waybel_0(X3,X0)
                  & v1_waybel_0(X3,X0)
                  & ~ v1_xboole_0(X3) )
              | ~ v4_waybel_7(X1,X0) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_waybel_7(X1,X0)
              | ! [X2] :
                  ( k1_yellow_0(X0,X2) != X1
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                  | ~ v1_waybel_7(X2,X0)
                  | ~ v12_waybel_0(X2,X0)
                  | ~ v1_waybel_0(X2,X0)
                  | v1_xboole_0(X2) ) )
            & ( ? [X2] :
                  ( k1_yellow_0(X0,X2) = X1
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                  & v1_waybel_7(X2,X0)
                  & v12_waybel_0(X2,X0)
                  & v1_waybel_0(X2,X0)
                  & ~ v1_xboole_0(X2) )
              | ~ v4_waybel_7(X1,X0) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_waybel_7(X1,X0)
          <=> ? [X2] :
                ( k1_yellow_0(X0,X2) = X1
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & v1_waybel_7(X2,X0)
                & v12_waybel_0(X2,X0)
                & v1_waybel_0(X2,X0)
                & ~ v1_xboole_0(X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_waybel_7(X1,X0)
          <=> ? [X2] :
                ( k1_yellow_0(X0,X2) = X1
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & v1_waybel_7(X2,X0)
                & v12_waybel_0(X2,X0)
                & v1_waybel_0(X2,X0)
                & ~ v1_xboole_0(X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v4_waybel_7(X1,X0)
          <=> ? [X2] :
                ( k1_yellow_0(X0,X2) = X1
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & v1_waybel_7(X2,X0)
                & v12_waybel_0(X2,X0)
                & v1_waybel_0(X2,X0)
                & ~ v1_xboole_0(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_waybel_7)).

fof(f1480,plain,
    ( ~ spl5_44
    | spl5_42
    | spl5_13 ),
    inference(avatar_split_clause,[],[f1475,f153,f1461,f1477])).

fof(f1475,plain,
    ( sK1 = k1_yellow_0(sK0,k5_waybel_0(sK0,sK1))
    | ~ r1_orders_2(sK0,sK1,sK3(sK0,sK1,k5_waybel_0(sK0,sK1)))
    | spl5_13 ),
    inference(subsumption_resolution,[],[f1474,f54])).

fof(f1474,plain,
    ( sK1 = k1_yellow_0(sK0,k5_waybel_0(sK0,sK1))
    | ~ r1_orders_2(sK0,sK1,sK3(sK0,sK1,k5_waybel_0(sK0,sK1)))
    | ~ v5_orders_2(sK0)
    | spl5_13 ),
    inference(subsumption_resolution,[],[f1473,f57])).

fof(f1473,plain,
    ( sK1 = k1_yellow_0(sK0,k5_waybel_0(sK0,sK1))
    | ~ r1_orders_2(sK0,sK1,sK3(sK0,sK1,k5_waybel_0(sK0,sK1)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | spl5_13 ),
    inference(subsumption_resolution,[],[f1447,f58])).

fof(f1447,plain,
    ( sK1 = k1_yellow_0(sK0,k5_waybel_0(sK0,sK1))
    | ~ r1_orders_2(sK0,sK1,sK3(sK0,sK1,k5_waybel_0(sK0,sK1)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | spl5_13 ),
    inference(resolution,[],[f1444,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X2) = X1
      | ~ r1_orders_2(X0,X1,sK3(X0,X1,X2))
      | ~ r2_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
                | ( ~ r1_orders_2(X0,X1,sK3(X0,X1,X2))
                  & r2_lattice3(X0,X2,sK3(X0,X1,X2))
                  & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X1,X4)
                      | ~ r2_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r2_lattice3(X0,X2,X1) )
                | ~ r1_yellow_0(X0,X2)
                | k1_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f45])).

fof(f45,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X1,X3)
          & r2_lattice3(X0,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X1,sK3(X0,X1,X2))
        & r2_lattice3(X0,X2,sK3(X0,X1,X2))
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
                | ? [X3] :
                    ( ~ r1_orders_2(X0,X1,X3)
                    & r2_lattice3(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X1,X4)
                      | ~ r2_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r2_lattice3(X0,X2,X1) )
                | ~ r1_yellow_0(X0,X2)
                | k1_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
                | ? [X3] :
                    ( ~ r1_orders_2(X0,X1,X3)
                    & r2_lattice3(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X1,X4)
                      | ~ r2_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r2_lattice3(X0,X2,X1) )
                | ~ r1_yellow_0(X0,X2)
                | k1_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X1,X3) ) )
                  & r2_lattice3(X0,X2,X1) )
               => ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 ) )
              & ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
               => ( ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X4)
                       => r1_orders_2(X0,X1,X4) ) )
                  & r2_lattice3(X0,X2,X1) ) ) ) ) ) ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X1,X3) ) )
                  & r2_lattice3(X0,X2,X1) )
               => ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 ) )
              & ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
               => ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X1,X3) ) )
                  & r2_lattice3(X0,X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_yellow_0)).

fof(f1444,plain,
    ( r2_lattice3(sK0,k5_waybel_0(sK0,sK1),sK1)
    | spl5_13 ),
    inference(subsumption_resolution,[],[f1443,f575])).

fof(f575,plain,(
    ! [X14] :
      ( m1_subset_1(sK4(sK0,X14,sK1),u1_struct_0(sK0))
      | r2_lattice3(sK0,X14,sK1) ) ),
    inference(subsumption_resolution,[],[f528,f57])).

fof(f528,plain,(
    ! [X14] :
      ( r2_lattice3(sK0,X14,sK1)
      | m1_subset_1(sK4(sK0,X14,sK1),u1_struct_0(sK0))
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f58,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f1443,plain,
    ( ~ m1_subset_1(sK4(sK0,k5_waybel_0(sK0,sK1),sK1),u1_struct_0(sK0))
    | r2_lattice3(sK0,k5_waybel_0(sK0,sK1),sK1)
    | spl5_13 ),
    inference(subsumption_resolution,[],[f1441,f577])).

fof(f577,plain,(
    ! [X16] :
      ( ~ r1_orders_2(sK0,sK4(sK0,X16,sK1),sK1)
      | r2_lattice3(sK0,X16,sK1) ) ),
    inference(subsumption_resolution,[],[f530,f57])).

fof(f530,plain,(
    ! [X16] :
      ( r2_lattice3(sK0,X16,sK1)
      | ~ r1_orders_2(sK0,sK4(sK0,X16,sK1),sK1)
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f58,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | ~ r1_orders_2(X0,sK4(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f1441,plain,
    ( r1_orders_2(sK0,sK4(sK0,k5_waybel_0(sK0,sK1),sK1),sK1)
    | ~ m1_subset_1(sK4(sK0,k5_waybel_0(sK0,sK1),sK1),u1_struct_0(sK0))
    | r2_lattice3(sK0,k5_waybel_0(sK0,sK1),sK1)
    | spl5_13 ),
    inference(resolution,[],[f566,f576])).

fof(f576,plain,(
    ! [X15] :
      ( r2_hidden(sK4(sK0,X15,sK1),X15)
      | r2_lattice3(sK0,X15,sK1) ) ),
    inference(subsumption_resolution,[],[f529,f57])).

fof(f529,plain,(
    ! [X15] :
      ( r2_lattice3(sK0,X15,sK1)
      | r2_hidden(sK4(sK0,X15,sK1),X15)
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f58,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | r2_hidden(sK4(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f566,plain,
    ( ! [X6] :
        ( ~ r2_hidden(X6,k5_waybel_0(sK0,sK1))
        | r1_orders_2(sK0,X6,sK1)
        | ~ m1_subset_1(X6,u1_struct_0(sK0)) )
    | spl5_13 ),
    inference(subsumption_resolution,[],[f565,f154])).

fof(f565,plain,(
    ! [X6] :
      ( r1_orders_2(sK0,X6,sK1)
      | ~ r2_hidden(X6,k5_waybel_0(sK0,sK1))
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f522,f57])).

fof(f522,plain,(
    ! [X6] :
      ( r1_orders_2(sK0,X6,sK1)
      | ~ r2_hidden(X6,k5_waybel_0(sK0,sK1))
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f58,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X2,X1)
      | ~ r2_hidden(X2,k5_waybel_0(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f1472,plain,
    ( spl5_43
    | spl5_42
    | spl5_13 ),
    inference(avatar_split_clause,[],[f1467,f153,f1461,f1469])).

fof(f1467,plain,
    ( sK1 = k1_yellow_0(sK0,k5_waybel_0(sK0,sK1))
    | r2_lattice3(sK0,k5_waybel_0(sK0,sK1),sK3(sK0,sK1,k5_waybel_0(sK0,sK1)))
    | spl5_13 ),
    inference(subsumption_resolution,[],[f1466,f54])).

fof(f1466,plain,
    ( sK1 = k1_yellow_0(sK0,k5_waybel_0(sK0,sK1))
    | r2_lattice3(sK0,k5_waybel_0(sK0,sK1),sK3(sK0,sK1,k5_waybel_0(sK0,sK1)))
    | ~ v5_orders_2(sK0)
    | spl5_13 ),
    inference(subsumption_resolution,[],[f1465,f57])).

fof(f1465,plain,
    ( sK1 = k1_yellow_0(sK0,k5_waybel_0(sK0,sK1))
    | r2_lattice3(sK0,k5_waybel_0(sK0,sK1),sK3(sK0,sK1,k5_waybel_0(sK0,sK1)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | spl5_13 ),
    inference(subsumption_resolution,[],[f1446,f58])).

fof(f1446,plain,
    ( sK1 = k1_yellow_0(sK0,k5_waybel_0(sK0,sK1))
    | r2_lattice3(sK0,k5_waybel_0(sK0,sK1),sK3(sK0,sK1,k5_waybel_0(sK0,sK1)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | spl5_13 ),
    inference(resolution,[],[f1444,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X2) = X1
      | r2_lattice3(X0,X2,sK3(X0,X1,X2))
      | ~ r2_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f1464,plain,
    ( spl5_41
    | spl5_42
    | spl5_13 ),
    inference(avatar_split_clause,[],[f1455,f153,f1461,f1457])).

fof(f1455,plain,
    ( sK1 = k1_yellow_0(sK0,k5_waybel_0(sK0,sK1))
    | m1_subset_1(sK3(sK0,sK1,k5_waybel_0(sK0,sK1)),u1_struct_0(sK0))
    | spl5_13 ),
    inference(subsumption_resolution,[],[f1454,f54])).

fof(f1454,plain,
    ( sK1 = k1_yellow_0(sK0,k5_waybel_0(sK0,sK1))
    | m1_subset_1(sK3(sK0,sK1,k5_waybel_0(sK0,sK1)),u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | spl5_13 ),
    inference(subsumption_resolution,[],[f1453,f57])).

fof(f1453,plain,
    ( sK1 = k1_yellow_0(sK0,k5_waybel_0(sK0,sK1))
    | m1_subset_1(sK3(sK0,sK1,k5_waybel_0(sK0,sK1)),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | spl5_13 ),
    inference(subsumption_resolution,[],[f1445,f58])).

fof(f1445,plain,
    ( sK1 = k1_yellow_0(sK0,k5_waybel_0(sK0,sK1))
    | m1_subset_1(sK3(sK0,sK1,k5_waybel_0(sK0,sK1)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | spl5_13 ),
    inference(resolution,[],[f1444,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X2) = X1
      | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | ~ r2_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f581,plain,(
    spl5_30 ),
    inference(avatar_contradiction_clause,[],[f580])).

fof(f580,plain,
    ( $false
    | spl5_30 ),
    inference(subsumption_resolution,[],[f498,f58])).

fof(f498,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | spl5_30 ),
    inference(avatar_component_clause,[],[f496])).

fof(f496,plain,
    ( spl5_30
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f503,plain,
    ( ~ spl5_30
    | spl5_31 ),
    inference(avatar_split_clause,[],[f494,f500,f496])).

fof(f494,plain,
    ( v1_waybel_7(k5_waybel_0(sK0,sK1),sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f493,f52])).

fof(f493,plain,
    ( v1_waybel_7(k5_waybel_0(sK0,sK1),sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v3_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f492,f53])).

fof(f492,plain,
    ( v1_waybel_7(k5_waybel_0(sK0,sK1),sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f491,f54])).

fof(f491,plain,
    ( v1_waybel_7(k5_waybel_0(sK0,sK1),sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f490,f55])).

fof(f490,plain,
    ( v1_waybel_7(k5_waybel_0(sK0,sK1),sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f489,f56])).

fof(f489,plain,
    ( v1_waybel_7(k5_waybel_0(sK0,sK1),sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f488,f57])).

fof(f488,plain,
    ( v1_waybel_7(k5_waybel_0(sK0,sK1),sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0) ),
    inference(resolution,[],[f59,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v1_waybel_7(k5_waybel_0(X0,X1),X0)
      | ~ v5_waybel_6(X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_waybel_7(k5_waybel_0(X0,X1),X0)
          | ~ v5_waybel_6(X1,X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_waybel_7(k5_waybel_0(X0,X1),X0)
          | ~ v5_waybel_6(X1,X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v5_waybel_6(X1,X0)
           => v1_waybel_7(k5_waybel_0(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_waybel_7)).

fof(f59,plain,(
    v5_waybel_6(sK1,sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f469,plain,(
    spl5_5 ),
    inference(avatar_contradiction_clause,[],[f468])).

fof(f468,plain,
    ( $false
    | spl5_5 ),
    inference(subsumption_resolution,[],[f123,f57])).

fof(f123,plain,
    ( ~ l1_orders_2(sK0)
    | spl5_5 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl5_5
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f315,plain,
    ( ~ spl5_5
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f285,f153,f121])).

fof(f285,plain,
    ( ~ v2_struct_0(sK0)
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f55,f71])).

fof(f71,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattice3)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : run_vampire %s %d
% 0.13/0.32  % Computer   : n012.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 16:53:07 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.20/0.42  % (23241)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.44  % (23249)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.44  % (23252)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.45  % (23246)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.45  % (23255)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.46  % (23242)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.46  % (23239)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.47  % (23243)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.47  % (23244)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.48  % (23238)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.48  % (23235)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.48  % (23236)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.49  % (23236)Refutation not found, incomplete strategy% (23236)------------------------------
% 0.20/0.49  % (23236)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (23236)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (23236)Memory used [KB]: 10618
% 0.20/0.49  % (23236)Time elapsed: 0.094 s
% 0.20/0.49  % (23236)------------------------------
% 0.20/0.49  % (23236)------------------------------
% 0.20/0.49  % (23256)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.49  % (23237)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.49  % (23256)Refutation not found, incomplete strategy% (23256)------------------------------
% 0.20/0.49  % (23256)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (23256)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (23256)Memory used [KB]: 10618
% 0.20/0.49  % (23256)Time elapsed: 0.098 s
% 0.20/0.49  % (23256)------------------------------
% 0.20/0.49  % (23256)------------------------------
% 0.20/0.49  % (23245)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.49  % (23248)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.49  % (23254)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.49  % (23253)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.50  % (23250)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.50  % (23247)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.50  % (23255)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  % (23251)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.50  fof(f2486,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(avatar_sat_refutation,[],[f315,f469,f503,f581,f1464,f1472,f1480,f1921,f2485])).
% 0.20/0.50  fof(f2485,plain,(
% 0.20/0.50    spl5_13 | ~spl5_41 | ~spl5_43 | spl5_44),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f2484])).
% 0.20/0.50  fof(f2484,plain,(
% 0.20/0.50    $false | (spl5_13 | ~spl5_41 | ~spl5_43 | spl5_44)),
% 0.20/0.50    inference(subsumption_resolution,[],[f2482,f1471])).
% 0.20/0.50  fof(f1471,plain,(
% 0.20/0.50    r2_lattice3(sK0,k5_waybel_0(sK0,sK1),sK3(sK0,sK1,k5_waybel_0(sK0,sK1))) | ~spl5_43),
% 0.20/0.50    inference(avatar_component_clause,[],[f1469])).
% 0.20/0.50  fof(f1469,plain,(
% 0.20/0.50    spl5_43 <=> r2_lattice3(sK0,k5_waybel_0(sK0,sK1),sK3(sK0,sK1,k5_waybel_0(sK0,sK1)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).
% 0.20/0.50  fof(f2482,plain,(
% 0.20/0.50    ~r2_lattice3(sK0,k5_waybel_0(sK0,sK1),sK3(sK0,sK1,k5_waybel_0(sK0,sK1))) | (spl5_13 | ~spl5_41 | spl5_44)),
% 0.20/0.50    inference(resolution,[],[f1679,f586])).
% 0.20/0.50  fof(f586,plain,(
% 0.20/0.50    r2_hidden(sK1,k5_waybel_0(sK0,sK1)) | spl5_13),
% 0.20/0.50    inference(subsumption_resolution,[],[f585,f154])).
% 0.20/0.50  fof(f154,plain,(
% 0.20/0.50    ~v2_struct_0(sK0) | spl5_13),
% 0.20/0.50    inference(avatar_component_clause,[],[f153])).
% 0.20/0.50  fof(f153,plain,(
% 0.20/0.50    spl5_13 <=> v2_struct_0(sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.20/0.50  fof(f585,plain,(
% 0.20/0.50    r2_hidden(sK1,k5_waybel_0(sK0,sK1)) | v2_struct_0(sK0) | spl5_13),
% 0.20/0.50    inference(subsumption_resolution,[],[f584,f57])).
% 0.20/0.50  fof(f57,plain,(
% 0.20/0.50    l1_orders_2(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f40])).
% 0.20/0.50  fof(f40,plain,(
% 0.20/0.50    (~v4_waybel_7(sK1,sK0) & v5_waybel_6(sK1,sK0) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_orders_2(sK0) & v2_lattice3(sK0) & v1_lattice3(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0)),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f39,f38])).
% 0.20/0.50  fof(f38,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (~v4_waybel_7(X1,X0) & v5_waybel_6(X1,X0) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0)) => (? [X1] : (~v4_waybel_7(X1,sK0) & v5_waybel_6(X1,sK0) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_orders_2(sK0) & v2_lattice3(sK0) & v1_lattice3(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f39,plain,(
% 0.20/0.50    ? [X1] : (~v4_waybel_7(X1,sK0) & v5_waybel_6(X1,sK0) & m1_subset_1(X1,u1_struct_0(sK0))) => (~v4_waybel_7(sK1,sK0) & v5_waybel_6(sK1,sK0) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f16,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (~v4_waybel_7(X1,X0) & v5_waybel_6(X1,X0) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0))),
% 0.20/0.50    inference(flattening,[],[f15])).
% 0.20/0.50  fof(f15,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : ((~v4_waybel_7(X1,X0) & v5_waybel_6(X1,X0)) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f13])).
% 0.20/0.50  fof(f13,negated_conjecture,(
% 0.20/0.50    ~! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v5_waybel_6(X1,X0) => v4_waybel_7(X1,X0))))),
% 0.20/0.50    inference(negated_conjecture,[],[f12])).
% 0.20/0.50  fof(f12,conjecture,(
% 0.20/0.50    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v5_waybel_6(X1,X0) => v4_waybel_7(X1,X0))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_waybel_7)).
% 0.20/0.50  fof(f584,plain,(
% 0.20/0.50    r2_hidden(sK1,k5_waybel_0(sK0,sK1)) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | spl5_13),
% 0.20/0.50    inference(subsumption_resolution,[],[f583,f58])).
% 0.20/0.50  fof(f58,plain,(
% 0.20/0.50    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.50    inference(cnf_transformation,[],[f40])).
% 0.20/0.50  fof(f583,plain,(
% 0.20/0.50    r2_hidden(sK1,k5_waybel_0(sK0,sK1)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | spl5_13),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f582])).
% 0.20/0.50  fof(f582,plain,(
% 0.20/0.50    r2_hidden(sK1,k5_waybel_0(sK0,sK1)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | spl5_13),
% 0.20/0.50    inference(resolution,[],[f541,f85])).
% 0.20/0.50  fof(f85,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (r2_hidden(X2,k5_waybel_0(X0,X1)) | ~r1_orders_2(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f47])).
% 0.20/0.50  fof(f47,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k5_waybel_0(X0,X1)) | ~r1_orders_2(X0,X2,X1)) & (r1_orders_2(X0,X2,X1) | ~r2_hidden(X2,k5_waybel_0(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(nnf_transformation,[],[f35])).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k5_waybel_0(X0,X1)) <=> r1_orders_2(X0,X2,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f34])).
% 0.20/0.50  fof(f34,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k5_waybel_0(X0,X1)) <=> r1_orders_2(X0,X2,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f9])).
% 0.20/0.50  fof(f9,axiom,(
% 0.20/0.50    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k5_waybel_0(X0,X1)) <=> r1_orders_2(X0,X2,X1)))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_waybel_0)).
% 0.20/0.50  fof(f541,plain,(
% 0.20/0.50    r1_orders_2(sK0,sK1,sK1) | spl5_13),
% 0.20/0.50    inference(subsumption_resolution,[],[f540,f154])).
% 0.20/0.50  fof(f540,plain,(
% 0.20/0.50    r1_orders_2(sK0,sK1,sK1) | v2_struct_0(sK0)),
% 0.20/0.50    inference(subsumption_resolution,[],[f539,f52])).
% 0.20/0.50  fof(f52,plain,(
% 0.20/0.50    v3_orders_2(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f40])).
% 0.20/0.50  fof(f539,plain,(
% 0.20/0.50    r1_orders_2(sK0,sK1,sK1) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.20/0.50    inference(subsumption_resolution,[],[f511,f57])).
% 0.20/0.50  fof(f511,plain,(
% 0.20/0.50    r1_orders_2(sK0,sK1,sK1) | ~l1_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.20/0.50    inference(resolution,[],[f58,f70])).
% 0.20/0.50  fof(f70,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f23])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f22])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r1_orders_2(X0,X1,X1)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_orders_2)).
% 0.20/0.50  fof(f1679,plain,(
% 0.20/0.50    ( ! [X0] : (~r2_hidden(sK1,X0) | ~r2_lattice3(sK0,X0,sK3(sK0,sK1,k5_waybel_0(sK0,sK1)))) ) | (~spl5_41 | spl5_44)),
% 0.20/0.50    inference(subsumption_resolution,[],[f1678,f57])).
% 0.20/0.50  fof(f1678,plain,(
% 0.20/0.50    ( ! [X0] : (~r2_hidden(sK1,X0) | ~r2_lattice3(sK0,X0,sK3(sK0,sK1,k5_waybel_0(sK0,sK1))) | ~l1_orders_2(sK0)) ) | (~spl5_41 | spl5_44)),
% 0.20/0.50    inference(subsumption_resolution,[],[f1677,f1459])).
% 0.20/0.50  fof(f1459,plain,(
% 0.20/0.50    m1_subset_1(sK3(sK0,sK1,k5_waybel_0(sK0,sK1)),u1_struct_0(sK0)) | ~spl5_41),
% 0.20/0.50    inference(avatar_component_clause,[],[f1457])).
% 0.20/0.50  fof(f1457,plain,(
% 0.20/0.50    spl5_41 <=> m1_subset_1(sK3(sK0,sK1,k5_waybel_0(sK0,sK1)),u1_struct_0(sK0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).
% 0.20/0.50  fof(f1677,plain,(
% 0.20/0.50    ( ! [X0] : (~r2_hidden(sK1,X0) | ~r2_lattice3(sK0,X0,sK3(sK0,sK1,k5_waybel_0(sK0,sK1))) | ~m1_subset_1(sK3(sK0,sK1,k5_waybel_0(sK0,sK1)),u1_struct_0(sK0)) | ~l1_orders_2(sK0)) ) | spl5_44),
% 0.20/0.50    inference(subsumption_resolution,[],[f1675,f58])).
% 0.20/0.50  fof(f1675,plain,(
% 0.20/0.50    ( ! [X0] : (~r2_hidden(sK1,X0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~r2_lattice3(sK0,X0,sK3(sK0,sK1,k5_waybel_0(sK0,sK1))) | ~m1_subset_1(sK3(sK0,sK1,k5_waybel_0(sK0,sK1)),u1_struct_0(sK0)) | ~l1_orders_2(sK0)) ) | spl5_44),
% 0.20/0.50    inference(resolution,[],[f1479,f86])).
% 0.20/0.50  fof(f86,plain,(
% 0.20/0.50    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f51])).
% 0.20/0.50  fof(f51,plain,(
% 0.20/0.50    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | (~r1_orders_2(X0,sK4(X0,X1,X2),X2) & r2_hidden(sK4(X0,X1,X2),X1) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f49,f50])).
% 0.20/0.50  fof(f50,plain,(
% 0.20/0.50    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,sK4(X0,X1,X2),X2) & r2_hidden(sK4(X0,X1,X2),X1) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f49,plain,(
% 0.20/0.50    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.20/0.50    inference(rectify,[],[f48])).
% 0.20/0.50  fof(f48,plain,(
% 0.20/0.50    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.20/0.50    inference(nnf_transformation,[],[f37])).
% 0.20/0.50  fof(f37,plain,(
% 0.20/0.50    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.20/0.50    inference(flattening,[],[f36])).
% 0.20/0.50  fof(f36,plain,(
% 0.20/0.50    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X3,X2))))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattice3)).
% 0.20/0.50  fof(f1479,plain,(
% 0.20/0.50    ~r1_orders_2(sK0,sK1,sK3(sK0,sK1,k5_waybel_0(sK0,sK1))) | spl5_44),
% 0.20/0.50    inference(avatar_component_clause,[],[f1477])).
% 0.20/0.50  fof(f1477,plain,(
% 0.20/0.50    spl5_44 <=> r1_orders_2(sK0,sK1,sK3(sK0,sK1,k5_waybel_0(sK0,sK1)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).
% 0.20/0.50  fof(f1921,plain,(
% 0.20/0.50    spl5_13 | ~spl5_31 | ~spl5_42),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f1920])).
% 0.20/0.50  fof(f1920,plain,(
% 0.20/0.50    $false | (spl5_13 | ~spl5_31 | ~spl5_42)),
% 0.20/0.50    inference(subsumption_resolution,[],[f1919,f52])).
% 0.20/0.50  fof(f1919,plain,(
% 0.20/0.50    ~v3_orders_2(sK0) | (spl5_13 | ~spl5_31 | ~spl5_42)),
% 0.20/0.50    inference(subsumption_resolution,[],[f1918,f53])).
% 0.20/0.50  fof(f53,plain,(
% 0.20/0.50    v4_orders_2(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f40])).
% 0.20/0.50  fof(f1918,plain,(
% 0.20/0.50    ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | (spl5_13 | ~spl5_31 | ~spl5_42)),
% 0.20/0.50    inference(subsumption_resolution,[],[f1917,f54])).
% 0.20/0.50  fof(f54,plain,(
% 0.20/0.50    v5_orders_2(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f40])).
% 0.20/0.50  fof(f1917,plain,(
% 0.20/0.50    ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | (spl5_13 | ~spl5_31 | ~spl5_42)),
% 0.20/0.50    inference(subsumption_resolution,[],[f1916,f55])).
% 0.20/0.50  fof(f55,plain,(
% 0.20/0.50    v1_lattice3(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f40])).
% 0.20/0.50  fof(f1916,plain,(
% 0.20/0.50    ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | (spl5_13 | ~spl5_31 | ~spl5_42)),
% 0.20/0.50    inference(subsumption_resolution,[],[f1915,f56])).
% 0.20/0.50  fof(f56,plain,(
% 0.20/0.50    v2_lattice3(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f40])).
% 0.20/0.50  fof(f1915,plain,(
% 0.20/0.50    ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | (spl5_13 | ~spl5_31 | ~spl5_42)),
% 0.20/0.50    inference(subsumption_resolution,[],[f1914,f57])).
% 0.20/0.50  fof(f1914,plain,(
% 0.20/0.50    ~l1_orders_2(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | (spl5_13 | ~spl5_31 | ~spl5_42)),
% 0.20/0.50    inference(subsumption_resolution,[],[f1913,f559])).
% 0.20/0.50  fof(f559,plain,(
% 0.20/0.50    ~v1_xboole_0(k5_waybel_0(sK0,sK1)) | spl5_13),
% 0.20/0.50    inference(subsumption_resolution,[],[f558,f154])).
% 0.20/0.50  fof(f558,plain,(
% 0.20/0.50    ~v1_xboole_0(k5_waybel_0(sK0,sK1)) | v2_struct_0(sK0)),
% 0.20/0.50    inference(subsumption_resolution,[],[f557,f52])).
% 0.20/0.50  fof(f557,plain,(
% 0.20/0.50    ~v1_xboole_0(k5_waybel_0(sK0,sK1)) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.20/0.50    inference(subsumption_resolution,[],[f519,f57])).
% 0.20/0.50  fof(f519,plain,(
% 0.20/0.50    ~v1_xboole_0(k5_waybel_0(sK0,sK1)) | ~l1_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.20/0.50    inference(resolution,[],[f58,f81])).
% 0.20/0.50  fof(f81,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v1_xboole_0(k5_waybel_0(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f31])).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    ! [X0,X1] : ((v1_waybel_0(k5_waybel_0(X0,X1),X0) & ~v1_xboole_0(k5_waybel_0(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f30])).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    ! [X0,X1] : ((v1_waybel_0(k5_waybel_0(X0,X1),X0) & ~v1_xboole_0(k5_waybel_0(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f8])).
% 0.20/0.50  fof(f8,axiom,(
% 0.20/0.50    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (v1_waybel_0(k5_waybel_0(X0,X1),X0) & ~v1_xboole_0(k5_waybel_0(X0,X1))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_waybel_0)).
% 0.20/0.50  fof(f1913,plain,(
% 0.20/0.50    v1_xboole_0(k5_waybel_0(sK0,sK1)) | ~l1_orders_2(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | (spl5_13 | ~spl5_31 | ~spl5_42)),
% 0.20/0.50    inference(subsumption_resolution,[],[f1912,f562])).
% 0.20/0.50  fof(f562,plain,(
% 0.20/0.50    v1_waybel_0(k5_waybel_0(sK0,sK1),sK0) | spl5_13),
% 0.20/0.50    inference(subsumption_resolution,[],[f561,f154])).
% 0.20/0.50  fof(f561,plain,(
% 0.20/0.50    v1_waybel_0(k5_waybel_0(sK0,sK1),sK0) | v2_struct_0(sK0)),
% 0.20/0.50    inference(subsumption_resolution,[],[f560,f52])).
% 0.20/0.50  fof(f560,plain,(
% 0.20/0.50    v1_waybel_0(k5_waybel_0(sK0,sK1),sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.20/0.50    inference(subsumption_resolution,[],[f520,f57])).
% 0.20/0.50  fof(f520,plain,(
% 0.20/0.50    v1_waybel_0(k5_waybel_0(sK0,sK1),sK0) | ~l1_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.20/0.50    inference(resolution,[],[f58,f82])).
% 0.20/0.50  fof(f82,plain,(
% 0.20/0.50    ( ! [X0,X1] : (v1_waybel_0(k5_waybel_0(X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f31])).
% 0.20/0.50  fof(f1912,plain,(
% 0.20/0.50    ~v1_waybel_0(k5_waybel_0(sK0,sK1),sK0) | v1_xboole_0(k5_waybel_0(sK0,sK1)) | ~l1_orders_2(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | (spl5_13 | ~spl5_31 | ~spl5_42)),
% 0.20/0.50    inference(subsumption_resolution,[],[f1911,f556])).
% 0.20/0.50  fof(f556,plain,(
% 0.20/0.50    v12_waybel_0(k5_waybel_0(sK0,sK1),sK0) | spl5_13),
% 0.20/0.50    inference(subsumption_resolution,[],[f555,f154])).
% 0.20/0.50  fof(f555,plain,(
% 0.20/0.50    v12_waybel_0(k5_waybel_0(sK0,sK1),sK0) | v2_struct_0(sK0)),
% 0.20/0.50    inference(subsumption_resolution,[],[f554,f53])).
% 0.20/0.50  fof(f554,plain,(
% 0.20/0.50    v12_waybel_0(k5_waybel_0(sK0,sK1),sK0) | ~v4_orders_2(sK0) | v2_struct_0(sK0)),
% 0.20/0.50    inference(subsumption_resolution,[],[f518,f57])).
% 0.20/0.50  fof(f518,plain,(
% 0.20/0.50    v12_waybel_0(k5_waybel_0(sK0,sK1),sK0) | ~l1_orders_2(sK0) | ~v4_orders_2(sK0) | v2_struct_0(sK0)),
% 0.20/0.50    inference(resolution,[],[f58,f80])).
% 0.20/0.50  fof(f80,plain,(
% 0.20/0.50    ( ! [X0,X1] : (v12_waybel_0(k5_waybel_0(X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v4_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f29])).
% 0.20/0.50  fof(f29,plain,(
% 0.20/0.50    ! [X0,X1] : (v12_waybel_0(k5_waybel_0(X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v4_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f28])).
% 0.20/0.50  fof(f28,plain,(
% 0.20/0.50    ! [X0,X1] : (v12_waybel_0(k5_waybel_0(X0,X1),X0) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v4_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f7])).
% 0.20/0.50  fof(f7,axiom,(
% 0.20/0.50    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v4_orders_2(X0) & ~v2_struct_0(X0)) => v12_waybel_0(k5_waybel_0(X0,X1),X0))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc12_waybel_0)).
% 0.20/0.50  fof(f1911,plain,(
% 0.20/0.50    ~v12_waybel_0(k5_waybel_0(sK0,sK1),sK0) | ~v1_waybel_0(k5_waybel_0(sK0,sK1),sK0) | v1_xboole_0(k5_waybel_0(sK0,sK1)) | ~l1_orders_2(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | (spl5_13 | ~spl5_31 | ~spl5_42)),
% 0.20/0.50    inference(subsumption_resolution,[],[f1910,f502])).
% 0.20/0.50  fof(f502,plain,(
% 0.20/0.50    v1_waybel_7(k5_waybel_0(sK0,sK1),sK0) | ~spl5_31),
% 0.20/0.50    inference(avatar_component_clause,[],[f500])).
% 0.20/0.50  fof(f500,plain,(
% 0.20/0.50    spl5_31 <=> v1_waybel_7(k5_waybel_0(sK0,sK1),sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).
% 0.20/0.50  fof(f1910,plain,(
% 0.20/0.50    ~v1_waybel_7(k5_waybel_0(sK0,sK1),sK0) | ~v12_waybel_0(k5_waybel_0(sK0,sK1),sK0) | ~v1_waybel_0(k5_waybel_0(sK0,sK1),sK0) | v1_xboole_0(k5_waybel_0(sK0,sK1)) | ~l1_orders_2(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | (spl5_13 | ~spl5_42)),
% 0.20/0.50    inference(subsumption_resolution,[],[f1909,f564])).
% 0.20/0.50  fof(f564,plain,(
% 0.20/0.50    m1_subset_1(k5_waybel_0(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl5_13),
% 0.20/0.50    inference(subsumption_resolution,[],[f563,f154])).
% 0.20/0.50  fof(f563,plain,(
% 0.20/0.50    m1_subset_1(k5_waybel_0(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)),
% 0.20/0.50    inference(subsumption_resolution,[],[f521,f57])).
% 0.20/0.50  fof(f521,plain,(
% 0.20/0.50    m1_subset_1(k5_waybel_0(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | v2_struct_0(sK0)),
% 0.20/0.50    inference(resolution,[],[f58,f83])).
% 0.20/0.50  fof(f83,plain,(
% 0.20/0.50    ( ! [X0,X1] : (m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f33])).
% 0.20/0.50  fof(f33,plain,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f32])).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,axiom,(
% 0.20/0.50    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & ~v2_struct_0(X0)) => m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_waybel_0)).
% 0.20/0.50  fof(f1909,plain,(
% 0.20/0.50    ~m1_subset_1(k5_waybel_0(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_waybel_7(k5_waybel_0(sK0,sK1),sK0) | ~v12_waybel_0(k5_waybel_0(sK0,sK1),sK0) | ~v1_waybel_0(k5_waybel_0(sK0,sK1),sK0) | v1_xboole_0(k5_waybel_0(sK0,sK1)) | ~l1_orders_2(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~spl5_42),
% 0.20/0.50    inference(subsumption_resolution,[],[f1908,f60])).
% 0.20/0.50  fof(f60,plain,(
% 0.20/0.50    ~v4_waybel_7(sK1,sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f40])).
% 0.20/0.50  fof(f1908,plain,(
% 0.20/0.50    v4_waybel_7(sK1,sK0) | ~m1_subset_1(k5_waybel_0(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_waybel_7(k5_waybel_0(sK0,sK1),sK0) | ~v12_waybel_0(k5_waybel_0(sK0,sK1),sK0) | ~v1_waybel_0(k5_waybel_0(sK0,sK1),sK0) | v1_xboole_0(k5_waybel_0(sK0,sK1)) | ~l1_orders_2(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~spl5_42),
% 0.20/0.50    inference(subsumption_resolution,[],[f1875,f58])).
% 0.20/0.50  fof(f1875,plain,(
% 0.20/0.50    ~m1_subset_1(sK1,u1_struct_0(sK0)) | v4_waybel_7(sK1,sK0) | ~m1_subset_1(k5_waybel_0(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_waybel_7(k5_waybel_0(sK0,sK1),sK0) | ~v12_waybel_0(k5_waybel_0(sK0,sK1),sK0) | ~v1_waybel_0(k5_waybel_0(sK0,sK1),sK0) | v1_xboole_0(k5_waybel_0(sK0,sK1)) | ~l1_orders_2(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~spl5_42),
% 0.20/0.50    inference(superposition,[],[f90,f1463])).
% 0.20/0.50  fof(f1463,plain,(
% 0.20/0.50    sK1 = k1_yellow_0(sK0,k5_waybel_0(sK0,sK1)) | ~spl5_42),
% 0.20/0.50    inference(avatar_component_clause,[],[f1461])).
% 0.20/0.50  fof(f1461,plain,(
% 0.20/0.50    spl5_42 <=> sK1 = k1_yellow_0(sK0,k5_waybel_0(sK0,sK1))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).
% 0.20/0.50  fof(f90,plain,(
% 0.20/0.50    ( ! [X2,X0] : (v4_waybel_7(k1_yellow_0(X0,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_waybel_7(X2,X0) | ~v12_waybel_0(X2,X0) | ~v1_waybel_0(X2,X0) | v1_xboole_0(X2) | ~m1_subset_1(k1_yellow_0(X0,X2),u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0)) )),
% 0.20/0.50    inference(equality_resolution,[],[f67])).
% 0.20/0.50  fof(f67,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (v4_waybel_7(X1,X0) | k1_yellow_0(X0,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_waybel_7(X2,X0) | ~v12_waybel_0(X2,X0) | ~v1_waybel_0(X2,X0) | v1_xboole_0(X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f44])).
% 0.20/0.50  fof(f44,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (((v4_waybel_7(X1,X0) | ! [X2] : (k1_yellow_0(X0,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_waybel_7(X2,X0) | ~v12_waybel_0(X2,X0) | ~v1_waybel_0(X2,X0) | v1_xboole_0(X2))) & ((k1_yellow_0(X0,sK2(X0,X1)) = X1 & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) & v1_waybel_7(sK2(X0,X1),X0) & v12_waybel_0(sK2(X0,X1),X0) & v1_waybel_0(sK2(X0,X1),X0) & ~v1_xboole_0(sK2(X0,X1))) | ~v4_waybel_7(X1,X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0))),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f42,f43])).
% 0.20/0.50  fof(f43,plain,(
% 0.20/0.50    ! [X1,X0] : (? [X3] : (k1_yellow_0(X0,X3) = X1 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v1_waybel_7(X3,X0) & v12_waybel_0(X3,X0) & v1_waybel_0(X3,X0) & ~v1_xboole_0(X3)) => (k1_yellow_0(X0,sK2(X0,X1)) = X1 & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) & v1_waybel_7(sK2(X0,X1),X0) & v12_waybel_0(sK2(X0,X1),X0) & v1_waybel_0(sK2(X0,X1),X0) & ~v1_xboole_0(sK2(X0,X1))))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f42,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (((v4_waybel_7(X1,X0) | ! [X2] : (k1_yellow_0(X0,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_waybel_7(X2,X0) | ~v12_waybel_0(X2,X0) | ~v1_waybel_0(X2,X0) | v1_xboole_0(X2))) & (? [X3] : (k1_yellow_0(X0,X3) = X1 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v1_waybel_7(X3,X0) & v12_waybel_0(X3,X0) & v1_waybel_0(X3,X0) & ~v1_xboole_0(X3)) | ~v4_waybel_7(X1,X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0))),
% 0.20/0.50    inference(rectify,[],[f41])).
% 0.20/0.50  fof(f41,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (((v4_waybel_7(X1,X0) | ! [X2] : (k1_yellow_0(X0,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_waybel_7(X2,X0) | ~v12_waybel_0(X2,X0) | ~v1_waybel_0(X2,X0) | v1_xboole_0(X2))) & (? [X2] : (k1_yellow_0(X0,X2) = X1 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v1_waybel_7(X2,X0) & v12_waybel_0(X2,X0) & v1_waybel_0(X2,X0) & ~v1_xboole_0(X2)) | ~v4_waybel_7(X1,X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0))),
% 0.20/0.50    inference(nnf_transformation,[],[f18])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : ((v4_waybel_7(X1,X0) <=> ? [X2] : (k1_yellow_0(X0,X2) = X1 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v1_waybel_7(X2,X0) & v12_waybel_0(X2,X0) & v1_waybel_0(X2,X0) & ~v1_xboole_0(X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0))),
% 0.20/0.50    inference(flattening,[],[f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : ((v4_waybel_7(X1,X0) <=> ? [X2] : (k1_yellow_0(X0,X2) = X1 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v1_waybel_7(X2,X0) & v12_waybel_0(X2,X0) & v1_waybel_0(X2,X0) & ~v1_xboole_0(X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f10])).
% 0.20/0.51  fof(f10,axiom,(
% 0.20/0.51    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v4_waybel_7(X1,X0) <=> ? [X2] : (k1_yellow_0(X0,X2) = X1 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v1_waybel_7(X2,X0) & v12_waybel_0(X2,X0) & v1_waybel_0(X2,X0) & ~v1_xboole_0(X2)))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_waybel_7)).
% 0.20/0.51  fof(f1480,plain,(
% 0.20/0.51    ~spl5_44 | spl5_42 | spl5_13),
% 0.20/0.51    inference(avatar_split_clause,[],[f1475,f153,f1461,f1477])).
% 0.20/0.51  fof(f1475,plain,(
% 0.20/0.51    sK1 = k1_yellow_0(sK0,k5_waybel_0(sK0,sK1)) | ~r1_orders_2(sK0,sK1,sK3(sK0,sK1,k5_waybel_0(sK0,sK1))) | spl5_13),
% 0.20/0.51    inference(subsumption_resolution,[],[f1474,f54])).
% 0.20/0.51  fof(f1474,plain,(
% 0.20/0.51    sK1 = k1_yellow_0(sK0,k5_waybel_0(sK0,sK1)) | ~r1_orders_2(sK0,sK1,sK3(sK0,sK1,k5_waybel_0(sK0,sK1))) | ~v5_orders_2(sK0) | spl5_13),
% 0.20/0.51    inference(subsumption_resolution,[],[f1473,f57])).
% 0.20/0.51  fof(f1473,plain,(
% 0.20/0.51    sK1 = k1_yellow_0(sK0,k5_waybel_0(sK0,sK1)) | ~r1_orders_2(sK0,sK1,sK3(sK0,sK1,k5_waybel_0(sK0,sK1))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | spl5_13),
% 0.20/0.51    inference(subsumption_resolution,[],[f1447,f58])).
% 0.20/0.51  fof(f1447,plain,(
% 0.20/0.51    sK1 = k1_yellow_0(sK0,k5_waybel_0(sK0,sK1)) | ~r1_orders_2(sK0,sK1,sK3(sK0,sK1,k5_waybel_0(sK0,sK1))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | spl5_13),
% 0.20/0.51    inference(resolution,[],[f1444,f76])).
% 0.20/0.51  fof(f76,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k1_yellow_0(X0,X2) = X1 | ~r1_orders_2(X0,X1,sK3(X0,X1,X2)) | ~r2_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f46])).
% 0.20/0.51  fof(f46,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : (((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) | (~r1_orders_2(X0,X1,sK3(X0,X1,X2)) & r2_lattice3(X0,X2,sK3(X0,X1,X2)) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))) | ~r2_lattice3(X0,X2,X1)) & ((! [X4] : (r1_orders_2(X0,X1,X4) | ~r2_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X2,X1)) | ~r1_yellow_0(X0,X2) | k1_yellow_0(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f45])).
% 0.20/0.51  fof(f45,plain,(
% 0.20/0.51    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X1,X3) & r2_lattice3(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X1,sK3(X0,X1,X2)) & r2_lattice3(X0,X2,sK3(X0,X1,X2)) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : (((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) | ? [X3] : (~r1_orders_2(X0,X1,X3) & r2_lattice3(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X2,X1)) & ((! [X4] : (r1_orders_2(X0,X1,X4) | ~r2_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X2,X1)) | ~r1_yellow_0(X0,X2) | k1_yellow_0(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 0.20/0.51    inference(flattening,[],[f26])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : (((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) | (? [X3] : ((~r1_orders_2(X0,X1,X3) & r2_lattice3(X0,X2,X3)) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X2,X1))) & ((! [X4] : ((r1_orders_2(X0,X1,X4) | ~r2_lattice3(X0,X2,X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X2,X1)) | (~r1_yellow_0(X0,X2) | k1_yellow_0(X0,X2) != X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f14])).
% 0.20/0.51  fof(f14,plain,(
% 0.20/0.51    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (((! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X3) => r1_orders_2(X0,X1,X3))) & r2_lattice3(X0,X2,X1)) => (r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1)) & ((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) => (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X4) => r1_orders_2(X0,X1,X4))) & r2_lattice3(X0,X2,X1))))))),
% 0.20/0.51    inference(rectify,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (((! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X3) => r1_orders_2(X0,X1,X3))) & r2_lattice3(X0,X2,X1)) => (r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1)) & ((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X3) => r1_orders_2(X0,X1,X3))) & r2_lattice3(X0,X2,X1))))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_yellow_0)).
% 0.20/0.51  fof(f1444,plain,(
% 0.20/0.51    r2_lattice3(sK0,k5_waybel_0(sK0,sK1),sK1) | spl5_13),
% 0.20/0.51    inference(subsumption_resolution,[],[f1443,f575])).
% 0.20/0.51  fof(f575,plain,(
% 0.20/0.51    ( ! [X14] : (m1_subset_1(sK4(sK0,X14,sK1),u1_struct_0(sK0)) | r2_lattice3(sK0,X14,sK1)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f528,f57])).
% 0.20/0.51  fof(f528,plain,(
% 0.20/0.51    ( ! [X14] : (r2_lattice3(sK0,X14,sK1) | m1_subset_1(sK4(sK0,X14,sK1),u1_struct_0(sK0)) | ~l1_orders_2(sK0)) )),
% 0.20/0.51    inference(resolution,[],[f58,f87])).
% 0.20/0.51  fof(f87,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f51])).
% 0.20/0.51  fof(f1443,plain,(
% 0.20/0.51    ~m1_subset_1(sK4(sK0,k5_waybel_0(sK0,sK1),sK1),u1_struct_0(sK0)) | r2_lattice3(sK0,k5_waybel_0(sK0,sK1),sK1) | spl5_13),
% 0.20/0.51    inference(subsumption_resolution,[],[f1441,f577])).
% 0.20/0.51  fof(f577,plain,(
% 0.20/0.51    ( ! [X16] : (~r1_orders_2(sK0,sK4(sK0,X16,sK1),sK1) | r2_lattice3(sK0,X16,sK1)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f530,f57])).
% 0.20/0.51  fof(f530,plain,(
% 0.20/0.51    ( ! [X16] : (r2_lattice3(sK0,X16,sK1) | ~r1_orders_2(sK0,sK4(sK0,X16,sK1),sK1) | ~l1_orders_2(sK0)) )),
% 0.20/0.51    inference(resolution,[],[f58,f89])).
% 0.20/0.51  fof(f89,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | ~r1_orders_2(X0,sK4(X0,X1,X2),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f51])).
% 0.20/0.51  fof(f1441,plain,(
% 0.20/0.51    r1_orders_2(sK0,sK4(sK0,k5_waybel_0(sK0,sK1),sK1),sK1) | ~m1_subset_1(sK4(sK0,k5_waybel_0(sK0,sK1),sK1),u1_struct_0(sK0)) | r2_lattice3(sK0,k5_waybel_0(sK0,sK1),sK1) | spl5_13),
% 0.20/0.51    inference(resolution,[],[f566,f576])).
% 0.20/0.51  fof(f576,plain,(
% 0.20/0.51    ( ! [X15] : (r2_hidden(sK4(sK0,X15,sK1),X15) | r2_lattice3(sK0,X15,sK1)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f529,f57])).
% 0.20/0.51  fof(f529,plain,(
% 0.20/0.51    ( ! [X15] : (r2_lattice3(sK0,X15,sK1) | r2_hidden(sK4(sK0,X15,sK1),X15) | ~l1_orders_2(sK0)) )),
% 0.20/0.51    inference(resolution,[],[f58,f88])).
% 0.20/0.51  fof(f88,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | r2_hidden(sK4(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f51])).
% 0.20/0.51  fof(f566,plain,(
% 0.20/0.51    ( ! [X6] : (~r2_hidden(X6,k5_waybel_0(sK0,sK1)) | r1_orders_2(sK0,X6,sK1) | ~m1_subset_1(X6,u1_struct_0(sK0))) ) | spl5_13),
% 0.20/0.51    inference(subsumption_resolution,[],[f565,f154])).
% 0.20/0.51  fof(f565,plain,(
% 0.20/0.51    ( ! [X6] : (r1_orders_2(sK0,X6,sK1) | ~r2_hidden(X6,k5_waybel_0(sK0,sK1)) | ~m1_subset_1(X6,u1_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f522,f57])).
% 0.20/0.51  fof(f522,plain,(
% 0.20/0.51    ( ! [X6] : (r1_orders_2(sK0,X6,sK1) | ~r2_hidden(X6,k5_waybel_0(sK0,sK1)) | ~m1_subset_1(X6,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.51    inference(resolution,[],[f58,f84])).
% 0.20/0.51  fof(f84,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (r1_orders_2(X0,X2,X1) | ~r2_hidden(X2,k5_waybel_0(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f47])).
% 0.20/0.51  fof(f1472,plain,(
% 0.20/0.51    spl5_43 | spl5_42 | spl5_13),
% 0.20/0.51    inference(avatar_split_clause,[],[f1467,f153,f1461,f1469])).
% 0.20/0.51  fof(f1467,plain,(
% 0.20/0.51    sK1 = k1_yellow_0(sK0,k5_waybel_0(sK0,sK1)) | r2_lattice3(sK0,k5_waybel_0(sK0,sK1),sK3(sK0,sK1,k5_waybel_0(sK0,sK1))) | spl5_13),
% 0.20/0.51    inference(subsumption_resolution,[],[f1466,f54])).
% 0.20/0.51  fof(f1466,plain,(
% 0.20/0.51    sK1 = k1_yellow_0(sK0,k5_waybel_0(sK0,sK1)) | r2_lattice3(sK0,k5_waybel_0(sK0,sK1),sK3(sK0,sK1,k5_waybel_0(sK0,sK1))) | ~v5_orders_2(sK0) | spl5_13),
% 0.20/0.51    inference(subsumption_resolution,[],[f1465,f57])).
% 0.20/0.51  fof(f1465,plain,(
% 0.20/0.51    sK1 = k1_yellow_0(sK0,k5_waybel_0(sK0,sK1)) | r2_lattice3(sK0,k5_waybel_0(sK0,sK1),sK3(sK0,sK1,k5_waybel_0(sK0,sK1))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | spl5_13),
% 0.20/0.51    inference(subsumption_resolution,[],[f1446,f58])).
% 0.20/0.51  fof(f1446,plain,(
% 0.20/0.51    sK1 = k1_yellow_0(sK0,k5_waybel_0(sK0,sK1)) | r2_lattice3(sK0,k5_waybel_0(sK0,sK1),sK3(sK0,sK1,k5_waybel_0(sK0,sK1))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | spl5_13),
% 0.20/0.51    inference(resolution,[],[f1444,f75])).
% 0.20/0.51  fof(f75,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k1_yellow_0(X0,X2) = X1 | r2_lattice3(X0,X2,sK3(X0,X1,X2)) | ~r2_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f46])).
% 0.20/0.51  fof(f1464,plain,(
% 0.20/0.51    spl5_41 | spl5_42 | spl5_13),
% 0.20/0.51    inference(avatar_split_clause,[],[f1455,f153,f1461,f1457])).
% 0.20/0.51  fof(f1455,plain,(
% 0.20/0.51    sK1 = k1_yellow_0(sK0,k5_waybel_0(sK0,sK1)) | m1_subset_1(sK3(sK0,sK1,k5_waybel_0(sK0,sK1)),u1_struct_0(sK0)) | spl5_13),
% 0.20/0.51    inference(subsumption_resolution,[],[f1454,f54])).
% 0.20/0.51  fof(f1454,plain,(
% 0.20/0.51    sK1 = k1_yellow_0(sK0,k5_waybel_0(sK0,sK1)) | m1_subset_1(sK3(sK0,sK1,k5_waybel_0(sK0,sK1)),u1_struct_0(sK0)) | ~v5_orders_2(sK0) | spl5_13),
% 0.20/0.51    inference(subsumption_resolution,[],[f1453,f57])).
% 0.20/0.51  fof(f1453,plain,(
% 0.20/0.51    sK1 = k1_yellow_0(sK0,k5_waybel_0(sK0,sK1)) | m1_subset_1(sK3(sK0,sK1,k5_waybel_0(sK0,sK1)),u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | spl5_13),
% 0.20/0.51    inference(subsumption_resolution,[],[f1445,f58])).
% 0.20/0.51  fof(f1445,plain,(
% 0.20/0.51    sK1 = k1_yellow_0(sK0,k5_waybel_0(sK0,sK1)) | m1_subset_1(sK3(sK0,sK1,k5_waybel_0(sK0,sK1)),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | spl5_13),
% 0.20/0.51    inference(resolution,[],[f1444,f74])).
% 0.20/0.51  fof(f74,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k1_yellow_0(X0,X2) = X1 | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) | ~r2_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f46])).
% 0.20/0.51  fof(f581,plain,(
% 0.20/0.51    spl5_30),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f580])).
% 0.20/0.51  fof(f580,plain,(
% 0.20/0.51    $false | spl5_30),
% 0.20/0.51    inference(subsumption_resolution,[],[f498,f58])).
% 0.20/0.51  fof(f498,plain,(
% 0.20/0.51    ~m1_subset_1(sK1,u1_struct_0(sK0)) | spl5_30),
% 0.20/0.51    inference(avatar_component_clause,[],[f496])).
% 0.20/0.51  fof(f496,plain,(
% 0.20/0.51    spl5_30 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).
% 0.20/0.51  fof(f503,plain,(
% 0.20/0.51    ~spl5_30 | spl5_31),
% 0.20/0.51    inference(avatar_split_clause,[],[f494,f500,f496])).
% 0.20/0.51  fof(f494,plain,(
% 0.20/0.51    v1_waybel_7(k5_waybel_0(sK0,sK1),sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.51    inference(subsumption_resolution,[],[f493,f52])).
% 0.20/0.51  fof(f493,plain,(
% 0.20/0.51    v1_waybel_7(k5_waybel_0(sK0,sK1),sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~v3_orders_2(sK0)),
% 0.20/0.51    inference(subsumption_resolution,[],[f492,f53])).
% 0.20/0.51  fof(f492,plain,(
% 0.20/0.51    v1_waybel_7(k5_waybel_0(sK0,sK1),sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0)),
% 0.20/0.51    inference(subsumption_resolution,[],[f491,f54])).
% 0.20/0.51  fof(f491,plain,(
% 0.20/0.51    v1_waybel_7(k5_waybel_0(sK0,sK1),sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0)),
% 0.20/0.51    inference(subsumption_resolution,[],[f490,f55])).
% 0.20/0.51  fof(f490,plain,(
% 0.20/0.51    v1_waybel_7(k5_waybel_0(sK0,sK1),sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0)),
% 0.20/0.51    inference(subsumption_resolution,[],[f489,f56])).
% 0.20/0.51  fof(f489,plain,(
% 0.20/0.51    v1_waybel_7(k5_waybel_0(sK0,sK1),sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0)),
% 0.20/0.51    inference(subsumption_resolution,[],[f488,f57])).
% 0.20/0.51  fof(f488,plain,(
% 0.20/0.51    v1_waybel_7(k5_waybel_0(sK0,sK1),sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0)),
% 0.20/0.51    inference(resolution,[],[f59,f68])).
% 0.20/0.51  fof(f68,plain,(
% 0.20/0.51    ( ! [X0,X1] : (v1_waybel_7(k5_waybel_0(X0,X1),X0) | ~v5_waybel_6(X1,X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f20])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (v1_waybel_7(k5_waybel_0(X0,X1),X0) | ~v5_waybel_6(X1,X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0))),
% 0.20/0.51    inference(flattening,[],[f19])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : ((v1_waybel_7(k5_waybel_0(X0,X1),X0) | ~v5_waybel_6(X1,X0)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f11])).
% 0.20/0.51  fof(f11,axiom,(
% 0.20/0.51    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v5_waybel_6(X1,X0) => v1_waybel_7(k5_waybel_0(X0,X1),X0))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_waybel_7)).
% 0.20/0.51  fof(f59,plain,(
% 0.20/0.51    v5_waybel_6(sK1,sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f40])).
% 0.20/0.51  fof(f469,plain,(
% 0.20/0.51    spl5_5),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f468])).
% 0.20/0.51  fof(f468,plain,(
% 0.20/0.51    $false | spl5_5),
% 0.20/0.51    inference(subsumption_resolution,[],[f123,f57])).
% 0.20/0.51  fof(f123,plain,(
% 0.20/0.51    ~l1_orders_2(sK0) | spl5_5),
% 0.20/0.51    inference(avatar_component_clause,[],[f121])).
% 0.20/0.51  fof(f121,plain,(
% 0.20/0.51    spl5_5 <=> l1_orders_2(sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.20/0.51  fof(f315,plain,(
% 0.20/0.51    ~spl5_5 | ~spl5_13),
% 0.20/0.51    inference(avatar_split_clause,[],[f285,f153,f121])).
% 0.20/0.51  fof(f285,plain,(
% 0.20/0.51    ~v2_struct_0(sK0) | ~l1_orders_2(sK0)),
% 0.20/0.51    inference(resolution,[],[f55,f71])).
% 0.20/0.51  fof(f71,plain,(
% 0.20/0.51    ( ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f25])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0))),
% 0.20/0.51    inference(flattening,[],[f24])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    ! [X0] : ((~v2_struct_0(X0) | ~v1_lattice3(X0)) | ~l1_orders_2(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0] : (l1_orders_2(X0) => (v1_lattice3(X0) => ~v2_struct_0(X0)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattice3)).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (23255)------------------------------
% 0.20/0.51  % (23255)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (23255)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (23255)Memory used [KB]: 6908
% 0.20/0.51  % (23255)Time elapsed: 0.055 s
% 0.20/0.51  % (23255)------------------------------
% 0.20/0.51  % (23255)------------------------------
% 0.20/0.51  % (23247)Refutation not found, incomplete strategy% (23247)------------------------------
% 0.20/0.51  % (23247)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (23247)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (23247)Memory used [KB]: 10746
% 0.20/0.51  % (23247)Time elapsed: 0.111 s
% 0.20/0.51  % (23247)------------------------------
% 0.20/0.51  % (23247)------------------------------
% 0.20/0.51  % (23231)Success in time 0.17 s
%------------------------------------------------------------------------------
