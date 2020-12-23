%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1573+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:25 EST 2020

% Result     : Theorem 3.56s
% Output     : Refutation 3.56s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 310 expanded)
%              Number of leaves         :   14 ( 103 expanded)
%              Depth                    :   22
%              Number of atoms          :  401 (1563 expanded)
%              Number of equality atoms :   20 ( 239 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20515,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f20180,f20282,f20439,f20493,f20514])).

fof(f20514,plain,
    ( spl1238_5
    | ~ spl1238_6 ),
    inference(avatar_contradiction_clause,[],[f20513])).

fof(f20513,plain,
    ( $false
    | spl1238_5
    | ~ spl1238_6 ),
    inference(subsumption_resolution,[],[f20512,f10391])).

fof(f10391,plain,(
    ~ v2_struct_0(sK125) ),
    inference(cnf_transformation,[],[f7420])).

fof(f7420,plain,
    ( k1_yellow_0(sK125,sK126) != k1_yellow_0(sK125,k3_xboole_0(sK126,u1_struct_0(sK125)))
    & ( r1_yellow_0(sK125,k3_xboole_0(sK126,u1_struct_0(sK125)))
      | r1_yellow_0(sK125,sK126) )
    & l1_orders_2(sK125)
    & ~ v2_struct_0(sK125) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK125,sK126])],[f3140,f7419,f7418])).

fof(f7418,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k1_yellow_0(X0,X1) != k1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
            & ( r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
              | r1_yellow_0(X0,X1) ) )
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k1_yellow_0(sK125,X1) != k1_yellow_0(sK125,k3_xboole_0(X1,u1_struct_0(sK125)))
          & ( r1_yellow_0(sK125,k3_xboole_0(X1,u1_struct_0(sK125)))
            | r1_yellow_0(sK125,X1) ) )
      & l1_orders_2(sK125)
      & ~ v2_struct_0(sK125) ) ),
    introduced(choice_axiom,[])).

fof(f7419,plain,
    ( ? [X1] :
        ( k1_yellow_0(sK125,X1) != k1_yellow_0(sK125,k3_xboole_0(X1,u1_struct_0(sK125)))
        & ( r1_yellow_0(sK125,k3_xboole_0(X1,u1_struct_0(sK125)))
          | r1_yellow_0(sK125,X1) ) )
   => ( k1_yellow_0(sK125,sK126) != k1_yellow_0(sK125,k3_xboole_0(sK126,u1_struct_0(sK125)))
      & ( r1_yellow_0(sK125,k3_xboole_0(sK126,u1_struct_0(sK125)))
        | r1_yellow_0(sK125,sK126) ) ) ),
    introduced(choice_axiom,[])).

fof(f3140,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_yellow_0(X0,X1) != k1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
          & ( r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
            | r1_yellow_0(X0,X1) ) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3139])).

fof(f3139,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_yellow_0(X0,X1) != k1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
          & ( r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
            | r1_yellow_0(X0,X1) ) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3034])).

fof(f3034,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
              | r1_yellow_0(X0,X1) )
           => k1_yellow_0(X0,X1) = k1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0))) ) ) ),
    inference(negated_conjecture,[],[f3033])).

fof(f3033,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
            | r1_yellow_0(X0,X1) )
         => k1_yellow_0(X0,X1) = k1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_yellow_0)).

fof(f20512,plain,
    ( v2_struct_0(sK125)
    | spl1238_5
    | ~ spl1238_6 ),
    inference(subsumption_resolution,[],[f20511,f10392])).

fof(f10392,plain,(
    l1_orders_2(sK125) ),
    inference(cnf_transformation,[],[f7420])).

fof(f20511,plain,
    ( ~ l1_orders_2(sK125)
    | v2_struct_0(sK125)
    | spl1238_5
    | ~ spl1238_6 ),
    inference(subsumption_resolution,[],[f20510,f20174])).

fof(f20174,plain,
    ( ~ r1_yellow_0(sK125,sK126)
    | spl1238_5 ),
    inference(avatar_component_clause,[],[f20173])).

fof(f20173,plain,
    ( spl1238_5
  <=> r1_yellow_0(sK125,sK126) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1238_5])])).

fof(f20510,plain,
    ( r1_yellow_0(sK125,sK126)
    | ~ l1_orders_2(sK125)
    | v2_struct_0(sK125)
    | ~ spl1238_6 ),
    inference(resolution,[],[f20179,f12434])).

fof(f12434,plain,(
    ! [X0,X1] :
      ( ~ r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
      | r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4377])).

fof(f4377,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_yellow_0(X0,X1)
            | ~ r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0))) )
          & ( r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
            | ~ r2_yellow_0(X0,X1) )
          & ( r1_yellow_0(X0,X1)
            | ~ r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0))) )
          & ( r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
            | ~ r1_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f4376])).

fof(f4376,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_yellow_0(X0,X1)
            | ~ r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0))) )
          & ( r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
            | ~ r2_yellow_0(X0,X1) )
          & ( r1_yellow_0(X0,X1)
            | ~ r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0))) )
          & ( r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
            | ~ r1_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3032])).

fof(f3032,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
           => r2_yellow_0(X0,X1) )
          & ( r2_yellow_0(X0,X1)
           => r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0))) )
          & ( r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
           => r1_yellow_0(X0,X1) )
          & ( r1_yellow_0(X0,X1)
           => r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_yellow_0)).

fof(f20179,plain,
    ( r1_yellow_0(sK125,k3_xboole_0(sK126,u1_struct_0(sK125)))
    | ~ spl1238_6 ),
    inference(avatar_component_clause,[],[f20177])).

fof(f20177,plain,
    ( spl1238_6
  <=> r1_yellow_0(sK125,k3_xboole_0(sK126,u1_struct_0(sK125))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1238_6])])).

fof(f20493,plain,
    ( ~ spl1238_5
    | ~ spl1238_12 ),
    inference(avatar_contradiction_clause,[],[f20492])).

fof(f20492,plain,
    ( $false
    | ~ spl1238_5
    | ~ spl1238_12 ),
    inference(subsumption_resolution,[],[f20471,f20467])).

fof(f20467,plain,
    ( r2_lattice3(sK125,sK126,sK440(sK125,sK126,k3_xboole_0(sK126,u1_struct_0(sK125))))
    | ~ spl1238_5
    | ~ spl1238_12 ),
    inference(subsumption_resolution,[],[f20466,f10391])).

fof(f20466,plain,
    ( r2_lattice3(sK125,sK126,sK440(sK125,sK126,k3_xboole_0(sK126,u1_struct_0(sK125))))
    | v2_struct_0(sK125)
    | ~ spl1238_5
    | ~ spl1238_12 ),
    inference(subsumption_resolution,[],[f20465,f10392])).

fof(f20465,plain,
    ( r2_lattice3(sK125,sK126,sK440(sK125,sK126,k3_xboole_0(sK126,u1_struct_0(sK125))))
    | ~ l1_orders_2(sK125)
    | v2_struct_0(sK125)
    | ~ spl1238_5
    | ~ spl1238_12 ),
    inference(subsumption_resolution,[],[f20459,f20188])).

fof(f20188,plain,
    ( m1_subset_1(sK440(sK125,sK126,k3_xboole_0(sK126,u1_struct_0(sK125))),u1_struct_0(sK125))
    | ~ spl1238_5 ),
    inference(subsumption_resolution,[],[f20187,f10391])).

fof(f20187,plain,
    ( m1_subset_1(sK440(sK125,sK126,k3_xboole_0(sK126,u1_struct_0(sK125))),u1_struct_0(sK125))
    | v2_struct_0(sK125)
    | ~ spl1238_5 ),
    inference(subsumption_resolution,[],[f20186,f10392])).

fof(f20186,plain,
    ( m1_subset_1(sK440(sK125,sK126,k3_xboole_0(sK126,u1_struct_0(sK125))),u1_struct_0(sK125))
    | ~ l1_orders_2(sK125)
    | v2_struct_0(sK125)
    | ~ spl1238_5 ),
    inference(subsumption_resolution,[],[f20181,f20175])).

fof(f20175,plain,
    ( r1_yellow_0(sK125,sK126)
    | ~ spl1238_5 ),
    inference(avatar_component_clause,[],[f20173])).

fof(f20181,plain,
    ( m1_subset_1(sK440(sK125,sK126,k3_xboole_0(sK126,u1_struct_0(sK125))),u1_struct_0(sK125))
    | ~ r1_yellow_0(sK125,sK126)
    | ~ l1_orders_2(sK125)
    | v2_struct_0(sK125) ),
    inference(resolution,[],[f17714,f18309])).

fof(f18309,plain,(
    ! [X2,X0,X1] :
      ( sQ1237_eqProxy(k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
      | m1_subset_1(sK440(X0,X1,X2),u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_proxy_replacement,[],[f12444,f17680])).

fof(f17680,plain,(
    ! [X1,X0] :
      ( sQ1237_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ1237_eqProxy])])).

fof(f12444,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2)
      | m1_subset_1(sK440(X0,X1,X2),u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f8348])).

fof(f8348,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2)
          | ( ( ~ r2_lattice3(X0,X2,sK440(X0,X1,X2))
              | ~ r2_lattice3(X0,X1,sK440(X0,X1,X2)) )
            & ( r2_lattice3(X0,X2,sK440(X0,X1,X2))
              | r2_lattice3(X0,X1,sK440(X0,X1,X2)) )
            & m1_subset_1(sK440(X0,X1,X2),u1_struct_0(X0)) )
          | ~ r1_yellow_0(X0,X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK440])],[f8346,f8347])).

fof(f8347,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_lattice3(X0,X2,X3)
            | ~ r2_lattice3(X0,X1,X3) )
          & ( r2_lattice3(X0,X2,X3)
            | r2_lattice3(X0,X1,X3) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ( ~ r2_lattice3(X0,X2,sK440(X0,X1,X2))
          | ~ r2_lattice3(X0,X1,sK440(X0,X1,X2)) )
        & ( r2_lattice3(X0,X2,sK440(X0,X1,X2))
          | r2_lattice3(X0,X1,sK440(X0,X1,X2)) )
        & m1_subset_1(sK440(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f8346,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2)
          | ? [X3] :
              ( ( ~ r2_lattice3(X0,X2,X3)
                | ~ r2_lattice3(X0,X1,X3) )
              & ( r2_lattice3(X0,X2,X3)
                | r2_lattice3(X0,X1,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r1_yellow_0(X0,X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f8345])).

fof(f8345,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2)
          | ? [X3] :
              ( ( ~ r2_lattice3(X0,X2,X3)
                | ~ r2_lattice3(X0,X1,X3) )
              & ( r2_lattice3(X0,X2,X3)
                | r2_lattice3(X0,X1,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r1_yellow_0(X0,X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f4383])).

fof(f4383,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2)
          | ? [X3] :
              ( ( r2_lattice3(X0,X1,X3)
              <~> r2_lattice3(X0,X2,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r1_yellow_0(X0,X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f4382])).

fof(f4382,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2)
          | ? [X3] :
              ( ( r2_lattice3(X0,X1,X3)
              <~> r2_lattice3(X0,X2,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r1_yellow_0(X0,X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3028])).

fof(f3028,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1,X2] :
          ( ( ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_lattice3(X0,X1,X3)
                <=> r2_lattice3(X0,X2,X3) ) )
            & r1_yellow_0(X0,X1) )
         => k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_yellow_0)).

fof(f17714,plain,(
    ~ sQ1237_eqProxy(k1_yellow_0(sK125,sK126),k1_yellow_0(sK125,k3_xboole_0(sK126,u1_struct_0(sK125)))) ),
    inference(equality_proxy_replacement,[],[f10394,f17680])).

fof(f10394,plain,(
    k1_yellow_0(sK125,sK126) != k1_yellow_0(sK125,k3_xboole_0(sK126,u1_struct_0(sK125))) ),
    inference(cnf_transformation,[],[f7420])).

fof(f20459,plain,
    ( r2_lattice3(sK125,sK126,sK440(sK125,sK126,k3_xboole_0(sK126,u1_struct_0(sK125))))
    | ~ m1_subset_1(sK440(sK125,sK126,k3_xboole_0(sK126,u1_struct_0(sK125))),u1_struct_0(sK125))
    | ~ l1_orders_2(sK125)
    | v2_struct_0(sK125)
    | ~ spl1238_12 ),
    inference(resolution,[],[f20281,f12438])).

fof(f12438,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
      | r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4379])).

fof(f4379,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ~ r1_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2) )
            & ( r1_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
              | ~ r1_lattice3(X0,X1,X2) )
            & ( r2_lattice3(X0,X1,X2)
              | ~ r2_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2) )
            & ( r2_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f4378])).

fof(f4378,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ~ r1_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2) )
            & ( r1_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
              | ~ r1_lattice3(X0,X1,X2) )
            & ( r2_lattice3(X0,X1,X2)
              | ~ r2_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2) )
            & ( r2_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3035])).

fof(f3035,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( ( r1_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
             => r1_lattice3(X0,X1,X2) )
            & ( r1_lattice3(X0,X1,X2)
             => r1_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2) )
            & ( r2_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
             => r2_lattice3(X0,X1,X2) )
            & ( r2_lattice3(X0,X1,X2)
             => r2_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_yellow_0)).

fof(f20281,plain,
    ( r2_lattice3(sK125,k3_xboole_0(sK126,u1_struct_0(sK125)),sK440(sK125,sK126,k3_xboole_0(sK126,u1_struct_0(sK125))))
    | ~ spl1238_12 ),
    inference(avatar_component_clause,[],[f20279])).

fof(f20279,plain,
    ( spl1238_12
  <=> r2_lattice3(sK125,k3_xboole_0(sK126,u1_struct_0(sK125)),sK440(sK125,sK126,k3_xboole_0(sK126,u1_struct_0(sK125)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1238_12])])).

fof(f20471,plain,
    ( ~ r2_lattice3(sK125,sK126,sK440(sK125,sK126,k3_xboole_0(sK126,u1_struct_0(sK125))))
    | ~ spl1238_5
    | ~ spl1238_12 ),
    inference(subsumption_resolution,[],[f20470,f10391])).

fof(f20470,plain,
    ( ~ r2_lattice3(sK125,sK126,sK440(sK125,sK126,k3_xboole_0(sK126,u1_struct_0(sK125))))
    | v2_struct_0(sK125)
    | ~ spl1238_5
    | ~ spl1238_12 ),
    inference(subsumption_resolution,[],[f20469,f10392])).

fof(f20469,plain,
    ( ~ r2_lattice3(sK125,sK126,sK440(sK125,sK126,k3_xboole_0(sK126,u1_struct_0(sK125))))
    | ~ l1_orders_2(sK125)
    | v2_struct_0(sK125)
    | ~ spl1238_5
    | ~ spl1238_12 ),
    inference(subsumption_resolution,[],[f20468,f20175])).

fof(f20468,plain,
    ( ~ r2_lattice3(sK125,sK126,sK440(sK125,sK126,k3_xboole_0(sK126,u1_struct_0(sK125))))
    | ~ r1_yellow_0(sK125,sK126)
    | ~ l1_orders_2(sK125)
    | v2_struct_0(sK125)
    | ~ spl1238_12 ),
    inference(subsumption_resolution,[],[f20460,f17714])).

fof(f20460,plain,
    ( sQ1237_eqProxy(k1_yellow_0(sK125,sK126),k1_yellow_0(sK125,k3_xboole_0(sK126,u1_struct_0(sK125))))
    | ~ r2_lattice3(sK125,sK126,sK440(sK125,sK126,k3_xboole_0(sK126,u1_struct_0(sK125))))
    | ~ r1_yellow_0(sK125,sK126)
    | ~ l1_orders_2(sK125)
    | v2_struct_0(sK125)
    | ~ spl1238_12 ),
    inference(resolution,[],[f20281,f18307])).

fof(f18307,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_lattice3(X0,X2,sK440(X0,X1,X2))
      | sQ1237_eqProxy(k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
      | ~ r2_lattice3(X0,X1,sK440(X0,X1,X2))
      | ~ r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_proxy_replacement,[],[f12446,f17680])).

fof(f12446,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2)
      | ~ r2_lattice3(X0,X2,sK440(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,sK440(X0,X1,X2))
      | ~ r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f8348])).

fof(f20439,plain,
    ( ~ spl1238_5
    | ~ spl1238_11 ),
    inference(avatar_contradiction_clause,[],[f20438])).

fof(f20438,plain,
    ( $false
    | ~ spl1238_5
    | ~ spl1238_11 ),
    inference(subsumption_resolution,[],[f20437,f10391])).

fof(f20437,plain,
    ( v2_struct_0(sK125)
    | ~ spl1238_5
    | ~ spl1238_11 ),
    inference(subsumption_resolution,[],[f20436,f10392])).

fof(f20436,plain,
    ( ~ l1_orders_2(sK125)
    | v2_struct_0(sK125)
    | ~ spl1238_5
    | ~ spl1238_11 ),
    inference(subsumption_resolution,[],[f20435,f20175])).

fof(f20435,plain,
    ( ~ r1_yellow_0(sK125,sK126)
    | ~ l1_orders_2(sK125)
    | v2_struct_0(sK125)
    | ~ spl1238_5
    | ~ spl1238_11 ),
    inference(subsumption_resolution,[],[f20434,f20277])).

fof(f20277,plain,
    ( r2_lattice3(sK125,sK126,sK440(sK125,sK126,k3_xboole_0(sK126,u1_struct_0(sK125))))
    | ~ spl1238_11 ),
    inference(avatar_component_clause,[],[f20275])).

fof(f20275,plain,
    ( spl1238_11
  <=> r2_lattice3(sK125,sK126,sK440(sK125,sK126,k3_xboole_0(sK126,u1_struct_0(sK125)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1238_11])])).

fof(f20434,plain,
    ( ~ r2_lattice3(sK125,sK126,sK440(sK125,sK126,k3_xboole_0(sK126,u1_struct_0(sK125))))
    | ~ r1_yellow_0(sK125,sK126)
    | ~ l1_orders_2(sK125)
    | v2_struct_0(sK125)
    | ~ spl1238_5
    | ~ spl1238_11 ),
    inference(subsumption_resolution,[],[f20433,f17714])).

fof(f20433,plain,
    ( sQ1237_eqProxy(k1_yellow_0(sK125,sK126),k1_yellow_0(sK125,k3_xboole_0(sK126,u1_struct_0(sK125))))
    | ~ r2_lattice3(sK125,sK126,sK440(sK125,sK126,k3_xboole_0(sK126,u1_struct_0(sK125))))
    | ~ r1_yellow_0(sK125,sK126)
    | ~ l1_orders_2(sK125)
    | v2_struct_0(sK125)
    | ~ spl1238_5
    | ~ spl1238_11 ),
    inference(subsumption_resolution,[],[f20423,f13848])).

fof(f13848,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f20423,plain,
    ( ~ r1_tarski(k3_xboole_0(sK126,u1_struct_0(sK125)),sK126)
    | sQ1237_eqProxy(k1_yellow_0(sK125,sK126),k1_yellow_0(sK125,k3_xboole_0(sK126,u1_struct_0(sK125))))
    | ~ r2_lattice3(sK125,sK126,sK440(sK125,sK126,k3_xboole_0(sK126,u1_struct_0(sK125))))
    | ~ r1_yellow_0(sK125,sK126)
    | ~ l1_orders_2(sK125)
    | v2_struct_0(sK125)
    | ~ spl1238_5
    | ~ spl1238_11 ),
    inference(resolution,[],[f20294,f18307])).

fof(f20294,plain,
    ( ! [X3] :
        ( r2_lattice3(sK125,X3,sK440(sK125,sK126,k3_xboole_0(sK126,u1_struct_0(sK125))))
        | ~ r1_tarski(X3,sK126) )
    | ~ spl1238_5
    | ~ spl1238_11 ),
    inference(subsumption_resolution,[],[f20293,f10392])).

fof(f20293,plain,
    ( ! [X3] :
        ( r2_lattice3(sK125,X3,sK440(sK125,sK126,k3_xboole_0(sK126,u1_struct_0(sK125))))
        | ~ r1_tarski(X3,sK126)
        | ~ l1_orders_2(sK125) )
    | ~ spl1238_5
    | ~ spl1238_11 ),
    inference(subsumption_resolution,[],[f20286,f20188])).

fof(f20286,plain,
    ( ! [X3] :
        ( r2_lattice3(sK125,X3,sK440(sK125,sK126,k3_xboole_0(sK126,u1_struct_0(sK125))))
        | ~ m1_subset_1(sK440(sK125,sK126,k3_xboole_0(sK126,u1_struct_0(sK125))),u1_struct_0(sK125))
        | ~ r1_tarski(X3,sK126)
        | ~ l1_orders_2(sK125) )
    | ~ spl1238_11 ),
    inference(resolution,[],[f20277,f11448])).

fof(f11448,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_lattice3(X0,X2,X3)
      | r2_lattice3(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_tarski(X1,X2)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3708])).

fof(f3708,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ! [X3] :
              ( ( ( r2_lattice3(X0,X1,X3)
                  | ~ r2_lattice3(X0,X2,X3) )
                & ( r1_lattice3(X0,X1,X3)
                  | ~ r1_lattice3(X0,X2,X3) ) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r1_tarski(X1,X2) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3039])).

fof(f3039,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X0))
             => ( ( r2_lattice3(X0,X2,X3)
                 => r2_lattice3(X0,X1,X3) )
                & ( r1_lattice3(X0,X2,X3)
                 => r1_lattice3(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_yellow_0)).

fof(f20282,plain,
    ( spl1238_11
    | spl1238_12
    | ~ spl1238_5 ),
    inference(avatar_split_clause,[],[f20191,f20173,f20279,f20275])).

fof(f20191,plain,
    ( r2_lattice3(sK125,k3_xboole_0(sK126,u1_struct_0(sK125)),sK440(sK125,sK126,k3_xboole_0(sK126,u1_struct_0(sK125))))
    | r2_lattice3(sK125,sK126,sK440(sK125,sK126,k3_xboole_0(sK126,u1_struct_0(sK125))))
    | ~ spl1238_5 ),
    inference(subsumption_resolution,[],[f20190,f10391])).

fof(f20190,plain,
    ( r2_lattice3(sK125,k3_xboole_0(sK126,u1_struct_0(sK125)),sK440(sK125,sK126,k3_xboole_0(sK126,u1_struct_0(sK125))))
    | r2_lattice3(sK125,sK126,sK440(sK125,sK126,k3_xboole_0(sK126,u1_struct_0(sK125))))
    | v2_struct_0(sK125)
    | ~ spl1238_5 ),
    inference(subsumption_resolution,[],[f20189,f10392])).

fof(f20189,plain,
    ( r2_lattice3(sK125,k3_xboole_0(sK126,u1_struct_0(sK125)),sK440(sK125,sK126,k3_xboole_0(sK126,u1_struct_0(sK125))))
    | r2_lattice3(sK125,sK126,sK440(sK125,sK126,k3_xboole_0(sK126,u1_struct_0(sK125))))
    | ~ l1_orders_2(sK125)
    | v2_struct_0(sK125)
    | ~ spl1238_5 ),
    inference(subsumption_resolution,[],[f20182,f20175])).

fof(f20182,plain,
    ( r2_lattice3(sK125,k3_xboole_0(sK126,u1_struct_0(sK125)),sK440(sK125,sK126,k3_xboole_0(sK126,u1_struct_0(sK125))))
    | r2_lattice3(sK125,sK126,sK440(sK125,sK126,k3_xboole_0(sK126,u1_struct_0(sK125))))
    | ~ r1_yellow_0(sK125,sK126)
    | ~ l1_orders_2(sK125)
    | v2_struct_0(sK125) ),
    inference(resolution,[],[f17714,f18308])).

fof(f18308,plain,(
    ! [X2,X0,X1] :
      ( sQ1237_eqProxy(k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
      | r2_lattice3(X0,X2,sK440(X0,X1,X2))
      | r2_lattice3(X0,X1,sK440(X0,X1,X2))
      | ~ r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_proxy_replacement,[],[f12445,f17680])).

fof(f12445,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2)
      | r2_lattice3(X0,X2,sK440(X0,X1,X2))
      | r2_lattice3(X0,X1,sK440(X0,X1,X2))
      | ~ r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f8348])).

fof(f20180,plain,
    ( spl1238_5
    | spl1238_6 ),
    inference(avatar_split_clause,[],[f10393,f20177,f20173])).

fof(f10393,plain,
    ( r1_yellow_0(sK125,k3_xboole_0(sK126,u1_struct_0(sK125)))
    | r1_yellow_0(sK125,sK126) ),
    inference(cnf_transformation,[],[f7420])).
%------------------------------------------------------------------------------
