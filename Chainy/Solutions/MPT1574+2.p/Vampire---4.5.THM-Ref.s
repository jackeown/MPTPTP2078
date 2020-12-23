%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1574+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:25 EST 2020

% Result     : Theorem 4.07s
% Output     : Refutation 4.07s
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
fof(f20522,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f20187,f20289,f20446,f20500,f20521])).

fof(f20521,plain,
    ( spl1238_5
    | ~ spl1238_6 ),
    inference(avatar_contradiction_clause,[],[f20520])).

fof(f20520,plain,
    ( $false
    | spl1238_5
    | ~ spl1238_6 ),
    inference(subsumption_resolution,[],[f20519,f10394])).

fof(f10394,plain,(
    ~ v2_struct_0(sK125) ),
    inference(cnf_transformation,[],[f7423])).

fof(f7423,plain,
    ( k2_yellow_0(sK125,sK126) != k2_yellow_0(sK125,k3_xboole_0(sK126,u1_struct_0(sK125)))
    & ( r2_yellow_0(sK125,k3_xboole_0(sK126,u1_struct_0(sK125)))
      | r2_yellow_0(sK125,sK126) )
    & l1_orders_2(sK125)
    & ~ v2_struct_0(sK125) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK125,sK126])],[f3141,f7422,f7421])).

fof(f7421,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k2_yellow_0(X0,X1) != k2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
            & ( r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
              | r2_yellow_0(X0,X1) ) )
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k2_yellow_0(sK125,X1) != k2_yellow_0(sK125,k3_xboole_0(X1,u1_struct_0(sK125)))
          & ( r2_yellow_0(sK125,k3_xboole_0(X1,u1_struct_0(sK125)))
            | r2_yellow_0(sK125,X1) ) )
      & l1_orders_2(sK125)
      & ~ v2_struct_0(sK125) ) ),
    introduced(choice_axiom,[])).

fof(f7422,plain,
    ( ? [X1] :
        ( k2_yellow_0(sK125,X1) != k2_yellow_0(sK125,k3_xboole_0(X1,u1_struct_0(sK125)))
        & ( r2_yellow_0(sK125,k3_xboole_0(X1,u1_struct_0(sK125)))
          | r2_yellow_0(sK125,X1) ) )
   => ( k2_yellow_0(sK125,sK126) != k2_yellow_0(sK125,k3_xboole_0(sK126,u1_struct_0(sK125)))
      & ( r2_yellow_0(sK125,k3_xboole_0(sK126,u1_struct_0(sK125)))
        | r2_yellow_0(sK125,sK126) ) ) ),
    introduced(choice_axiom,[])).

fof(f3141,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_yellow_0(X0,X1) != k2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
          & ( r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
            | r2_yellow_0(X0,X1) ) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3140])).

fof(f3140,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_yellow_0(X0,X1) != k2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
          & ( r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
            | r2_yellow_0(X0,X1) ) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3035])).

fof(f3035,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
              | r2_yellow_0(X0,X1) )
           => k2_yellow_0(X0,X1) = k2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0))) ) ) ),
    inference(negated_conjecture,[],[f3034])).

fof(f3034,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
            | r2_yellow_0(X0,X1) )
         => k2_yellow_0(X0,X1) = k2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_yellow_0)).

fof(f20519,plain,
    ( v2_struct_0(sK125)
    | spl1238_5
    | ~ spl1238_6 ),
    inference(subsumption_resolution,[],[f20518,f10395])).

fof(f10395,plain,(
    l1_orders_2(sK125) ),
    inference(cnf_transformation,[],[f7423])).

fof(f20518,plain,
    ( ~ l1_orders_2(sK125)
    | v2_struct_0(sK125)
    | spl1238_5
    | ~ spl1238_6 ),
    inference(subsumption_resolution,[],[f20517,f20181])).

fof(f20181,plain,
    ( ~ r2_yellow_0(sK125,sK126)
    | spl1238_5 ),
    inference(avatar_component_clause,[],[f20180])).

fof(f20180,plain,
    ( spl1238_5
  <=> r2_yellow_0(sK125,sK126) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1238_5])])).

fof(f20517,plain,
    ( r2_yellow_0(sK125,sK126)
    | ~ l1_orders_2(sK125)
    | v2_struct_0(sK125)
    | ~ spl1238_6 ),
    inference(resolution,[],[f20186,f12439])).

fof(f12439,plain,(
    ! [X0,X1] :
      ( ~ r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
      | r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4378])).

fof(f4378,plain,(
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
    inference(flattening,[],[f4377])).

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

fof(f20186,plain,
    ( r2_yellow_0(sK125,k3_xboole_0(sK126,u1_struct_0(sK125)))
    | ~ spl1238_6 ),
    inference(avatar_component_clause,[],[f20184])).

fof(f20184,plain,
    ( spl1238_6
  <=> r2_yellow_0(sK125,k3_xboole_0(sK126,u1_struct_0(sK125))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1238_6])])).

fof(f20500,plain,
    ( ~ spl1238_5
    | ~ spl1238_12 ),
    inference(avatar_contradiction_clause,[],[f20499])).

fof(f20499,plain,
    ( $false
    | ~ spl1238_5
    | ~ spl1238_12 ),
    inference(subsumption_resolution,[],[f20478,f20474])).

fof(f20474,plain,
    ( r1_lattice3(sK125,sK126,sK440(sK125,sK126,k3_xboole_0(sK126,u1_struct_0(sK125))))
    | ~ spl1238_5
    | ~ spl1238_12 ),
    inference(subsumption_resolution,[],[f20473,f10394])).

fof(f20473,plain,
    ( r1_lattice3(sK125,sK126,sK440(sK125,sK126,k3_xboole_0(sK126,u1_struct_0(sK125))))
    | v2_struct_0(sK125)
    | ~ spl1238_5
    | ~ spl1238_12 ),
    inference(subsumption_resolution,[],[f20472,f10395])).

fof(f20472,plain,
    ( r1_lattice3(sK125,sK126,sK440(sK125,sK126,k3_xboole_0(sK126,u1_struct_0(sK125))))
    | ~ l1_orders_2(sK125)
    | v2_struct_0(sK125)
    | ~ spl1238_5
    | ~ spl1238_12 ),
    inference(subsumption_resolution,[],[f20466,f20195])).

fof(f20195,plain,
    ( m1_subset_1(sK440(sK125,sK126,k3_xboole_0(sK126,u1_struct_0(sK125))),u1_struct_0(sK125))
    | ~ spl1238_5 ),
    inference(subsumption_resolution,[],[f20194,f10394])).

fof(f20194,plain,
    ( m1_subset_1(sK440(sK125,sK126,k3_xboole_0(sK126,u1_struct_0(sK125))),u1_struct_0(sK125))
    | v2_struct_0(sK125)
    | ~ spl1238_5 ),
    inference(subsumption_resolution,[],[f20193,f10395])).

fof(f20193,plain,
    ( m1_subset_1(sK440(sK125,sK126,k3_xboole_0(sK126,u1_struct_0(sK125))),u1_struct_0(sK125))
    | ~ l1_orders_2(sK125)
    | v2_struct_0(sK125)
    | ~ spl1238_5 ),
    inference(subsumption_resolution,[],[f20188,f20182])).

fof(f20182,plain,
    ( r2_yellow_0(sK125,sK126)
    | ~ spl1238_5 ),
    inference(avatar_component_clause,[],[f20180])).

fof(f20188,plain,
    ( m1_subset_1(sK440(sK125,sK126,k3_xboole_0(sK126,u1_struct_0(sK125))),u1_struct_0(sK125))
    | ~ r2_yellow_0(sK125,sK126)
    | ~ l1_orders_2(sK125)
    | v2_struct_0(sK125) ),
    inference(resolution,[],[f17719,f18316])).

fof(f18316,plain,(
    ! [X2,X0,X1] :
      ( sQ1237_eqProxy(k2_yellow_0(X0,X1),k2_yellow_0(X0,X2))
      | m1_subset_1(sK440(X0,X1,X2),u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_proxy_replacement,[],[f12449,f17685])).

fof(f17685,plain,(
    ! [X1,X0] :
      ( sQ1237_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ1237_eqProxy])])).

fof(f12449,plain,(
    ! [X2,X0,X1] :
      ( k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2)
      | m1_subset_1(sK440(X0,X1,X2),u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f8351])).

fof(f8351,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2)
          | ( ( ~ r1_lattice3(X0,X2,sK440(X0,X1,X2))
              | ~ r1_lattice3(X0,X1,sK440(X0,X1,X2)) )
            & ( r1_lattice3(X0,X2,sK440(X0,X1,X2))
              | r1_lattice3(X0,X1,sK440(X0,X1,X2)) )
            & m1_subset_1(sK440(X0,X1,X2),u1_struct_0(X0)) )
          | ~ r2_yellow_0(X0,X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK440])],[f8349,f8350])).

fof(f8350,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r1_lattice3(X0,X2,X3)
            | ~ r1_lattice3(X0,X1,X3) )
          & ( r1_lattice3(X0,X2,X3)
            | r1_lattice3(X0,X1,X3) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ( ~ r1_lattice3(X0,X2,sK440(X0,X1,X2))
          | ~ r1_lattice3(X0,X1,sK440(X0,X1,X2)) )
        & ( r1_lattice3(X0,X2,sK440(X0,X1,X2))
          | r1_lattice3(X0,X1,sK440(X0,X1,X2)) )
        & m1_subset_1(sK440(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f8349,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2)
          | ? [X3] :
              ( ( ~ r1_lattice3(X0,X2,X3)
                | ~ r1_lattice3(X0,X1,X3) )
              & ( r1_lattice3(X0,X2,X3)
                | r1_lattice3(X0,X1,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r2_yellow_0(X0,X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f8348])).

fof(f8348,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2)
          | ? [X3] :
              ( ( ~ r1_lattice3(X0,X2,X3)
                | ~ r1_lattice3(X0,X1,X3) )
              & ( r1_lattice3(X0,X2,X3)
                | r1_lattice3(X0,X1,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r2_yellow_0(X0,X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f4386])).

fof(f4386,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2)
          | ? [X3] :
              ( ( r1_lattice3(X0,X1,X3)
              <~> r1_lattice3(X0,X2,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r2_yellow_0(X0,X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f4385])).

fof(f4385,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2)
          | ? [X3] :
              ( ( r1_lattice3(X0,X1,X3)
              <~> r1_lattice3(X0,X2,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r2_yellow_0(X0,X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3030])).

fof(f3030,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1,X2] :
          ( ( ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r1_lattice3(X0,X1,X3)
                <=> r1_lattice3(X0,X2,X3) ) )
            & r2_yellow_0(X0,X1) )
         => k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_yellow_0)).

fof(f17719,plain,(
    ~ sQ1237_eqProxy(k2_yellow_0(sK125,sK126),k2_yellow_0(sK125,k3_xboole_0(sK126,u1_struct_0(sK125)))) ),
    inference(equality_proxy_replacement,[],[f10397,f17685])).

fof(f10397,plain,(
    k2_yellow_0(sK125,sK126) != k2_yellow_0(sK125,k3_xboole_0(sK126,u1_struct_0(sK125))) ),
    inference(cnf_transformation,[],[f7423])).

fof(f20466,plain,
    ( r1_lattice3(sK125,sK126,sK440(sK125,sK126,k3_xboole_0(sK126,u1_struct_0(sK125))))
    | ~ m1_subset_1(sK440(sK125,sK126,k3_xboole_0(sK126,u1_struct_0(sK125))),u1_struct_0(sK125))
    | ~ l1_orders_2(sK125)
    | v2_struct_0(sK125)
    | ~ spl1238_12 ),
    inference(resolution,[],[f20288,f12445])).

fof(f12445,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
      | r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4382])).

fof(f4382,plain,(
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
    inference(flattening,[],[f4381])).

fof(f4381,plain,(
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
    inference(ennf_transformation,[],[f3036])).

fof(f3036,axiom,(
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

fof(f20288,plain,
    ( r1_lattice3(sK125,k3_xboole_0(sK126,u1_struct_0(sK125)),sK440(sK125,sK126,k3_xboole_0(sK126,u1_struct_0(sK125))))
    | ~ spl1238_12 ),
    inference(avatar_component_clause,[],[f20286])).

fof(f20286,plain,
    ( spl1238_12
  <=> r1_lattice3(sK125,k3_xboole_0(sK126,u1_struct_0(sK125)),sK440(sK125,sK126,k3_xboole_0(sK126,u1_struct_0(sK125)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1238_12])])).

fof(f20478,plain,
    ( ~ r1_lattice3(sK125,sK126,sK440(sK125,sK126,k3_xboole_0(sK126,u1_struct_0(sK125))))
    | ~ spl1238_5
    | ~ spl1238_12 ),
    inference(subsumption_resolution,[],[f20477,f10394])).

fof(f20477,plain,
    ( ~ r1_lattice3(sK125,sK126,sK440(sK125,sK126,k3_xboole_0(sK126,u1_struct_0(sK125))))
    | v2_struct_0(sK125)
    | ~ spl1238_5
    | ~ spl1238_12 ),
    inference(subsumption_resolution,[],[f20476,f10395])).

fof(f20476,plain,
    ( ~ r1_lattice3(sK125,sK126,sK440(sK125,sK126,k3_xboole_0(sK126,u1_struct_0(sK125))))
    | ~ l1_orders_2(sK125)
    | v2_struct_0(sK125)
    | ~ spl1238_5
    | ~ spl1238_12 ),
    inference(subsumption_resolution,[],[f20475,f20182])).

fof(f20475,plain,
    ( ~ r1_lattice3(sK125,sK126,sK440(sK125,sK126,k3_xboole_0(sK126,u1_struct_0(sK125))))
    | ~ r2_yellow_0(sK125,sK126)
    | ~ l1_orders_2(sK125)
    | v2_struct_0(sK125)
    | ~ spl1238_12 ),
    inference(subsumption_resolution,[],[f20467,f17719])).

fof(f20467,plain,
    ( sQ1237_eqProxy(k2_yellow_0(sK125,sK126),k2_yellow_0(sK125,k3_xboole_0(sK126,u1_struct_0(sK125))))
    | ~ r1_lattice3(sK125,sK126,sK440(sK125,sK126,k3_xboole_0(sK126,u1_struct_0(sK125))))
    | ~ r2_yellow_0(sK125,sK126)
    | ~ l1_orders_2(sK125)
    | v2_struct_0(sK125)
    | ~ spl1238_12 ),
    inference(resolution,[],[f20288,f18314])).

fof(f18314,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattice3(X0,X2,sK440(X0,X1,X2))
      | sQ1237_eqProxy(k2_yellow_0(X0,X1),k2_yellow_0(X0,X2))
      | ~ r1_lattice3(X0,X1,sK440(X0,X1,X2))
      | ~ r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_proxy_replacement,[],[f12451,f17685])).

fof(f12451,plain,(
    ! [X2,X0,X1] :
      ( k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2)
      | ~ r1_lattice3(X0,X2,sK440(X0,X1,X2))
      | ~ r1_lattice3(X0,X1,sK440(X0,X1,X2))
      | ~ r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f8351])).

fof(f20446,plain,
    ( ~ spl1238_5
    | ~ spl1238_11 ),
    inference(avatar_contradiction_clause,[],[f20445])).

fof(f20445,plain,
    ( $false
    | ~ spl1238_5
    | ~ spl1238_11 ),
    inference(subsumption_resolution,[],[f20444,f10394])).

fof(f20444,plain,
    ( v2_struct_0(sK125)
    | ~ spl1238_5
    | ~ spl1238_11 ),
    inference(subsumption_resolution,[],[f20443,f10395])).

fof(f20443,plain,
    ( ~ l1_orders_2(sK125)
    | v2_struct_0(sK125)
    | ~ spl1238_5
    | ~ spl1238_11 ),
    inference(subsumption_resolution,[],[f20442,f20182])).

fof(f20442,plain,
    ( ~ r2_yellow_0(sK125,sK126)
    | ~ l1_orders_2(sK125)
    | v2_struct_0(sK125)
    | ~ spl1238_5
    | ~ spl1238_11 ),
    inference(subsumption_resolution,[],[f20441,f20284])).

fof(f20284,plain,
    ( r1_lattice3(sK125,sK126,sK440(sK125,sK126,k3_xboole_0(sK126,u1_struct_0(sK125))))
    | ~ spl1238_11 ),
    inference(avatar_component_clause,[],[f20282])).

fof(f20282,plain,
    ( spl1238_11
  <=> r1_lattice3(sK125,sK126,sK440(sK125,sK126,k3_xboole_0(sK126,u1_struct_0(sK125)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1238_11])])).

fof(f20441,plain,
    ( ~ r1_lattice3(sK125,sK126,sK440(sK125,sK126,k3_xboole_0(sK126,u1_struct_0(sK125))))
    | ~ r2_yellow_0(sK125,sK126)
    | ~ l1_orders_2(sK125)
    | v2_struct_0(sK125)
    | ~ spl1238_5
    | ~ spl1238_11 ),
    inference(subsumption_resolution,[],[f20440,f17719])).

fof(f20440,plain,
    ( sQ1237_eqProxy(k2_yellow_0(sK125,sK126),k2_yellow_0(sK125,k3_xboole_0(sK126,u1_struct_0(sK125))))
    | ~ r1_lattice3(sK125,sK126,sK440(sK125,sK126,k3_xboole_0(sK126,u1_struct_0(sK125))))
    | ~ r2_yellow_0(sK125,sK126)
    | ~ l1_orders_2(sK125)
    | v2_struct_0(sK125)
    | ~ spl1238_5
    | ~ spl1238_11 ),
    inference(subsumption_resolution,[],[f20430,f13853])).

fof(f13853,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f20430,plain,
    ( ~ r1_tarski(k3_xboole_0(sK126,u1_struct_0(sK125)),sK126)
    | sQ1237_eqProxy(k2_yellow_0(sK125,sK126),k2_yellow_0(sK125,k3_xboole_0(sK126,u1_struct_0(sK125))))
    | ~ r1_lattice3(sK125,sK126,sK440(sK125,sK126,k3_xboole_0(sK126,u1_struct_0(sK125))))
    | ~ r2_yellow_0(sK125,sK126)
    | ~ l1_orders_2(sK125)
    | v2_struct_0(sK125)
    | ~ spl1238_5
    | ~ spl1238_11 ),
    inference(resolution,[],[f20301,f18314])).

fof(f20301,plain,
    ( ! [X3] :
        ( r1_lattice3(sK125,X3,sK440(sK125,sK126,k3_xboole_0(sK126,u1_struct_0(sK125))))
        | ~ r1_tarski(X3,sK126) )
    | ~ spl1238_5
    | ~ spl1238_11 ),
    inference(subsumption_resolution,[],[f20300,f10395])).

fof(f20300,plain,
    ( ! [X3] :
        ( r1_lattice3(sK125,X3,sK440(sK125,sK126,k3_xboole_0(sK126,u1_struct_0(sK125))))
        | ~ r1_tarski(X3,sK126)
        | ~ l1_orders_2(sK125) )
    | ~ spl1238_5
    | ~ spl1238_11 ),
    inference(subsumption_resolution,[],[f20293,f20195])).

fof(f20293,plain,
    ( ! [X3] :
        ( r1_lattice3(sK125,X3,sK440(sK125,sK126,k3_xboole_0(sK126,u1_struct_0(sK125))))
        | ~ m1_subset_1(sK440(sK125,sK126,k3_xboole_0(sK126,u1_struct_0(sK125))),u1_struct_0(sK125))
        | ~ r1_tarski(X3,sK126)
        | ~ l1_orders_2(sK125) )
    | ~ spl1238_11 ),
    inference(resolution,[],[f20284,f11450])).

fof(f11450,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_lattice3(X0,X2,X3)
      | r1_lattice3(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_tarski(X1,X2)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3709])).

fof(f3709,plain,(
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
    inference(ennf_transformation,[],[f3040])).

fof(f3040,axiom,(
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

fof(f20289,plain,
    ( spl1238_11
    | spl1238_12
    | ~ spl1238_5 ),
    inference(avatar_split_clause,[],[f20198,f20180,f20286,f20282])).

fof(f20198,plain,
    ( r1_lattice3(sK125,k3_xboole_0(sK126,u1_struct_0(sK125)),sK440(sK125,sK126,k3_xboole_0(sK126,u1_struct_0(sK125))))
    | r1_lattice3(sK125,sK126,sK440(sK125,sK126,k3_xboole_0(sK126,u1_struct_0(sK125))))
    | ~ spl1238_5 ),
    inference(subsumption_resolution,[],[f20197,f10394])).

fof(f20197,plain,
    ( r1_lattice3(sK125,k3_xboole_0(sK126,u1_struct_0(sK125)),sK440(sK125,sK126,k3_xboole_0(sK126,u1_struct_0(sK125))))
    | r1_lattice3(sK125,sK126,sK440(sK125,sK126,k3_xboole_0(sK126,u1_struct_0(sK125))))
    | v2_struct_0(sK125)
    | ~ spl1238_5 ),
    inference(subsumption_resolution,[],[f20196,f10395])).

fof(f20196,plain,
    ( r1_lattice3(sK125,k3_xboole_0(sK126,u1_struct_0(sK125)),sK440(sK125,sK126,k3_xboole_0(sK126,u1_struct_0(sK125))))
    | r1_lattice3(sK125,sK126,sK440(sK125,sK126,k3_xboole_0(sK126,u1_struct_0(sK125))))
    | ~ l1_orders_2(sK125)
    | v2_struct_0(sK125)
    | ~ spl1238_5 ),
    inference(subsumption_resolution,[],[f20189,f20182])).

fof(f20189,plain,
    ( r1_lattice3(sK125,k3_xboole_0(sK126,u1_struct_0(sK125)),sK440(sK125,sK126,k3_xboole_0(sK126,u1_struct_0(sK125))))
    | r1_lattice3(sK125,sK126,sK440(sK125,sK126,k3_xboole_0(sK126,u1_struct_0(sK125))))
    | ~ r2_yellow_0(sK125,sK126)
    | ~ l1_orders_2(sK125)
    | v2_struct_0(sK125) ),
    inference(resolution,[],[f17719,f18315])).

fof(f18315,plain,(
    ! [X2,X0,X1] :
      ( sQ1237_eqProxy(k2_yellow_0(X0,X1),k2_yellow_0(X0,X2))
      | r1_lattice3(X0,X2,sK440(X0,X1,X2))
      | r1_lattice3(X0,X1,sK440(X0,X1,X2))
      | ~ r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_proxy_replacement,[],[f12450,f17685])).

fof(f12450,plain,(
    ! [X2,X0,X1] :
      ( k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2)
      | r1_lattice3(X0,X2,sK440(X0,X1,X2))
      | r1_lattice3(X0,X1,sK440(X0,X1,X2))
      | ~ r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f8351])).

fof(f20187,plain,
    ( spl1238_5
    | spl1238_6 ),
    inference(avatar_split_clause,[],[f10396,f20184,f20180])).

fof(f10396,plain,
    ( r2_yellow_0(sK125,k3_xboole_0(sK126,u1_struct_0(sK125)))
    | r2_yellow_0(sK125,sK126) ),
    inference(cnf_transformation,[],[f7423])).
%------------------------------------------------------------------------------
