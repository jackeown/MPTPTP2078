%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : yellow_0__t13_yellow_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:36 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 303 expanded)
%              Number of leaves         :   22 ( 102 expanded)
%              Depth                    :   20
%              Number of atoms          :  474 (1760 expanded)
%              Number of equality atoms :   43 ( 235 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f546,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f85,f92,f99,f100,f122,f129,f189,f422,f526,f540,f545])).

fof(f545,plain,
    ( ~ spl6_22
    | ~ spl6_50
    | ~ spl6_52 ),
    inference(avatar_contradiction_clause,[],[f544])).

fof(f544,plain,
    ( $false
    | ~ spl6_22
    | ~ spl6_50
    | ~ spl6_52 ),
    inference(subsumption_resolution,[],[f542,f418])).

fof(f418,plain,
    ( m1_subset_1(sK3(sK0),u1_struct_0(sK0))
    | ~ spl6_52 ),
    inference(avatar_component_clause,[],[f417])).

fof(f417,plain,
    ( spl6_52
  <=> m1_subset_1(sK3(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_52])])).

fof(f542,plain,
    ( ~ m1_subset_1(sK3(sK0),u1_struct_0(sK0))
    | ~ spl6_22
    | ~ spl6_50 ),
    inference(resolution,[],[f415,f188])).

fof(f188,plain,
    ( ! [X1] :
        ( ~ r2_lattice3(sK1,u1_struct_0(sK0),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f187])).

fof(f187,plain,
    ( spl6_22
  <=> ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_lattice3(sK1,u1_struct_0(sK0),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f415,plain,
    ( r2_lattice3(sK1,u1_struct_0(sK0),sK3(sK0))
    | ~ spl6_50 ),
    inference(avatar_component_clause,[],[f414])).

fof(f414,plain,
    ( spl6_50
  <=> r2_lattice3(sK1,u1_struct_0(sK0),sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_50])])).

fof(f540,plain,
    ( ~ spl6_6
    | spl6_53 ),
    inference(avatar_contradiction_clause,[],[f539])).

fof(f539,plain,
    ( $false
    | ~ spl6_6
    | ~ spl6_53 ),
    inference(subsumption_resolution,[],[f538,f48])).

fof(f48,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ( ( ~ v2_yellow_0(sK1)
        & v2_yellow_0(sK0) )
      | ( ~ v1_yellow_0(sK1)
        & v1_yellow_0(sK0) ) )
    & g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
    & l1_orders_2(sK1)
    & l1_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f34,f33])).

fof(f33,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ( ~ v2_yellow_0(X1)
                & v2_yellow_0(X0) )
              | ( ~ v1_yellow_0(X1)
                & v1_yellow_0(X0) ) )
            & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
            & l1_orders_2(X1) )
        & l1_orders_2(X0) )
   => ( ? [X1] :
          ( ( ( ~ v2_yellow_0(X1)
              & v2_yellow_0(sK0) )
            | ( ~ v1_yellow_0(X1)
              & v1_yellow_0(sK0) ) )
          & g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
      & l1_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ( ~ v2_yellow_0(X1)
              & v2_yellow_0(X0) )
            | ( ~ v1_yellow_0(X1)
              & v1_yellow_0(X0) ) )
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
     => ( ( ( ~ v2_yellow_0(sK1)
            & v2_yellow_0(X0) )
          | ( ~ v1_yellow_0(sK1)
            & v1_yellow_0(X0) ) )
        & g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) = g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        & l1_orders_2(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( ~ v2_yellow_0(X1)
              & v2_yellow_0(X0) )
            | ( ~ v1_yellow_0(X1)
              & v1_yellow_0(X0) ) )
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
      & l1_orders_2(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( ~ v2_yellow_0(X1)
              & v2_yellow_0(X0) )
            | ( ~ v1_yellow_0(X1)
              & v1_yellow_0(X0) ) )
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( l1_orders_2(X1)
           => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
             => ( ( v2_yellow_0(X0)
                 => v2_yellow_0(X1) )
                & ( v1_yellow_0(X0)
                 => v1_yellow_0(X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
           => ( ( v2_yellow_0(X0)
               => v2_yellow_0(X1) )
              & ( v1_yellow_0(X0)
               => v1_yellow_0(X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t13_yellow_0.p',t13_yellow_0)).

fof(f538,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl6_6
    | ~ spl6_53 ),
    inference(subsumption_resolution,[],[f537,f98])).

fof(f98,plain,
    ( v2_yellow_0(sK0)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl6_6
  <=> v2_yellow_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f537,plain,
    ( ~ v2_yellow_0(sK0)
    | ~ l1_orders_2(sK0)
    | ~ spl6_53 ),
    inference(resolution,[],[f421,f60])).

fof(f60,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(X0),u1_struct_0(X0))
      | ~ v2_yellow_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ( ( v2_yellow_0(X0)
          | ! [X1] :
              ( ~ r2_lattice3(X0,u1_struct_0(X0),X1)
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ( r2_lattice3(X0,u1_struct_0(X0),sK3(X0))
            & m1_subset_1(sK3(X0),u1_struct_0(X0)) )
          | ~ v2_yellow_0(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f41,f42])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X2] :
          ( r2_lattice3(X0,u1_struct_0(X0),X2)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( r2_lattice3(X0,u1_struct_0(X0),sK3(X0))
        & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ( ( v2_yellow_0(X0)
          | ! [X1] :
              ( ~ r2_lattice3(X0,u1_struct_0(X0),X1)
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ? [X2] :
              ( r2_lattice3(X0,u1_struct_0(X0),X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ v2_yellow_0(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( ( v2_yellow_0(X0)
          | ! [X1] :
              ( ~ r2_lattice3(X0,u1_struct_0(X0),X1)
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ? [X1] :
              ( r2_lattice3(X0,u1_struct_0(X0),X1)
              & m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v2_yellow_0(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v2_yellow_0(X0)
      <=> ? [X1] :
            ( r2_lattice3(X0,u1_struct_0(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_yellow_0(X0)
      <=> ? [X1] :
            ( r2_lattice3(X0,u1_struct_0(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t13_yellow_0.p',d5_yellow_0)).

fof(f421,plain,
    ( ~ m1_subset_1(sK3(sK0),u1_struct_0(sK0))
    | ~ spl6_53 ),
    inference(avatar_component_clause,[],[f420])).

fof(f420,plain,
    ( spl6_53
  <=> ~ m1_subset_1(sK3(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_53])])).

fof(f526,plain,
    ( spl6_1
    | ~ spl6_4
    | ~ spl6_10 ),
    inference(avatar_contradiction_clause,[],[f525])).

fof(f525,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_4
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f524,f48])).

fof(f524,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl6_1
    | ~ spl6_4
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f523,f91])).

fof(f91,plain,
    ( v1_yellow_0(sK0)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl6_4
  <=> v1_yellow_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f523,plain,
    ( ~ v1_yellow_0(sK0)
    | ~ l1_orders_2(sK0)
    | ~ spl6_1
    | ~ spl6_4
    | ~ spl6_10 ),
    inference(resolution,[],[f522,f57])).

fof(f57,plain,(
    ! [X0] :
      ( m1_subset_1(sK2(X0),u1_struct_0(X0))
      | ~ v1_yellow_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( ( v1_yellow_0(X0)
          | ! [X1] :
              ( ~ r1_lattice3(X0,u1_struct_0(X0),X1)
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ( r1_lattice3(X0,u1_struct_0(X0),sK2(X0))
            & m1_subset_1(sK2(X0),u1_struct_0(X0)) )
          | ~ v1_yellow_0(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f37,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X2] :
          ( r1_lattice3(X0,u1_struct_0(X0),X2)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( r1_lattice3(X0,u1_struct_0(X0),sK2(X0))
        & m1_subset_1(sK2(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ( ( v1_yellow_0(X0)
          | ! [X1] :
              ( ~ r1_lattice3(X0,u1_struct_0(X0),X1)
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ? [X2] :
              ( r1_lattice3(X0,u1_struct_0(X0),X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ v1_yellow_0(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( ( v1_yellow_0(X0)
          | ! [X1] :
              ( ~ r1_lattice3(X0,u1_struct_0(X0),X1)
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ? [X1] :
              ( r1_lattice3(X0,u1_struct_0(X0),X1)
              & m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v1_yellow_0(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_yellow_0(X0)
      <=> ? [X1] :
            ( r1_lattice3(X0,u1_struct_0(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_yellow_0(X0)
      <=> ? [X1] :
            ( r1_lattice3(X0,u1_struct_0(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t13_yellow_0.p',d4_yellow_0)).

fof(f522,plain,
    ( ~ m1_subset_1(sK2(sK0),u1_struct_0(sK0))
    | ~ spl6_1
    | ~ spl6_4
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f521,f167])).

fof(f167,plain,
    ( ! [X0] :
        ( ~ r1_lattice3(sK1,u1_struct_0(sK0),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl6_1
    | ~ spl6_10 ),
    inference(forward_demodulation,[],[f166,f149])).

fof(f149,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK1)
    | ~ spl6_10 ),
    inference(equality_resolution,[],[f121])).

fof(f121,plain,
    ( ! [X14,X15] :
        ( g1_orders_2(X14,X15) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | u1_struct_0(sK1) = X14 )
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl6_10
  <=> ! [X15,X14] :
        ( g1_orders_2(X14,X15) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | u1_struct_0(sK1) = X14 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f166,plain,
    ( ! [X0] :
        ( ~ r1_lattice3(sK1,u1_struct_0(sK0),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) )
    | ~ spl6_1
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f165,f49])).

fof(f49,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f165,plain,
    ( ! [X0] :
        ( ~ r1_lattice3(sK1,u1_struct_0(sK0),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ l1_orders_2(sK1) )
    | ~ spl6_1
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f156,f78])).

fof(f78,plain,
    ( ~ v1_yellow_0(sK1)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl6_1
  <=> ~ v1_yellow_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f156,plain,
    ( ! [X0] :
        ( ~ r1_lattice3(sK1,u1_struct_0(sK0),X0)
        | v1_yellow_0(sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ l1_orders_2(sK1) )
    | ~ spl6_10 ),
    inference(superposition,[],[f59,f149])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r1_lattice3(X0,u1_struct_0(X0),X1)
      | v1_yellow_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f521,plain,
    ( ~ m1_subset_1(sK2(sK0),u1_struct_0(sK0))
    | r1_lattice3(sK1,u1_struct_0(sK0),sK2(sK0))
    | ~ spl6_4
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f520,f48])).

fof(f520,plain,
    ( ~ m1_subset_1(sK2(sK0),u1_struct_0(sK0))
    | r1_lattice3(sK1,u1_struct_0(sK0),sK2(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl6_4
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f519,f91])).

fof(f519,plain,
    ( ~ m1_subset_1(sK2(sK0),u1_struct_0(sK0))
    | r1_lattice3(sK1,u1_struct_0(sK0),sK2(sK0))
    | ~ v1_yellow_0(sK0)
    | ~ l1_orders_2(sK0)
    | ~ spl6_10 ),
    inference(resolution,[],[f472,f58])).

fof(f58,plain,(
    ! [X0] :
      ( r1_lattice3(X0,u1_struct_0(X0),sK2(X0))
      | ~ v1_yellow_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f472,plain,
    ( ! [X0,X1] :
        ( ~ r1_lattice3(sK0,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_lattice3(sK1,X1,X0) )
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f461,f48])).

fof(f461,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,X1,X0)
        | r1_lattice3(sK1,X1,X0)
        | ~ l1_orders_2(sK0) )
    | ~ spl6_10 ),
    inference(duplicate_literal_removal,[],[f460])).

fof(f460,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_lattice3(sK1,X1,X0)
        | ~ l1_orders_2(sK0) )
    | ~ spl6_10 ),
    inference(equality_resolution,[],[f381])).

fof(f381,plain,
    ( ! [X6,X8,X7] :
        ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X6),u1_orders_2(X6))
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | ~ r1_lattice3(X6,X7,X8)
        | ~ m1_subset_1(X8,u1_struct_0(X6))
        | r1_lattice3(sK1,X7,X8)
        | ~ l1_orders_2(X6) )
    | ~ spl6_10 ),
    inference(forward_demodulation,[],[f111,f149])).

fof(f111,plain,(
    ! [X6,X8,X7] :
      ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X6),u1_orders_2(X6))
      | ~ r1_lattice3(X6,X7,X8)
      | ~ m1_subset_1(X8,u1_struct_0(sK1))
      | ~ m1_subset_1(X8,u1_struct_0(X6))
      | r1_lattice3(sK1,X7,X8)
      | ~ l1_orders_2(X6) ) ),
    inference(subsumption_resolution,[],[f103,f49])).

fof(f103,plain,(
    ! [X6,X8,X7] :
      ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X6),u1_orders_2(X6))
      | ~ r1_lattice3(X6,X7,X8)
      | ~ m1_subset_1(X8,u1_struct_0(sK1))
      | ~ m1_subset_1(X8,u1_struct_0(X6))
      | r1_lattice3(sK1,X7,X8)
      | ~ l1_orders_2(sK1)
      | ~ l1_orders_2(X6) ) ),
    inference(superposition,[],[f71,f50])).

fof(f50,plain,(
    g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) ),
    inference(cnf_transformation,[],[f35])).

fof(f71,plain,(
    ! [X4,X2,X0,X1] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ r1_lattice3(X0,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | r1_lattice3(X1,X2,X4)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r1_lattice3(X1,X2,X4)
      | ~ r1_lattice3(X0,X2,X3)
      | X3 != X4
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2,X3] :
              ( ! [X4] :
                  ( ( ( r1_lattice3(X1,X2,X4)
                      | ~ r1_lattice3(X0,X2,X3) )
                    & ( r2_lattice3(X1,X2,X4)
                      | ~ r2_lattice3(X0,X2,X3) ) )
                  | X3 != X4
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2,X3] :
              ( ! [X4] :
                  ( ( ( r1_lattice3(X1,X2,X4)
                      | ~ r1_lattice3(X0,X2,X3) )
                    & ( r2_lattice3(X1,X2,X4)
                      | ~ r2_lattice3(X0,X2,X3) ) )
                  | X3 != X4
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
           => ! [X2,X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( X3 = X4
                     => ( ( r1_lattice3(X0,X2,X3)
                         => r1_lattice3(X1,X2,X4) )
                        & ( r2_lattice3(X0,X2,X3)
                         => r2_lattice3(X1,X2,X4) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t13_yellow_0.p',t2_yellow_0)).

fof(f422,plain,
    ( ~ spl6_7
    | spl6_50
    | ~ spl6_53
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f409,f120,f420,f414,f94])).

fof(f94,plain,
    ( spl6_7
  <=> ~ v2_yellow_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f409,plain,
    ( ~ m1_subset_1(sK3(sK0),u1_struct_0(sK0))
    | r2_lattice3(sK1,u1_struct_0(sK0),sK3(sK0))
    | ~ v2_yellow_0(sK0)
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f408,f48])).

fof(f408,plain,
    ( ~ m1_subset_1(sK3(sK0),u1_struct_0(sK0))
    | r2_lattice3(sK1,u1_struct_0(sK0),sK3(sK0))
    | ~ v2_yellow_0(sK0)
    | ~ l1_orders_2(sK0)
    | ~ spl6_10 ),
    inference(resolution,[],[f407,f61])).

fof(f61,plain,(
    ! [X0] :
      ( r2_lattice3(X0,u1_struct_0(X0),sK3(X0))
      | ~ v2_yellow_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f407,plain,
    ( ! [X0,X1] :
        ( ~ r2_lattice3(sK0,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_lattice3(sK1,X1,X0) )
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f396,f48])).

fof(f396,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X1,X0)
        | r2_lattice3(sK1,X1,X0)
        | ~ l1_orders_2(sK0) )
    | ~ spl6_10 ),
    inference(duplicate_literal_removal,[],[f395])).

fof(f395,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_lattice3(sK1,X1,X0)
        | ~ l1_orders_2(sK0) )
    | ~ spl6_10 ),
    inference(equality_resolution,[],[f359])).

fof(f359,plain,
    ( ! [X2,X0,X1] :
        ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_lattice3(X0,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | r2_lattice3(sK1,X1,X2)
        | ~ l1_orders_2(X0) )
    | ~ spl6_10 ),
    inference(forward_demodulation,[],[f109,f149])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_lattice3(sK1,X1,X2)
      | ~ l1_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f101,f49])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_lattice3(sK1,X1,X2)
      | ~ l1_orders_2(sK1)
      | ~ l1_orders_2(X0) ) ),
    inference(superposition,[],[f72,f50])).

fof(f72,plain,(
    ! [X4,X2,X0,X1] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ r2_lattice3(X0,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | r2_lattice3(X1,X2,X4)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_lattice3(X1,X2,X4)
      | ~ r2_lattice3(X0,X2,X3)
      | X3 != X4
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f189,plain,
    ( spl6_2
    | spl6_22
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f185,f120,f187,f80])).

fof(f80,plain,
    ( spl6_2
  <=> v2_yellow_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f185,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_lattice3(sK1,u1_struct_0(sK0),X1)
        | v2_yellow_0(sK1) )
    | ~ spl6_10 ),
    inference(forward_demodulation,[],[f184,f149])).

fof(f184,plain,
    ( ! [X1] :
        ( ~ r2_lattice3(sK1,u1_struct_0(sK0),X1)
        | v2_yellow_0(sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1)) )
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f159,f49])).

fof(f159,plain,
    ( ! [X1] :
        ( ~ r2_lattice3(sK1,u1_struct_0(sK0),X1)
        | v2_yellow_0(sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ l1_orders_2(sK1) )
    | ~ spl6_10 ),
    inference(superposition,[],[f62,f149])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r2_lattice3(X0,u1_struct_0(X0),X1)
      | v2_yellow_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f129,plain,(
    spl6_9 ),
    inference(avatar_contradiction_clause,[],[f128])).

fof(f128,plain,
    ( $false
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f127,f49])).

fof(f127,plain,
    ( ~ l1_orders_2(sK1)
    | ~ spl6_9 ),
    inference(resolution,[],[f118,f55])).

fof(f55,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t13_yellow_0.p',dt_u1_orders_2)).

fof(f118,plain,
    ( ~ m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl6_9
  <=> ~ m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f122,plain,
    ( ~ spl6_9
    | spl6_10 ),
    inference(avatar_split_clause,[],[f106,f120,f117])).

fof(f106,plain,(
    ! [X14,X15] :
      ( g1_orders_2(X14,X15) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
      | u1_struct_0(sK1) = X14
      | ~ m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) ) ),
    inference(superposition,[],[f68,f50])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X0 = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2,X3] :
          ( g1_orders_2(X0,X1) = g1_orders_2(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t13_yellow_0.p',free_g1_orders_2)).

fof(f100,plain,
    ( spl6_4
    | spl6_6 ),
    inference(avatar_split_clause,[],[f51,f97,f90])).

fof(f51,plain,
    ( v2_yellow_0(sK0)
    | v1_yellow_0(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f99,plain,
    ( ~ spl6_1
    | spl6_6 ),
    inference(avatar_split_clause,[],[f52,f97,f77])).

fof(f52,plain,
    ( v2_yellow_0(sK0)
    | ~ v1_yellow_0(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f92,plain,
    ( spl6_4
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f53,f83,f90])).

fof(f83,plain,
    ( spl6_3
  <=> ~ v2_yellow_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f53,plain,
    ( ~ v2_yellow_0(sK1)
    | v1_yellow_0(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f85,plain,
    ( ~ spl6_1
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f54,f83,f77])).

fof(f54,plain,
    ( ~ v2_yellow_0(sK1)
    | ~ v1_yellow_0(sK1) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
