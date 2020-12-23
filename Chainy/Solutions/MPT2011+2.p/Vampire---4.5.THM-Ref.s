%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT2011+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:39 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 592 expanded)
%              Number of leaves         :   18 ( 238 expanded)
%              Depth                    :   14
%              Number of atoms          :  456 (6352 expanded)
%              Number of equality atoms :   61 (  65 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6550,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f5468,f6531,f6545,f6547,f6549])).

fof(f6549,plain,(
    ~ spl129_1 ),
    inference(avatar_contradiction_clause,[],[f6548])).

fof(f6548,plain,
    ( $false
    | ~ spl129_1 ),
    inference(subsumption_resolution,[],[f5455,f5487])).

fof(f5487,plain,(
    ~ v2_struct_0(k3_waybel_2(sK20,sK21,sK22)) ),
    inference(unit_resulting_resolution,[],[f4923,f4924,f4926,f4929,f4925,f4933])).

fof(f4933,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k3_waybel_2(X0,X1,X2))
      | ~ l1_waybel_0(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4387])).

fof(f4387,plain,(
    ! [X0,X1,X2] :
      ( ( v6_waybel_0(k3_waybel_2(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_waybel_2(X0,X1,X2)) )
      | ~ l1_waybel_0(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f4386])).

fof(f4386,plain,(
    ! [X0,X1,X2] :
      ( ( v6_waybel_0(k3_waybel_2(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_waybel_2(X0,X1,X2)) )
      | ~ l1_waybel_0(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4344])).

fof(f4344,axiom,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( v6_waybel_0(k3_waybel_2(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_waybel_2(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_waybel_2)).

fof(f4925,plain,(
    m1_subset_1(sK21,u1_struct_0(sK20)) ),
    inference(cnf_transformation,[],[f4655])).

fof(f4655,plain,
    ( ( ~ l1_waybel_0(k3_waybel_2(sK20,sK21,sK22),sK20)
      | ~ v7_waybel_0(k3_waybel_2(sK20,sK21,sK22))
      | ~ v4_orders_2(k3_waybel_2(sK20,sK21,sK22))
      | v2_struct_0(k3_waybel_2(sK20,sK21,sK22)) )
    & l1_waybel_0(sK22,sK20)
    & v7_waybel_0(sK22)
    & v4_orders_2(sK22)
    & ~ v2_struct_0(sK22)
    & m1_subset_1(sK21,u1_struct_0(sK20))
    & l1_orders_2(sK20)
    & ~ v2_struct_0(sK20) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK20,sK21,sK22])],[f4383,f4654,f4653,f4652])).

fof(f4652,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ l1_waybel_0(k3_waybel_2(X0,X1,X2),X0)
                  | ~ v7_waybel_0(k3_waybel_2(X0,X1,X2))
                  | ~ v4_orders_2(k3_waybel_2(X0,X1,X2))
                  | v2_struct_0(k3_waybel_2(X0,X1,X2)) )
                & l1_waybel_0(X2,X0)
                & v7_waybel_0(X2)
                & v4_orders_2(X2)
                & ~ v2_struct_0(X2) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ l1_waybel_0(k3_waybel_2(sK20,X1,X2),sK20)
                | ~ v7_waybel_0(k3_waybel_2(sK20,X1,X2))
                | ~ v4_orders_2(k3_waybel_2(sK20,X1,X2))
                | v2_struct_0(k3_waybel_2(sK20,X1,X2)) )
              & l1_waybel_0(X2,sK20)
              & v7_waybel_0(X2)
              & v4_orders_2(X2)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,u1_struct_0(sK20)) )
      & l1_orders_2(sK20)
      & ~ v2_struct_0(sK20) ) ),
    introduced(choice_axiom,[])).

fof(f4653,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ l1_waybel_0(k3_waybel_2(sK20,X1,X2),sK20)
              | ~ v7_waybel_0(k3_waybel_2(sK20,X1,X2))
              | ~ v4_orders_2(k3_waybel_2(sK20,X1,X2))
              | v2_struct_0(k3_waybel_2(sK20,X1,X2)) )
            & l1_waybel_0(X2,sK20)
            & v7_waybel_0(X2)
            & v4_orders_2(X2)
            & ~ v2_struct_0(X2) )
        & m1_subset_1(X1,u1_struct_0(sK20)) )
   => ( ? [X2] :
          ( ( ~ l1_waybel_0(k3_waybel_2(sK20,sK21,X2),sK20)
            | ~ v7_waybel_0(k3_waybel_2(sK20,sK21,X2))
            | ~ v4_orders_2(k3_waybel_2(sK20,sK21,X2))
            | v2_struct_0(k3_waybel_2(sK20,sK21,X2)) )
          & l1_waybel_0(X2,sK20)
          & v7_waybel_0(X2)
          & v4_orders_2(X2)
          & ~ v2_struct_0(X2) )
      & m1_subset_1(sK21,u1_struct_0(sK20)) ) ),
    introduced(choice_axiom,[])).

fof(f4654,plain,
    ( ? [X2] :
        ( ( ~ l1_waybel_0(k3_waybel_2(sK20,sK21,X2),sK20)
          | ~ v7_waybel_0(k3_waybel_2(sK20,sK21,X2))
          | ~ v4_orders_2(k3_waybel_2(sK20,sK21,X2))
          | v2_struct_0(k3_waybel_2(sK20,sK21,X2)) )
        & l1_waybel_0(X2,sK20)
        & v7_waybel_0(X2)
        & v4_orders_2(X2)
        & ~ v2_struct_0(X2) )
   => ( ( ~ l1_waybel_0(k3_waybel_2(sK20,sK21,sK22),sK20)
        | ~ v7_waybel_0(k3_waybel_2(sK20,sK21,sK22))
        | ~ v4_orders_2(k3_waybel_2(sK20,sK21,sK22))
        | v2_struct_0(k3_waybel_2(sK20,sK21,sK22)) )
      & l1_waybel_0(sK22,sK20)
      & v7_waybel_0(sK22)
      & v4_orders_2(sK22)
      & ~ v2_struct_0(sK22) ) ),
    introduced(choice_axiom,[])).

fof(f4383,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ l1_waybel_0(k3_waybel_2(X0,X1,X2),X0)
                | ~ v7_waybel_0(k3_waybel_2(X0,X1,X2))
                | ~ v4_orders_2(k3_waybel_2(X0,X1,X2))
                | v2_struct_0(k3_waybel_2(X0,X1,X2)) )
              & l1_waybel_0(X2,X0)
              & v7_waybel_0(X2)
              & v4_orders_2(X2)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f4382])).

fof(f4382,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ l1_waybel_0(k3_waybel_2(X0,X1,X2),X0)
                | ~ v7_waybel_0(k3_waybel_2(X0,X1,X2))
                | ~ v4_orders_2(k3_waybel_2(X0,X1,X2))
                | v2_struct_0(k3_waybel_2(X0,X1,X2)) )
              & l1_waybel_0(X2,X0)
              & v7_waybel_0(X2)
              & v4_orders_2(X2)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4357])).

fof(f4357,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( ( l1_waybel_0(X2,X0)
                  & v7_waybel_0(X2)
                  & v4_orders_2(X2)
                  & ~ v2_struct_0(X2) )
               => ( l1_waybel_0(k3_waybel_2(X0,X1,X2),X0)
                  & v7_waybel_0(k3_waybel_2(X0,X1,X2))
                  & v4_orders_2(k3_waybel_2(X0,X1,X2))
                  & ~ v2_struct_0(k3_waybel_2(X0,X1,X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f4356])).

fof(f4356,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( l1_waybel_0(X2,X0)
                & v7_waybel_0(X2)
                & v4_orders_2(X2)
                & ~ v2_struct_0(X2) )
             => ( l1_waybel_0(k3_waybel_2(X0,X1,X2),X0)
                & v7_waybel_0(k3_waybel_2(X0,X1,X2))
                & v4_orders_2(k3_waybel_2(X0,X1,X2))
                & ~ v2_struct_0(k3_waybel_2(X0,X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_waybel_9)).

fof(f4929,plain,(
    l1_waybel_0(sK22,sK20) ),
    inference(cnf_transformation,[],[f4655])).

fof(f4926,plain,(
    ~ v2_struct_0(sK22) ),
    inference(cnf_transformation,[],[f4655])).

fof(f4924,plain,(
    l1_orders_2(sK20) ),
    inference(cnf_transformation,[],[f4655])).

fof(f4923,plain,(
    ~ v2_struct_0(sK20) ),
    inference(cnf_transformation,[],[f4655])).

fof(f5455,plain,
    ( v2_struct_0(k3_waybel_2(sK20,sK21,sK22))
    | ~ spl129_1 ),
    inference(avatar_component_clause,[],[f5453])).

fof(f5453,plain,
    ( spl129_1
  <=> v2_struct_0(k3_waybel_2(sK20,sK21,sK22)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl129_1])])).

fof(f6547,plain,(
    spl129_4 ),
    inference(avatar_contradiction_clause,[],[f6546])).

fof(f6546,plain,
    ( $false
    | spl129_4 ),
    inference(subsumption_resolution,[],[f5467,f5486])).

fof(f5486,plain,(
    l1_waybel_0(k3_waybel_2(sK20,sK21,sK22),sK20) ),
    inference(unit_resulting_resolution,[],[f4923,f4924,f4926,f4929,f4925,f4932])).

fof(f4932,plain,(
    ! [X2,X0,X1] :
      ( l1_waybel_0(k3_waybel_2(X0,X1,X2),X0)
      | ~ l1_waybel_0(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4385])).

fof(f4385,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k3_waybel_2(X0,X1,X2),X0)
        & v6_waybel_0(k3_waybel_2(X0,X1,X2),X0) )
      | ~ l1_waybel_0(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f4384])).

fof(f4384,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k3_waybel_2(X0,X1,X2),X0)
        & v6_waybel_0(k3_waybel_2(X0,X1,X2),X0) )
      | ~ l1_waybel_0(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4328])).

fof(f4328,axiom,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_waybel_0(k3_waybel_2(X0,X1,X2),X0)
        & v6_waybel_0(k3_waybel_2(X0,X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_waybel_2)).

fof(f5467,plain,
    ( ~ l1_waybel_0(k3_waybel_2(sK20,sK21,sK22),sK20)
    | spl129_4 ),
    inference(avatar_component_clause,[],[f5465])).

fof(f5465,plain,
    ( spl129_4
  <=> l1_waybel_0(k3_waybel_2(sK20,sK21,sK22),sK20) ),
    introduced(avatar_definition,[new_symbols(naming,[spl129_4])])).

fof(f6545,plain,(
    spl129_3 ),
    inference(avatar_contradiction_clause,[],[f6544])).

fof(f6544,plain,
    ( $false
    | spl129_3 ),
    inference(subsumption_resolution,[],[f5463,f5490])).

fof(f5490,plain,(
    v7_waybel_0(k3_waybel_2(sK20,sK21,sK22)) ),
    inference(unit_resulting_resolution,[],[f4923,f4924,f4928,f4926,f4929,f4925,f4936])).

fof(f4936,plain,(
    ! [X2,X0,X1] :
      ( v7_waybel_0(k3_waybel_2(X0,X1,X2))
      | ~ l1_waybel_0(X2,X0)
      | ~ v7_waybel_0(X2)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4389])).

fof(f4389,plain,(
    ! [X0,X1,X2] :
      ( ( v7_waybel_0(k3_waybel_2(X0,X1,X2))
        & v6_waybel_0(k3_waybel_2(X0,X1,X2),X0) )
      | ~ l1_waybel_0(X2,X0)
      | ~ v7_waybel_0(X2)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f4388])).

fof(f4388,plain,(
    ! [X0,X1,X2] :
      ( ( v7_waybel_0(k3_waybel_2(X0,X1,X2))
        & v6_waybel_0(k3_waybel_2(X0,X1,X2),X0) )
      | ~ l1_waybel_0(X2,X0)
      | ~ v7_waybel_0(X2)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4346])).

fof(f4346,axiom,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(X2,X0)
        & v7_waybel_0(X2)
        & ~ v2_struct_0(X2)
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_waybel_0(k3_waybel_2(X0,X1,X2))
        & v6_waybel_0(k3_waybel_2(X0,X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_waybel_2)).

fof(f4928,plain,(
    v7_waybel_0(sK22) ),
    inference(cnf_transformation,[],[f4655])).

fof(f5463,plain,
    ( ~ v7_waybel_0(k3_waybel_2(sK20,sK21,sK22))
    | spl129_3 ),
    inference(avatar_component_clause,[],[f5461])).

fof(f5461,plain,
    ( spl129_3
  <=> v7_waybel_0(k3_waybel_2(sK20,sK21,sK22)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl129_3])])).

fof(f6531,plain,(
    spl129_2 ),
    inference(avatar_contradiction_clause,[],[f6530])).

fof(f6530,plain,
    ( $false
    | spl129_2 ),
    inference(subsumption_resolution,[],[f6529,f5582])).

fof(f5582,plain,(
    v4_orders_2(k7_lattice3(k7_lattice3(sK22))) ),
    inference(forward_demodulation,[],[f5566,f5568])).

fof(f5568,plain,(
    g1_orders_2(u1_struct_0(sK22),u1_orders_2(sK22)) = k7_lattice3(k7_lattice3(sK22)) ),
    inference(unit_resulting_resolution,[],[f5498,f5249])).

fof(f5249,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = k7_lattice3(k7_lattice3(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f4553])).

fof(f4553,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = k7_lattice3(k7_lattice3(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2961])).

fof(f2961,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = k7_lattice3(k7_lattice3(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_lattice3)).

fof(f5498,plain,(
    l1_orders_2(sK22) ),
    inference(unit_resulting_resolution,[],[f4929,f5472,f4946])).

fof(f4946,plain,(
    ! [X0,X1] :
      ( l1_orders_2(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4395])).

fof(f4395,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_orders_2(X1)
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3197])).

fof(f3197,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_waybel_0)).

fof(f5472,plain,(
    l1_struct_0(sK20) ),
    inference(unit_resulting_resolution,[],[f4924,f5263])).

fof(f5263,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f4566])).

fof(f4566,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1895])).

fof(f1895,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f5566,plain,(
    v4_orders_2(g1_orders_2(u1_struct_0(sK22),u1_orders_2(sK22))) ),
    inference(unit_resulting_resolution,[],[f4926,f4927,f5498,f5229])).

fof(f5229,plain,(
    ! [X0] :
      ( v4_orders_2(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)))
      | ~ v4_orders_2(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4827])).

fof(f4827,plain,(
    ! [X0] :
      ( ( ( v4_orders_2(X0)
          | ~ v4_orders_2(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))) )
        & ( v4_orders_2(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)))
          | ~ v4_orders_2(X0) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f4526])).

fof(f4526,plain,(
    ! [X0] :
      ( ( v4_orders_2(X0)
      <=> v4_orders_2(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f4525])).

fof(f4525,plain,(
    ! [X0] :
      ( ( v4_orders_2(X0)
      <=> v4_orders_2(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3984])).

fof(f3984,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( v4_orders_2(X0)
      <=> v4_orders_2(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l16_yellow_6)).

fof(f4927,plain,(
    v4_orders_2(sK22) ),
    inference(cnf_transformation,[],[f4655])).

fof(f6529,plain,
    ( ~ v4_orders_2(k7_lattice3(k7_lattice3(sK22)))
    | spl129_2 ),
    inference(forward_demodulation,[],[f6510,f5642])).

fof(f5642,plain,(
    g1_orders_2(u1_struct_0(k3_waybel_2(sK20,sK21,sK22)),u1_orders_2(k3_waybel_2(sK20,sK21,sK22))) = k7_lattice3(k7_lattice3(sK22)) ),
    inference(forward_demodulation,[],[f5634,f5568])).

fof(f5634,plain,(
    g1_orders_2(u1_struct_0(sK22),u1_orders_2(sK22)) = g1_orders_2(u1_struct_0(k3_waybel_2(sK20,sK21,sK22)),u1_orders_2(k3_waybel_2(sK20,sK21,sK22))) ),
    inference(unit_resulting_resolution,[],[f4923,f4924,f4926,f4929,f4925,f5486,f5489,f5407])).

fof(f5407,plain,(
    ! [X2,X0,X1] :
      ( g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) = g1_orders_2(u1_struct_0(k3_waybel_2(X0,X1,X2)),u1_orders_2(k3_waybel_2(X0,X1,X2)))
      | ~ l1_waybel_0(k3_waybel_2(X0,X1,X2),X0)
      | ~ v6_waybel_0(k3_waybel_2(X0,X1,X2),X0)
      | ~ l1_waybel_0(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f4939])).

fof(f4939,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
      | k3_waybel_2(X0,X1,X2) != X3
      | ~ l1_waybel_0(X3,X0)
      | ~ v6_waybel_0(X3,X0)
      | ~ l1_waybel_0(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4662])).

fof(f4662,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k3_waybel_2(X0,X1,X2) = X3
                      | ( ! [X5] :
                            ( k11_lattice3(X0,X1,X5) != k1_funct_1(u1_waybel_0(X0,X3),sK23(X0,X1,X2,X3))
                            | k1_funct_1(u1_waybel_0(X0,X2),sK23(X0,X1,X2,X3)) != X5
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & m1_subset_1(sK23(X0,X1,X2,X3),u1_struct_0(X3)) )
                      | g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) != g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) )
                    & ( ( ! [X6] :
                            ( ( k1_funct_1(u1_waybel_0(X0,X3),X6) = k11_lattice3(X0,X1,sK24(X0,X1,X2,X3,X6))
                              & k1_funct_1(u1_waybel_0(X0,X2),X6) = sK24(X0,X1,X2,X3,X6)
                              & m1_subset_1(sK24(X0,X1,X2,X3,X6),u1_struct_0(X0)) )
                            | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                        & g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) )
                      | k3_waybel_2(X0,X1,X2) != X3 ) )
                  | ~ l1_waybel_0(X3,X0)
                  | ~ v6_waybel_0(X3,X0) )
              | ~ l1_waybel_0(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK23,sK24])],[f4659,f4661,f4660])).

fof(f4660,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(u1_waybel_0(X0,X3),X4) != k11_lattice3(X0,X1,X5)
              | k1_funct_1(u1_waybel_0(X0,X2),X4) != X5
              | ~ m1_subset_1(X5,u1_struct_0(X0)) )
          & m1_subset_1(X4,u1_struct_0(X3)) )
     => ( ! [X5] :
            ( k11_lattice3(X0,X1,X5) != k1_funct_1(u1_waybel_0(X0,X3),sK23(X0,X1,X2,X3))
            | k1_funct_1(u1_waybel_0(X0,X2),sK23(X0,X1,X2,X3)) != X5
            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
        & m1_subset_1(sK23(X0,X1,X2,X3),u1_struct_0(X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f4661,plain,(
    ! [X6,X3,X2,X1,X0] :
      ( ? [X7] :
          ( k1_funct_1(u1_waybel_0(X0,X3),X6) = k11_lattice3(X0,X1,X7)
          & k1_funct_1(u1_waybel_0(X0,X2),X6) = X7
          & m1_subset_1(X7,u1_struct_0(X0)) )
     => ( k1_funct_1(u1_waybel_0(X0,X3),X6) = k11_lattice3(X0,X1,sK24(X0,X1,X2,X3,X6))
        & k1_funct_1(u1_waybel_0(X0,X2),X6) = sK24(X0,X1,X2,X3,X6)
        & m1_subset_1(sK24(X0,X1,X2,X3,X6),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f4659,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k3_waybel_2(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ! [X5] :
                              ( k1_funct_1(u1_waybel_0(X0,X3),X4) != k11_lattice3(X0,X1,X5)
                              | k1_funct_1(u1_waybel_0(X0,X2),X4) != X5
                              | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                          & m1_subset_1(X4,u1_struct_0(X3)) )
                      | g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) != g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) )
                    & ( ( ! [X6] :
                            ( ? [X7] :
                                ( k1_funct_1(u1_waybel_0(X0,X3),X6) = k11_lattice3(X0,X1,X7)
                                & k1_funct_1(u1_waybel_0(X0,X2),X6) = X7
                                & m1_subset_1(X7,u1_struct_0(X0)) )
                            | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                        & g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) )
                      | k3_waybel_2(X0,X1,X2) != X3 ) )
                  | ~ l1_waybel_0(X3,X0)
                  | ~ v6_waybel_0(X3,X0) )
              | ~ l1_waybel_0(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f4658])).

fof(f4658,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k3_waybel_2(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ! [X5] :
                              ( k1_funct_1(u1_waybel_0(X0,X3),X4) != k11_lattice3(X0,X1,X5)
                              | k1_funct_1(u1_waybel_0(X0,X2),X4) != X5
                              | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                          & m1_subset_1(X4,u1_struct_0(X3)) )
                      | g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) != g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) )
                    & ( ( ! [X4] :
                            ( ? [X5] :
                                ( k1_funct_1(u1_waybel_0(X0,X3),X4) = k11_lattice3(X0,X1,X5)
                                & k1_funct_1(u1_waybel_0(X0,X2),X4) = X5
                                & m1_subset_1(X5,u1_struct_0(X0)) )
                            | ~ m1_subset_1(X4,u1_struct_0(X3)) )
                        & g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) )
                      | k3_waybel_2(X0,X1,X2) != X3 ) )
                  | ~ l1_waybel_0(X3,X0)
                  | ~ v6_waybel_0(X3,X0) )
              | ~ l1_waybel_0(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f4657])).

fof(f4657,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k3_waybel_2(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ! [X5] :
                              ( k1_funct_1(u1_waybel_0(X0,X3),X4) != k11_lattice3(X0,X1,X5)
                              | k1_funct_1(u1_waybel_0(X0,X2),X4) != X5
                              | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                          & m1_subset_1(X4,u1_struct_0(X3)) )
                      | g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) != g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) )
                    & ( ( ! [X4] :
                            ( ? [X5] :
                                ( k1_funct_1(u1_waybel_0(X0,X3),X4) = k11_lattice3(X0,X1,X5)
                                & k1_funct_1(u1_waybel_0(X0,X2),X4) = X5
                                & m1_subset_1(X5,u1_struct_0(X0)) )
                            | ~ m1_subset_1(X4,u1_struct_0(X3)) )
                        & g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) )
                      | k3_waybel_2(X0,X1,X2) != X3 ) )
                  | ~ l1_waybel_0(X3,X0)
                  | ~ v6_waybel_0(X3,X0) )
              | ~ l1_waybel_0(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f4393])).

fof(f4393,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k3_waybel_2(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( ? [X5] :
                              ( k1_funct_1(u1_waybel_0(X0,X3),X4) = k11_lattice3(X0,X1,X5)
                              & k1_funct_1(u1_waybel_0(X0,X2),X4) = X5
                              & m1_subset_1(X5,u1_struct_0(X0)) )
                          | ~ m1_subset_1(X4,u1_struct_0(X3)) )
                      & g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) ) )
                  | ~ l1_waybel_0(X3,X0)
                  | ~ v6_waybel_0(X3,X0) )
              | ~ l1_waybel_0(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f4392])).

fof(f4392,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k3_waybel_2(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( ? [X5] :
                              ( k1_funct_1(u1_waybel_0(X0,X3),X4) = k11_lattice3(X0,X1,X5)
                              & k1_funct_1(u1_waybel_0(X0,X2),X4) = X5
                              & m1_subset_1(X5,u1_struct_0(X0)) )
                          | ~ m1_subset_1(X4,u1_struct_0(X3)) )
                      & g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) ) )
                  | ~ l1_waybel_0(X3,X0)
                  | ~ v6_waybel_0(X3,X0) )
              | ~ l1_waybel_0(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4320])).

fof(f4320,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( l1_waybel_0(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( l1_waybel_0(X3,X0)
                    & v6_waybel_0(X3,X0) )
                 => ( k3_waybel_2(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X3))
                         => ? [X5] :
                              ( k1_funct_1(u1_waybel_0(X0,X3),X4) = k11_lattice3(X0,X1,X5)
                              & k1_funct_1(u1_waybel_0(X0,X2),X4) = X5
                              & m1_subset_1(X5,u1_struct_0(X0)) ) )
                      & g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_waybel_2)).

fof(f5489,plain,(
    v6_waybel_0(k3_waybel_2(sK20,sK21,sK22),sK20) ),
    inference(unit_resulting_resolution,[],[f4923,f4924,f4928,f4926,f4929,f4925,f4935])).

fof(f4935,plain,(
    ! [X2,X0,X1] :
      ( v6_waybel_0(k3_waybel_2(X0,X1,X2),X0)
      | ~ l1_waybel_0(X2,X0)
      | ~ v7_waybel_0(X2)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4389])).

fof(f6510,plain,
    ( ~ v4_orders_2(g1_orders_2(u1_struct_0(k3_waybel_2(sK20,sK21,sK22)),u1_orders_2(k3_waybel_2(sK20,sK21,sK22))))
    | spl129_2 ),
    inference(unit_resulting_resolution,[],[f5487,f5459,f5623,f5230])).

fof(f5230,plain,(
    ! [X0] :
      ( v4_orders_2(X0)
      | ~ v4_orders_2(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4827])).

fof(f5623,plain,(
    l1_orders_2(k3_waybel_2(sK20,sK21,sK22)) ),
    inference(unit_resulting_resolution,[],[f5472,f5486,f4946])).

fof(f5459,plain,
    ( ~ v4_orders_2(k3_waybel_2(sK20,sK21,sK22))
    | spl129_2 ),
    inference(avatar_component_clause,[],[f5457])).

fof(f5457,plain,
    ( spl129_2
  <=> v4_orders_2(k3_waybel_2(sK20,sK21,sK22)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl129_2])])).

fof(f5468,plain,
    ( spl129_1
    | ~ spl129_2
    | ~ spl129_3
    | ~ spl129_4 ),
    inference(avatar_split_clause,[],[f4930,f5465,f5461,f5457,f5453])).

fof(f4930,plain,
    ( ~ l1_waybel_0(k3_waybel_2(sK20,sK21,sK22),sK20)
    | ~ v7_waybel_0(k3_waybel_2(sK20,sK21,sK22))
    | ~ v4_orders_2(k3_waybel_2(sK20,sK21,sK22))
    | v2_struct_0(k3_waybel_2(sK20,sK21,sK22)) ),
    inference(cnf_transformation,[],[f4655])).
%------------------------------------------------------------------------------
