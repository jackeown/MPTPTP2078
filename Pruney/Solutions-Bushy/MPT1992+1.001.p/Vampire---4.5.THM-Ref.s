%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1992+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:01 EST 2020

% Result     : Theorem 1.53s
% Output     : Refutation 1.53s
% Verified   : 
% Statistics : Number of formulae       :  294 ( 713 expanded)
%              Number of leaves         :   49 ( 217 expanded)
%              Depth                    :   20
%              Number of atoms          : 1410 (5837 expanded)
%              Number of equality atoms :   17 (  18 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f708,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f169,f221,f415,f439,f443,f468,f522,f528,f538,f605,f620,f658,f697,f707])).

fof(f707,plain,
    ( spl10_6
    | ~ spl10_21
    | spl10_22
    | ~ spl10_25 ),
    inference(avatar_contradiction_clause,[],[f706])).

fof(f706,plain,
    ( $false
    | spl10_6
    | ~ spl10_21
    | spl10_22
    | ~ spl10_25 ),
    inference(subsumption_resolution,[],[f705,f219])).

fof(f219,plain,
    ( ~ v2_struct_0(sK6)
    | spl10_6 ),
    inference(avatar_component_clause,[],[f218])).

fof(f218,plain,
    ( spl10_6
  <=> v2_struct_0(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f705,plain,
    ( v2_struct_0(sK6)
    | ~ spl10_21
    | spl10_22
    | ~ spl10_25 ),
    inference(subsumption_resolution,[],[f704,f108])).

fof(f108,plain,(
    v3_orders_2(sK6) ),
    inference(cnf_transformation,[],[f88])).

fof(f88,plain,
    ( ( r2_subset_1(k4_waybel_0(sK6,k12_waybel_0(sK6,k3_subset_1(u1_struct_0(sK6),k5_waybel_0(sK6,k4_yellow_0(sK6))))),k1_waybel_3(sK6,k4_yellow_0(sK6)))
      | sP0(sK6) )
    & v1_waybel_3(k4_yellow_0(sK6),sK6)
    & l1_orders_2(sK6)
    & v3_waybel_3(sK6)
    & v2_lattice3(sK6)
    & v1_lattice3(sK6)
    & v5_orders_2(sK6)
    & v4_orders_2(sK6)
    & v3_orders_2(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f76,f87])).

fof(f87,plain,
    ( ? [X0] :
        ( ( r2_subset_1(k4_waybel_0(X0,k12_waybel_0(X0,k3_subset_1(u1_struct_0(X0),k5_waybel_0(X0,k4_yellow_0(X0))))),k1_waybel_3(X0,k4_yellow_0(X0)))
          | sP0(X0) )
        & v1_waybel_3(k4_yellow_0(X0),X0)
        & l1_orders_2(X0)
        & v3_waybel_3(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
   => ( ( r2_subset_1(k4_waybel_0(sK6,k12_waybel_0(sK6,k3_subset_1(u1_struct_0(sK6),k5_waybel_0(sK6,k4_yellow_0(sK6))))),k1_waybel_3(sK6,k4_yellow_0(sK6)))
        | sP0(sK6) )
      & v1_waybel_3(k4_yellow_0(sK6),sK6)
      & l1_orders_2(sK6)
      & v3_waybel_3(sK6)
      & v2_lattice3(sK6)
      & v1_lattice3(sK6)
      & v5_orders_2(sK6)
      & v4_orders_2(sK6)
      & v3_orders_2(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f76,plain,(
    ? [X0] :
      ( ( r2_subset_1(k4_waybel_0(X0,k12_waybel_0(X0,k3_subset_1(u1_struct_0(X0),k5_waybel_0(X0,k4_yellow_0(X0))))),k1_waybel_3(X0,k4_yellow_0(X0)))
        | sP0(X0) )
      & v1_waybel_3(k4_yellow_0(X0),X0)
      & l1_orders_2(X0)
      & v3_waybel_3(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(definition_folding,[],[f30,f75])).

fof(f75,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ~ r3_orders_2(X0,X2,k4_yellow_0(X0))
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & r1_waybel_3(X0,k2_yellow_0(X0,X1),k4_yellow_0(X0))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_finset_1(X1)
          & ~ v1_xboole_0(X1) )
      | ~ sP0(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f30,plain,(
    ? [X0] :
      ( ( r2_subset_1(k4_waybel_0(X0,k12_waybel_0(X0,k3_subset_1(u1_struct_0(X0),k5_waybel_0(X0,k4_yellow_0(X0))))),k1_waybel_3(X0,k4_yellow_0(X0)))
        | ? [X1] :
            ( ! [X2] :
                ( ~ r3_orders_2(X0,X2,k4_yellow_0(X0))
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & r1_waybel_3(X0,k2_yellow_0(X0,X1),k4_yellow_0(X0))
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_finset_1(X1)
            & ~ v1_xboole_0(X1) ) )
      & v1_waybel_3(k4_yellow_0(X0),X0)
      & l1_orders_2(X0)
      & v3_waybel_3(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ? [X0] :
      ( ( r2_subset_1(k4_waybel_0(X0,k12_waybel_0(X0,k3_subset_1(u1_struct_0(X0),k5_waybel_0(X0,k4_yellow_0(X0))))),k1_waybel_3(X0,k4_yellow_0(X0)))
        | ? [X1] :
            ( ! [X2] :
                ( ~ r3_orders_2(X0,X2,k4_yellow_0(X0))
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & r1_waybel_3(X0,k2_yellow_0(X0,X1),k4_yellow_0(X0))
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_finset_1(X1)
            & ~ v1_xboole_0(X1) ) )
      & v1_waybel_3(k4_yellow_0(X0),X0)
      & l1_orders_2(X0)
      & v3_waybel_3(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v3_waybel_3(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0) )
       => ( v1_waybel_3(k4_yellow_0(X0),X0)
         => ( ~ r2_subset_1(k4_waybel_0(X0,k12_waybel_0(X0,k3_subset_1(u1_struct_0(X0),k5_waybel_0(X0,k4_yellow_0(X0))))),k1_waybel_3(X0,k4_yellow_0(X0)))
            & ! [X1] :
                ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
                  & v1_finset_1(X1)
                  & ~ v1_xboole_0(X1) )
               => ~ ( ! [X2] :
                        ( m1_subset_1(X2,u1_struct_0(X0))
                       => ~ ( r3_orders_2(X0,X2,k4_yellow_0(X0))
                            & r2_hidden(X2,X1) ) )
                    & r1_waybel_3(X0,k2_yellow_0(X0,X1),k4_yellow_0(X0)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f26])).

fof(f26,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_waybel_3(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ( v1_waybel_3(k4_yellow_0(X0),X0)
       => ( ~ r2_subset_1(k4_waybel_0(X0,k12_waybel_0(X0,k3_subset_1(u1_struct_0(X0),k5_waybel_0(X0,k4_yellow_0(X0))))),k1_waybel_3(X0,k4_yellow_0(X0)))
          & ! [X1] :
              ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
                & v1_finset_1(X1)
                & ~ v1_xboole_0(X1) )
             => ~ ( ! [X2] :
                      ( m1_subset_1(X2,u1_struct_0(X0))
                     => ~ ( r3_orders_2(X0,X2,k4_yellow_0(X0))
                          & r2_hidden(X2,X1) ) )
                  & r1_waybel_3(X0,k2_yellow_0(X0,X1),k4_yellow_0(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_waybel_7)).

fof(f704,plain,
    ( ~ v3_orders_2(sK6)
    | v2_struct_0(sK6)
    | ~ spl10_21
    | spl10_22
    | ~ spl10_25 ),
    inference(subsumption_resolution,[],[f703,f109])).

fof(f109,plain,(
    v4_orders_2(sK6) ),
    inference(cnf_transformation,[],[f88])).

fof(f703,plain,
    ( ~ v4_orders_2(sK6)
    | ~ v3_orders_2(sK6)
    | v2_struct_0(sK6)
    | ~ spl10_21
    | spl10_22
    | ~ spl10_25 ),
    inference(subsumption_resolution,[],[f702,f114])).

fof(f114,plain,(
    l1_orders_2(sK6) ),
    inference(cnf_transformation,[],[f88])).

fof(f702,plain,
    ( ~ l1_orders_2(sK6)
    | ~ v4_orders_2(sK6)
    | ~ v3_orders_2(sK6)
    | v2_struct_0(sK6)
    | ~ spl10_21
    | spl10_22
    | ~ spl10_25 ),
    inference(subsumption_resolution,[],[f701,f673])).

fof(f673,plain,
    ( v2_waybel_0(k12_waybel_0(sK6,k3_subset_1(u1_struct_0(sK6),k5_waybel_0(sK6,k4_yellow_0(sK6)))),sK6)
    | ~ spl10_25 ),
    inference(avatar_component_clause,[],[f672])).

fof(f672,plain,
    ( spl10_25
  <=> v2_waybel_0(k12_waybel_0(sK6,k3_subset_1(u1_struct_0(sK6),k5_waybel_0(sK6,k4_yellow_0(sK6)))),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_25])])).

fof(f701,plain,
    ( ~ v2_waybel_0(k12_waybel_0(sK6,k3_subset_1(u1_struct_0(sK6),k5_waybel_0(sK6,k4_yellow_0(sK6)))),sK6)
    | ~ l1_orders_2(sK6)
    | ~ v4_orders_2(sK6)
    | ~ v3_orders_2(sK6)
    | v2_struct_0(sK6)
    | ~ spl10_21
    | spl10_22 ),
    inference(subsumption_resolution,[],[f700,f599])).

fof(f599,plain,
    ( m1_subset_1(k12_waybel_0(sK6,k3_subset_1(u1_struct_0(sK6),k5_waybel_0(sK6,k4_yellow_0(sK6)))),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ spl10_21 ),
    inference(avatar_component_clause,[],[f598])).

fof(f598,plain,
    ( spl10_21
  <=> m1_subset_1(k12_waybel_0(sK6,k3_subset_1(u1_struct_0(sK6),k5_waybel_0(sK6,k4_yellow_0(sK6)))),k1_zfmisc_1(u1_struct_0(sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_21])])).

fof(f700,plain,
    ( ~ m1_subset_1(k12_waybel_0(sK6,k3_subset_1(u1_struct_0(sK6),k5_waybel_0(sK6,k4_yellow_0(sK6)))),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ v2_waybel_0(k12_waybel_0(sK6,k3_subset_1(u1_struct_0(sK6),k5_waybel_0(sK6,k4_yellow_0(sK6)))),sK6)
    | ~ l1_orders_2(sK6)
    | ~ v4_orders_2(sK6)
    | ~ v3_orders_2(sK6)
    | v2_struct_0(sK6)
    | spl10_22 ),
    inference(resolution,[],[f604,f145])).

fof(f145,plain,(
    ! [X0,X1] :
      ( v2_waybel_0(k4_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_waybel_0(X1,X0)
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v2_waybel_0(k4_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_waybel_0(X1,X0)
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v2_waybel_0(k4_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_waybel_0(X1,X0)
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v2_waybel_0(X1,X0)
        & l1_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => v2_waybel_0(k4_waybel_0(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc16_waybel_0)).

fof(f604,plain,
    ( ~ v2_waybel_0(k4_waybel_0(sK6,k12_waybel_0(sK6,k3_subset_1(u1_struct_0(sK6),k5_waybel_0(sK6,k4_yellow_0(sK6))))),sK6)
    | spl10_22 ),
    inference(avatar_component_clause,[],[f602])).

fof(f602,plain,
    ( spl10_22
  <=> v2_waybel_0(k4_waybel_0(sK6,k12_waybel_0(sK6,k3_subset_1(u1_struct_0(sK6),k5_waybel_0(sK6,k4_yellow_0(sK6))))),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).

fof(f697,plain,
    ( ~ spl10_12
    | spl10_25 ),
    inference(avatar_contradiction_clause,[],[f696])).

fof(f696,plain,
    ( $false
    | ~ spl10_12
    | spl10_25 ),
    inference(subsumption_resolution,[],[f695,f108])).

fof(f695,plain,
    ( ~ v3_orders_2(sK6)
    | ~ spl10_12
    | spl10_25 ),
    inference(subsumption_resolution,[],[f694,f109])).

fof(f694,plain,
    ( ~ v4_orders_2(sK6)
    | ~ v3_orders_2(sK6)
    | ~ spl10_12
    | spl10_25 ),
    inference(subsumption_resolution,[],[f693,f110])).

fof(f110,plain,(
    v5_orders_2(sK6) ),
    inference(cnf_transformation,[],[f88])).

fof(f693,plain,
    ( ~ v5_orders_2(sK6)
    | ~ v4_orders_2(sK6)
    | ~ v3_orders_2(sK6)
    | ~ spl10_12
    | spl10_25 ),
    inference(subsumption_resolution,[],[f692,f112])).

fof(f112,plain,(
    v2_lattice3(sK6) ),
    inference(cnf_transformation,[],[f88])).

fof(f692,plain,
    ( ~ v2_lattice3(sK6)
    | ~ v5_orders_2(sK6)
    | ~ v4_orders_2(sK6)
    | ~ v3_orders_2(sK6)
    | ~ spl10_12
    | spl10_25 ),
    inference(subsumption_resolution,[],[f691,f114])).

fof(f691,plain,
    ( ~ l1_orders_2(sK6)
    | ~ v2_lattice3(sK6)
    | ~ v5_orders_2(sK6)
    | ~ v4_orders_2(sK6)
    | ~ v3_orders_2(sK6)
    | ~ spl10_12
    | spl10_25 ),
    inference(subsumption_resolution,[],[f690,f516])).

fof(f516,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK6),k5_waybel_0(sK6,k4_yellow_0(sK6))),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ spl10_12 ),
    inference(avatar_component_clause,[],[f515])).

fof(f515,plain,
    ( spl10_12
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK6),k5_waybel_0(sK6,k4_yellow_0(sK6))),k1_zfmisc_1(u1_struct_0(sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f690,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK6),k5_waybel_0(sK6,k4_yellow_0(sK6))),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ l1_orders_2(sK6)
    | ~ v2_lattice3(sK6)
    | ~ v5_orders_2(sK6)
    | ~ v4_orders_2(sK6)
    | ~ v3_orders_2(sK6)
    | spl10_25 ),
    inference(resolution,[],[f674,f148])).

fof(f148,plain,(
    ! [X0,X1] :
      ( v2_waybel_0(k12_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v2_waybel_0(k12_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v2_waybel_0(k12_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => v2_waybel_0(k12_waybel_0(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc22_waybel_0)).

fof(f674,plain,
    ( ~ v2_waybel_0(k12_waybel_0(sK6,k3_subset_1(u1_struct_0(sK6),k5_waybel_0(sK6,k4_yellow_0(sK6)))),sK6)
    | spl10_25 ),
    inference(avatar_component_clause,[],[f672])).

fof(f658,plain,
    ( spl10_6
    | ~ spl10_12
    | spl10_21 ),
    inference(avatar_contradiction_clause,[],[f657])).

fof(f657,plain,
    ( $false
    | spl10_6
    | ~ spl10_12
    | spl10_21 ),
    inference(subsumption_resolution,[],[f656,f219])).

fof(f656,plain,
    ( v2_struct_0(sK6)
    | ~ spl10_12
    | spl10_21 ),
    inference(subsumption_resolution,[],[f655,f114])).

fof(f655,plain,
    ( ~ l1_orders_2(sK6)
    | v2_struct_0(sK6)
    | ~ spl10_12
    | spl10_21 ),
    inference(subsumption_resolution,[],[f654,f516])).

fof(f654,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK6),k5_waybel_0(sK6,k4_yellow_0(sK6))),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ l1_orders_2(sK6)
    | v2_struct_0(sK6)
    | spl10_21 ),
    inference(resolution,[],[f600,f144])).

fof(f144,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k12_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k12_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k12_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k12_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k12_waybel_0)).

fof(f600,plain,
    ( ~ m1_subset_1(k12_waybel_0(sK6,k3_subset_1(u1_struct_0(sK6),k5_waybel_0(sK6,k4_yellow_0(sK6)))),k1_zfmisc_1(u1_struct_0(sK6)))
    | spl10_21 ),
    inference(avatar_component_clause,[],[f598])).

fof(f620,plain,
    ( spl10_6
    | ~ spl10_10
    | spl10_20 ),
    inference(avatar_contradiction_clause,[],[f619])).

fof(f619,plain,
    ( $false
    | spl10_6
    | ~ spl10_10
    | spl10_20 ),
    inference(subsumption_resolution,[],[f618,f219])).

fof(f618,plain,
    ( v2_struct_0(sK6)
    | spl10_6
    | ~ spl10_10
    | spl10_20 ),
    inference(subsumption_resolution,[],[f617,f108])).

fof(f617,plain,
    ( ~ v3_orders_2(sK6)
    | v2_struct_0(sK6)
    | spl10_6
    | ~ spl10_10
    | spl10_20 ),
    inference(subsumption_resolution,[],[f616,f114])).

fof(f616,plain,
    ( ~ l1_orders_2(sK6)
    | ~ v3_orders_2(sK6)
    | v2_struct_0(sK6)
    | spl10_6
    | ~ spl10_10
    | spl10_20 ),
    inference(subsumption_resolution,[],[f615,f459])).

fof(f459,plain,
    ( m1_subset_1(k4_yellow_0(sK6),u1_struct_0(sK6))
    | ~ spl10_10 ),
    inference(avatar_component_clause,[],[f458])).

fof(f458,plain,
    ( spl10_10
  <=> m1_subset_1(k4_yellow_0(sK6),u1_struct_0(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f615,plain,
    ( ~ m1_subset_1(k4_yellow_0(sK6),u1_struct_0(sK6))
    | ~ l1_orders_2(sK6)
    | ~ v3_orders_2(sK6)
    | v2_struct_0(sK6)
    | spl10_6
    | ~ spl10_10
    | spl10_20 ),
    inference(subsumption_resolution,[],[f614,f115])).

fof(f115,plain,(
    v1_waybel_3(k4_yellow_0(sK6),sK6) ),
    inference(cnf_transformation,[],[f88])).

fof(f614,plain,
    ( ~ v1_waybel_3(k4_yellow_0(sK6),sK6)
    | ~ m1_subset_1(k4_yellow_0(sK6),u1_struct_0(sK6))
    | ~ l1_orders_2(sK6)
    | ~ v3_orders_2(sK6)
    | v2_struct_0(sK6)
    | spl10_6
    | ~ spl10_10
    | spl10_20 ),
    inference(resolution,[],[f613,f131])).

fof(f131,plain,(
    ! [X0,X1] :
      ( r1_waybel_3(X0,X1,X1)
      | ~ v1_waybel_3(X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f91])).

fof(f91,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_waybel_3(X1,X0)
              | ~ r1_waybel_3(X0,X1,X1) )
            & ( r1_waybel_3(X0,X1,X1)
              | ~ v1_waybel_3(X1,X0) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_waybel_3(X1,X0)
          <=> r1_waybel_3(X0,X1,X1) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_waybel_3(X1,X0)
          <=> r1_waybel_3(X0,X1,X1) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v1_waybel_3(X1,X0)
          <=> r1_waybel_3(X0,X1,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_waybel_3)).

fof(f613,plain,
    ( ~ r1_waybel_3(sK6,k4_yellow_0(sK6),k4_yellow_0(sK6))
    | spl10_6
    | ~ spl10_10
    | spl10_20 ),
    inference(subsumption_resolution,[],[f612,f459])).

fof(f612,plain,
    ( ~ r1_waybel_3(sK6,k4_yellow_0(sK6),k4_yellow_0(sK6))
    | ~ m1_subset_1(k4_yellow_0(sK6),u1_struct_0(sK6))
    | spl10_6
    | ~ spl10_10
    | spl10_20 ),
    inference(resolution,[],[f611,f160])).

fof(f160,plain,(
    ! [X0,X3,X1] :
      ( sP3(X0,X1,X3)
      | ~ r1_waybel_3(X1,X3,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X1)) ) ),
    inference(equality_resolution,[],[f157])).

fof(f157,plain,(
    ! [X2,X0,X3,X1] :
      ( sP3(X0,X1,X2)
      | ~ r1_waybel_3(X1,X3,X0)
      | X2 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f102])).

fof(f102,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | ! [X3] :
            ( ~ r1_waybel_3(X1,X3,X0)
            | X2 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ( r1_waybel_3(X1,sK9(X0,X1,X2),X0)
          & sK9(X0,X1,X2) = X2
          & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X1)) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f100,f101])).

fof(f101,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r1_waybel_3(X1,X4,X0)
          & X2 = X4
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( r1_waybel_3(X1,sK9(X0,X1,X2),X0)
        & sK9(X0,X1,X2) = X2
        & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f100,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | ! [X3] :
            ( ~ r1_waybel_3(X1,X3,X0)
            | X2 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ? [X4] :
            ( r1_waybel_3(X1,X4,X0)
            & X2 = X4
            & m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(rectify,[],[f99])).

fof(f99,plain,(
    ! [X2,X1,X0] :
      ( ( sP3(X2,X1,X0)
        | ! [X3] :
            ( ~ r1_waybel_3(X1,X3,X2)
            | X0 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ? [X3] :
            ( r1_waybel_3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) )
        | ~ sP3(X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f81])).

fof(f81,plain,(
    ! [X2,X1,X0] :
      ( sP3(X2,X1,X0)
    <=> ? [X3] :
          ( r1_waybel_3(X1,X3,X2)
          & X0 = X3
          & m1_subset_1(X3,u1_struct_0(X1)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f611,plain,
    ( ~ sP3(k4_yellow_0(sK6),sK6,k4_yellow_0(sK6))
    | spl10_6
    | ~ spl10_10
    | spl10_20 ),
    inference(subsumption_resolution,[],[f610,f219])).

fof(f610,plain,
    ( ~ sP3(k4_yellow_0(sK6),sK6,k4_yellow_0(sK6))
    | v2_struct_0(sK6)
    | ~ spl10_10
    | spl10_20 ),
    inference(subsumption_resolution,[],[f609,f108])).

fof(f609,plain,
    ( ~ sP3(k4_yellow_0(sK6),sK6,k4_yellow_0(sK6))
    | ~ v3_orders_2(sK6)
    | v2_struct_0(sK6)
    | ~ spl10_10
    | spl10_20 ),
    inference(subsumption_resolution,[],[f608,f114])).

fof(f608,plain,
    ( ~ sP3(k4_yellow_0(sK6),sK6,k4_yellow_0(sK6))
    | ~ l1_orders_2(sK6)
    | ~ v3_orders_2(sK6)
    | v2_struct_0(sK6)
    | ~ spl10_10
    | spl10_20 ),
    inference(subsumption_resolution,[],[f606,f459])).

fof(f606,plain,
    ( ~ sP3(k4_yellow_0(sK6),sK6,k4_yellow_0(sK6))
    | ~ m1_subset_1(k4_yellow_0(sK6),u1_struct_0(sK6))
    | ~ l1_orders_2(sK6)
    | ~ v3_orders_2(sK6)
    | v2_struct_0(sK6)
    | spl10_20 ),
    inference(resolution,[],[f596,f283])).

fof(f283,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k1_waybel_3(X0,X1))
      | ~ sP3(X1,X0,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f281,f158])).

fof(f158,plain,(
    ! [X2,X0,X1] :
      ( sP4(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f83,plain,(
    ! [X0,X1,X2] :
      ( sP4(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(definition_folding,[],[f72,f82,f81])).

fof(f82,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_waybel_3(X1,X2))
      <=> sP3(X2,X1,X0) )
      | ~ sP4(X0,X1,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f72,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_waybel_3(X1,X2))
      <=> ? [X3] :
            ( r1_waybel_3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f71])).

fof(f71,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_waybel_3(X1,X2))
      <=> ? [X3] :
            ( r1_waybel_3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X1))
        & l1_orders_2(X1)
        & v3_orders_2(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_0_waybel_3(X1,X2))
      <=> ? [X3] :
            ( r1_waybel_3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_0_waybel_3)).

fof(f281,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k1_waybel_3(X0,X1))
      | ~ sP3(X1,X0,X2)
      | ~ sP4(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(superposition,[],[f153,f130])).

fof(f130,plain,(
    ! [X0,X1] :
      ( k1_waybel_3(X0,X1) = a_2_0_waybel_3(X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_waybel_3(X0,X1) = a_2_0_waybel_3(X0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_waybel_3(X0,X1) = a_2_0_waybel_3(X0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k1_waybel_3(X0,X1) = a_2_0_waybel_3(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_waybel_3)).

fof(f153,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,a_2_0_waybel_3(X1,X2))
      | ~ sP3(X2,X1,X0)
      | ~ sP4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f98])).

fof(f98,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_waybel_3(X1,X2))
          | ~ sP3(X2,X1,X0) )
        & ( sP3(X2,X1,X0)
          | ~ r2_hidden(X0,a_2_0_waybel_3(X1,X2)) ) )
      | ~ sP4(X0,X1,X2) ) ),
    inference(nnf_transformation,[],[f82])).

fof(f596,plain,
    ( ~ r2_hidden(k4_yellow_0(sK6),k1_waybel_3(sK6,k4_yellow_0(sK6)))
    | spl10_20 ),
    inference(avatar_component_clause,[],[f594])).

fof(f594,plain,
    ( spl10_20
  <=> r2_hidden(k4_yellow_0(sK6),k1_waybel_3(sK6,k4_yellow_0(sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_20])])).

fof(f605,plain,
    ( ~ spl10_20
    | ~ spl10_21
    | ~ spl10_22
    | ~ spl10_2
    | spl10_3
    | spl10_6
    | ~ spl10_9 ),
    inference(avatar_split_clause,[],[f592,f412,f218,f195,f166,f602,f598,f594])).

fof(f166,plain,
    ( spl10_2
  <=> r2_subset_1(k4_waybel_0(sK6,k12_waybel_0(sK6,k3_subset_1(u1_struct_0(sK6),k5_waybel_0(sK6,k4_yellow_0(sK6))))),k1_waybel_3(sK6,k4_yellow_0(sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f195,plain,
    ( spl10_3
  <=> v1_xboole_0(k4_waybel_0(sK6,k12_waybel_0(sK6,k3_subset_1(u1_struct_0(sK6),k5_waybel_0(sK6,k4_yellow_0(sK6)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f412,plain,
    ( spl10_9
  <=> v2_yellow_0(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f592,plain,
    ( ~ v2_waybel_0(k4_waybel_0(sK6,k12_waybel_0(sK6,k3_subset_1(u1_struct_0(sK6),k5_waybel_0(sK6,k4_yellow_0(sK6))))),sK6)
    | ~ m1_subset_1(k12_waybel_0(sK6,k3_subset_1(u1_struct_0(sK6),k5_waybel_0(sK6,k4_yellow_0(sK6)))),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(k4_yellow_0(sK6),k1_waybel_3(sK6,k4_yellow_0(sK6)))
    | ~ spl10_2
    | spl10_3
    | spl10_6
    | ~ spl10_9 ),
    inference(subsumption_resolution,[],[f591,f219])).

fof(f591,plain,
    ( ~ v2_waybel_0(k4_waybel_0(sK6,k12_waybel_0(sK6,k3_subset_1(u1_struct_0(sK6),k5_waybel_0(sK6,k4_yellow_0(sK6))))),sK6)
    | v2_struct_0(sK6)
    | ~ m1_subset_1(k12_waybel_0(sK6,k3_subset_1(u1_struct_0(sK6),k5_waybel_0(sK6,k4_yellow_0(sK6)))),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(k4_yellow_0(sK6),k1_waybel_3(sK6,k4_yellow_0(sK6)))
    | ~ spl10_2
    | spl10_3
    | ~ spl10_9 ),
    inference(subsumption_resolution,[],[f590,f108])).

fof(f590,plain,
    ( ~ v2_waybel_0(k4_waybel_0(sK6,k12_waybel_0(sK6,k3_subset_1(u1_struct_0(sK6),k5_waybel_0(sK6,k4_yellow_0(sK6))))),sK6)
    | ~ v3_orders_2(sK6)
    | v2_struct_0(sK6)
    | ~ m1_subset_1(k12_waybel_0(sK6,k3_subset_1(u1_struct_0(sK6),k5_waybel_0(sK6,k4_yellow_0(sK6)))),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(k4_yellow_0(sK6),k1_waybel_3(sK6,k4_yellow_0(sK6)))
    | ~ spl10_2
    | spl10_3
    | ~ spl10_9 ),
    inference(subsumption_resolution,[],[f589,f109])).

fof(f589,plain,
    ( ~ v2_waybel_0(k4_waybel_0(sK6,k12_waybel_0(sK6,k3_subset_1(u1_struct_0(sK6),k5_waybel_0(sK6,k4_yellow_0(sK6))))),sK6)
    | ~ v4_orders_2(sK6)
    | ~ v3_orders_2(sK6)
    | v2_struct_0(sK6)
    | ~ m1_subset_1(k12_waybel_0(sK6,k3_subset_1(u1_struct_0(sK6),k5_waybel_0(sK6,k4_yellow_0(sK6)))),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(k4_yellow_0(sK6),k1_waybel_3(sK6,k4_yellow_0(sK6)))
    | ~ spl10_2
    | spl10_3
    | ~ spl10_9 ),
    inference(subsumption_resolution,[],[f588,f110])).

fof(f588,plain,
    ( ~ v2_waybel_0(k4_waybel_0(sK6,k12_waybel_0(sK6,k3_subset_1(u1_struct_0(sK6),k5_waybel_0(sK6,k4_yellow_0(sK6))))),sK6)
    | ~ v5_orders_2(sK6)
    | ~ v4_orders_2(sK6)
    | ~ v3_orders_2(sK6)
    | v2_struct_0(sK6)
    | ~ m1_subset_1(k12_waybel_0(sK6,k3_subset_1(u1_struct_0(sK6),k5_waybel_0(sK6,k4_yellow_0(sK6)))),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(k4_yellow_0(sK6),k1_waybel_3(sK6,k4_yellow_0(sK6)))
    | ~ spl10_2
    | spl10_3
    | ~ spl10_9 ),
    inference(subsumption_resolution,[],[f587,f413])).

fof(f413,plain,
    ( v2_yellow_0(sK6)
    | ~ spl10_9 ),
    inference(avatar_component_clause,[],[f412])).

fof(f587,plain,
    ( ~ v2_waybel_0(k4_waybel_0(sK6,k12_waybel_0(sK6,k3_subset_1(u1_struct_0(sK6),k5_waybel_0(sK6,k4_yellow_0(sK6))))),sK6)
    | ~ v2_yellow_0(sK6)
    | ~ v5_orders_2(sK6)
    | ~ v4_orders_2(sK6)
    | ~ v3_orders_2(sK6)
    | v2_struct_0(sK6)
    | ~ m1_subset_1(k12_waybel_0(sK6,k3_subset_1(u1_struct_0(sK6),k5_waybel_0(sK6,k4_yellow_0(sK6)))),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(k4_yellow_0(sK6),k1_waybel_3(sK6,k4_yellow_0(sK6)))
    | ~ spl10_2
    | spl10_3 ),
    inference(subsumption_resolution,[],[f586,f114])).

fof(f586,plain,
    ( ~ v2_waybel_0(k4_waybel_0(sK6,k12_waybel_0(sK6,k3_subset_1(u1_struct_0(sK6),k5_waybel_0(sK6,k4_yellow_0(sK6))))),sK6)
    | ~ l1_orders_2(sK6)
    | ~ v2_yellow_0(sK6)
    | ~ v5_orders_2(sK6)
    | ~ v4_orders_2(sK6)
    | ~ v3_orders_2(sK6)
    | v2_struct_0(sK6)
    | ~ m1_subset_1(k12_waybel_0(sK6,k3_subset_1(u1_struct_0(sK6),k5_waybel_0(sK6,k4_yellow_0(sK6)))),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(k4_yellow_0(sK6),k1_waybel_3(sK6,k4_yellow_0(sK6)))
    | ~ spl10_2
    | spl10_3 ),
    inference(subsumption_resolution,[],[f583,f196])).

fof(f196,plain,
    ( ~ v1_xboole_0(k4_waybel_0(sK6,k12_waybel_0(sK6,k3_subset_1(u1_struct_0(sK6),k5_waybel_0(sK6,k4_yellow_0(sK6))))))
    | spl10_3 ),
    inference(avatar_component_clause,[],[f195])).

fof(f583,plain,
    ( ~ v2_waybel_0(k4_waybel_0(sK6,k12_waybel_0(sK6,k3_subset_1(u1_struct_0(sK6),k5_waybel_0(sK6,k4_yellow_0(sK6))))),sK6)
    | v1_xboole_0(k4_waybel_0(sK6,k12_waybel_0(sK6,k3_subset_1(u1_struct_0(sK6),k5_waybel_0(sK6,k4_yellow_0(sK6))))))
    | ~ l1_orders_2(sK6)
    | ~ v2_yellow_0(sK6)
    | ~ v5_orders_2(sK6)
    | ~ v4_orders_2(sK6)
    | ~ v3_orders_2(sK6)
    | v2_struct_0(sK6)
    | ~ m1_subset_1(k12_waybel_0(sK6,k3_subset_1(u1_struct_0(sK6),k5_waybel_0(sK6,k4_yellow_0(sK6)))),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(k4_yellow_0(sK6),k1_waybel_3(sK6,k4_yellow_0(sK6)))
    | ~ spl10_2 ),
    inference(resolution,[],[f433,f444])).

fof(f444,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k4_waybel_0(sK6,k12_waybel_0(sK6,k3_subset_1(u1_struct_0(sK6),k5_waybel_0(sK6,k4_yellow_0(sK6))))))
        | ~ r2_hidden(X0,k1_waybel_3(sK6,k4_yellow_0(sK6))) )
    | ~ spl10_2 ),
    inference(resolution,[],[f168,f186])).

fof(f186,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_subset_1(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(resolution,[],[f185,f136])).

fof(f136,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK8(X0,X1),X1)
          & r2_hidden(sK8(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f46,f94])).

fof(f94,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK8(X0,X1),X1)
        & r2_hidden(sK8(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f185,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r2_subset_1(X0,X1) ) ),
    inference(subsumption_resolution,[],[f184,f171])).

fof(f171,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(resolution,[],[f135,f149])).

fof(f149,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

fof(f135,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK8(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f95])).

fof(f184,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r2_subset_1(X0,X1)
      | v1_xboole_0(X1) ) ),
    inference(subsumption_resolution,[],[f139,f170])).

fof(f170,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f134,f149])).

fof(f134,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK8(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f95])).

fof(f139,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r2_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ( ( r2_subset_1(X0,X1)
          | ~ r1_xboole_0(X0,X1) )
        & ( r1_xboole_0(X0,X1)
          | ~ r2_subset_1(X0,X1) ) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( r2_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( r2_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r2_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_subset_1)).

fof(f168,plain,
    ( r2_subset_1(k4_waybel_0(sK6,k12_waybel_0(sK6,k3_subset_1(u1_struct_0(sK6),k5_waybel_0(sK6,k4_yellow_0(sK6))))),k1_waybel_3(sK6,k4_yellow_0(sK6)))
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f166])).

fof(f433,plain,(
    ! [X4,X5] :
      ( r2_hidden(k4_yellow_0(X4),k4_waybel_0(X4,X5))
      | ~ v2_waybel_0(k4_waybel_0(X4,X5),X4)
      | v1_xboole_0(k4_waybel_0(X4,X5))
      | ~ l1_orders_2(X4)
      | ~ v2_yellow_0(X4)
      | ~ v5_orders_2(X4)
      | ~ v4_orders_2(X4)
      | ~ v3_orders_2(X4)
      | v2_struct_0(X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4))) ) ),
    inference(subsumption_resolution,[],[f430,f142])).

fof(f142,plain,(
    ! [X0,X1] :
      ( v13_waybel_0(k4_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v13_waybel_0(k4_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v13_waybel_0(k4_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v4_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => v13_waybel_0(k4_waybel_0(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc11_waybel_0)).

fof(f430,plain,(
    ! [X4,X5] :
      ( r2_hidden(k4_yellow_0(X4),k4_waybel_0(X4,X5))
      | ~ v13_waybel_0(k4_waybel_0(X4,X5),X4)
      | ~ v2_waybel_0(k4_waybel_0(X4,X5),X4)
      | v1_xboole_0(k4_waybel_0(X4,X5))
      | ~ l1_orders_2(X4)
      | ~ v2_yellow_0(X4)
      | ~ v5_orders_2(X4)
      | ~ v4_orders_2(X4)
      | ~ v3_orders_2(X4)
      | v2_struct_0(X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4))) ) ),
    inference(duplicate_literal_removal,[],[f418])).

fof(f418,plain,(
    ! [X4,X5] :
      ( r2_hidden(k4_yellow_0(X4),k4_waybel_0(X4,X5))
      | ~ v13_waybel_0(k4_waybel_0(X4,X5),X4)
      | ~ v2_waybel_0(k4_waybel_0(X4,X5),X4)
      | v1_xboole_0(k4_waybel_0(X4,X5))
      | ~ l1_orders_2(X4)
      | ~ v2_yellow_0(X4)
      | ~ v5_orders_2(X4)
      | ~ v4_orders_2(X4)
      | ~ v3_orders_2(X4)
      | v2_struct_0(X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4)))
      | ~ l1_orders_2(X4) ) ),
    inference(resolution,[],[f129,f147])).

fof(f147,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0) )
     => m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_waybel_0)).

fof(f129,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(k4_yellow_0(X0),X1)
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(k4_yellow_0(X0),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(k4_yellow_0(X0),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_yellow_0(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => r2_hidden(k4_yellow_0(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_waybel_4)).

fof(f538,plain,
    ( spl10_6
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_13 ),
    inference(avatar_contradiction_clause,[],[f537])).

fof(f537,plain,
    ( $false
    | spl10_6
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_13 ),
    inference(subsumption_resolution,[],[f536,f219])).

fof(f536,plain,
    ( v2_struct_0(sK6)
    | spl10_6
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_13 ),
    inference(subsumption_resolution,[],[f535,f114])).

fof(f535,plain,
    ( ~ l1_orders_2(sK6)
    | v2_struct_0(sK6)
    | spl10_6
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_13 ),
    inference(subsumption_resolution,[],[f534,f459])).

fof(f534,plain,
    ( ~ m1_subset_1(k4_yellow_0(sK6),u1_struct_0(sK6))
    | ~ l1_orders_2(sK6)
    | v2_struct_0(sK6)
    | spl10_6
    | ~ spl10_9
    | ~ spl10_13 ),
    inference(resolution,[],[f533,f143])).

fof(f143,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_waybel_0)).

fof(f533,plain,
    ( ~ m1_subset_1(k5_waybel_0(sK6,k4_yellow_0(sK6)),k1_zfmisc_1(u1_struct_0(sK6)))
    | spl10_6
    | ~ spl10_9
    | ~ spl10_13 ),
    inference(subsumption_resolution,[],[f532,f219])).

fof(f532,plain,
    ( v2_struct_0(sK6)
    | ~ m1_subset_1(k5_waybel_0(sK6,k4_yellow_0(sK6)),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ spl10_9
    | ~ spl10_13 ),
    inference(subsumption_resolution,[],[f531,f110])).

fof(f531,plain,
    ( ~ v5_orders_2(sK6)
    | v2_struct_0(sK6)
    | ~ m1_subset_1(k5_waybel_0(sK6,k4_yellow_0(sK6)),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ spl10_9
    | ~ spl10_13 ),
    inference(subsumption_resolution,[],[f530,f413])).

fof(f530,plain,
    ( ~ v2_yellow_0(sK6)
    | ~ v5_orders_2(sK6)
    | v2_struct_0(sK6)
    | ~ m1_subset_1(k5_waybel_0(sK6,k4_yellow_0(sK6)),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ spl10_13 ),
    inference(subsumption_resolution,[],[f529,f114])).

fof(f529,plain,
    ( ~ l1_orders_2(sK6)
    | ~ v2_yellow_0(sK6)
    | ~ v5_orders_2(sK6)
    | v2_struct_0(sK6)
    | ~ m1_subset_1(k5_waybel_0(sK6,k4_yellow_0(sK6)),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ spl10_13 ),
    inference(resolution,[],[f521,f288])).

fof(f288,plain,(
    ! [X2,X3] :
      ( ~ v1_xboole_0(k12_waybel_0(X2,k3_subset_1(u1_struct_0(X2),X3)))
      | ~ l1_orders_2(X2)
      | ~ v2_yellow_0(X2)
      | ~ v5_orders_2(X2)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(resolution,[],[f141,f138])).

fof(f138,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f141,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_xboole_0(k12_waybel_0(X0,X1))
      | ~ l1_orders_2(X0)
      | ~ v2_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k12_waybel_0(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v2_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k12_waybel_0(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v2_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v2_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k12_waybel_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc18_waybel_0)).

fof(f521,plain,
    ( v1_xboole_0(k12_waybel_0(sK6,k3_subset_1(u1_struct_0(sK6),k5_waybel_0(sK6,k4_yellow_0(sK6)))))
    | ~ spl10_13 ),
    inference(avatar_component_clause,[],[f519])).

fof(f519,plain,
    ( spl10_13
  <=> v1_xboole_0(k12_waybel_0(sK6,k3_subset_1(u1_struct_0(sK6),k5_waybel_0(sK6,k4_yellow_0(sK6))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).

fof(f528,plain,
    ( spl10_6
    | ~ spl10_10
    | spl10_12 ),
    inference(avatar_contradiction_clause,[],[f527])).

fof(f527,plain,
    ( $false
    | spl10_6
    | ~ spl10_10
    | spl10_12 ),
    inference(subsumption_resolution,[],[f526,f219])).

fof(f526,plain,
    ( v2_struct_0(sK6)
    | ~ spl10_10
    | spl10_12 ),
    inference(subsumption_resolution,[],[f525,f114])).

fof(f525,plain,
    ( ~ l1_orders_2(sK6)
    | v2_struct_0(sK6)
    | ~ spl10_10
    | spl10_12 ),
    inference(subsumption_resolution,[],[f524,f459])).

fof(f524,plain,
    ( ~ m1_subset_1(k4_yellow_0(sK6),u1_struct_0(sK6))
    | ~ l1_orders_2(sK6)
    | v2_struct_0(sK6)
    | spl10_12 ),
    inference(resolution,[],[f523,f143])).

fof(f523,plain,
    ( ~ m1_subset_1(k5_waybel_0(sK6,k4_yellow_0(sK6)),k1_zfmisc_1(u1_struct_0(sK6)))
    | spl10_12 ),
    inference(resolution,[],[f517,f138])).

fof(f517,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK6),k5_waybel_0(sK6,k4_yellow_0(sK6))),k1_zfmisc_1(u1_struct_0(sK6)))
    | spl10_12 ),
    inference(avatar_component_clause,[],[f515])).

fof(f522,plain,
    ( ~ spl10_12
    | spl10_13
    | ~ spl10_3
    | spl10_6 ),
    inference(avatar_split_clause,[],[f513,f218,f195,f519,f515])).

fof(f513,plain,
    ( v1_xboole_0(k12_waybel_0(sK6,k3_subset_1(u1_struct_0(sK6),k5_waybel_0(sK6,k4_yellow_0(sK6)))))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK6),k5_waybel_0(sK6,k4_yellow_0(sK6))),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ spl10_3
    | spl10_6 ),
    inference(subsumption_resolution,[],[f512,f219])).

fof(f512,plain,
    ( v1_xboole_0(k12_waybel_0(sK6,k3_subset_1(u1_struct_0(sK6),k5_waybel_0(sK6,k4_yellow_0(sK6)))))
    | v2_struct_0(sK6)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK6),k5_waybel_0(sK6,k4_yellow_0(sK6))),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f511,f108])).

fof(f511,plain,
    ( v1_xboole_0(k12_waybel_0(sK6,k3_subset_1(u1_struct_0(sK6),k5_waybel_0(sK6,k4_yellow_0(sK6)))))
    | ~ v3_orders_2(sK6)
    | v2_struct_0(sK6)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK6),k5_waybel_0(sK6,k4_yellow_0(sK6))),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f510,f114])).

fof(f510,plain,
    ( v1_xboole_0(k12_waybel_0(sK6,k3_subset_1(u1_struct_0(sK6),k5_waybel_0(sK6,k4_yellow_0(sK6)))))
    | ~ l1_orders_2(sK6)
    | ~ v3_orders_2(sK6)
    | v2_struct_0(sK6)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK6),k5_waybel_0(sK6,k4_yellow_0(sK6))),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ spl10_3 ),
    inference(resolution,[],[f316,f197])).

fof(f197,plain,
    ( v1_xboole_0(k4_waybel_0(sK6,k12_waybel_0(sK6,k3_subset_1(u1_struct_0(sK6),k5_waybel_0(sK6,k4_yellow_0(sK6))))))
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f195])).

fof(f316,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k4_waybel_0(X0,k12_waybel_0(X0,X1)))
      | v1_xboole_0(k12_waybel_0(X0,X1))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(duplicate_literal_removal,[],[f302])).

fof(f302,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k4_waybel_0(X0,k12_waybel_0(X0,X1)))
      | v1_xboole_0(k12_waybel_0(X0,X1))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f146,f144])).

fof(f146,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_xboole_0(k4_waybel_0(X0,X1))
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k4_waybel_0(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k4_waybel_0(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k4_waybel_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_waybel_0)).

fof(f468,plain,(
    spl10_10 ),
    inference(avatar_contradiction_clause,[],[f467])).

fof(f467,plain,
    ( $false
    | spl10_10 ),
    inference(subsumption_resolution,[],[f465,f114])).

fof(f465,plain,
    ( ~ l1_orders_2(sK6)
    | spl10_10 ),
    inference(resolution,[],[f460,f117])).

fof(f117,plain,(
    ! [X0] :
      ( m1_subset_1(k4_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( m1_subset_1(k4_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(k4_yellow_0(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_yellow_0)).

fof(f460,plain,
    ( ~ m1_subset_1(k4_yellow_0(sK6),u1_struct_0(sK6))
    | spl10_10 ),
    inference(avatar_component_clause,[],[f458])).

fof(f443,plain,(
    ~ spl10_6 ),
    inference(avatar_contradiction_clause,[],[f442])).

fof(f442,plain,
    ( $false
    | ~ spl10_6 ),
    inference(subsumption_resolution,[],[f441,f114])).

fof(f441,plain,
    ( ~ l1_orders_2(sK6)
    | ~ spl10_6 ),
    inference(subsumption_resolution,[],[f440,f112])).

fof(f440,plain,
    ( ~ v2_lattice3(sK6)
    | ~ l1_orders_2(sK6)
    | ~ spl10_6 ),
    inference(resolution,[],[f220,f118])).

fof(f118,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_lattice3)).

fof(f220,plain,
    ( v2_struct_0(sK6)
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f218])).

fof(f439,plain,
    ( ~ spl10_5
    | spl10_9 ),
    inference(avatar_contradiction_clause,[],[f438])).

fof(f438,plain,
    ( $false
    | ~ spl10_5
    | spl10_9 ),
    inference(subsumption_resolution,[],[f437,f216])).

fof(f216,plain,
    ( v24_waybel_0(sK6)
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f214])).

fof(f214,plain,
    ( spl10_5
  <=> v24_waybel_0(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f437,plain,
    ( ~ v24_waybel_0(sK6)
    | spl10_9 ),
    inference(subsumption_resolution,[],[f436,f114])).

fof(f436,plain,
    ( ~ l1_orders_2(sK6)
    | ~ v24_waybel_0(sK6)
    | spl10_9 ),
    inference(subsumption_resolution,[],[f435,f108])).

fof(f435,plain,
    ( ~ v3_orders_2(sK6)
    | ~ l1_orders_2(sK6)
    | ~ v24_waybel_0(sK6)
    | spl10_9 ),
    inference(subsumption_resolution,[],[f434,f111])).

fof(f111,plain,(
    v1_lattice3(sK6) ),
    inference(cnf_transformation,[],[f88])).

fof(f434,plain,
    ( ~ v1_lattice3(sK6)
    | ~ v3_orders_2(sK6)
    | ~ l1_orders_2(sK6)
    | ~ v24_waybel_0(sK6)
    | spl10_9 ),
    inference(resolution,[],[f414,f181])).

fof(f181,plain,(
    ! [X0] :
      ( v2_yellow_0(X0)
      | ~ v1_lattice3(X0)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ v24_waybel_0(X0) ) ),
    inference(resolution,[],[f127,f126])).

fof(f126,plain,(
    ! [X0] :
      ( ~ sP2(X0)
      | v2_yellow_0(X0) ) ),
    inference(cnf_transformation,[],[f90])).

fof(f90,plain,(
    ! [X0] :
      ( ( v2_yellow_0(X0)
        & v1_lattice3(X0)
        & v3_orders_2(X0) )
      | ~ sP2(X0) ) ),
    inference(nnf_transformation,[],[f79])).

fof(f79,plain,(
    ! [X0] :
      ( ( v2_yellow_0(X0)
        & v1_lattice3(X0)
        & v3_orders_2(X0) )
      | ~ sP2(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f127,plain,(
    ! [X0] :
      ( sP2(X0)
      | ~ v24_waybel_0(X0)
      | ~ v1_lattice3(X0)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f80,plain,(
    ! [X0] :
      ( sP2(X0)
      | ~ v24_waybel_0(X0)
      | ~ v1_lattice3(X0)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f37,f79])).

fof(f37,plain,(
    ! [X0] :
      ( ( v2_yellow_0(X0)
        & v1_lattice3(X0)
        & v3_orders_2(X0) )
      | ~ v24_waybel_0(X0)
      | ~ v1_lattice3(X0)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( v2_yellow_0(X0)
        & v1_lattice3(X0)
        & v3_orders_2(X0) )
      | ~ v24_waybel_0(X0)
      | ~ v1_lattice3(X0)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( ( v24_waybel_0(X0)
          & v1_lattice3(X0)
          & v3_orders_2(X0) )
       => ( v2_yellow_0(X0)
          & v1_lattice3(X0)
          & v3_orders_2(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc10_waybel_0)).

fof(f414,plain,
    ( ~ v2_yellow_0(sK6)
    | spl10_9 ),
    inference(avatar_component_clause,[],[f412])).

fof(f415,plain,
    ( spl10_6
    | ~ spl10_9
    | ~ spl10_1 ),
    inference(avatar_split_clause,[],[f410,f162,f412,f218])).

fof(f162,plain,
    ( spl10_1
  <=> sP0(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f410,plain,
    ( ~ v2_yellow_0(sK6)
    | v2_struct_0(sK6)
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f409,f108])).

fof(f409,plain,
    ( ~ v2_yellow_0(sK6)
    | v2_struct_0(sK6)
    | ~ v3_orders_2(sK6)
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f408,f114])).

fof(f408,plain,
    ( ~ v2_yellow_0(sK6)
    | ~ l1_orders_2(sK6)
    | v2_struct_0(sK6)
    | ~ v3_orders_2(sK6)
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f407,f110])).

fof(f407,plain,
    ( ~ v2_yellow_0(sK6)
    | ~ v5_orders_2(sK6)
    | ~ l1_orders_2(sK6)
    | v2_struct_0(sK6)
    | ~ v3_orders_2(sK6)
    | ~ spl10_1 ),
    inference(resolution,[],[f399,f164])).

fof(f164,plain,
    ( sP0(sK6)
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f162])).

fof(f399,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | ~ v2_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(resolution,[],[f390,f133])).

fof(f133,plain,(
    ! [X0] : m1_subset_1(sK7(X0),X0) ),
    inference(cnf_transformation,[],[f93])).

fof(f93,plain,(
    ! [X0] : m1_subset_1(sK7(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f11,f92])).

fof(f92,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK7(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f11,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f390,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X5,sK5(X4))
      | v2_struct_0(X4)
      | ~ v2_yellow_0(X4)
      | ~ v5_orders_2(X4)
      | ~ l1_orders_2(X4)
      | ~ sP0(X4)
      | ~ v3_orders_2(X4) ) ),
    inference(subsumption_resolution,[],[f389,f103])).

fof(f103,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK5(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f86,plain,(
    ! [X0] :
      ( ( ! [X2] :
            ( ~ r3_orders_2(X0,X2,k4_yellow_0(X0))
            | ~ r2_hidden(X2,sK5(X0))
            | ~ m1_subset_1(X2,u1_struct_0(X0)) )
        & r1_waybel_3(X0,k2_yellow_0(X0,sK5(X0)),k4_yellow_0(X0))
        & m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0)))
        & v1_finset_1(sK5(X0))
        & ~ v1_xboole_0(sK5(X0)) )
      | ~ sP0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f84,f85])).

fof(f85,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ~ r3_orders_2(X0,X2,k4_yellow_0(X0))
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & r1_waybel_3(X0,k2_yellow_0(X0,X1),k4_yellow_0(X0))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_finset_1(X1)
          & ~ v1_xboole_0(X1) )
     => ( ! [X2] :
            ( ~ r3_orders_2(X0,X2,k4_yellow_0(X0))
            | ~ r2_hidden(X2,sK5(X0))
            | ~ m1_subset_1(X2,u1_struct_0(X0)) )
        & r1_waybel_3(X0,k2_yellow_0(X0,sK5(X0)),k4_yellow_0(X0))
        & m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0)))
        & v1_finset_1(sK5(X0))
        & ~ v1_xboole_0(sK5(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f84,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ~ r3_orders_2(X0,X2,k4_yellow_0(X0))
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & r1_waybel_3(X0,k2_yellow_0(X0,X1),k4_yellow_0(X0))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_finset_1(X1)
          & ~ v1_xboole_0(X1) )
      | ~ sP0(X0) ) ),
    inference(nnf_transformation,[],[f75])).

fof(f389,plain,(
    ! [X4,X5] :
      ( ~ v3_orders_2(X4)
      | v2_struct_0(X4)
      | ~ v2_yellow_0(X4)
      | ~ v5_orders_2(X4)
      | ~ l1_orders_2(X4)
      | ~ sP0(X4)
      | v1_xboole_0(sK5(X4))
      | ~ m1_subset_1(X5,sK5(X4)) ) ),
    inference(resolution,[],[f386,f137])).

fof(f137,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f386,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK5(X1))
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1)
      | ~ v2_yellow_0(X1)
      | ~ v5_orders_2(X1)
      | ~ l1_orders_2(X1)
      | ~ sP0(X1) ) ),
    inference(subsumption_resolution,[],[f385,f203])).

fof(f203,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X3,sK5(X4))
      | m1_subset_1(X3,u1_struct_0(X4))
      | ~ sP0(X4) ) ),
    inference(resolution,[],[f159,f105])).

fof(f105,plain,(
    ! [X0] :
      ( m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f159,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f73])).

fof(f73,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f385,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1)
      | ~ v2_yellow_0(X1)
      | ~ v5_orders_2(X1)
      | ~ r2_hidden(X0,sK5(X1))
      | ~ sP0(X1) ) ),
    inference(resolution,[],[f384,f259])).

fof(f259,plain,(
    ! [X2,X0] :
      ( ~ r3_orders_2(X0,X2,k4_yellow_0(X0))
      | ~ r2_hidden(X2,sK5(X0))
      | ~ sP0(X0) ) ),
    inference(subsumption_resolution,[],[f107,f203])).

fof(f107,plain,(
    ! [X2,X0] :
      ( ~ r3_orders_2(X0,X2,k4_yellow_0(X0))
      | ~ r2_hidden(X2,sK5(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f384,plain,(
    ! [X0,X1] :
      ( r3_orders_2(X0,X1,k4_yellow_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v2_yellow_0(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f383,f117])).

fof(f383,plain,(
    ! [X0,X1] :
      ( r3_orders_2(X0,X1,k4_yellow_0(X0))
      | ~ m1_subset_1(k4_yellow_0(X0),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v2_yellow_0(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f380])).

fof(f380,plain,(
    ! [X0,X1] :
      ( r3_orders_2(X0,X1,k4_yellow_0(X0))
      | ~ m1_subset_1(k4_yellow_0(X0),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f151,f128])).

fof(f128,plain,(
    ! [X0,X1] :
      ( r1_orders_2(X0,X1,k4_yellow_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,X1,k4_yellow_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,X1,k4_yellow_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r1_orders_2(X0,X1,k4_yellow_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_yellow_0)).

fof(f151,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X1,X2)
      | r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f97])).

fof(f97,plain,(
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
    inference(nnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f69])).

fof(f69,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(f221,plain,
    ( spl10_5
    | spl10_6 ),
    inference(avatar_split_clause,[],[f212,f218,f214])).

fof(f212,plain,
    ( v2_struct_0(sK6)
    | v24_waybel_0(sK6) ),
    inference(subsumption_resolution,[],[f211,f114])).

fof(f211,plain,
    ( v2_struct_0(sK6)
    | ~ l1_orders_2(sK6)
    | v24_waybel_0(sK6) ),
    inference(subsumption_resolution,[],[f210,f108])).

fof(f210,plain,
    ( ~ v3_orders_2(sK6)
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6)
    | v24_waybel_0(sK6) ),
    inference(resolution,[],[f178,f113])).

fof(f113,plain,(
    v3_waybel_3(sK6) ),
    inference(cnf_transformation,[],[f88])).

fof(f178,plain,(
    ! [X1] :
      ( ~ v3_waybel_3(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X1)
      | v24_waybel_0(X1) ) ),
    inference(resolution,[],[f123,f121])).

fof(f121,plain,(
    ! [X0] :
      ( ~ sP1(X0)
      | v24_waybel_0(X0) ) ),
    inference(cnf_transformation,[],[f89])).

fof(f89,plain,(
    ! [X0] :
      ( ( v2_waybel_3(X0)
        & v24_waybel_0(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f77])).

fof(f77,plain,(
    ! [X0] :
      ( ( v2_waybel_3(X0)
        & v24_waybel_0(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f123,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v3_waybel_3(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v3_waybel_3(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f35,f77])).

fof(f35,plain,(
    ! [X0] :
      ( ( v2_waybel_3(X0)
        & v24_waybel_0(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
      | ~ v3_waybel_3(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( v2_waybel_3(X0)
        & v24_waybel_0(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
      | ~ v3_waybel_3(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( ( v3_waybel_3(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ( v2_waybel_3(X0)
          & v24_waybel_0(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_waybel_3)).

fof(f169,plain,
    ( spl10_1
    | spl10_2 ),
    inference(avatar_split_clause,[],[f116,f166,f162])).

fof(f116,plain,
    ( r2_subset_1(k4_waybel_0(sK6,k12_waybel_0(sK6,k3_subset_1(u1_struct_0(sK6),k5_waybel_0(sK6,k4_yellow_0(sK6))))),k1_waybel_3(sK6,k4_yellow_0(sK6)))
    | sP0(sK6) ),
    inference(cnf_transformation,[],[f88])).

%------------------------------------------------------------------------------
