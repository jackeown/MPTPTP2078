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
% DateTime   : Thu Dec  3 13:16:36 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  147 ( 315 expanded)
%              Number of leaves         :   32 ( 118 expanded)
%              Depth                    :   11
%              Number of atoms          :  459 ( 898 expanded)
%              Number of equality atoms :   57 ( 258 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f205,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f83,f155,f158,f172,f174,f177,f179,f181,f183,f185,f196,f198,f200,f202,f204])).

fof(f204,plain,(
    spl3_13 ),
    inference(avatar_contradiction_clause,[],[f203])).

fof(f203,plain,
    ( $false
    | spl3_13 ),
    inference(resolution,[],[f191,f89])).

fof(f89,plain,(
    r2_hidden(k2_xboole_0(sK1,sK2),k9_setfam_1(sK0)) ),
    inference(resolution,[],[f86,f67])).

fof(f67,plain,(
    m1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(sK0)))) ),
    inference(definition_unfolding,[],[f44,f47])).

fof(f47,plain,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_yellow_1)).

fof(f44,plain,(
    m1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0))) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,
    ( ( k3_xboole_0(sK1,sK2) != k12_lattice3(k3_yellow_1(sK0),sK1,sK2)
      | k2_xboole_0(sK1,sK2) != k13_lattice3(k3_yellow_1(sK0),sK1,sK2) )
    & m1_subset_1(sK2,u1_struct_0(k3_yellow_1(sK0)))
    & m1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f42,f41])).

fof(f41,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( k3_xboole_0(X1,X2) != k12_lattice3(k3_yellow_1(X0),X1,X2)
              | k2_xboole_0(X1,X2) != k13_lattice3(k3_yellow_1(X0),X1,X2) )
            & m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0))) )
        & m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) )
   => ( ? [X2] :
          ( ( k3_xboole_0(sK1,X2) != k12_lattice3(k3_yellow_1(sK0),sK1,X2)
            | k2_xboole_0(sK1,X2) != k13_lattice3(k3_yellow_1(sK0),sK1,X2) )
          & m1_subset_1(X2,u1_struct_0(k3_yellow_1(sK0))) )
      & m1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X2] :
        ( ( k3_xboole_0(sK1,X2) != k12_lattice3(k3_yellow_1(sK0),sK1,X2)
          | k2_xboole_0(sK1,X2) != k13_lattice3(k3_yellow_1(sK0),sK1,X2) )
        & m1_subset_1(X2,u1_struct_0(k3_yellow_1(sK0))) )
   => ( ( k3_xboole_0(sK1,sK2) != k12_lattice3(k3_yellow_1(sK0),sK1,sK2)
        | k2_xboole_0(sK1,sK2) != k13_lattice3(k3_yellow_1(sK0),sK1,sK2) )
      & m1_subset_1(sK2,u1_struct_0(k3_yellow_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( k3_xboole_0(X1,X2) != k12_lattice3(k3_yellow_1(X0),X1,X2)
            | k2_xboole_0(X1,X2) != k13_lattice3(k3_yellow_1(X0),X1,X2) )
          & m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0))) )
      & m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))
           => ( k3_xboole_0(X1,X2) = k12_lattice3(k3_yellow_1(X0),X1,X2)
              & k2_xboole_0(X1,X2) = k13_lattice3(k3_yellow_1(X0),X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))
         => ( k3_xboole_0(X1,X2) = k12_lattice3(k3_yellow_1(X0),X1,X2)
            & k2_xboole_0(X1,X2) = k13_lattice3(k3_yellow_1(X0),X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_yellow_1)).

fof(f86,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(sK0))))
      | r2_hidden(k2_xboole_0(X0,sK2),k9_setfam_1(sK0)) ) ),
    inference(resolution,[],[f73,f66])).

fof(f66,plain,(
    m1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(sK0)))) ),
    inference(definition_unfolding,[],[f45,f47])).

fof(f45,plain,(
    m1_subset_1(sK2,u1_struct_0(k3_yellow_1(sK0))) ),
    inference(cnf_transformation,[],[f43])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X0))))
      | r2_hidden(k2_xboole_0(X1,X2),k9_setfam_1(X0))
      | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0)))) ) ),
    inference(definition_unfolding,[],[f61,f47,f47])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_xboole_0(X1,X2),k9_setfam_1(X0))
      | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(k2_xboole_0(X1,X2),k9_setfam_1(X0))
            & r2_hidden(k3_xboole_0(X1,X2),k9_setfam_1(X0)) )
          | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0))) )
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))
         => ( r2_hidden(k2_xboole_0(X1,X2),k9_setfam_1(X0))
            & r2_hidden(k3_xboole_0(X1,X2),k9_setfam_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l19_yellow_1)).

fof(f191,plain,
    ( ~ r2_hidden(k2_xboole_0(sK1,sK2),k9_setfam_1(sK0))
    | spl3_13 ),
    inference(avatar_component_clause,[],[f189])).

fof(f189,plain,
    ( spl3_13
  <=> r2_hidden(k2_xboole_0(sK1,sK2),k9_setfam_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f202,plain,(
    ~ spl3_10 ),
    inference(avatar_contradiction_clause,[],[f201])).

fof(f201,plain,
    ( $false
    | ~ spl3_10 ),
    inference(resolution,[],[f163,f50])).

fof(f50,plain,(
    ! [X0] : ~ v2_struct_0(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] : ~ v2_struct_0(k1_lattice3(X0)) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v3_lattices(k1_lattice3(X0))
      & ~ v2_struct_0(k1_lattice3(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_lattice3)).

fof(f163,plain,
    ( v2_struct_0(k1_lattice3(sK0))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f161])).

fof(f161,plain,
    ( spl3_10
  <=> v2_struct_0(k1_lattice3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f200,plain,
    ( spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | spl3_14 ),
    inference(avatar_split_clause,[],[f199,f193,f169,f165,f161])).

fof(f165,plain,
    ( spl3_11
  <=> v10_lattices(k1_lattice3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f169,plain,
    ( spl3_12
  <=> l3_lattices(k1_lattice3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f193,plain,
    ( spl3_14
  <=> v1_lattice3(k3_lattice3(k1_lattice3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f199,plain,
    ( ~ l3_lattices(k1_lattice3(sK0))
    | ~ v10_lattices(k1_lattice3(sK0))
    | v2_struct_0(k1_lattice3(sK0))
    | spl3_14 ),
    inference(resolution,[],[f195,f58])).

fof(f58,plain,(
    ! [X0] :
      ( v1_lattice3(k3_lattice3(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( v2_lattice3(k3_lattice3(X0))
        & v1_lattice3(k3_lattice3(X0))
        & v5_orders_2(k3_lattice3(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( v2_lattice3(k3_lattice3(X0))
        & v1_lattice3(k3_lattice3(X0))
        & v5_orders_2(k3_lattice3(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_lattice3(k3_lattice3(X0))
        & v1_lattice3(k3_lattice3(X0))
        & v5_orders_2(k3_lattice3(X0)) ) ) ),
    inference(pure_predicate_removal,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_lattice3(k3_lattice3(X0))
        & v1_lattice3(k3_lattice3(X0))
        & v5_orders_2(k3_lattice3(X0))
        & v1_orders_2(k3_lattice3(X0)) ) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_lattice3(k3_lattice3(X0))
        & v1_lattice3(k3_lattice3(X0))
        & v5_orders_2(k3_lattice3(X0))
        & v3_orders_2(k3_lattice3(X0))
        & v1_orders_2(k3_lattice3(X0)) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_lattice3(k3_lattice3(X0))
        & v1_lattice3(k3_lattice3(X0))
        & v5_orders_2(k3_lattice3(X0))
        & v4_orders_2(k3_lattice3(X0))
        & v3_orders_2(k3_lattice3(X0))
        & v1_orders_2(k3_lattice3(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_yellow_1)).

fof(f195,plain,
    ( ~ v1_lattice3(k3_lattice3(k1_lattice3(sK0)))
    | spl3_14 ),
    inference(avatar_component_clause,[],[f193])).

fof(f198,plain,(
    ~ spl3_3 ),
    inference(avatar_contradiction_clause,[],[f197])).

fof(f197,plain,
    ( $false
    | ~ spl3_3 ),
    inference(resolution,[],[f130,f90])).

fof(f90,plain,(
    ~ v1_xboole_0(k9_setfam_1(sK0)) ),
    inference(resolution,[],[f88,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

fof(f88,plain,(
    r2_hidden(k2_xboole_0(sK2,sK2),k9_setfam_1(sK0)) ),
    inference(resolution,[],[f86,f66])).

fof(f130,plain,
    ( v1_xboole_0(k9_setfam_1(sK0))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl3_3
  <=> v1_xboole_0(k9_setfam_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f196,plain,
    ( spl3_3
    | ~ spl3_13
    | ~ spl3_5
    | ~ spl3_14
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_9
    | spl3_1 ),
    inference(avatar_split_clause,[],[f187,f76,f152,f148,f144,f193,f136,f189,f128])).

fof(f136,plain,
    ( spl3_5
  <=> v5_orders_2(k3_lattice3(k1_lattice3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f144,plain,
    ( spl3_7
  <=> l1_orders_2(k3_lattice3(k1_lattice3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f148,plain,
    ( spl3_8
  <=> m1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f152,plain,
    ( spl3_9
  <=> m1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f76,plain,
    ( spl3_1
  <=> k2_xboole_0(sK1,sK2) = k13_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f187,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(sK0))))
    | ~ m1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(sK0))))
    | ~ l1_orders_2(k3_lattice3(k1_lattice3(sK0)))
    | ~ v1_lattice3(k3_lattice3(k1_lattice3(sK0)))
    | ~ v5_orders_2(k3_lattice3(k1_lattice3(sK0)))
    | ~ r2_hidden(k2_xboole_0(sK1,sK2),k9_setfam_1(sK0))
    | v1_xboole_0(k9_setfam_1(sK0))
    | spl3_1 ),
    inference(trivial_inequality_removal,[],[f186])).

fof(f186,plain,
    ( k2_xboole_0(sK1,sK2) != k2_xboole_0(sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(sK0))))
    | ~ m1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(sK0))))
    | ~ l1_orders_2(k3_lattice3(k1_lattice3(sK0)))
    | ~ v1_lattice3(k3_lattice3(k1_lattice3(sK0)))
    | ~ v5_orders_2(k3_lattice3(k1_lattice3(sK0)))
    | ~ r2_hidden(k2_xboole_0(sK1,sK2),k9_setfam_1(sK0))
    | v1_xboole_0(k9_setfam_1(sK0))
    | spl3_1 ),
    inference(superposition,[],[f78,f122])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k13_lattice3(k3_lattice3(k1_lattice3(X0)),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X0))))
      | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0))))
      | ~ l1_orders_2(k3_lattice3(k1_lattice3(X0)))
      | ~ v1_lattice3(k3_lattice3(k1_lattice3(X0)))
      | ~ v5_orders_2(k3_lattice3(k1_lattice3(X0)))
      | ~ r2_hidden(k2_xboole_0(X1,X2),k9_setfam_1(X0))
      | v1_xboole_0(k9_setfam_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f121])).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k13_lattice3(k3_lattice3(k1_lattice3(X0)),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X0))))
      | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0))))
      | ~ l1_orders_2(k3_lattice3(k1_lattice3(X0)))
      | ~ v1_lattice3(k3_lattice3(k1_lattice3(X0)))
      | ~ v5_orders_2(k3_lattice3(k1_lattice3(X0)))
      | ~ r2_hidden(k2_xboole_0(X1,X2),k9_setfam_1(X0))
      | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X0))))
      | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0))))
      | v1_xboole_0(k9_setfam_1(X0)) ) ),
    inference(superposition,[],[f63,f107])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k10_lattice3(k3_lattice3(k1_lattice3(X0)),X1,X2)
      | ~ r2_hidden(k2_xboole_0(X1,X2),k9_setfam_1(X0))
      | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X0))))
      | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0))))
      | v1_xboole_0(k9_setfam_1(X0)) ) ),
    inference(superposition,[],[f72,f68])).

fof(f68,plain,(
    ! [X0] : k3_lattice3(k1_lattice3(X0)) = g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))) ),
    inference(definition_unfolding,[],[f48,f47,f49])).

fof(f49,plain,(
    ! [X0] : k2_yellow_1(X0) = g1_orders_2(X0,k1_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_yellow_1(X0) = g1_orders_2(X0,k1_yellow_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_yellow_1)).

fof(f48,plain,(
    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_yellow_1)).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k10_lattice3(g1_orders_2(X0,k1_yellow_1(X0)),X1,X2)
      | ~ r2_hidden(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))))
      | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))))
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f56,f49,f49,f49])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k10_lattice3(k2_yellow_1(X0),X1,X2)
      | ~ r2_hidden(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_xboole_0(X1,X2) = k10_lattice3(k2_yellow_1(X0),X1,X2)
              | ~ r2_hidden(k2_xboole_0(X1,X2),X0)
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_xboole_0(X1,X2) = k10_lattice3(k2_yellow_1(X0),X1,X2)
              | ~ r2_hidden(k2_xboole_0(X1,X2),X0)
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
             => ( r2_hidden(k2_xboole_0(X1,X2),X0)
               => k2_xboole_0(X1,X2) = k10_lattice3(k2_yellow_1(X0),X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_yellow_1)).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k13_lattice3)).

fof(f78,plain,
    ( k2_xboole_0(sK1,sK2) != k13_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f76])).

fof(f185,plain,(
    spl3_9 ),
    inference(avatar_contradiction_clause,[],[f184])).

fof(f184,plain,
    ( $false
    | spl3_9 ),
    inference(resolution,[],[f154,f66])).

fof(f154,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(sK0))))
    | spl3_9 ),
    inference(avatar_component_clause,[],[f152])).

fof(f183,plain,(
    spl3_8 ),
    inference(avatar_contradiction_clause,[],[f182])).

fof(f182,plain,
    ( $false
    | spl3_8 ),
    inference(resolution,[],[f150,f67])).

fof(f150,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(sK0))))
    | spl3_8 ),
    inference(avatar_component_clause,[],[f148])).

fof(f181,plain,(
    spl3_4 ),
    inference(avatar_contradiction_clause,[],[f180])).

fof(f180,plain,
    ( $false
    | spl3_4 ),
    inference(resolution,[],[f134,f99])).

fof(f99,plain,(
    r2_hidden(k3_xboole_0(sK1,sK2),k9_setfam_1(sK0)) ),
    inference(resolution,[],[f91,f67])).

fof(f91,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(sK0))))
      | r2_hidden(k3_xboole_0(X0,sK2),k9_setfam_1(sK0)) ) ),
    inference(resolution,[],[f74,f66])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X0))))
      | r2_hidden(k3_xboole_0(X1,X2),k9_setfam_1(X0))
      | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0)))) ) ),
    inference(definition_unfolding,[],[f60,f47,f47])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k3_xboole_0(X1,X2),k9_setfam_1(X0))
      | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f134,plain,
    ( ~ r2_hidden(k3_xboole_0(sK1,sK2),k9_setfam_1(sK0))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl3_4
  <=> r2_hidden(k3_xboole_0(sK1,sK2),k9_setfam_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f179,plain,(
    spl3_7 ),
    inference(avatar_contradiction_clause,[],[f178])).

fof(f178,plain,
    ( $false
    | spl3_7 ),
    inference(resolution,[],[f146,f85])).

fof(f85,plain,(
    ! [X1] : l1_orders_2(k3_lattice3(k1_lattice3(X1))) ),
    inference(superposition,[],[f69,f68])).

fof(f69,plain,(
    ! [X0] : l1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) ),
    inference(definition_unfolding,[],[f53,f49])).

fof(f53,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).

fof(f146,plain,
    ( ~ l1_orders_2(k3_lattice3(k1_lattice3(sK0)))
    | spl3_7 ),
    inference(avatar_component_clause,[],[f144])).

fof(f177,plain,(
    spl3_12 ),
    inference(avatar_contradiction_clause,[],[f176])).

fof(f176,plain,
    ( $false
    | spl3_12 ),
    inference(resolution,[],[f171,f51])).

fof(f51,plain,(
    ! [X0] : l3_lattices(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] : l3_lattices(k1_lattice3(X0)) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l3_lattices(k1_lattice3(X0))
      & v3_lattices(k1_lattice3(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_lattice3)).

fof(f171,plain,
    ( ~ l3_lattices(k1_lattice3(sK0))
    | spl3_12 ),
    inference(avatar_component_clause,[],[f169])).

fof(f174,plain,(
    spl3_11 ),
    inference(avatar_contradiction_clause,[],[f173])).

fof(f173,plain,
    ( $false
    | spl3_11 ),
    inference(resolution,[],[f167,f52])).

fof(f52,plain,(
    ! [X0] : v10_lattices(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] : v10_lattices(k1_lattice3(X0)) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v10_lattices(k1_lattice3(X0))
      & v3_lattices(k1_lattice3(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_lattice3)).

fof(f167,plain,
    ( ~ v10_lattices(k1_lattice3(sK0))
    | spl3_11 ),
    inference(avatar_component_clause,[],[f165])).

fof(f172,plain,
    ( spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | spl3_6 ),
    inference(avatar_split_clause,[],[f159,f140,f169,f165,f161])).

fof(f140,plain,
    ( spl3_6
  <=> v2_lattice3(k3_lattice3(k1_lattice3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f159,plain,
    ( ~ l3_lattices(k1_lattice3(sK0))
    | ~ v10_lattices(k1_lattice3(sK0))
    | v2_struct_0(k1_lattice3(sK0))
    | spl3_6 ),
    inference(resolution,[],[f142,f59])).

fof(f59,plain,(
    ! [X0] :
      ( v2_lattice3(k3_lattice3(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f142,plain,
    ( ~ v2_lattice3(k3_lattice3(k1_lattice3(sK0)))
    | spl3_6 ),
    inference(avatar_component_clause,[],[f140])).

fof(f158,plain,(
    spl3_5 ),
    inference(avatar_contradiction_clause,[],[f156])).

fof(f156,plain,
    ( $false
    | spl3_5 ),
    inference(resolution,[],[f138,f84])).

fof(f84,plain,(
    ! [X0] : v5_orders_2(k3_lattice3(k1_lattice3(X0))) ),
    inference(superposition,[],[f70,f68])).

fof(f70,plain,(
    ! [X0] : v5_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) ),
    inference(definition_unfolding,[],[f54,f49])).

fof(f54,plain,(
    ! [X0] : v5_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] : v5_orders_2(k2_yellow_1(X0)) ),
    inference(pure_predicate_removal,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v4_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow_1)).

fof(f138,plain,
    ( ~ v5_orders_2(k3_lattice3(k1_lattice3(sK0)))
    | spl3_5 ),
    inference(avatar_component_clause,[],[f136])).

fof(f155,plain,
    ( spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_9
    | spl3_2 ),
    inference(avatar_split_clause,[],[f126,f80,f152,f148,f144,f140,f136,f132,f128])).

fof(f80,plain,
    ( spl3_2
  <=> k3_xboole_0(sK1,sK2) = k12_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f126,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(sK0))))
    | ~ m1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(sK0))))
    | ~ l1_orders_2(k3_lattice3(k1_lattice3(sK0)))
    | ~ v2_lattice3(k3_lattice3(k1_lattice3(sK0)))
    | ~ v5_orders_2(k3_lattice3(k1_lattice3(sK0)))
    | ~ r2_hidden(k3_xboole_0(sK1,sK2),k9_setfam_1(sK0))
    | v1_xboole_0(k9_setfam_1(sK0))
    | spl3_2 ),
    inference(trivial_inequality_removal,[],[f125])).

fof(f125,plain,
    ( k3_xboole_0(sK1,sK2) != k3_xboole_0(sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(sK0))))
    | ~ m1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(sK0))))
    | ~ l1_orders_2(k3_lattice3(k1_lattice3(sK0)))
    | ~ v2_lattice3(k3_lattice3(k1_lattice3(sK0)))
    | ~ v5_orders_2(k3_lattice3(k1_lattice3(sK0)))
    | ~ r2_hidden(k3_xboole_0(sK1,sK2),k9_setfam_1(sK0))
    | v1_xboole_0(k9_setfam_1(sK0))
    | spl3_2 ),
    inference(superposition,[],[f82,f117])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k12_lattice3(k3_lattice3(k1_lattice3(X0)),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X0))))
      | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0))))
      | ~ l1_orders_2(k3_lattice3(k1_lattice3(X0)))
      | ~ v2_lattice3(k3_lattice3(k1_lattice3(X0)))
      | ~ v5_orders_2(k3_lattice3(k1_lattice3(X0)))
      | ~ r2_hidden(k3_xboole_0(X1,X2),k9_setfam_1(X0))
      | v1_xboole_0(k9_setfam_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f116])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k12_lattice3(k3_lattice3(k1_lattice3(X0)),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X0))))
      | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0))))
      | ~ l1_orders_2(k3_lattice3(k1_lattice3(X0)))
      | ~ v2_lattice3(k3_lattice3(k1_lattice3(X0)))
      | ~ v5_orders_2(k3_lattice3(k1_lattice3(X0)))
      | ~ r2_hidden(k3_xboole_0(X1,X2),k9_setfam_1(X0))
      | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X0))))
      | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0))))
      | v1_xboole_0(k9_setfam_1(X0)) ) ),
    inference(superposition,[],[f64,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k11_lattice3(k3_lattice3(k1_lattice3(X0)),X1,X2)
      | ~ r2_hidden(k3_xboole_0(X1,X2),k9_setfam_1(X0))
      | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X0))))
      | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0))))
      | v1_xboole_0(k9_setfam_1(X0)) ) ),
    inference(superposition,[],[f71,f68])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k11_lattice3(g1_orders_2(X0,k1_yellow_1(X0)),X1,X2)
      | ~ r2_hidden(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))))
      | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))))
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f55,f49,f49,f49])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k11_lattice3(k2_yellow_1(X0),X1,X2)
      | ~ r2_hidden(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k3_xboole_0(X1,X2) = k11_lattice3(k2_yellow_1(X0),X1,X2)
              | ~ r2_hidden(k3_xboole_0(X1,X2),X0)
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k3_xboole_0(X1,X2) = k11_lattice3(k2_yellow_1(X0),X1,X2)
              | ~ r2_hidden(k3_xboole_0(X1,X2),X0)
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
             => ( r2_hidden(k3_xboole_0(X1,X2),X0)
               => k3_xboole_0(X1,X2) = k11_lattice3(k2_yellow_1(X0),X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_yellow_1)).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

fof(f82,plain,
    ( k3_xboole_0(sK1,sK2) != k12_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f80])).

fof(f83,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f65,f80,f76])).

fof(f65,plain,
    ( k3_xboole_0(sK1,sK2) != k12_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2)
    | k2_xboole_0(sK1,sK2) != k13_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) ),
    inference(definition_unfolding,[],[f46,f47,f47])).

fof(f46,plain,
    ( k3_xboole_0(sK1,sK2) != k12_lattice3(k3_yellow_1(sK0),sK1,sK2)
    | k2_xboole_0(sK1,sK2) != k13_lattice3(k3_yellow_1(sK0),sK1,sK2) ),
    inference(cnf_transformation,[],[f43])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:11:30 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.43  % (20238)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.44  % (20238)Refutation found. Thanks to Tanya!
% 0.22/0.44  % SZS status Theorem for theBenchmark
% 0.22/0.44  % SZS output start Proof for theBenchmark
% 0.22/0.44  fof(f205,plain,(
% 0.22/0.44    $false),
% 0.22/0.44    inference(avatar_sat_refutation,[],[f83,f155,f158,f172,f174,f177,f179,f181,f183,f185,f196,f198,f200,f202,f204])).
% 0.22/0.44  fof(f204,plain,(
% 0.22/0.44    spl3_13),
% 0.22/0.44    inference(avatar_contradiction_clause,[],[f203])).
% 0.22/0.44  fof(f203,plain,(
% 0.22/0.44    $false | spl3_13),
% 0.22/0.44    inference(resolution,[],[f191,f89])).
% 0.22/0.44  fof(f89,plain,(
% 0.22/0.44    r2_hidden(k2_xboole_0(sK1,sK2),k9_setfam_1(sK0))),
% 0.22/0.44    inference(resolution,[],[f86,f67])).
% 0.22/0.44  fof(f67,plain,(
% 0.22/0.44    m1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(sK0))))),
% 0.22/0.44    inference(definition_unfolding,[],[f44,f47])).
% 0.22/0.44  fof(f47,plain,(
% 0.22/0.44    ( ! [X0] : (k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f8])).
% 0.22/0.44  fof(f8,axiom,(
% 0.22/0.44    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_yellow_1)).
% 0.22/0.44  fof(f44,plain,(
% 0.22/0.44    m1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0)))),
% 0.22/0.44    inference(cnf_transformation,[],[f43])).
% 0.22/0.44  fof(f43,plain,(
% 0.22/0.44    ((k3_xboole_0(sK1,sK2) != k12_lattice3(k3_yellow_1(sK0),sK1,sK2) | k2_xboole_0(sK1,sK2) != k13_lattice3(k3_yellow_1(sK0),sK1,sK2)) & m1_subset_1(sK2,u1_struct_0(k3_yellow_1(sK0)))) & m1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0)))),
% 0.22/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f42,f41])).
% 0.22/0.44  fof(f41,plain,(
% 0.22/0.44    ? [X0,X1] : (? [X2] : ((k3_xboole_0(X1,X2) != k12_lattice3(k3_yellow_1(X0),X1,X2) | k2_xboole_0(X1,X2) != k13_lattice3(k3_yellow_1(X0),X1,X2)) & m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))) => (? [X2] : ((k3_xboole_0(sK1,X2) != k12_lattice3(k3_yellow_1(sK0),sK1,X2) | k2_xboole_0(sK1,X2) != k13_lattice3(k3_yellow_1(sK0),sK1,X2)) & m1_subset_1(X2,u1_struct_0(k3_yellow_1(sK0)))) & m1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0))))),
% 0.22/0.44    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f42,plain,(
% 0.22/0.44    ? [X2] : ((k3_xboole_0(sK1,X2) != k12_lattice3(k3_yellow_1(sK0),sK1,X2) | k2_xboole_0(sK1,X2) != k13_lattice3(k3_yellow_1(sK0),sK1,X2)) & m1_subset_1(X2,u1_struct_0(k3_yellow_1(sK0)))) => ((k3_xboole_0(sK1,sK2) != k12_lattice3(k3_yellow_1(sK0),sK1,sK2) | k2_xboole_0(sK1,sK2) != k13_lattice3(k3_yellow_1(sK0),sK1,sK2)) & m1_subset_1(sK2,u1_struct_0(k3_yellow_1(sK0))))),
% 0.22/0.44    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f28,plain,(
% 0.22/0.44    ? [X0,X1] : (? [X2] : ((k3_xboole_0(X1,X2) != k12_lattice3(k3_yellow_1(X0),X1,X2) | k2_xboole_0(X1,X2) != k13_lattice3(k3_yellow_1(X0),X1,X2)) & m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))))),
% 0.22/0.44    inference(ennf_transformation,[],[f17])).
% 0.22/0.44  fof(f17,negated_conjecture,(
% 0.22/0.44    ~! [X0,X1] : (m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0))) => (k3_xboole_0(X1,X2) = k12_lattice3(k3_yellow_1(X0),X1,X2) & k2_xboole_0(X1,X2) = k13_lattice3(k3_yellow_1(X0),X1,X2))))),
% 0.22/0.44    inference(negated_conjecture,[],[f16])).
% 0.22/0.44  fof(f16,conjecture,(
% 0.22/0.44    ! [X0,X1] : (m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0))) => (k3_xboole_0(X1,X2) = k12_lattice3(k3_yellow_1(X0),X1,X2) & k2_xboole_0(X1,X2) = k13_lattice3(k3_yellow_1(X0),X1,X2))))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_yellow_1)).
% 0.22/0.44  fof(f86,plain,(
% 0.22/0.44    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(sK0)))) | r2_hidden(k2_xboole_0(X0,sK2),k9_setfam_1(sK0))) )),
% 0.22/0.44    inference(resolution,[],[f73,f66])).
% 0.22/0.44  fof(f66,plain,(
% 0.22/0.44    m1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(sK0))))),
% 0.22/0.44    inference(definition_unfolding,[],[f45,f47])).
% 0.22/0.44  fof(f45,plain,(
% 0.22/0.44    m1_subset_1(sK2,u1_struct_0(k3_yellow_1(sK0)))),
% 0.22/0.44    inference(cnf_transformation,[],[f43])).
% 0.22/0.44  fof(f73,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X0)))) | r2_hidden(k2_xboole_0(X1,X2),k9_setfam_1(X0)) | ~m1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0))))) )),
% 0.22/0.44    inference(definition_unfolding,[],[f61,f47,f47])).
% 0.22/0.44  fof(f61,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (r2_hidden(k2_xboole_0(X1,X2),k9_setfam_1(X0)) | ~m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f35])).
% 0.22/0.44  fof(f35,plain,(
% 0.22/0.44    ! [X0,X1] : (! [X2] : ((r2_hidden(k2_xboole_0(X1,X2),k9_setfam_1(X0)) & r2_hidden(k3_xboole_0(X1,X2),k9_setfam_1(X0))) | ~m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))))),
% 0.22/0.44    inference(ennf_transformation,[],[f12])).
% 0.22/0.44  fof(f12,axiom,(
% 0.22/0.44    ! [X0,X1] : (m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0))) => (r2_hidden(k2_xboole_0(X1,X2),k9_setfam_1(X0)) & r2_hidden(k3_xboole_0(X1,X2),k9_setfam_1(X0)))))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l19_yellow_1)).
% 0.22/0.44  fof(f191,plain,(
% 0.22/0.44    ~r2_hidden(k2_xboole_0(sK1,sK2),k9_setfam_1(sK0)) | spl3_13),
% 0.22/0.44    inference(avatar_component_clause,[],[f189])).
% 0.22/0.44  fof(f189,plain,(
% 0.22/0.44    spl3_13 <=> r2_hidden(k2_xboole_0(sK1,sK2),k9_setfam_1(sK0))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.22/0.44  fof(f202,plain,(
% 0.22/0.44    ~spl3_10),
% 0.22/0.44    inference(avatar_contradiction_clause,[],[f201])).
% 0.22/0.44  fof(f201,plain,(
% 0.22/0.44    $false | ~spl3_10),
% 0.22/0.44    inference(resolution,[],[f163,f50])).
% 0.22/0.44  fof(f50,plain,(
% 0.22/0.44    ( ! [X0] : (~v2_struct_0(k1_lattice3(X0))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f27])).
% 0.22/0.44  fof(f27,plain,(
% 0.22/0.44    ! [X0] : ~v2_struct_0(k1_lattice3(X0))),
% 0.22/0.44    inference(pure_predicate_removal,[],[f3])).
% 0.22/0.44  fof(f3,axiom,(
% 0.22/0.44    ! [X0] : (v3_lattices(k1_lattice3(X0)) & ~v2_struct_0(k1_lattice3(X0)))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_lattice3)).
% 0.22/0.44  fof(f163,plain,(
% 0.22/0.44    v2_struct_0(k1_lattice3(sK0)) | ~spl3_10),
% 0.22/0.44    inference(avatar_component_clause,[],[f161])).
% 0.22/0.44  fof(f161,plain,(
% 0.22/0.44    spl3_10 <=> v2_struct_0(k1_lattice3(sK0))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.44  fof(f200,plain,(
% 0.22/0.44    spl3_10 | ~spl3_11 | ~spl3_12 | spl3_14),
% 0.22/0.44    inference(avatar_split_clause,[],[f199,f193,f169,f165,f161])).
% 0.22/0.44  fof(f165,plain,(
% 0.22/0.44    spl3_11 <=> v10_lattices(k1_lattice3(sK0))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.44  fof(f169,plain,(
% 0.22/0.44    spl3_12 <=> l3_lattices(k1_lattice3(sK0))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.22/0.44  fof(f193,plain,(
% 0.22/0.44    spl3_14 <=> v1_lattice3(k3_lattice3(k1_lattice3(sK0)))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.22/0.44  fof(f199,plain,(
% 0.22/0.44    ~l3_lattices(k1_lattice3(sK0)) | ~v10_lattices(k1_lattice3(sK0)) | v2_struct_0(k1_lattice3(sK0)) | spl3_14),
% 0.22/0.44    inference(resolution,[],[f195,f58])).
% 0.22/0.44  fof(f58,plain,(
% 0.22/0.44    ( ! [X0] : (v1_lattice3(k3_lattice3(X0)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f34])).
% 0.22/0.44  fof(f34,plain,(
% 0.22/0.44    ! [X0] : ((v2_lattice3(k3_lattice3(X0)) & v1_lattice3(k3_lattice3(X0)) & v5_orders_2(k3_lattice3(X0))) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.44    inference(flattening,[],[f33])).
% 0.22/0.44  fof(f33,plain,(
% 0.22/0.44    ! [X0] : ((v2_lattice3(k3_lattice3(X0)) & v1_lattice3(k3_lattice3(X0)) & v5_orders_2(k3_lattice3(X0))) | (~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.44    inference(ennf_transformation,[],[f22])).
% 0.22/0.44  fof(f22,plain,(
% 0.22/0.44    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (v2_lattice3(k3_lattice3(X0)) & v1_lattice3(k3_lattice3(X0)) & v5_orders_2(k3_lattice3(X0))))),
% 0.22/0.44    inference(pure_predicate_removal,[],[f21])).
% 0.22/0.44  fof(f21,plain,(
% 0.22/0.44    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (v2_lattice3(k3_lattice3(X0)) & v1_lattice3(k3_lattice3(X0)) & v5_orders_2(k3_lattice3(X0)) & v1_orders_2(k3_lattice3(X0))))),
% 0.22/0.44    inference(pure_predicate_removal,[],[f18])).
% 0.22/0.44  fof(f18,plain,(
% 0.22/0.44    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (v2_lattice3(k3_lattice3(X0)) & v1_lattice3(k3_lattice3(X0)) & v5_orders_2(k3_lattice3(X0)) & v3_orders_2(k3_lattice3(X0)) & v1_orders_2(k3_lattice3(X0))))),
% 0.22/0.44    inference(pure_predicate_removal,[],[f10])).
% 0.22/0.44  fof(f10,axiom,(
% 0.22/0.44    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (v2_lattice3(k3_lattice3(X0)) & v1_lattice3(k3_lattice3(X0)) & v5_orders_2(k3_lattice3(X0)) & v4_orders_2(k3_lattice3(X0)) & v3_orders_2(k3_lattice3(X0)) & v1_orders_2(k3_lattice3(X0))))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_yellow_1)).
% 0.22/0.44  fof(f195,plain,(
% 0.22/0.44    ~v1_lattice3(k3_lattice3(k1_lattice3(sK0))) | spl3_14),
% 0.22/0.44    inference(avatar_component_clause,[],[f193])).
% 0.22/0.44  fof(f198,plain,(
% 0.22/0.44    ~spl3_3),
% 0.22/0.44    inference(avatar_contradiction_clause,[],[f197])).
% 0.22/0.44  fof(f197,plain,(
% 0.22/0.44    $false | ~spl3_3),
% 0.22/0.44    inference(resolution,[],[f130,f90])).
% 0.22/0.44  fof(f90,plain,(
% 0.22/0.44    ~v1_xboole_0(k9_setfam_1(sK0))),
% 0.22/0.44    inference(resolution,[],[f88,f62])).
% 0.22/0.44  fof(f62,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~v1_xboole_0(X1)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f36])).
% 0.22/0.44  fof(f36,plain,(
% 0.22/0.44    ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1))),
% 0.22/0.44    inference(ennf_transformation,[],[f1])).
% 0.22/0.44  fof(f1,axiom,(
% 0.22/0.44    ! [X0,X1] : ~(v1_xboole_0(X1) & r2_hidden(X0,X1))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).
% 0.22/0.44  fof(f88,plain,(
% 0.22/0.44    r2_hidden(k2_xboole_0(sK2,sK2),k9_setfam_1(sK0))),
% 0.22/0.44    inference(resolution,[],[f86,f66])).
% 0.22/0.44  fof(f130,plain,(
% 0.22/0.44    v1_xboole_0(k9_setfam_1(sK0)) | ~spl3_3),
% 0.22/0.44    inference(avatar_component_clause,[],[f128])).
% 0.22/0.44  fof(f128,plain,(
% 0.22/0.44    spl3_3 <=> v1_xboole_0(k9_setfam_1(sK0))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.44  fof(f196,plain,(
% 0.22/0.44    spl3_3 | ~spl3_13 | ~spl3_5 | ~spl3_14 | ~spl3_7 | ~spl3_8 | ~spl3_9 | spl3_1),
% 0.22/0.44    inference(avatar_split_clause,[],[f187,f76,f152,f148,f144,f193,f136,f189,f128])).
% 0.22/0.44  fof(f136,plain,(
% 0.22/0.44    spl3_5 <=> v5_orders_2(k3_lattice3(k1_lattice3(sK0)))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.44  fof(f144,plain,(
% 0.22/0.44    spl3_7 <=> l1_orders_2(k3_lattice3(k1_lattice3(sK0)))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.44  fof(f148,plain,(
% 0.22/0.44    spl3_8 <=> m1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(sK0))))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.44  fof(f152,plain,(
% 0.22/0.44    spl3_9 <=> m1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(sK0))))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.44  fof(f76,plain,(
% 0.22/0.44    spl3_1 <=> k2_xboole_0(sK1,sK2) = k13_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.44  fof(f187,plain,(
% 0.22/0.44    ~m1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(sK0)))) | ~m1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(sK0)))) | ~l1_orders_2(k3_lattice3(k1_lattice3(sK0))) | ~v1_lattice3(k3_lattice3(k1_lattice3(sK0))) | ~v5_orders_2(k3_lattice3(k1_lattice3(sK0))) | ~r2_hidden(k2_xboole_0(sK1,sK2),k9_setfam_1(sK0)) | v1_xboole_0(k9_setfam_1(sK0)) | spl3_1),
% 0.22/0.44    inference(trivial_inequality_removal,[],[f186])).
% 0.22/0.44  fof(f186,plain,(
% 0.22/0.44    k2_xboole_0(sK1,sK2) != k2_xboole_0(sK1,sK2) | ~m1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(sK0)))) | ~m1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(sK0)))) | ~l1_orders_2(k3_lattice3(k1_lattice3(sK0))) | ~v1_lattice3(k3_lattice3(k1_lattice3(sK0))) | ~v5_orders_2(k3_lattice3(k1_lattice3(sK0))) | ~r2_hidden(k2_xboole_0(sK1,sK2),k9_setfam_1(sK0)) | v1_xboole_0(k9_setfam_1(sK0)) | spl3_1),
% 0.22/0.44    inference(superposition,[],[f78,f122])).
% 0.22/0.44  fof(f122,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k13_lattice3(k3_lattice3(k1_lattice3(X0)),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X0)))) | ~m1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0)))) | ~l1_orders_2(k3_lattice3(k1_lattice3(X0))) | ~v1_lattice3(k3_lattice3(k1_lattice3(X0))) | ~v5_orders_2(k3_lattice3(k1_lattice3(X0))) | ~r2_hidden(k2_xboole_0(X1,X2),k9_setfam_1(X0)) | v1_xboole_0(k9_setfam_1(X0))) )),
% 0.22/0.44    inference(duplicate_literal_removal,[],[f121])).
% 0.22/0.44  fof(f121,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k13_lattice3(k3_lattice3(k1_lattice3(X0)),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X0)))) | ~m1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0)))) | ~l1_orders_2(k3_lattice3(k1_lattice3(X0))) | ~v1_lattice3(k3_lattice3(k1_lattice3(X0))) | ~v5_orders_2(k3_lattice3(k1_lattice3(X0))) | ~r2_hidden(k2_xboole_0(X1,X2),k9_setfam_1(X0)) | ~m1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X0)))) | ~m1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0)))) | v1_xboole_0(k9_setfam_1(X0))) )),
% 0.22/0.44    inference(superposition,[],[f63,f107])).
% 0.22/0.44  fof(f107,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k10_lattice3(k3_lattice3(k1_lattice3(X0)),X1,X2) | ~r2_hidden(k2_xboole_0(X1,X2),k9_setfam_1(X0)) | ~m1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X0)))) | ~m1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0)))) | v1_xboole_0(k9_setfam_1(X0))) )),
% 0.22/0.44    inference(superposition,[],[f72,f68])).
% 0.22/0.44  fof(f68,plain,(
% 0.22/0.44    ( ! [X0] : (k3_lattice3(k1_lattice3(X0)) = g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0)))) )),
% 0.22/0.44    inference(definition_unfolding,[],[f48,f47,f49])).
% 0.22/0.44  fof(f49,plain,(
% 0.22/0.44    ( ! [X0] : (k2_yellow_1(X0) = g1_orders_2(X0,k1_yellow_1(X0))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f7])).
% 0.22/0.44  fof(f7,axiom,(
% 0.22/0.44    ! [X0] : k2_yellow_1(X0) = g1_orders_2(X0,k1_yellow_1(X0))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_yellow_1)).
% 0.22/0.44  fof(f48,plain,(
% 0.22/0.44    ( ! [X0] : (k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f13])).
% 0.22/0.44  fof(f13,axiom,(
% 0.22/0.44    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_yellow_1)).
% 0.22/0.44  fof(f72,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k10_lattice3(g1_orders_2(X0,k1_yellow_1(X0)),X1,X2) | ~r2_hidden(k2_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0)))) | v1_xboole_0(X0)) )),
% 0.22/0.44    inference(definition_unfolding,[],[f56,f49,f49,f49])).
% 0.22/0.44  fof(f56,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k10_lattice3(k2_yellow_1(X0),X1,X2) | ~r2_hidden(k2_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f32])).
% 0.22/0.44  fof(f32,plain,(
% 0.22/0.44    ! [X0] : (! [X1] : (! [X2] : (k2_xboole_0(X1,X2) = k10_lattice3(k2_yellow_1(X0),X1,X2) | ~r2_hidden(k2_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 0.22/0.44    inference(flattening,[],[f31])).
% 0.22/0.44  fof(f31,plain,(
% 0.22/0.44    ! [X0] : (! [X1] : (! [X2] : ((k2_xboole_0(X1,X2) = k10_lattice3(k2_yellow_1(X0),X1,X2) | ~r2_hidden(k2_xboole_0(X1,X2),X0)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 0.22/0.44    inference(ennf_transformation,[],[f14])).
% 0.22/0.44  fof(f14,axiom,(
% 0.22/0.44    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => (r2_hidden(k2_xboole_0(X1,X2),X0) => k2_xboole_0(X1,X2) = k10_lattice3(k2_yellow_1(X0),X1,X2)))))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_yellow_1)).
% 0.22/0.44  fof(f63,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f38])).
% 0.22/0.44  fof(f38,plain,(
% 0.22/0.44    ! [X0,X1,X2] : (k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0))),
% 0.22/0.44    inference(flattening,[],[f37])).
% 0.22/0.44  fof(f37,plain,(
% 0.22/0.44    ! [X0,X1,X2] : (k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)))),
% 0.22/0.44    inference(ennf_transformation,[],[f6])).
% 0.22/0.44  fof(f6,axiom,(
% 0.22/0.44    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0)) => k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k13_lattice3)).
% 0.22/0.44  fof(f78,plain,(
% 0.22/0.44    k2_xboole_0(sK1,sK2) != k13_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) | spl3_1),
% 0.22/0.44    inference(avatar_component_clause,[],[f76])).
% 0.22/0.44  fof(f185,plain,(
% 0.22/0.44    spl3_9),
% 0.22/0.44    inference(avatar_contradiction_clause,[],[f184])).
% 0.22/0.44  fof(f184,plain,(
% 0.22/0.44    $false | spl3_9),
% 0.22/0.44    inference(resolution,[],[f154,f66])).
% 0.22/0.44  fof(f154,plain,(
% 0.22/0.44    ~m1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(sK0)))) | spl3_9),
% 0.22/0.44    inference(avatar_component_clause,[],[f152])).
% 0.22/0.44  fof(f183,plain,(
% 0.22/0.44    spl3_8),
% 0.22/0.44    inference(avatar_contradiction_clause,[],[f182])).
% 0.22/0.44  fof(f182,plain,(
% 0.22/0.44    $false | spl3_8),
% 0.22/0.44    inference(resolution,[],[f150,f67])).
% 0.22/0.44  fof(f150,plain,(
% 0.22/0.44    ~m1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(sK0)))) | spl3_8),
% 0.22/0.44    inference(avatar_component_clause,[],[f148])).
% 0.22/0.44  fof(f181,plain,(
% 0.22/0.44    spl3_4),
% 0.22/0.44    inference(avatar_contradiction_clause,[],[f180])).
% 0.22/0.44  fof(f180,plain,(
% 0.22/0.44    $false | spl3_4),
% 0.22/0.44    inference(resolution,[],[f134,f99])).
% 0.22/0.44  fof(f99,plain,(
% 0.22/0.44    r2_hidden(k3_xboole_0(sK1,sK2),k9_setfam_1(sK0))),
% 0.22/0.44    inference(resolution,[],[f91,f67])).
% 0.22/0.44  fof(f91,plain,(
% 0.22/0.44    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(sK0)))) | r2_hidden(k3_xboole_0(X0,sK2),k9_setfam_1(sK0))) )),
% 0.22/0.44    inference(resolution,[],[f74,f66])).
% 0.22/0.44  fof(f74,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X0)))) | r2_hidden(k3_xboole_0(X1,X2),k9_setfam_1(X0)) | ~m1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0))))) )),
% 0.22/0.44    inference(definition_unfolding,[],[f60,f47,f47])).
% 0.22/0.44  fof(f60,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (r2_hidden(k3_xboole_0(X1,X2),k9_setfam_1(X0)) | ~m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f35])).
% 0.22/0.44  fof(f134,plain,(
% 0.22/0.44    ~r2_hidden(k3_xboole_0(sK1,sK2),k9_setfam_1(sK0)) | spl3_4),
% 0.22/0.44    inference(avatar_component_clause,[],[f132])).
% 0.22/0.44  fof(f132,plain,(
% 0.22/0.44    spl3_4 <=> r2_hidden(k3_xboole_0(sK1,sK2),k9_setfam_1(sK0))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.44  fof(f179,plain,(
% 0.22/0.44    spl3_7),
% 0.22/0.44    inference(avatar_contradiction_clause,[],[f178])).
% 0.22/0.44  fof(f178,plain,(
% 0.22/0.44    $false | spl3_7),
% 0.22/0.44    inference(resolution,[],[f146,f85])).
% 0.22/0.44  fof(f85,plain,(
% 0.22/0.44    ( ! [X1] : (l1_orders_2(k3_lattice3(k1_lattice3(X1)))) )),
% 0.22/0.44    inference(superposition,[],[f69,f68])).
% 0.22/0.44  fof(f69,plain,(
% 0.22/0.44    ( ! [X0] : (l1_orders_2(g1_orders_2(X0,k1_yellow_1(X0)))) )),
% 0.22/0.44    inference(definition_unfolding,[],[f53,f49])).
% 0.22/0.44  fof(f53,plain,(
% 0.22/0.44    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f23])).
% 0.22/0.44  fof(f23,plain,(
% 0.22/0.44    ! [X0] : l1_orders_2(k2_yellow_1(X0))),
% 0.22/0.44    inference(pure_predicate_removal,[],[f9])).
% 0.22/0.44  fof(f9,axiom,(
% 0.22/0.44    ! [X0] : (l1_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).
% 0.22/0.44  fof(f146,plain,(
% 0.22/0.44    ~l1_orders_2(k3_lattice3(k1_lattice3(sK0))) | spl3_7),
% 0.22/0.44    inference(avatar_component_clause,[],[f144])).
% 0.22/0.44  fof(f177,plain,(
% 0.22/0.44    spl3_12),
% 0.22/0.44    inference(avatar_contradiction_clause,[],[f176])).
% 0.22/0.44  fof(f176,plain,(
% 0.22/0.44    $false | spl3_12),
% 0.22/0.44    inference(resolution,[],[f171,f51])).
% 0.22/0.44  fof(f51,plain,(
% 0.22/0.44    ( ! [X0] : (l3_lattices(k1_lattice3(X0))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f26])).
% 0.22/0.44  fof(f26,plain,(
% 0.22/0.44    ! [X0] : l3_lattices(k1_lattice3(X0))),
% 0.22/0.44    inference(pure_predicate_removal,[],[f2])).
% 0.22/0.44  fof(f2,axiom,(
% 0.22/0.44    ! [X0] : (l3_lattices(k1_lattice3(X0)) & v3_lattices(k1_lattice3(X0)))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_lattice3)).
% 0.22/0.44  fof(f171,plain,(
% 0.22/0.44    ~l3_lattices(k1_lattice3(sK0)) | spl3_12),
% 0.22/0.44    inference(avatar_component_clause,[],[f169])).
% 0.22/0.44  fof(f174,plain,(
% 0.22/0.44    spl3_11),
% 0.22/0.44    inference(avatar_contradiction_clause,[],[f173])).
% 0.22/0.44  fof(f173,plain,(
% 0.22/0.44    $false | spl3_11),
% 0.22/0.44    inference(resolution,[],[f167,f52])).
% 0.22/0.44  fof(f52,plain,(
% 0.22/0.44    ( ! [X0] : (v10_lattices(k1_lattice3(X0))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f25])).
% 0.22/0.44  fof(f25,plain,(
% 0.22/0.44    ! [X0] : v10_lattices(k1_lattice3(X0))),
% 0.22/0.44    inference(pure_predicate_removal,[],[f4])).
% 0.22/0.44  fof(f4,axiom,(
% 0.22/0.44    ! [X0] : (v10_lattices(k1_lattice3(X0)) & v3_lattices(k1_lattice3(X0)))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_lattice3)).
% 0.22/0.44  fof(f167,plain,(
% 0.22/0.44    ~v10_lattices(k1_lattice3(sK0)) | spl3_11),
% 0.22/0.44    inference(avatar_component_clause,[],[f165])).
% 0.22/0.44  fof(f172,plain,(
% 0.22/0.44    spl3_10 | ~spl3_11 | ~spl3_12 | spl3_6),
% 0.22/0.44    inference(avatar_split_clause,[],[f159,f140,f169,f165,f161])).
% 0.22/0.44  fof(f140,plain,(
% 0.22/0.44    spl3_6 <=> v2_lattice3(k3_lattice3(k1_lattice3(sK0)))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.44  fof(f159,plain,(
% 0.22/0.44    ~l3_lattices(k1_lattice3(sK0)) | ~v10_lattices(k1_lattice3(sK0)) | v2_struct_0(k1_lattice3(sK0)) | spl3_6),
% 0.22/0.44    inference(resolution,[],[f142,f59])).
% 0.22/0.44  fof(f59,plain,(
% 0.22/0.44    ( ! [X0] : (v2_lattice3(k3_lattice3(X0)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f34])).
% 0.22/0.44  fof(f142,plain,(
% 0.22/0.44    ~v2_lattice3(k3_lattice3(k1_lattice3(sK0))) | spl3_6),
% 0.22/0.44    inference(avatar_component_clause,[],[f140])).
% 0.22/0.44  fof(f158,plain,(
% 0.22/0.44    spl3_5),
% 0.22/0.44    inference(avatar_contradiction_clause,[],[f156])).
% 0.22/0.44  fof(f156,plain,(
% 0.22/0.44    $false | spl3_5),
% 0.22/0.44    inference(resolution,[],[f138,f84])).
% 0.22/0.44  fof(f84,plain,(
% 0.22/0.44    ( ! [X0] : (v5_orders_2(k3_lattice3(k1_lattice3(X0)))) )),
% 0.22/0.44    inference(superposition,[],[f70,f68])).
% 0.22/0.44  fof(f70,plain,(
% 0.22/0.44    ( ! [X0] : (v5_orders_2(g1_orders_2(X0,k1_yellow_1(X0)))) )),
% 0.22/0.44    inference(definition_unfolding,[],[f54,f49])).
% 0.22/0.44  fof(f54,plain,(
% 0.22/0.44    ( ! [X0] : (v5_orders_2(k2_yellow_1(X0))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f24])).
% 0.22/0.44  fof(f24,plain,(
% 0.22/0.44    ! [X0] : v5_orders_2(k2_yellow_1(X0))),
% 0.22/0.44    inference(pure_predicate_removal,[],[f20])).
% 0.22/0.44  fof(f20,plain,(
% 0.22/0.44    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.22/0.44    inference(pure_predicate_removal,[],[f19])).
% 0.22/0.44  fof(f19,plain,(
% 0.22/0.44    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.22/0.44    inference(pure_predicate_removal,[],[f11])).
% 0.22/0.44  fof(f11,axiom,(
% 0.22/0.44    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v4_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow_1)).
% 0.22/0.44  fof(f138,plain,(
% 0.22/0.44    ~v5_orders_2(k3_lattice3(k1_lattice3(sK0))) | spl3_5),
% 0.22/0.44    inference(avatar_component_clause,[],[f136])).
% 0.22/0.44  fof(f155,plain,(
% 0.22/0.44    spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_6 | ~spl3_7 | ~spl3_8 | ~spl3_9 | spl3_2),
% 0.22/0.44    inference(avatar_split_clause,[],[f126,f80,f152,f148,f144,f140,f136,f132,f128])).
% 0.22/0.44  fof(f80,plain,(
% 0.22/0.44    spl3_2 <=> k3_xboole_0(sK1,sK2) = k12_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.44  fof(f126,plain,(
% 0.22/0.44    ~m1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(sK0)))) | ~m1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(sK0)))) | ~l1_orders_2(k3_lattice3(k1_lattice3(sK0))) | ~v2_lattice3(k3_lattice3(k1_lattice3(sK0))) | ~v5_orders_2(k3_lattice3(k1_lattice3(sK0))) | ~r2_hidden(k3_xboole_0(sK1,sK2),k9_setfam_1(sK0)) | v1_xboole_0(k9_setfam_1(sK0)) | spl3_2),
% 0.22/0.44    inference(trivial_inequality_removal,[],[f125])).
% 0.22/0.44  fof(f125,plain,(
% 0.22/0.44    k3_xboole_0(sK1,sK2) != k3_xboole_0(sK1,sK2) | ~m1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(sK0)))) | ~m1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(sK0)))) | ~l1_orders_2(k3_lattice3(k1_lattice3(sK0))) | ~v2_lattice3(k3_lattice3(k1_lattice3(sK0))) | ~v5_orders_2(k3_lattice3(k1_lattice3(sK0))) | ~r2_hidden(k3_xboole_0(sK1,sK2),k9_setfam_1(sK0)) | v1_xboole_0(k9_setfam_1(sK0)) | spl3_2),
% 0.22/0.44    inference(superposition,[],[f82,f117])).
% 0.22/0.44  fof(f117,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k12_lattice3(k3_lattice3(k1_lattice3(X0)),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X0)))) | ~m1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0)))) | ~l1_orders_2(k3_lattice3(k1_lattice3(X0))) | ~v2_lattice3(k3_lattice3(k1_lattice3(X0))) | ~v5_orders_2(k3_lattice3(k1_lattice3(X0))) | ~r2_hidden(k3_xboole_0(X1,X2),k9_setfam_1(X0)) | v1_xboole_0(k9_setfam_1(X0))) )),
% 0.22/0.44    inference(duplicate_literal_removal,[],[f116])).
% 0.22/0.44  fof(f116,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k12_lattice3(k3_lattice3(k1_lattice3(X0)),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X0)))) | ~m1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0)))) | ~l1_orders_2(k3_lattice3(k1_lattice3(X0))) | ~v2_lattice3(k3_lattice3(k1_lattice3(X0))) | ~v5_orders_2(k3_lattice3(k1_lattice3(X0))) | ~r2_hidden(k3_xboole_0(X1,X2),k9_setfam_1(X0)) | ~m1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X0)))) | ~m1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0)))) | v1_xboole_0(k9_setfam_1(X0))) )),
% 0.22/0.44    inference(superposition,[],[f64,f100])).
% 0.22/0.44  fof(f100,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k11_lattice3(k3_lattice3(k1_lattice3(X0)),X1,X2) | ~r2_hidden(k3_xboole_0(X1,X2),k9_setfam_1(X0)) | ~m1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X0)))) | ~m1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0)))) | v1_xboole_0(k9_setfam_1(X0))) )),
% 0.22/0.44    inference(superposition,[],[f71,f68])).
% 0.22/0.44  fof(f71,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k11_lattice3(g1_orders_2(X0,k1_yellow_1(X0)),X1,X2) | ~r2_hidden(k3_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0)))) | v1_xboole_0(X0)) )),
% 0.22/0.44    inference(definition_unfolding,[],[f55,f49,f49,f49])).
% 0.22/0.44  fof(f55,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k11_lattice3(k2_yellow_1(X0),X1,X2) | ~r2_hidden(k3_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f30])).
% 0.22/0.44  fof(f30,plain,(
% 0.22/0.44    ! [X0] : (! [X1] : (! [X2] : (k3_xboole_0(X1,X2) = k11_lattice3(k2_yellow_1(X0),X1,X2) | ~r2_hidden(k3_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 0.22/0.44    inference(flattening,[],[f29])).
% 0.22/0.44  fof(f29,plain,(
% 0.22/0.44    ! [X0] : (! [X1] : (! [X2] : ((k3_xboole_0(X1,X2) = k11_lattice3(k2_yellow_1(X0),X1,X2) | ~r2_hidden(k3_xboole_0(X1,X2),X0)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 0.22/0.44    inference(ennf_transformation,[],[f15])).
% 0.22/0.44  fof(f15,axiom,(
% 0.22/0.44    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => (r2_hidden(k3_xboole_0(X1,X2),X0) => k3_xboole_0(X1,X2) = k11_lattice3(k2_yellow_1(X0),X1,X2)))))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_yellow_1)).
% 0.22/0.44  fof(f64,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f40])).
% 0.22/0.44  fof(f40,plain,(
% 0.22/0.44    ! [X0,X1,X2] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 0.22/0.44    inference(flattening,[],[f39])).
% 0.22/0.44  fof(f39,plain,(
% 0.22/0.44    ! [X0,X1,X2] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 0.22/0.44    inference(ennf_transformation,[],[f5])).
% 0.22/0.44  fof(f5,axiom,(
% 0.22/0.44    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k12_lattice3)).
% 0.22/0.44  fof(f82,plain,(
% 0.22/0.44    k3_xboole_0(sK1,sK2) != k12_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) | spl3_2),
% 0.22/0.44    inference(avatar_component_clause,[],[f80])).
% 0.22/0.44  fof(f83,plain,(
% 0.22/0.44    ~spl3_1 | ~spl3_2),
% 0.22/0.44    inference(avatar_split_clause,[],[f65,f80,f76])).
% 0.22/0.44  fof(f65,plain,(
% 0.22/0.44    k3_xboole_0(sK1,sK2) != k12_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) | k2_xboole_0(sK1,sK2) != k13_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2)),
% 0.22/0.44    inference(definition_unfolding,[],[f46,f47,f47])).
% 0.22/0.44  fof(f46,plain,(
% 0.22/0.44    k3_xboole_0(sK1,sK2) != k12_lattice3(k3_yellow_1(sK0),sK1,sK2) | k2_xboole_0(sK1,sK2) != k13_lattice3(k3_yellow_1(sK0),sK1,sK2)),
% 0.22/0.44    inference(cnf_transformation,[],[f43])).
% 0.22/0.44  % SZS output end Proof for theBenchmark
% 0.22/0.44  % (20238)------------------------------
% 0.22/0.44  % (20238)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.44  % (20238)Termination reason: Refutation
% 0.22/0.44  
% 0.22/0.44  % (20238)Memory used [KB]: 6268
% 0.22/0.44  % (20238)Time elapsed: 0.011 s
% 0.22/0.44  % (20238)------------------------------
% 0.22/0.44  % (20238)------------------------------
% 0.22/0.45  % (20233)Success in time 0.077 s
%------------------------------------------------------------------------------
