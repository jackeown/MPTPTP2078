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
% DateTime   : Thu Dec  3 13:23:16 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :  266 ( 631 expanded)
%              Number of leaves         :   67 ( 318 expanded)
%              Depth                    :   11
%              Number of atoms          : 1689 (5824 expanded)
%              Number of equality atoms :   71 ( 314 expanded)
%              Maximal formula depth    :   27 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f559,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f120,f124,f128,f132,f136,f140,f144,f148,f152,f156,f160,f164,f168,f172,f176,f180,f184,f192,f210,f215,f220,f223,f229,f242,f244,f249,f257,f262,f267,f269,f274,f283,f290,f292,f301,f309,f330,f334,f387,f443,f459,f511,f529,f537,f546,f558])).

fof(f558,plain,
    ( spl8_33
    | ~ spl8_26
    | ~ spl8_4
    | spl8_1
    | ~ spl8_79 ),
    inference(avatar_split_clause,[],[f555,f543,f118,f130,f240,f278])).

fof(f278,plain,
    ( spl8_33
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_33])])).

fof(f240,plain,
    ( spl8_26
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).

fof(f130,plain,
    ( spl8_4
  <=> l1_waybel_0(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f118,plain,
    ( spl8_1
  <=> sK1 = k1_waybel_2(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f543,plain,
    ( spl8_79
  <=> sK1 = k4_yellow_2(sK0,u1_waybel_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_79])])).

fof(f555,plain,
    ( sK1 = k1_waybel_2(sK0,sK2)
    | ~ l1_waybel_0(sK2,sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_79 ),
    inference(superposition,[],[f91,f544])).

fof(f544,plain,
    ( sK1 = k4_yellow_2(sK0,u1_waybel_0(sK0,sK2))
    | ~ spl8_79 ),
    inference(avatar_component_clause,[],[f543])).

fof(f91,plain,(
    ! [X0,X1] :
      ( k1_waybel_2(X0,X1) = k4_yellow_2(X0,u1_waybel_0(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_waybel_2(X0,X1) = k4_yellow_2(X0,u1_waybel_0(X0,X1))
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_waybel_2(X0,X1) = k4_yellow_2(X0,u1_waybel_0(X0,X1))
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => k1_waybel_2(X0,X1) = k4_yellow_2(X0,u1_waybel_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_waybel_2)).

fof(f546,plain,
    ( spl8_33
    | ~ spl8_26
    | ~ spl8_52
    | spl8_79
    | ~ spl8_78 ),
    inference(avatar_split_clause,[],[f541,f535,f543,f377,f240,f278])).

fof(f377,plain,
    ( spl8_52
  <=> v1_relat_1(u1_waybel_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_52])])).

fof(f535,plain,
    ( spl8_78
  <=> sK1 = k1_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_78])])).

fof(f541,plain,
    ( sK1 = k4_yellow_2(sK0,u1_waybel_0(sK0,sK2))
    | ~ v1_relat_1(u1_waybel_0(sK0,sK2))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_78 ),
    inference(superposition,[],[f90,f536])).

fof(f536,plain,
    ( sK1 = k1_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)))
    | ~ spl8_78 ),
    inference(avatar_component_clause,[],[f535])).

fof(f90,plain,(
    ! [X0,X1] :
      ( k4_yellow_2(X0,X1) = k1_yellow_0(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_yellow_2(X0,X1) = k1_yellow_0(X0,k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_yellow_2(X0,X1) = k1_yellow_0(X0,k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_yellow_2(X0,X1) = k1_yellow_0(X0,k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_yellow_2)).

fof(f537,plain,
    ( ~ spl8_4
    | ~ spl8_24
    | spl8_78
    | ~ spl8_62 ),
    inference(avatar_split_clause,[],[f533,f441,f535,f232,f130])).

fof(f232,plain,
    ( spl8_24
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f441,plain,
    ( spl8_62
  <=> sK1 = k1_yellow_0(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_62])])).

fof(f533,plain,
    ( sK1 = k1_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)))
    | ~ l1_struct_0(sK0)
    | ~ l1_waybel_0(sK2,sK0)
    | ~ spl8_62 ),
    inference(superposition,[],[f442,f185])).

fof(f185,plain,(
    ! [X0,X1] :
      ( k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),u1_waybel_0(X1,X0)) = k2_relat_1(u1_waybel_0(X1,X0))
      | ~ l1_struct_0(X1)
      | ~ l1_waybel_0(X0,X1) ) ),
    inference(resolution,[],[f102,f104])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f102,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_1(u1_waybel_0(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(u1_waybel_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_waybel_0)).

fof(f442,plain,
    ( sK1 = k1_yellow_0(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)))
    | ~ spl8_62 ),
    inference(avatar_component_clause,[],[f441])).

fof(f529,plain,
    ( ~ spl8_26
    | ~ spl8_8
    | ~ spl8_37
    | ~ spl8_23
    | spl8_62
    | spl8_66 ),
    inference(avatar_split_clause,[],[f527,f457,f441,f227,f306,f146,f240])).

fof(f146,plain,
    ( spl8_8
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f306,plain,
    ( spl8_37
  <=> r1_yellow_0(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_37])])).

fof(f227,plain,
    ( spl8_23
  <=> r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).

fof(f457,plain,
    ( spl8_66
  <=> m1_subset_1(sK3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_66])])).

fof(f527,plain,
    ( sK1 = k1_yellow_0(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)))
    | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1)
    | ~ r1_yellow_0(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | spl8_66 ),
    inference(resolution,[],[f458,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | k1_yellow_0(X0,X1) = X2
      | ~ r2_lattice3(X0,X1,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ( ~ r1_orders_2(X0,X2,sK3(X0,X1,X2))
                & r2_lattice3(X0,X1,sK3(X0,X1,X2))
                & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) )
            & ( ( ! [X4] :
                    ( r1_orders_2(X0,X2,X4)
                    | ~ r2_lattice3(X0,X1,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2) )
              | k1_yellow_0(X0,X1) != X2 ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f50,f51])).

fof(f51,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK3(X0,X1,X2))
        & r2_lattice3(X0,X1,sK3(X0,X1,X2))
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) )
            & ( ( ! [X4] :
                    ( r1_orders_2(X0,X2,X4)
                    | ~ r2_lattice3(X0,X1,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2) )
              | k1_yellow_0(X0,X1) != X2 ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) )
            & ( ( ! [X3] :
                    ( r1_orders_2(X0,X2,X3)
                    | ~ r2_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2) )
              | k1_yellow_0(X0,X1) != X2 ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) )
            & ( ( ! [X3] :
                    ( r1_orders_2(X0,X2,X3)
                    | ~ r2_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2) )
              | k1_yellow_0(X0,X1) != X2 ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2) ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2) ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r1_yellow_0(X0,X1)
           => ( k1_yellow_0(X0,X1) = X2
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_lattice3(X0,X1,X3)
                     => r1_orders_2(X0,X2,X3) ) )
                & r2_lattice3(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_yellow_0)).

fof(f458,plain,
    ( ~ m1_subset_1(sK3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1),u1_struct_0(sK0))
    | spl8_66 ),
    inference(avatar_component_clause,[],[f457])).

fof(f511,plain,
    ( ~ spl8_23
    | spl8_62
    | ~ spl8_8
    | ~ spl8_42
    | spl8_65 ),
    inference(avatar_split_clause,[],[f508,f454,f332,f146,f441,f227])).

fof(f332,plain,
    ( spl8_42
  <=> ! [X2] :
        ( r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X2))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | k1_yellow_0(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2))) = X2
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_42])])).

fof(f454,plain,
    ( spl8_65
  <=> r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_65])])).

fof(f508,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | sK1 = k1_yellow_0(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)))
    | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1)
    | ~ spl8_42
    | spl8_65 ),
    inference(resolution,[],[f333,f455])).

fof(f455,plain,
    ( ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1))
    | spl8_65 ),
    inference(avatar_component_clause,[],[f454])).

fof(f333,plain,
    ( ! [X2] :
        ( r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X2))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | k1_yellow_0(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2))) = X2
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X2) )
    | ~ spl8_42 ),
    inference(avatar_component_clause,[],[f332])).

fof(f459,plain,
    ( ~ spl8_65
    | ~ spl8_66
    | ~ spl8_34
    | spl8_61 ),
    inference(avatar_split_clause,[],[f451,f438,f281,f457,f454])).

fof(f281,plain,
    ( spl8_34
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,sK1,X0)
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_34])])).

fof(f438,plain,
    ( spl8_61
  <=> r1_orders_2(sK0,sK1,sK3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_61])])).

fof(f451,plain,
    ( ~ m1_subset_1(sK3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1),u1_struct_0(sK0))
    | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1))
    | ~ spl8_34
    | spl8_61 ),
    inference(resolution,[],[f439,f282])).

fof(f282,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) )
    | ~ spl8_34 ),
    inference(avatar_component_clause,[],[f281])).

fof(f439,plain,
    ( ~ r1_orders_2(sK0,sK1,sK3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1))
    | spl8_61 ),
    inference(avatar_component_clause,[],[f438])).

fof(f443,plain,
    ( ~ spl8_61
    | spl8_62
    | ~ spl8_8
    | ~ spl8_23
    | ~ spl8_41 ),
    inference(avatar_split_clause,[],[f433,f328,f227,f146,f441,f438])).

fof(f328,plain,
    ( spl8_41
  <=> ! [X1] :
        ( ~ r1_orders_2(sK0,X1,sK3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k1_yellow_0(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2))) = X1
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_41])])).

fof(f433,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | sK1 = k1_yellow_0(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)))
    | ~ r1_orders_2(sK0,sK1,sK3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1))
    | ~ spl8_23
    | ~ spl8_41 ),
    inference(resolution,[],[f329,f228])).

fof(f228,plain,
    ( r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1)
    | ~ spl8_23 ),
    inference(avatar_component_clause,[],[f227])).

fof(f329,plain,
    ( ! [X1] :
        ( ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k1_yellow_0(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2))) = X1
        | ~ r1_orders_2(sK0,X1,sK3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X1)) )
    | ~ spl8_41 ),
    inference(avatar_component_clause,[],[f328])).

fof(f387,plain,
    ( ~ spl8_24
    | ~ spl8_4
    | spl8_52 ),
    inference(avatar_split_clause,[],[f386,f377,f130,f232])).

fof(f386,plain,
    ( ~ l1_waybel_0(sK2,sK0)
    | ~ l1_struct_0(sK0)
    | spl8_52 ),
    inference(resolution,[],[f385,f102])).

fof(f385,plain,
    ( ! [X0,X1] : ~ m1_subset_1(u1_waybel_0(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl8_52 ),
    inference(resolution,[],[f378,f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f378,plain,
    ( ~ v1_relat_1(u1_waybel_0(sK0,sK2))
    | spl8_52 ),
    inference(avatar_component_clause,[],[f377])).

fof(f334,plain,
    ( ~ spl8_26
    | spl8_42
    | ~ spl8_37 ),
    inference(avatar_split_clause,[],[f316,f306,f332,f240])).

fof(f316,plain,
    ( ! [X2] :
        ( r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X2))
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X2)
        | k1_yellow_0(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2))) = X2
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl8_37 ),
    inference(resolution,[],[f307,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_yellow_0(X0,X1)
      | r2_lattice3(X0,X1,sK3(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,X2)
      | k1_yellow_0(X0,X1) = X2
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f307,plain,
    ( r1_yellow_0(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)))
    | ~ spl8_37 ),
    inference(avatar_component_clause,[],[f306])).

fof(f330,plain,
    ( ~ spl8_26
    | spl8_41
    | ~ spl8_37 ),
    inference(avatar_split_clause,[],[f315,f306,f328,f240])).

fof(f315,plain,
    ( ! [X1] :
        ( ~ r1_orders_2(sK0,X1,sK3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X1))
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X1)
        | k1_yellow_0(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2))) = X1
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl8_37 ),
    inference(resolution,[],[f307,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_yellow_0(X0,X1)
      | ~ r1_orders_2(X0,X2,sK3(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,X2)
      | k1_yellow_0(X0,X1) = X2
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f309,plain,
    ( ~ spl8_13
    | ~ spl8_26
    | ~ spl8_8
    | spl8_37
    | ~ spl8_23
    | ~ spl8_36 ),
    inference(avatar_split_clause,[],[f304,f299,f227,f306,f146,f240,f166])).

fof(f166,plain,
    ( spl8_13
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f299,plain,
    ( spl8_36
  <=> ! [X0] :
        ( ~ r2_lattice3(sK0,X0,sK1)
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK6(sK0,X0,sK1))
        | r1_yellow_0(sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_36])])).

fof(f304,plain,
    ( ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1)
    | r1_yellow_0(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ spl8_36 ),
    inference(duplicate_literal_removal,[],[f302])).

fof(f302,plain,
    ( ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1)
    | r1_yellow_0(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)))
    | r1_yellow_0(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)))
    | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ spl8_36 ),
    inference(resolution,[],[f300,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,sK6(X0,X1,X2))
      | r1_yellow_0(X0,X1)
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_yellow_0(X0,X1)
            | ! [X2] :
                ( ( ~ r1_orders_2(X0,X2,sK6(X0,X1,X2))
                  & r2_lattice3(X0,X1,sK6(X0,X1,X2))
                  & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ( ! [X5] :
                  ( r1_orders_2(X0,sK7(X0,X1),X5)
                  | ~ r2_lattice3(X0,X1,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,sK7(X0,X1))
              & m1_subset_1(sK7(X0,X1),u1_struct_0(X0)) )
            | ~ r1_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f59,f61,f60])).

fof(f60,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK6(X0,X1,X2))
        & r2_lattice3(X0,X1,sK6(X0,X1,X2))
        & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( ! [X5] :
              ( r1_orders_2(X0,X4,X5)
              | ~ r2_lattice3(X0,X1,X5)
              | ~ m1_subset_1(X5,u1_struct_0(X0)) )
          & r2_lattice3(X0,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ! [X5] :
            ( r1_orders_2(X0,sK7(X0,X1),X5)
            | ~ r2_lattice3(X0,X1,X5)
            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
        & r2_lattice3(X0,X1,sK7(X0,X1))
        & m1_subset_1(sK7(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_yellow_0(X0,X1)
            | ! [X2] :
                ( ? [X3] :
                    ( ~ r1_orders_2(X0,X2,X3)
                    & r2_lattice3(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ? [X4] :
                ( ! [X5] :
                    ( r1_orders_2(X0,X4,X5)
                    | ~ r2_lattice3(X0,X1,X5)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X4)
                & m1_subset_1(X4,u1_struct_0(X0)) )
            | ~ r1_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(rectify,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_yellow_0(X0,X1)
            | ! [X2] :
                ( ? [X3] :
                    ( ~ r1_orders_2(X0,X2,X3)
                    & r2_lattice3(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ? [X2] :
                ( ! [X3] :
                    ( r1_orders_2(X0,X2,X3)
                    | ~ r2_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ r1_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f300,plain,
    ( ! [X0] :
        ( ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK6(sK0,X0,sK1))
        | ~ r2_lattice3(sK0,X0,sK1)
        | r1_yellow_0(sK0,X0) )
    | ~ spl8_36 ),
    inference(avatar_component_clause,[],[f299])).

fof(f301,plain,
    ( ~ spl8_13
    | ~ spl8_26
    | ~ spl8_8
    | spl8_36
    | ~ spl8_35 ),
    inference(avatar_split_clause,[],[f297,f288,f299,f146,f240,f166])).

fof(f288,plain,
    ( spl8_35
  <=> ! [X0] :
        ( ~ m1_subset_1(sK6(sK0,X0,sK1),u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X0,sK1)
        | r1_yellow_0(sK0,X0)
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK6(sK0,X0,sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_35])])).

fof(f297,plain,
    ( ! [X0] :
        ( ~ r2_lattice3(sK0,X0,sK1)
        | r1_yellow_0(sK0,X0)
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK6(sK0,X0,sK1))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0) )
    | ~ spl8_35 ),
    inference(duplicate_literal_removal,[],[f296])).

fof(f296,plain,
    ( ! [X0] :
        ( ~ r2_lattice3(sK0,X0,sK1)
        | r1_yellow_0(sK0,X0)
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK6(sK0,X0,sK1))
        | r1_yellow_0(sK0,X0)
        | ~ r2_lattice3(sK0,X0,sK1)
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0) )
    | ~ spl8_35 ),
    inference(resolution,[],[f289,f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))
      | r1_yellow_0(X0,X1)
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f289,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK6(sK0,X0,sK1),u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X0,sK1)
        | r1_yellow_0(sK0,X0)
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK6(sK0,X0,sK1)) )
    | ~ spl8_35 ),
    inference(avatar_component_clause,[],[f288])).

fof(f292,plain,
    ( ~ spl8_26
    | ~ spl8_12
    | ~ spl8_33 ),
    inference(avatar_split_clause,[],[f291,f278,f162,f240])).

fof(f162,plain,
    ( spl8_12
  <=> v1_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f291,plain,
    ( ~ v1_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ spl8_33 ),
    inference(resolution,[],[f279,f84])).

fof(f84,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattice3)).

fof(f279,plain,
    ( v2_struct_0(sK0)
    | ~ spl8_33 ),
    inference(avatar_component_clause,[],[f278])).

fof(f290,plain,
    ( ~ spl8_13
    | ~ spl8_26
    | ~ spl8_8
    | spl8_35
    | ~ spl8_34 ),
    inference(avatar_split_clause,[],[f284,f281,f288,f146,f240,f166])).

fof(f284,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK6(sK0,X0,sK1),u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK6(sK0,X0,sK1))
        | r1_yellow_0(sK0,X0)
        | ~ r2_lattice3(sK0,X0,sK1)
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0) )
    | ~ spl8_34 ),
    inference(resolution,[],[f282,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X2,sK6(X0,X1,X2))
      | r1_yellow_0(X0,X1)
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f283,plain,
    ( spl8_33
    | ~ spl8_15
    | ~ spl8_26
    | ~ spl8_8
    | spl8_34
    | ~ spl8_32 ),
    inference(avatar_split_clause,[],[f276,f272,f281,f146,f240,f174,f278])).

fof(f174,plain,
    ( spl8_15
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f272,plain,
    ( spl8_32
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r3_orders_2(sK0,sK1,X0)
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).

fof(f276,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
        | r1_orders_2(sK0,sK1,X0)
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_32 ),
    inference(duplicate_literal_removal,[],[f275])).

fof(f275,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
        | r1_orders_2(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_32 ),
    inference(resolution,[],[f273,f105])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_orders_2(X0,X1,X2)
      | r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
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
    inference(nnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(f273,plain,
    ( ! [X0] :
        ( r3_orders_2(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) )
    | ~ spl8_32 ),
    inference(avatar_component_clause,[],[f272])).

fof(f274,plain,
    ( ~ spl8_8
    | spl8_32
    | ~ spl8_2
    | ~ spl8_29 ),
    inference(avatar_split_clause,[],[f270,f255,f122,f272,f146])).

fof(f122,plain,
    ( spl8_2
  <=> r3_waybel_9(sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f255,plain,
    ( spl8_29
  <=> ! [X1,X0] :
        ( ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_waybel_9(sK0,sK2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r3_orders_2(sK0,X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).

fof(f270,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | r3_orders_2(sK0,sK1,X0) )
    | ~ spl8_2
    | ~ spl8_29 ),
    inference(resolution,[],[f256,f123])).

fof(f123,plain,
    ( r3_waybel_9(sK0,sK2,sK1)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f122])).

fof(f256,plain,
    ( ! [X0,X1] :
        ( ~ r3_waybel_9(sK0,sK2,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r3_orders_2(sK0,X1,X0) )
    | ~ spl8_29 ),
    inference(avatar_component_clause,[],[f255])).

fof(f269,plain,
    ( ~ spl8_4
    | spl8_29
    | ~ spl8_6
    | spl8_7
    | ~ spl8_5
    | ~ spl8_31 ),
    inference(avatar_split_clause,[],[f268,f265,f134,f142,f138,f255,f130])).

fof(f138,plain,
    ( spl8_6
  <=> v4_orders_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f142,plain,
    ( spl8_7
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f134,plain,
    ( spl8_5
  <=> v7_waybel_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f265,plain,
    ( spl8_31
  <=> ! [X1,X0,X2] :
        ( ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r3_orders_2(sK0,X2,X1)
        | ~ r3_waybel_9(sK0,X0,X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).

fof(f268,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(sK2)
        | ~ v4_orders_2(sK2)
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
        | ~ l1_waybel_0(sK2,sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r3_orders_2(sK0,X1,X0)
        | ~ r3_waybel_9(sK0,sK2,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl8_5
    | ~ spl8_31 ),
    inference(resolution,[],[f266,f135])).

fof(f135,plain,
    ( v7_waybel_0(sK2)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f134])).

fof(f266,plain,
    ( ! [X2,X0,X1] :
        ( ~ v7_waybel_0(X0)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1)
        | ~ l1_waybel_0(X0,sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r3_orders_2(sK0,X2,X1)
        | ~ r3_waybel_9(sK0,X0,X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl8_31 ),
    inference(avatar_component_clause,[],[f265])).

fof(f267,plain,
    ( ~ spl8_17
    | ~ spl8_16
    | ~ spl8_15
    | ~ spl8_14
    | ~ spl8_13
    | ~ spl8_12
    | ~ spl8_11
    | ~ spl8_10
    | ~ spl8_9
    | spl8_31
    | spl8_30 ),
    inference(avatar_split_clause,[],[f263,f260,f265,f150,f154,f158,f162,f166,f170,f174,f178,f182])).

fof(f182,plain,
    ( spl8_17
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f178,plain,
    ( spl8_16
  <=> v8_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f170,plain,
    ( spl8_14
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f158,plain,
    ( spl8_11
  <=> v2_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f154,plain,
    ( spl8_10
  <=> v1_compts_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f150,plain,
    ( spl8_9
  <=> l1_waybel_9(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f260,plain,
    ( spl8_30
  <=> m1_subset_1(sK5(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).

fof(f263,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r3_waybel_9(sK0,X0,X2)
        | r3_orders_2(sK0,X2,X1)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ l1_waybel_0(X0,sK0)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | ~ l1_waybel_9(sK0)
        | ~ v1_compts_1(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | ~ v8_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | spl8_30 ),
    inference(resolution,[],[f261,f113])).

fof(f113,plain,(
    ! [X4,X0,X3,X1] :
      ( m1_subset_1(sK5(X0),u1_struct_0(X0))
      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X3)
      | r3_orders_2(X0,X3,X4)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f112])).

fof(f112,plain,(
    ! [X4,X0,X3,X1] :
      ( r3_orders_2(X0,X3,X4)
      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X3)
      | m1_subset_1(sK5(X0),u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f94])).

fof(f94,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r3_orders_2(X0,X3,X4)
      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X2)
      | m1_subset_1(sK5(X0),u1_struct_0(X0))
      | X2 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r3_orders_2(X0,X3,X4)
                      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r3_waybel_9(X0,X1,X2)
                  | ( ~ v5_pre_topc(k4_waybel_1(X0,sK5(X0)),X0,X0)
                    & m1_subset_1(sK5(X0),u1_struct_0(X0)) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f55,f56])).

fof(f56,plain,(
    ! [X0] :
      ( ? [X5] :
          ( ~ v5_pre_topc(k4_waybel_1(X0,X5),X0,X0)
          & m1_subset_1(X5,u1_struct_0(X0)) )
     => ( ~ v5_pre_topc(k4_waybel_1(X0,sK5(X0)),X0,X0)
        & m1_subset_1(sK5(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r3_orders_2(X0,X3,X4)
                      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r3_waybel_9(X0,X1,X2)
                  | ? [X5] :
                      ( ~ v5_pre_topc(k4_waybel_1(X0,X5),X0,X0)
                      & m1_subset_1(X5,u1_struct_0(X0)) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X5] :
                      ( r3_orders_2(X0,X3,X5)
                      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ r3_waybel_9(X0,X1,X2)
                  | ? [X4] :
                      ( ~ v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X5] :
                      ( r3_orders_2(X0,X3,X5)
                      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ r3_waybel_9(X0,X1,X2)
                  | ? [X4] :
                      ( ~ v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( l1_waybel_9(X0)
        & v1_compts_1(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( r3_waybel_9(X0,X1,X2)
                      & ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) )
                      & X2 = X3 )
                   => ! [X5] :
                        ( m1_subset_1(X5,u1_struct_0(X0))
                       => ( r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5)
                         => r3_orders_2(X0,X3,X5) ) ) ) ) ) ) ) ),
    inference(rectify,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_waybel_9(X0)
        & v1_compts_1(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( r3_waybel_9(X0,X1,X2)
                      & ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) )
                      & X2 = X3 )
                   => ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X0))
                       => ( r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
                         => r3_orders_2(X0,X3,X4) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_waybel_9)).

fof(f261,plain,
    ( ~ m1_subset_1(sK5(sK0),u1_struct_0(sK0))
    | spl8_30 ),
    inference(avatar_component_clause,[],[f260])).

fof(f262,plain,
    ( ~ spl8_30
    | spl8_28 ),
    inference(avatar_split_clause,[],[f258,f252,f260])).

fof(f252,plain,
    ( spl8_28
  <=> v5_pre_topc(k4_waybel_1(sK0,sK5(sK0)),sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).

fof(f258,plain,
    ( ~ m1_subset_1(sK5(sK0),u1_struct_0(sK0))
    | spl8_28 ),
    inference(resolution,[],[f253,f78])).

fof(f78,plain,(
    ! [X3] :
      ( v5_pre_topc(k4_waybel_1(sK0,X3),sK0,sK0)
      | ~ m1_subset_1(X3,u1_struct_0(sK0)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,
    ( sK1 != k1_waybel_2(sK0,sK2)
    & r3_waybel_9(sK0,sK2,sK1)
    & v10_waybel_0(sK2,sK0)
    & ! [X3] :
        ( v5_pre_topc(k4_waybel_1(sK0,X3),sK0,sK0)
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    & l1_waybel_0(sK2,sK0)
    & v7_waybel_0(sK2)
    & v4_orders_2(sK2)
    & ~ v2_struct_0(sK2)
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_waybel_9(sK0)
    & v1_compts_1(sK0)
    & v2_lattice3(sK0)
    & v1_lattice3(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & v8_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f46,f45,f44])).

fof(f44,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k1_waybel_2(X0,X2) != X1
                & r3_waybel_9(X0,X2,X1)
                & v10_waybel_0(X2,X0)
                & ! [X3] :
                    ( v5_pre_topc(k4_waybel_1(X0,X3),X0,X0)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & l1_waybel_0(X2,X0)
                & v7_waybel_0(X2)
                & v4_orders_2(X2)
                & ~ v2_struct_0(X2) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_waybel_9(X0)
        & v1_compts_1(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k1_waybel_2(sK0,X2) != X1
              & r3_waybel_9(sK0,X2,X1)
              & v10_waybel_0(X2,sK0)
              & ! [X3] :
                  ( v5_pre_topc(k4_waybel_1(sK0,X3),sK0,sK0)
                  | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
              & l1_waybel_0(X2,sK0)
              & v7_waybel_0(X2)
              & v4_orders_2(X2)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_waybel_9(sK0)
      & v1_compts_1(sK0)
      & v2_lattice3(sK0)
      & v1_lattice3(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & v8_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k1_waybel_2(sK0,X2) != X1
            & r3_waybel_9(sK0,X2,X1)
            & v10_waybel_0(X2,sK0)
            & ! [X3] :
                ( v5_pre_topc(k4_waybel_1(sK0,X3),sK0,sK0)
                | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
            & l1_waybel_0(X2,sK0)
            & v7_waybel_0(X2)
            & v4_orders_2(X2)
            & ~ v2_struct_0(X2) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( k1_waybel_2(sK0,X2) != sK1
          & r3_waybel_9(sK0,X2,sK1)
          & v10_waybel_0(X2,sK0)
          & ! [X3] :
              ( v5_pre_topc(k4_waybel_1(sK0,X3),sK0,sK0)
              | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
          & l1_waybel_0(X2,sK0)
          & v7_waybel_0(X2)
          & v4_orders_2(X2)
          & ~ v2_struct_0(X2) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ? [X2] :
        ( k1_waybel_2(sK0,X2) != sK1
        & r3_waybel_9(sK0,X2,sK1)
        & v10_waybel_0(X2,sK0)
        & ! [X3] :
            ( v5_pre_topc(k4_waybel_1(sK0,X3),sK0,sK0)
            | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
        & l1_waybel_0(X2,sK0)
        & v7_waybel_0(X2)
        & v4_orders_2(X2)
        & ~ v2_struct_0(X2) )
   => ( sK1 != k1_waybel_2(sK0,sK2)
      & r3_waybel_9(sK0,sK2,sK1)
      & v10_waybel_0(sK2,sK0)
      & ! [X3] :
          ( v5_pre_topc(k4_waybel_1(sK0,X3),sK0,sK0)
          | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
      & l1_waybel_0(sK2,sK0)
      & v7_waybel_0(sK2)
      & v4_orders_2(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_waybel_2(X0,X2) != X1
              & r3_waybel_9(X0,X2,X1)
              & v10_waybel_0(X2,X0)
              & ! [X3] :
                  ( v5_pre_topc(k4_waybel_1(X0,X3),X0,X0)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & l1_waybel_0(X2,X0)
              & v7_waybel_0(X2)
              & v4_orders_2(X2)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_waybel_9(X0)
      & v1_compts_1(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & v8_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_waybel_2(X0,X2) != X1
              & r3_waybel_9(X0,X2,X1)
              & v10_waybel_0(X2,X0)
              & ! [X3] :
                  ( v5_pre_topc(k4_waybel_1(X0,X3),X0,X0)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & l1_waybel_0(X2,X0)
              & v7_waybel_0(X2)
              & v4_orders_2(X2)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_waybel_9(X0)
      & v1_compts_1(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & v8_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_waybel_9(X0)
          & v1_compts_1(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & v8_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( ( l1_waybel_0(X2,X0)
                  & v7_waybel_0(X2)
                  & v4_orders_2(X2)
                  & ~ v2_struct_0(X2) )
               => ( ( r3_waybel_9(X0,X2,X1)
                    & v10_waybel_0(X2,X0)
                    & ! [X3] :
                        ( m1_subset_1(X3,u1_struct_0(X0))
                       => v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) ) )
                 => k1_waybel_2(X0,X2) = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_waybel_9(X0)
        & v1_compts_1(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( l1_waybel_0(X2,X0)
                & v7_waybel_0(X2)
                & v4_orders_2(X2)
                & ~ v2_struct_0(X2) )
             => ( ( r3_waybel_9(X0,X2,X1)
                  & v10_waybel_0(X2,X0)
                  & ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) ) )
               => k1_waybel_2(X0,X2) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_waybel_9)).

fof(f253,plain,
    ( ~ v5_pre_topc(k4_waybel_1(sK0,sK5(sK0)),sK0,sK0)
    | spl8_28 ),
    inference(avatar_component_clause,[],[f252])).

fof(f257,plain,
    ( ~ spl8_28
    | ~ spl8_4
    | ~ spl8_9
    | spl8_29
    | ~ spl8_11
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_14
    | ~ spl8_15
    | ~ spl8_16
    | ~ spl8_17
    | ~ spl8_10
    | ~ spl8_27 ),
    inference(avatar_split_clause,[],[f250,f247,f154,f182,f178,f174,f170,f166,f162,f158,f255,f150,f130,f252])).

fof(f247,plain,
    ( spl8_27
  <=> ! [X1,X0,X2] :
        ( ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(X0),u1_waybel_0(X0,sK2)),X1)
        | ~ v2_pre_topc(X0)
        | ~ v8_pre_topc(X0)
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ v1_lattice3(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_compts_1(X0)
        | ~ l1_waybel_9(X0)
        | r3_orders_2(X0,X2,X1)
        | ~ l1_waybel_0(sK2,X0)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ v5_pre_topc(k4_waybel_1(X0,sK5(X0)),X0,X0)
        | ~ r3_waybel_9(X0,sK2,X2)
        | ~ m1_subset_1(X1,u1_struct_0(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).

fof(f250,plain,
    ( ! [X0,X1] :
        ( ~ v2_pre_topc(sK0)
        | ~ v8_pre_topc(sK0)
        | ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v2_lattice3(sK0)
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
        | ~ l1_waybel_9(sK0)
        | r3_orders_2(sK0,X1,X0)
        | ~ l1_waybel_0(sK2,sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v5_pre_topc(k4_waybel_1(sK0,sK5(sK0)),sK0,sK0)
        | ~ r3_waybel_9(sK0,sK2,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl8_10
    | ~ spl8_27 ),
    inference(resolution,[],[f248,f155])).

fof(f155,plain,
    ( v1_compts_1(sK0)
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f154])).

fof(f248,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_compts_1(X0)
        | ~ v2_pre_topc(X0)
        | ~ v8_pre_topc(X0)
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ v1_lattice3(X0)
        | ~ v2_lattice3(X0)
        | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(X0),u1_waybel_0(X0,sK2)),X1)
        | ~ l1_waybel_9(X0)
        | r3_orders_2(X0,X2,X1)
        | ~ l1_waybel_0(sK2,X0)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ v5_pre_topc(k4_waybel_1(X0,sK5(X0)),X0,X0)
        | ~ r3_waybel_9(X0,sK2,X2)
        | ~ m1_subset_1(X1,u1_struct_0(X0)) )
    | ~ spl8_27 ),
    inference(avatar_component_clause,[],[f247])).

fof(f249,plain,
    ( spl8_7
    | ~ spl8_6
    | spl8_27
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f245,f134,f247,f138,f142])).

fof(f245,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(X0),u1_waybel_0(X0,sK2)),X1)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ r3_waybel_9(X0,sK2,X2)
        | ~ v5_pre_topc(k4_waybel_1(X0,sK5(X0)),X0,X0)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ l1_waybel_0(sK2,X0)
        | r3_orders_2(X0,X2,X1)
        | ~ v4_orders_2(sK2)
        | v2_struct_0(sK2)
        | ~ l1_waybel_9(X0)
        | ~ v1_compts_1(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0)
        | ~ v8_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl8_5 ),
    inference(resolution,[],[f114,f135])).

fof(f114,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v7_waybel_0(X1)
      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X3)
      | ~ v5_pre_topc(k4_waybel_1(X0,sK5(X0)),X0,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | r3_orders_2(X0,X3,X4)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f111])).

fof(f111,plain,(
    ! [X4,X0,X3,X1] :
      ( r3_orders_2(X0,X3,X4)
      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X3)
      | ~ v5_pre_topc(k4_waybel_1(X0,sK5(X0)),X0,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f95])).

fof(f95,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r3_orders_2(X0,X3,X4)
      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ v5_pre_topc(k4_waybel_1(X0,sK5(X0)),X0,X0)
      | X2 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f244,plain,
    ( ~ spl8_9
    | spl8_26 ),
    inference(avatar_split_clause,[],[f243,f240,f150])).

fof(f243,plain,
    ( ~ l1_waybel_9(sK0)
    | spl8_26 ),
    inference(resolution,[],[f241,f82])).

fof(f82,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
      | ~ l1_waybel_9(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
      | ~ l1_waybel_9(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( l1_waybel_9(X0)
     => l1_orders_2(X0) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_waybel_9(X0)
     => ( l1_orders_2(X0)
        & l1_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_waybel_9)).

fof(f241,plain,
    ( ~ l1_orders_2(sK0)
    | spl8_26 ),
    inference(avatar_component_clause,[],[f240])).

fof(f242,plain,
    ( ~ spl8_26
    | spl8_24 ),
    inference(avatar_split_clause,[],[f238,f232,f240])).

fof(f238,plain,
    ( ~ l1_orders_2(sK0)
    | spl8_24 ),
    inference(resolution,[],[f233,f83])).

fof(f83,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f233,plain,
    ( ~ l1_struct_0(sK0)
    | spl8_24 ),
    inference(avatar_component_clause,[],[f232])).

fof(f229,plain,
    ( ~ spl8_8
    | spl8_23
    | ~ spl8_2
    | ~ spl8_20 ),
    inference(avatar_split_clause,[],[f224,f199,f122,f227,f146])).

fof(f199,plain,
    ( spl8_20
  <=> ! [X0] :
        ( r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
        | ~ r3_waybel_9(sK0,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f224,plain,
    ( r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl8_2
    | ~ spl8_20 ),
    inference(resolution,[],[f200,f123])).

fof(f200,plain,
    ( ! [X0] :
        ( ~ r3_waybel_9(sK0,sK2,X0)
        | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f199])).

fof(f223,plain,
    ( spl8_20
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | spl8_7
    | ~ spl8_3
    | ~ spl8_22 ),
    inference(avatar_split_clause,[],[f221,f218,f126,f142,f138,f134,f130,f199])).

fof(f126,plain,
    ( spl8_3
  <=> v10_waybel_0(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f218,plain,
    ( spl8_22
  <=> ! [X1,X0] :
        ( ~ r3_waybel_9(sK0,X0,X1)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1)
        | ~ v10_waybel_0(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f221,plain,
    ( ! [X0] :
        ( v2_struct_0(sK2)
        | ~ v4_orders_2(sK2)
        | ~ v7_waybel_0(sK2)
        | ~ l1_waybel_0(sK2,sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
        | ~ r3_waybel_9(sK0,sK2,X0) )
    | ~ spl8_3
    | ~ spl8_22 ),
    inference(resolution,[],[f219,f127])).

fof(f127,plain,
    ( v10_waybel_0(sK2,sK0)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f126])).

fof(f219,plain,
    ( ! [X0,X1] :
        ( ~ v10_waybel_0(X0,sK0)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1)
        | ~ r3_waybel_9(sK0,X0,X1) )
    | ~ spl8_22 ),
    inference(avatar_component_clause,[],[f218])).

fof(f220,plain,
    ( ~ spl8_17
    | ~ spl8_16
    | ~ spl8_15
    | ~ spl8_14
    | ~ spl8_13
    | ~ spl8_12
    | ~ spl8_11
    | ~ spl8_10
    | ~ spl8_9
    | spl8_22
    | spl8_21 ),
    inference(avatar_split_clause,[],[f216,f213,f218,f150,f154,f158,f162,f166,f170,f174,f178,f182])).

fof(f213,plain,
    ( spl8_21
  <=> m1_subset_1(sK4(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f216,plain,
    ( ! [X0,X1] :
        ( ~ r3_waybel_9(sK0,X0,X1)
        | ~ v10_waybel_0(X0,sK0)
        | r2_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_waybel_0(X0,sK0)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | ~ l1_waybel_9(sK0)
        | ~ v1_compts_1(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | ~ v8_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | spl8_21 ),
    inference(resolution,[],[f214,f115])).

fof(f115,plain,(
    ! [X0,X3,X1] :
      ( m1_subset_1(sK4(X0),u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X3)
      | ~ v10_waybel_0(X1,X0)
      | r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f110])).

fof(f110,plain,(
    ! [X0,X3,X1] :
      ( r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
      | ~ r3_waybel_9(X0,X1,X3)
      | ~ v10_waybel_0(X1,X0)
      | m1_subset_1(sK4(X0),u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f92])).

fof(f92,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ v10_waybel_0(X1,X0)
      | m1_subset_1(sK4(X0),u1_struct_0(X0))
      | X2 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
                  | ~ r3_waybel_9(X0,X1,X2)
                  | ~ v10_waybel_0(X1,X0)
                  | ( ~ v5_pre_topc(k4_waybel_1(X0,sK4(X0)),X0,X0)
                    & m1_subset_1(sK4(X0),u1_struct_0(X0)) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f33,f53])).

fof(f53,plain,(
    ! [X0] :
      ( ? [X4] :
          ( ~ v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ v5_pre_topc(k4_waybel_1(X0,sK4(X0)),X0,X0)
        & m1_subset_1(sK4(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
                  | ~ r3_waybel_9(X0,X1,X2)
                  | ~ v10_waybel_0(X1,X0)
                  | ? [X4] :
                      ( ~ v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
                  | ~ r3_waybel_9(X0,X1,X2)
                  | ~ v10_waybel_0(X1,X0)
                  | ? [X4] :
                      ( ~ v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_waybel_9(X0)
        & v1_compts_1(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( r3_waybel_9(X0,X1,X2)
                      & v10_waybel_0(X1,X0)
                      & ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) )
                      & X2 = X3 )
                   => r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l48_waybel_9)).

fof(f214,plain,
    ( ~ m1_subset_1(sK4(sK0),u1_struct_0(sK0))
    | spl8_21 ),
    inference(avatar_component_clause,[],[f213])).

fof(f215,plain,
    ( ~ spl8_21
    | spl8_19 ),
    inference(avatar_split_clause,[],[f211,f195,f213])).

fof(f195,plain,
    ( spl8_19
  <=> v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f211,plain,
    ( ~ m1_subset_1(sK4(sK0),u1_struct_0(sK0))
    | spl8_19 ),
    inference(resolution,[],[f196,f78])).

fof(f196,plain,
    ( ~ v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0)
    | spl8_19 ),
    inference(avatar_component_clause,[],[f195])).

fof(f210,plain,
    ( ~ spl8_19
    | ~ spl8_4
    | spl8_20
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_14
    | ~ spl8_15
    | ~ spl8_16
    | ~ spl8_17
    | ~ spl8_3
    | ~ spl8_18 ),
    inference(avatar_split_clause,[],[f193,f190,f126,f182,f178,f174,f170,f166,f162,f158,f154,f150,f199,f130,f195])).

fof(f190,plain,
    ( spl8_18
  <=> ! [X1,X0] :
        ( ~ r3_waybel_9(X0,sK2,X1)
        | ~ v2_pre_topc(X0)
        | ~ v8_pre_topc(X0)
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ v1_lattice3(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_compts_1(X0)
        | ~ l1_waybel_9(X0)
        | r2_lattice3(X0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(X0),u1_waybel_0(X0,sK2)),X1)
        | ~ l1_waybel_0(sK2,X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ v5_pre_topc(k4_waybel_1(X0,sK4(X0)),X0,X0)
        | ~ v10_waybel_0(sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f193,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK0)
        | ~ v8_pre_topc(sK0)
        | ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v1_compts_1(sK0)
        | ~ l1_waybel_9(sK0)
        | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
        | ~ l1_waybel_0(sK2,sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0)
        | ~ r3_waybel_9(sK0,sK2,X0) )
    | ~ spl8_3
    | ~ spl8_18 ),
    inference(resolution,[],[f191,f127])).

fof(f191,plain,
    ( ! [X0,X1] :
        ( ~ v10_waybel_0(sK2,X0)
        | ~ v2_pre_topc(X0)
        | ~ v8_pre_topc(X0)
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ v1_lattice3(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_compts_1(X0)
        | ~ l1_waybel_9(X0)
        | r2_lattice3(X0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(X0),u1_waybel_0(X0,sK2)),X1)
        | ~ l1_waybel_0(sK2,X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ v5_pre_topc(k4_waybel_1(X0,sK4(X0)),X0,X0)
        | ~ r3_waybel_9(X0,sK2,X1) )
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f190])).

fof(f192,plain,
    ( spl8_7
    | ~ spl8_6
    | spl8_18
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f186,f134,f190,f138,f142])).

fof(f186,plain,
    ( ! [X0,X1] :
        ( ~ r3_waybel_9(X0,sK2,X1)
        | ~ v10_waybel_0(sK2,X0)
        | ~ v5_pre_topc(k4_waybel_1(X0,sK4(X0)),X0,X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_waybel_0(sK2,X0)
        | r2_lattice3(X0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(X0),u1_waybel_0(X0,sK2)),X1)
        | ~ v4_orders_2(sK2)
        | v2_struct_0(sK2)
        | ~ l1_waybel_9(X0)
        | ~ v1_compts_1(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0)
        | ~ v8_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl8_5 ),
    inference(resolution,[],[f116,f135])).

fof(f116,plain,(
    ! [X0,X3,X1] :
      ( ~ v7_waybel_0(X1)
      | ~ r3_waybel_9(X0,X1,X3)
      | ~ v10_waybel_0(X1,X0)
      | ~ v5_pre_topc(k4_waybel_1(X0,sK4(X0)),X0,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f109])).

fof(f109,plain,(
    ! [X0,X3,X1] :
      ( r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
      | ~ r3_waybel_9(X0,X1,X3)
      | ~ v10_waybel_0(X1,X0)
      | ~ v5_pre_topc(k4_waybel_1(X0,sK4(X0)),X0,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f93])).

fof(f93,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ v10_waybel_0(X1,X0)
      | ~ v5_pre_topc(k4_waybel_1(X0,sK4(X0)),X0,X0)
      | X2 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f184,plain,(
    spl8_17 ),
    inference(avatar_split_clause,[],[f64,f182])).

fof(f64,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f180,plain,(
    spl8_16 ),
    inference(avatar_split_clause,[],[f65,f178])).

fof(f65,plain,(
    v8_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f176,plain,(
    spl8_15 ),
    inference(avatar_split_clause,[],[f66,f174])).

fof(f66,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f172,plain,(
    spl8_14 ),
    inference(avatar_split_clause,[],[f67,f170])).

fof(f67,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f168,plain,(
    spl8_13 ),
    inference(avatar_split_clause,[],[f68,f166])).

fof(f68,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f164,plain,(
    spl8_12 ),
    inference(avatar_split_clause,[],[f69,f162])).

fof(f69,plain,(
    v1_lattice3(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f160,plain,(
    spl8_11 ),
    inference(avatar_split_clause,[],[f70,f158])).

fof(f70,plain,(
    v2_lattice3(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f156,plain,(
    spl8_10 ),
    inference(avatar_split_clause,[],[f71,f154])).

fof(f71,plain,(
    v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f152,plain,(
    spl8_9 ),
    inference(avatar_split_clause,[],[f72,f150])).

fof(f72,plain,(
    l1_waybel_9(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f148,plain,(
    spl8_8 ),
    inference(avatar_split_clause,[],[f73,f146])).

fof(f73,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f47])).

fof(f144,plain,(
    ~ spl8_7 ),
    inference(avatar_split_clause,[],[f74,f142])).

fof(f74,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f140,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f75,f138])).

fof(f75,plain,(
    v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f136,plain,(
    spl8_5 ),
    inference(avatar_split_clause,[],[f76,f134])).

fof(f76,plain,(
    v7_waybel_0(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f132,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f77,f130])).

fof(f77,plain,(
    l1_waybel_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f128,plain,(
    spl8_3 ),
    inference(avatar_split_clause,[],[f79,f126])).

fof(f79,plain,(
    v10_waybel_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f124,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f80,f122])).

fof(f80,plain,(
    r3_waybel_9(sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f120,plain,(
    ~ spl8_1 ),
    inference(avatar_split_clause,[],[f81,f118])).

fof(f81,plain,(
    sK1 != k1_waybel_2(sK0,sK2) ),
    inference(cnf_transformation,[],[f47])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:00:30 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.23/0.48  % (9114)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.23/0.49  % (9108)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.23/0.50  % (9122)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.23/0.50  % (9122)Refutation not found, incomplete strategy% (9122)------------------------------
% 0.23/0.50  % (9122)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.50  % (9122)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.50  
% 0.23/0.50  % (9122)Memory used [KB]: 10618
% 0.23/0.50  % (9122)Time elapsed: 0.068 s
% 0.23/0.50  % (9122)------------------------------
% 0.23/0.50  % (9122)------------------------------
% 0.23/0.51  % (9108)Refutation found. Thanks to Tanya!
% 0.23/0.51  % SZS status Theorem for theBenchmark
% 0.23/0.51  % SZS output start Proof for theBenchmark
% 0.23/0.51  fof(f559,plain,(
% 0.23/0.51    $false),
% 0.23/0.51    inference(avatar_sat_refutation,[],[f120,f124,f128,f132,f136,f140,f144,f148,f152,f156,f160,f164,f168,f172,f176,f180,f184,f192,f210,f215,f220,f223,f229,f242,f244,f249,f257,f262,f267,f269,f274,f283,f290,f292,f301,f309,f330,f334,f387,f443,f459,f511,f529,f537,f546,f558])).
% 0.23/0.51  fof(f558,plain,(
% 0.23/0.51    spl8_33 | ~spl8_26 | ~spl8_4 | spl8_1 | ~spl8_79),
% 0.23/0.51    inference(avatar_split_clause,[],[f555,f543,f118,f130,f240,f278])).
% 0.23/0.51  fof(f278,plain,(
% 0.23/0.51    spl8_33 <=> v2_struct_0(sK0)),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_33])])).
% 0.23/0.51  fof(f240,plain,(
% 0.23/0.51    spl8_26 <=> l1_orders_2(sK0)),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).
% 0.23/0.51  fof(f130,plain,(
% 0.23/0.51    spl8_4 <=> l1_waybel_0(sK2,sK0)),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.23/0.51  fof(f118,plain,(
% 0.23/0.51    spl8_1 <=> sK1 = k1_waybel_2(sK0,sK2)),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.23/0.51  fof(f543,plain,(
% 0.23/0.51    spl8_79 <=> sK1 = k4_yellow_2(sK0,u1_waybel_0(sK0,sK2))),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_79])])).
% 0.23/0.51  fof(f555,plain,(
% 0.23/0.51    sK1 = k1_waybel_2(sK0,sK2) | ~l1_waybel_0(sK2,sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | ~spl8_79),
% 0.23/0.51    inference(superposition,[],[f91,f544])).
% 0.23/0.51  fof(f544,plain,(
% 0.23/0.51    sK1 = k4_yellow_2(sK0,u1_waybel_0(sK0,sK2)) | ~spl8_79),
% 0.23/0.51    inference(avatar_component_clause,[],[f543])).
% 0.23/0.51  fof(f91,plain,(
% 0.23/0.51    ( ! [X0,X1] : (k1_waybel_2(X0,X1) = k4_yellow_2(X0,u1_waybel_0(X0,X1)) | ~l1_waybel_0(X1,X0) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f31])).
% 0.23/0.51  fof(f31,plain,(
% 0.23/0.51    ! [X0] : (! [X1] : (k1_waybel_2(X0,X1) = k4_yellow_2(X0,u1_waybel_0(X0,X1)) | ~l1_waybel_0(X1,X0)) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 0.23/0.51    inference(flattening,[],[f30])).
% 0.23/0.51  fof(f30,plain,(
% 0.23/0.51    ! [X0] : (! [X1] : (k1_waybel_2(X0,X1) = k4_yellow_2(X0,u1_waybel_0(X0,X1)) | ~l1_waybel_0(X1,X0)) | (~l1_orders_2(X0) | v2_struct_0(X0)))),
% 0.23/0.51    inference(ennf_transformation,[],[f9])).
% 0.23/0.51  fof(f9,axiom,(
% 0.23/0.51    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (l1_waybel_0(X1,X0) => k1_waybel_2(X0,X1) = k4_yellow_2(X0,u1_waybel_0(X0,X1))))),
% 0.23/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_waybel_2)).
% 0.23/0.51  fof(f546,plain,(
% 0.23/0.51    spl8_33 | ~spl8_26 | ~spl8_52 | spl8_79 | ~spl8_78),
% 0.23/0.51    inference(avatar_split_clause,[],[f541,f535,f543,f377,f240,f278])).
% 0.23/0.51  fof(f377,plain,(
% 0.23/0.51    spl8_52 <=> v1_relat_1(u1_waybel_0(sK0,sK2))),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_52])])).
% 0.23/0.51  fof(f535,plain,(
% 0.23/0.51    spl8_78 <=> sK1 = k1_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)))),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_78])])).
% 0.23/0.51  fof(f541,plain,(
% 0.23/0.51    sK1 = k4_yellow_2(sK0,u1_waybel_0(sK0,sK2)) | ~v1_relat_1(u1_waybel_0(sK0,sK2)) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | ~spl8_78),
% 0.23/0.51    inference(superposition,[],[f90,f536])).
% 0.23/0.51  fof(f536,plain,(
% 0.23/0.51    sK1 = k1_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2))) | ~spl8_78),
% 0.23/0.51    inference(avatar_component_clause,[],[f535])).
% 0.23/0.51  fof(f90,plain,(
% 0.23/0.51    ( ! [X0,X1] : (k4_yellow_2(X0,X1) = k1_yellow_0(X0,k2_relat_1(X1)) | ~v1_relat_1(X1) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f29])).
% 0.23/0.51  fof(f29,plain,(
% 0.23/0.51    ! [X0] : (! [X1] : (k4_yellow_2(X0,X1) = k1_yellow_0(X0,k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 0.23/0.51    inference(flattening,[],[f28])).
% 0.23/0.51  fof(f28,plain,(
% 0.23/0.51    ! [X0] : (! [X1] : (k4_yellow_2(X0,X1) = k1_yellow_0(X0,k2_relat_1(X1)) | ~v1_relat_1(X1)) | (~l1_orders_2(X0) | v2_struct_0(X0)))),
% 0.23/0.51    inference(ennf_transformation,[],[f10])).
% 0.23/0.51  fof(f10,axiom,(
% 0.23/0.51    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (v1_relat_1(X1) => k4_yellow_2(X0,X1) = k1_yellow_0(X0,k2_relat_1(X1))))),
% 0.23/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_yellow_2)).
% 0.23/0.51  fof(f537,plain,(
% 0.23/0.51    ~spl8_4 | ~spl8_24 | spl8_78 | ~spl8_62),
% 0.23/0.51    inference(avatar_split_clause,[],[f533,f441,f535,f232,f130])).
% 0.23/0.51  fof(f232,plain,(
% 0.23/0.51    spl8_24 <=> l1_struct_0(sK0)),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).
% 0.23/0.51  fof(f441,plain,(
% 0.23/0.51    spl8_62 <=> sK1 = k1_yellow_0(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)))),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_62])])).
% 0.23/0.51  fof(f533,plain,(
% 0.23/0.51    sK1 = k1_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2))) | ~l1_struct_0(sK0) | ~l1_waybel_0(sK2,sK0) | ~spl8_62),
% 0.23/0.51    inference(superposition,[],[f442,f185])).
% 0.23/0.51  fof(f185,plain,(
% 0.23/0.51    ( ! [X0,X1] : (k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),u1_waybel_0(X1,X0)) = k2_relat_1(u1_waybel_0(X1,X0)) | ~l1_struct_0(X1) | ~l1_waybel_0(X0,X1)) )),
% 0.23/0.51    inference(resolution,[],[f102,f104])).
% 0.23/0.51  fof(f104,plain,(
% 0.23/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f41])).
% 0.23/0.51  fof(f41,plain,(
% 0.23/0.51    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.23/0.51    inference(ennf_transformation,[],[f2])).
% 0.23/0.51  fof(f2,axiom,(
% 0.23/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.23/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.23/0.51  fof(f102,plain,(
% 0.23/0.51    ( ! [X0,X1] : (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f39])).
% 0.23/0.51  fof(f39,plain,(
% 0.23/0.51    ! [X0,X1] : (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0))),
% 0.23/0.51    inference(flattening,[],[f38])).
% 0.23/0.51  fof(f38,plain,(
% 0.23/0.51    ! [X0,X1] : (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | (~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)))),
% 0.23/0.51    inference(ennf_transformation,[],[f19])).
% 0.23/0.51  fof(f19,plain,(
% 0.23/0.51    ! [X0,X1] : ((l1_waybel_0(X1,X0) & l1_struct_0(X0)) => m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))))),
% 0.23/0.51    inference(pure_predicate_removal,[],[f18])).
% 0.23/0.51  fof(f18,plain,(
% 0.23/0.51    ! [X0,X1] : ((l1_waybel_0(X1,X0) & l1_struct_0(X0)) => (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_1(u1_waybel_0(X0,X1))))),
% 0.23/0.51    inference(pure_predicate_removal,[],[f8])).
% 0.23/0.51  fof(f8,axiom,(
% 0.23/0.51    ! [X0,X1] : ((l1_waybel_0(X1,X0) & l1_struct_0(X0)) => (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(u1_waybel_0(X0,X1))))),
% 0.23/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_waybel_0)).
% 0.23/0.51  fof(f442,plain,(
% 0.23/0.51    sK1 = k1_yellow_0(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2))) | ~spl8_62),
% 0.23/0.51    inference(avatar_component_clause,[],[f441])).
% 0.23/0.51  fof(f529,plain,(
% 0.23/0.51    ~spl8_26 | ~spl8_8 | ~spl8_37 | ~spl8_23 | spl8_62 | spl8_66),
% 0.23/0.51    inference(avatar_split_clause,[],[f527,f457,f441,f227,f306,f146,f240])).
% 0.23/0.51  fof(f146,plain,(
% 0.23/0.51    spl8_8 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.23/0.51  fof(f306,plain,(
% 0.23/0.51    spl8_37 <=> r1_yellow_0(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)))),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_37])])).
% 0.23/0.51  fof(f227,plain,(
% 0.23/0.51    spl8_23 <=> r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1)),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).
% 0.23/0.51  fof(f457,plain,(
% 0.23/0.51    spl8_66 <=> m1_subset_1(sK3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1),u1_struct_0(sK0))),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_66])])).
% 0.23/0.51  fof(f527,plain,(
% 0.23/0.51    sK1 = k1_yellow_0(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2))) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1) | ~r1_yellow_0(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | spl8_66),
% 0.23/0.51    inference(resolution,[],[f458,f87])).
% 0.23/0.51  fof(f87,plain,(
% 0.23/0.51    ( ! [X2,X0,X1] : (m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) | k1_yellow_0(X0,X1) = X2 | ~r2_lattice3(X0,X1,X2) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f52])).
% 0.23/0.51  fof(f52,plain,(
% 0.23/0.51    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | (~r1_orders_2(X0,X2,sK3(X0,X1,X2)) & r2_lattice3(X0,X1,sK3(X0,X1,X2)) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.23/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f50,f51])).
% 0.23/0.51  fof(f51,plain,(
% 0.23/0.51    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X2,sK3(X0,X1,X2)) & r2_lattice3(X0,X1,sK3(X0,X1,X2)) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))))),
% 0.23/0.51    introduced(choice_axiom,[])).
% 0.23/0.51  fof(f50,plain,(
% 0.23/0.51    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.23/0.51    inference(rectify,[],[f49])).
% 0.23/0.51  fof(f49,plain,(
% 0.23/0.51    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.23/0.51    inference(flattening,[],[f48])).
% 0.23/0.51  fof(f48,plain,(
% 0.23/0.51    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) & ((! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.23/0.51    inference(nnf_transformation,[],[f27])).
% 0.23/0.51  fof(f27,plain,(
% 0.23/0.51    ! [X0] : (! [X1,X2] : ((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.23/0.51    inference(flattening,[],[f26])).
% 0.23/0.51  fof(f26,plain,(
% 0.23/0.51    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.23/0.51    inference(ennf_transformation,[],[f6])).
% 0.23/0.51  fof(f6,axiom,(
% 0.23/0.51    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_yellow_0(X0,X1) => (k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X3) => r1_orders_2(X0,X2,X3))) & r2_lattice3(X0,X1,X2))))))),
% 0.23/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_yellow_0)).
% 0.23/0.51  fof(f458,plain,(
% 0.23/0.51    ~m1_subset_1(sK3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1),u1_struct_0(sK0)) | spl8_66),
% 0.23/0.51    inference(avatar_component_clause,[],[f457])).
% 0.23/0.51  fof(f511,plain,(
% 0.23/0.51    ~spl8_23 | spl8_62 | ~spl8_8 | ~spl8_42 | spl8_65),
% 0.23/0.51    inference(avatar_split_clause,[],[f508,f454,f332,f146,f441,f227])).
% 0.23/0.51  fof(f332,plain,(
% 0.23/0.51    spl8_42 <=> ! [X2] : (r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X2)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | k1_yellow_0(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2))) = X2 | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X2))),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_42])])).
% 0.23/0.51  fof(f454,plain,(
% 0.23/0.51    spl8_65 <=> r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1))),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_65])])).
% 0.23/0.51  fof(f508,plain,(
% 0.23/0.51    ~m1_subset_1(sK1,u1_struct_0(sK0)) | sK1 = k1_yellow_0(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2))) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1) | (~spl8_42 | spl8_65)),
% 0.23/0.51    inference(resolution,[],[f333,f455])).
% 0.23/0.51  fof(f455,plain,(
% 0.23/0.51    ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1)) | spl8_65),
% 0.23/0.51    inference(avatar_component_clause,[],[f454])).
% 0.23/0.51  fof(f333,plain,(
% 0.23/0.51    ( ! [X2] : (r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X2)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | k1_yellow_0(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2))) = X2 | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X2)) ) | ~spl8_42),
% 0.23/0.51    inference(avatar_component_clause,[],[f332])).
% 0.23/0.51  fof(f459,plain,(
% 0.23/0.51    ~spl8_65 | ~spl8_66 | ~spl8_34 | spl8_61),
% 0.23/0.51    inference(avatar_split_clause,[],[f451,f438,f281,f457,f454])).
% 0.23/0.51  fof(f281,plain,(
% 0.23/0.51    spl8_34 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,sK1,X0) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0))),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_34])])).
% 0.23/0.51  fof(f438,plain,(
% 0.23/0.51    spl8_61 <=> r1_orders_2(sK0,sK1,sK3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1))),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_61])])).
% 0.23/0.51  fof(f451,plain,(
% 0.23/0.51    ~m1_subset_1(sK3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1),u1_struct_0(sK0)) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1)) | (~spl8_34 | spl8_61)),
% 0.23/0.51    inference(resolution,[],[f439,f282])).
% 0.23/0.51  fof(f282,plain,(
% 0.23/0.51    ( ! [X0] : (r1_orders_2(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)) ) | ~spl8_34),
% 0.23/0.51    inference(avatar_component_clause,[],[f281])).
% 0.23/0.51  fof(f439,plain,(
% 0.23/0.51    ~r1_orders_2(sK0,sK1,sK3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1)) | spl8_61),
% 0.23/0.51    inference(avatar_component_clause,[],[f438])).
% 0.23/0.51  fof(f443,plain,(
% 0.23/0.51    ~spl8_61 | spl8_62 | ~spl8_8 | ~spl8_23 | ~spl8_41),
% 0.23/0.51    inference(avatar_split_clause,[],[f433,f328,f227,f146,f441,f438])).
% 0.23/0.51  fof(f328,plain,(
% 0.23/0.51    spl8_41 <=> ! [X1] : (~r1_orders_2(sK0,X1,sK3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X1)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k1_yellow_0(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2))) = X1 | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X1))),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_41])])).
% 0.23/0.51  fof(f433,plain,(
% 0.23/0.51    ~m1_subset_1(sK1,u1_struct_0(sK0)) | sK1 = k1_yellow_0(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2))) | ~r1_orders_2(sK0,sK1,sK3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1)) | (~spl8_23 | ~spl8_41)),
% 0.23/0.51    inference(resolution,[],[f329,f228])).
% 0.23/0.51  fof(f228,plain,(
% 0.23/0.51    r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1) | ~spl8_23),
% 0.23/0.51    inference(avatar_component_clause,[],[f227])).
% 0.23/0.51  fof(f329,plain,(
% 0.23/0.51    ( ! [X1] : (~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k1_yellow_0(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2))) = X1 | ~r1_orders_2(sK0,X1,sK3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X1))) ) | ~spl8_41),
% 0.23/0.51    inference(avatar_component_clause,[],[f328])).
% 0.23/0.51  fof(f387,plain,(
% 0.23/0.51    ~spl8_24 | ~spl8_4 | spl8_52),
% 0.23/0.51    inference(avatar_split_clause,[],[f386,f377,f130,f232])).
% 0.23/0.51  fof(f386,plain,(
% 0.23/0.51    ~l1_waybel_0(sK2,sK0) | ~l1_struct_0(sK0) | spl8_52),
% 0.23/0.51    inference(resolution,[],[f385,f102])).
% 0.23/0.51  fof(f385,plain,(
% 0.23/0.51    ( ! [X0,X1] : (~m1_subset_1(u1_waybel_0(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl8_52),
% 0.23/0.51    inference(resolution,[],[f378,f103])).
% 0.23/0.51  fof(f103,plain,(
% 0.23/0.51    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.23/0.51    inference(cnf_transformation,[],[f40])).
% 0.23/0.51  fof(f40,plain,(
% 0.23/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.23/0.51    inference(ennf_transformation,[],[f1])).
% 0.23/0.51  fof(f1,axiom,(
% 0.23/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.23/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.23/0.51  fof(f378,plain,(
% 0.23/0.51    ~v1_relat_1(u1_waybel_0(sK0,sK2)) | spl8_52),
% 0.23/0.51    inference(avatar_component_clause,[],[f377])).
% 0.23/0.51  fof(f334,plain,(
% 0.23/0.51    ~spl8_26 | spl8_42 | ~spl8_37),
% 0.23/0.51    inference(avatar_split_clause,[],[f316,f306,f332,f240])).
% 0.23/0.51  fof(f316,plain,(
% 0.23/0.51    ( ! [X2] : (r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X2)) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X2) | k1_yellow_0(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2))) = X2 | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~l1_orders_2(sK0)) ) | ~spl8_37),
% 0.23/0.51    inference(resolution,[],[f307,f88])).
% 0.23/0.51  fof(f88,plain,(
% 0.23/0.51    ( ! [X2,X0,X1] : (~r1_yellow_0(X0,X1) | r2_lattice3(X0,X1,sK3(X0,X1,X2)) | ~r2_lattice3(X0,X1,X2) | k1_yellow_0(X0,X1) = X2 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f52])).
% 0.23/0.51  fof(f307,plain,(
% 0.23/0.51    r1_yellow_0(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2))) | ~spl8_37),
% 0.23/0.51    inference(avatar_component_clause,[],[f306])).
% 0.23/0.51  fof(f330,plain,(
% 0.23/0.51    ~spl8_26 | spl8_41 | ~spl8_37),
% 0.23/0.51    inference(avatar_split_clause,[],[f315,f306,f328,f240])).
% 0.23/0.51  fof(f315,plain,(
% 0.23/0.51    ( ! [X1] : (~r1_orders_2(sK0,X1,sK3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X1)) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X1) | k1_yellow_0(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2))) = X1 | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_orders_2(sK0)) ) | ~spl8_37),
% 0.23/0.51    inference(resolution,[],[f307,f89])).
% 0.23/0.51  fof(f89,plain,(
% 0.23/0.51    ( ! [X2,X0,X1] : (~r1_yellow_0(X0,X1) | ~r1_orders_2(X0,X2,sK3(X0,X1,X2)) | ~r2_lattice3(X0,X1,X2) | k1_yellow_0(X0,X1) = X2 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f52])).
% 0.23/0.51  fof(f309,plain,(
% 0.23/0.51    ~spl8_13 | ~spl8_26 | ~spl8_8 | spl8_37 | ~spl8_23 | ~spl8_36),
% 0.23/0.51    inference(avatar_split_clause,[],[f304,f299,f227,f306,f146,f240,f166])).
% 0.23/0.51  fof(f166,plain,(
% 0.23/0.51    spl8_13 <=> v5_orders_2(sK0)),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 0.23/0.51  fof(f299,plain,(
% 0.23/0.51    spl8_36 <=> ! [X0] : (~r2_lattice3(sK0,X0,sK1) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK6(sK0,X0,sK1)) | r1_yellow_0(sK0,X0))),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_36])])).
% 0.23/0.51  fof(f304,plain,(
% 0.23/0.51    ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1) | r1_yellow_0(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~spl8_36),
% 0.23/0.51    inference(duplicate_literal_removal,[],[f302])).
% 0.23/0.51  fof(f302,plain,(
% 0.23/0.51    ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1) | r1_yellow_0(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2))) | r1_yellow_0(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2))) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~spl8_36),
% 0.23/0.51    inference(resolution,[],[f300,f100])).
% 0.23/0.51  fof(f100,plain,(
% 0.23/0.51    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,sK6(X0,X1,X2)) | r1_yellow_0(X0,X1) | ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f62])).
% 0.23/0.51  fof(f62,plain,(
% 0.23/0.51    ! [X0] : (! [X1] : ((r1_yellow_0(X0,X1) | ! [X2] : ((~r1_orders_2(X0,X2,sK6(X0,X1,X2)) & r2_lattice3(X0,X1,sK6(X0,X1,X2)) & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)))) & ((! [X5] : (r1_orders_2(X0,sK7(X0,X1),X5) | ~r2_lattice3(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r2_lattice3(X0,X1,sK7(X0,X1)) & m1_subset_1(sK7(X0,X1),u1_struct_0(X0))) | ~r1_yellow_0(X0,X1))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 0.23/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f59,f61,f60])).
% 0.23/0.51  fof(f60,plain,(
% 0.23/0.51    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X2,sK6(X0,X1,X2)) & r2_lattice3(X0,X1,sK6(X0,X1,X2)) & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))))),
% 0.23/0.51    introduced(choice_axiom,[])).
% 0.23/0.51  fof(f61,plain,(
% 0.23/0.51    ! [X1,X0] : (? [X4] : (! [X5] : (r1_orders_2(X0,X4,X5) | ~r2_lattice3(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r2_lattice3(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) => (! [X5] : (r1_orders_2(X0,sK7(X0,X1),X5) | ~r2_lattice3(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r2_lattice3(X0,X1,sK7(X0,X1)) & m1_subset_1(sK7(X0,X1),u1_struct_0(X0))))),
% 0.23/0.51    introduced(choice_axiom,[])).
% 0.23/0.51  fof(f59,plain,(
% 0.23/0.51    ! [X0] : (! [X1] : ((r1_yellow_0(X0,X1) | ! [X2] : (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)))) & (? [X4] : (! [X5] : (r1_orders_2(X0,X4,X5) | ~r2_lattice3(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r2_lattice3(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_yellow_0(X0,X1))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 0.23/0.51    inference(rectify,[],[f58])).
% 0.23/0.51  fof(f58,plain,(
% 0.23/0.51    ! [X0] : (! [X1] : ((r1_yellow_0(X0,X1) | ! [X2] : (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)))) & (? [X2] : (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~r1_yellow_0(X0,X1))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 0.23/0.51    inference(nnf_transformation,[],[f37])).
% 0.23/0.51  fof(f37,plain,(
% 0.23/0.51    ! [X0] : (! [X1] : (r1_yellow_0(X0,X1) <=> ? [X2] : (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 0.23/0.51    inference(flattening,[],[f36])).
% 0.23/0.51  fof(f36,plain,(
% 0.23/0.51    ! [X0] : (! [X1] : (r1_yellow_0(X0,X1) <=> ? [X2] : (! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0)))),
% 0.23/0.51    inference(ennf_transformation,[],[f7])).
% 0.23/0.51  fof(f7,axiom,(
% 0.23/0.51    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (r1_yellow_0(X0,X1) <=> ? [X2] : (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X3) => r1_orders_2(X0,X2,X3))) & r2_lattice3(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0)))))),
% 0.23/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_yellow_0)).
% 0.23/0.51  fof(f300,plain,(
% 0.23/0.51    ( ! [X0] : (~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK6(sK0,X0,sK1)) | ~r2_lattice3(sK0,X0,sK1) | r1_yellow_0(sK0,X0)) ) | ~spl8_36),
% 0.23/0.51    inference(avatar_component_clause,[],[f299])).
% 0.23/0.51  fof(f301,plain,(
% 0.23/0.51    ~spl8_13 | ~spl8_26 | ~spl8_8 | spl8_36 | ~spl8_35),
% 0.23/0.51    inference(avatar_split_clause,[],[f297,f288,f299,f146,f240,f166])).
% 0.23/0.51  fof(f288,plain,(
% 0.23/0.51    spl8_35 <=> ! [X0] : (~m1_subset_1(sK6(sK0,X0,sK1),u1_struct_0(sK0)) | ~r2_lattice3(sK0,X0,sK1) | r1_yellow_0(sK0,X0) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK6(sK0,X0,sK1)))),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_35])])).
% 0.23/0.51  fof(f297,plain,(
% 0.23/0.51    ( ! [X0] : (~r2_lattice3(sK0,X0,sK1) | r1_yellow_0(sK0,X0) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK6(sK0,X0,sK1)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0)) ) | ~spl8_35),
% 0.23/0.51    inference(duplicate_literal_removal,[],[f296])).
% 0.23/0.51  fof(f296,plain,(
% 0.23/0.51    ( ! [X0] : (~r2_lattice3(sK0,X0,sK1) | r1_yellow_0(sK0,X0) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK6(sK0,X0,sK1)) | r1_yellow_0(sK0,X0) | ~r2_lattice3(sK0,X0,sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0)) ) | ~spl8_35),
% 0.23/0.51    inference(resolution,[],[f289,f99])).
% 0.23/0.51  fof(f99,plain,(
% 0.23/0.51    ( ! [X2,X0,X1] : (m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) | r1_yellow_0(X0,X1) | ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f62])).
% 0.23/0.51  fof(f289,plain,(
% 0.23/0.51    ( ! [X0] : (~m1_subset_1(sK6(sK0,X0,sK1),u1_struct_0(sK0)) | ~r2_lattice3(sK0,X0,sK1) | r1_yellow_0(sK0,X0) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK6(sK0,X0,sK1))) ) | ~spl8_35),
% 0.23/0.51    inference(avatar_component_clause,[],[f288])).
% 0.23/0.51  fof(f292,plain,(
% 0.23/0.51    ~spl8_26 | ~spl8_12 | ~spl8_33),
% 0.23/0.51    inference(avatar_split_clause,[],[f291,f278,f162,f240])).
% 0.23/0.51  fof(f162,plain,(
% 0.23/0.51    spl8_12 <=> v1_lattice3(sK0)),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 0.23/0.51  fof(f291,plain,(
% 0.23/0.51    ~v1_lattice3(sK0) | ~l1_orders_2(sK0) | ~spl8_33),
% 0.23/0.51    inference(resolution,[],[f279,f84])).
% 0.23/0.51  fof(f84,plain,(
% 0.23/0.51    ( ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f25])).
% 0.23/0.51  fof(f25,plain,(
% 0.23/0.51    ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0))),
% 0.23/0.51    inference(flattening,[],[f24])).
% 0.23/0.51  fof(f24,plain,(
% 0.23/0.51    ! [X0] : ((~v2_struct_0(X0) | ~v1_lattice3(X0)) | ~l1_orders_2(X0))),
% 0.23/0.51    inference(ennf_transformation,[],[f5])).
% 0.23/0.51  fof(f5,axiom,(
% 0.23/0.51    ! [X0] : (l1_orders_2(X0) => (v1_lattice3(X0) => ~v2_struct_0(X0)))),
% 0.23/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattice3)).
% 0.23/0.51  fof(f279,plain,(
% 0.23/0.51    v2_struct_0(sK0) | ~spl8_33),
% 0.23/0.51    inference(avatar_component_clause,[],[f278])).
% 0.23/0.51  fof(f290,plain,(
% 0.23/0.51    ~spl8_13 | ~spl8_26 | ~spl8_8 | spl8_35 | ~spl8_34),
% 0.23/0.51    inference(avatar_split_clause,[],[f284,f281,f288,f146,f240,f166])).
% 0.23/0.51  fof(f284,plain,(
% 0.23/0.51    ( ! [X0] : (~m1_subset_1(sK6(sK0,X0,sK1),u1_struct_0(sK0)) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK6(sK0,X0,sK1)) | r1_yellow_0(sK0,X0) | ~r2_lattice3(sK0,X0,sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0)) ) | ~spl8_34),
% 0.23/0.51    inference(resolution,[],[f282,f101])).
% 0.23/0.51  fof(f101,plain,(
% 0.23/0.51    ( ! [X2,X0,X1] : (~r1_orders_2(X0,X2,sK6(X0,X1,X2)) | r1_yellow_0(X0,X1) | ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f62])).
% 0.23/0.51  fof(f283,plain,(
% 0.23/0.51    spl8_33 | ~spl8_15 | ~spl8_26 | ~spl8_8 | spl8_34 | ~spl8_32),
% 0.23/0.51    inference(avatar_split_clause,[],[f276,f272,f281,f146,f240,f174,f278])).
% 0.23/0.51  fof(f174,plain,(
% 0.23/0.51    spl8_15 <=> v3_orders_2(sK0)),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).
% 0.23/0.51  fof(f272,plain,(
% 0.23/0.51    spl8_32 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r3_orders_2(sK0,sK1,X0) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0))),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).
% 0.23/0.51  fof(f276,plain,(
% 0.23/0.51    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | r1_orders_2(sK0,sK1,X0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl8_32),
% 0.23/0.51    inference(duplicate_literal_removal,[],[f275])).
% 0.23/0.51  fof(f275,plain,(
% 0.23/0.51    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | r1_orders_2(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl8_32),
% 0.23/0.51    inference(resolution,[],[f273,f105])).
% 0.23/0.51  fof(f105,plain,(
% 0.23/0.51    ( ! [X2,X0,X1] : (~r3_orders_2(X0,X1,X2) | r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f63])).
% 0.23/0.51  fof(f63,plain,(
% 0.23/0.51    ! [X0,X1,X2] : (((r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.23/0.51    inference(nnf_transformation,[],[f43])).
% 0.23/0.51  fof(f43,plain,(
% 0.23/0.51    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.23/0.51    inference(flattening,[],[f42])).
% 0.23/0.51  fof(f42,plain,(
% 0.23/0.51    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.23/0.51    inference(ennf_transformation,[],[f4])).
% 0.23/0.51  fof(f4,axiom,(
% 0.23/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 0.23/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).
% 0.23/0.51  fof(f273,plain,(
% 0.23/0.51    ( ! [X0] : (r3_orders_2(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)) ) | ~spl8_32),
% 0.23/0.51    inference(avatar_component_clause,[],[f272])).
% 0.23/0.51  fof(f274,plain,(
% 0.23/0.51    ~spl8_8 | spl8_32 | ~spl8_2 | ~spl8_29),
% 0.23/0.51    inference(avatar_split_clause,[],[f270,f255,f122,f272,f146])).
% 0.23/0.51  fof(f122,plain,(
% 0.23/0.51    spl8_2 <=> r3_waybel_9(sK0,sK2,sK1)),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.23/0.51  fof(f255,plain,(
% 0.23/0.51    spl8_29 <=> ! [X1,X0] : (~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK2,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r3_orders_2(sK0,X1,X0))),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).
% 0.23/0.51  fof(f270,plain,(
% 0.23/0.51    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | r3_orders_2(sK0,sK1,X0)) ) | (~spl8_2 | ~spl8_29)),
% 0.23/0.51    inference(resolution,[],[f256,f123])).
% 0.23/0.51  fof(f123,plain,(
% 0.23/0.51    r3_waybel_9(sK0,sK2,sK1) | ~spl8_2),
% 0.23/0.51    inference(avatar_component_clause,[],[f122])).
% 0.23/0.51  fof(f256,plain,(
% 0.23/0.51    ( ! [X0,X1] : (~r3_waybel_9(sK0,sK2,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r3_orders_2(sK0,X1,X0)) ) | ~spl8_29),
% 0.23/0.51    inference(avatar_component_clause,[],[f255])).
% 0.23/0.51  fof(f269,plain,(
% 0.23/0.51    ~spl8_4 | spl8_29 | ~spl8_6 | spl8_7 | ~spl8_5 | ~spl8_31),
% 0.23/0.51    inference(avatar_split_clause,[],[f268,f265,f134,f142,f138,f255,f130])).
% 0.23/0.51  fof(f138,plain,(
% 0.23/0.51    spl8_6 <=> v4_orders_2(sK2)),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.23/0.51  fof(f142,plain,(
% 0.23/0.51    spl8_7 <=> v2_struct_0(sK2)),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.23/0.51  fof(f134,plain,(
% 0.23/0.51    spl8_5 <=> v7_waybel_0(sK2)),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.23/0.51  fof(f265,plain,(
% 0.23/0.51    spl8_31 <=> ! [X1,X0,X2] : (~r2_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~l1_waybel_0(X0,sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | r3_orders_2(sK0,X2,X1) | ~r3_waybel_9(sK0,X0,X2) | ~m1_subset_1(X1,u1_struct_0(sK0)))),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).
% 0.23/0.51  fof(f268,plain,(
% 0.23/0.51    ( ! [X0,X1] : (v2_struct_0(sK2) | ~v4_orders_2(sK2) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | ~l1_waybel_0(sK2,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r3_orders_2(sK0,X1,X0) | ~r3_waybel_9(sK0,sK2,X1) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl8_5 | ~spl8_31)),
% 0.23/0.51    inference(resolution,[],[f266,f135])).
% 0.23/0.51  fof(f135,plain,(
% 0.23/0.51    v7_waybel_0(sK2) | ~spl8_5),
% 0.23/0.51    inference(avatar_component_clause,[],[f134])).
% 0.23/0.51  fof(f266,plain,(
% 0.23/0.51    ( ! [X2,X0,X1] : (~v7_waybel_0(X0) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1) | ~l1_waybel_0(X0,sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | r3_orders_2(sK0,X2,X1) | ~r3_waybel_9(sK0,X0,X2) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | ~spl8_31),
% 0.23/0.51    inference(avatar_component_clause,[],[f265])).
% 0.23/0.51  fof(f267,plain,(
% 0.23/0.51    ~spl8_17 | ~spl8_16 | ~spl8_15 | ~spl8_14 | ~spl8_13 | ~spl8_12 | ~spl8_11 | ~spl8_10 | ~spl8_9 | spl8_31 | spl8_30),
% 0.23/0.51    inference(avatar_split_clause,[],[f263,f260,f265,f150,f154,f158,f162,f166,f170,f174,f178,f182])).
% 0.23/0.51  fof(f182,plain,(
% 0.23/0.51    spl8_17 <=> v2_pre_topc(sK0)),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).
% 0.23/0.51  fof(f178,plain,(
% 0.23/0.51    spl8_16 <=> v8_pre_topc(sK0)),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).
% 0.23/0.51  fof(f170,plain,(
% 0.23/0.51    spl8_14 <=> v4_orders_2(sK0)),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 0.23/0.51  fof(f158,plain,(
% 0.23/0.51    spl8_11 <=> v2_lattice3(sK0)),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 0.23/0.51  fof(f154,plain,(
% 0.23/0.51    spl8_10 <=> v1_compts_1(sK0)),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 0.23/0.51  fof(f150,plain,(
% 0.23/0.51    spl8_9 <=> l1_waybel_9(sK0)),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.23/0.51  fof(f260,plain,(
% 0.23/0.51    spl8_30 <=> m1_subset_1(sK5(sK0),u1_struct_0(sK0))),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).
% 0.23/0.51  fof(f263,plain,(
% 0.23/0.51    ( ! [X2,X0,X1] : (~r2_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X0,X2) | r3_orders_2(sK0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_waybel_9(sK0) | ~v1_compts_1(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) ) | spl8_30),
% 0.23/0.51    inference(resolution,[],[f261,f113])).
% 0.23/0.51  fof(f113,plain,(
% 0.23/0.51    ( ! [X4,X0,X3,X1] : (m1_subset_1(sK5(X0),u1_struct_0(X0)) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X3) | r3_orders_2(X0,X3,X4) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.23/0.51    inference(duplicate_literal_removal,[],[f112])).
% 0.23/0.51  fof(f112,plain,(
% 0.23/0.51    ( ! [X4,X0,X3,X1] : (r3_orders_2(X0,X3,X4) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X3) | m1_subset_1(sK5(X0),u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.23/0.51    inference(equality_resolution,[],[f94])).
% 0.23/0.51  fof(f94,plain,(
% 0.23/0.51    ( ! [X4,X2,X0,X3,X1] : (r3_orders_2(X0,X3,X4) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X2) | m1_subset_1(sK5(X0),u1_struct_0(X0)) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f57])).
% 0.23/0.51  fof(f57,plain,(
% 0.23/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r3_orders_2(X0,X3,X4) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_waybel_9(X0,X1,X2) | (~v5_pre_topc(k4_waybel_1(X0,sK5(X0)),X0,X0) & m1_subset_1(sK5(X0),u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.23/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f55,f56])).
% 0.23/0.51  fof(f56,plain,(
% 0.23/0.51    ! [X0] : (? [X5] : (~v5_pre_topc(k4_waybel_1(X0,X5),X0,X0) & m1_subset_1(X5,u1_struct_0(X0))) => (~v5_pre_topc(k4_waybel_1(X0,sK5(X0)),X0,X0) & m1_subset_1(sK5(X0),u1_struct_0(X0))))),
% 0.23/0.51    introduced(choice_axiom,[])).
% 0.23/0.51  fof(f55,plain,(
% 0.23/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r3_orders_2(X0,X3,X4) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_waybel_9(X0,X1,X2) | ? [X5] : (~v5_pre_topc(k4_waybel_1(X0,X5),X0,X0) & m1_subset_1(X5,u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.23/0.51    inference(rectify,[],[f35])).
% 0.23/0.51  fof(f35,plain,(
% 0.23/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X5] : (r3_orders_2(X0,X3,X5) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~r3_waybel_9(X0,X1,X2) | ? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.23/0.51    inference(flattening,[],[f34])).
% 0.23/0.51  fof(f34,plain,(
% 0.23/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((! [X5] : ((r3_orders_2(X0,X3,X5) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5)) | ~m1_subset_1(X5,u1_struct_0(X0))) | (~r3_waybel_9(X0,X1,X2) | ? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.23/0.51    inference(ennf_transformation,[],[f16])).
% 0.23/0.51  fof(f16,plain,(
% 0.23/0.51    ! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r3_waybel_9(X0,X1,X2) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)) & X2 = X3) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X0)) => (r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5) => r3_orders_2(X0,X3,X5))))))))),
% 0.23/0.51    inference(rectify,[],[f13])).
% 0.23/0.51  fof(f13,axiom,(
% 0.23/0.51    ! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r3_waybel_9(X0,X1,X2) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)) & X2 = X3) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) => r3_orders_2(X0,X3,X4))))))))),
% 0.23/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_waybel_9)).
% 0.23/0.51  fof(f261,plain,(
% 0.23/0.51    ~m1_subset_1(sK5(sK0),u1_struct_0(sK0)) | spl8_30),
% 0.23/0.51    inference(avatar_component_clause,[],[f260])).
% 0.23/0.51  fof(f262,plain,(
% 0.23/0.51    ~spl8_30 | spl8_28),
% 0.23/0.51    inference(avatar_split_clause,[],[f258,f252,f260])).
% 0.23/0.51  fof(f252,plain,(
% 0.23/0.51    spl8_28 <=> v5_pre_topc(k4_waybel_1(sK0,sK5(sK0)),sK0,sK0)),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).
% 0.23/0.51  fof(f258,plain,(
% 0.23/0.51    ~m1_subset_1(sK5(sK0),u1_struct_0(sK0)) | spl8_28),
% 0.23/0.51    inference(resolution,[],[f253,f78])).
% 0.23/0.51  fof(f78,plain,(
% 0.23/0.51    ( ! [X3] : (v5_pre_topc(k4_waybel_1(sK0,X3),sK0,sK0) | ~m1_subset_1(X3,u1_struct_0(sK0))) )),
% 0.23/0.51    inference(cnf_transformation,[],[f47])).
% 0.23/0.51  fof(f47,plain,(
% 0.23/0.51    ((sK1 != k1_waybel_2(sK0,sK2) & r3_waybel_9(sK0,sK2,sK1) & v10_waybel_0(sK2,sK0) & ! [X3] : (v5_pre_topc(k4_waybel_1(sK0,X3),sK0,sK0) | ~m1_subset_1(X3,u1_struct_0(sK0))) & l1_waybel_0(sK2,sK0) & v7_waybel_0(sK2) & v4_orders_2(sK2) & ~v2_struct_0(sK2)) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_waybel_9(sK0) & v1_compts_1(sK0) & v2_lattice3(sK0) & v1_lattice3(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & v8_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.23/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f46,f45,f44])).
% 0.23/0.51  fof(f44,plain,(
% 0.23/0.51    ? [X0] : (? [X1] : (? [X2] : (k1_waybel_2(X0,X2) != X1 & r3_waybel_9(X0,X2,X1) & v10_waybel_0(X2,X0) & ! [X3] : (v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0))) & l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (k1_waybel_2(sK0,X2) != X1 & r3_waybel_9(sK0,X2,X1) & v10_waybel_0(X2,sK0) & ! [X3] : (v5_pre_topc(k4_waybel_1(sK0,X3),sK0,sK0) | ~m1_subset_1(X3,u1_struct_0(sK0))) & l1_waybel_0(X2,sK0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_waybel_9(sK0) & v1_compts_1(sK0) & v2_lattice3(sK0) & v1_lattice3(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & v8_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.23/0.51    introduced(choice_axiom,[])).
% 0.23/0.51  fof(f45,plain,(
% 0.23/0.51    ? [X1] : (? [X2] : (k1_waybel_2(sK0,X2) != X1 & r3_waybel_9(sK0,X2,X1) & v10_waybel_0(X2,sK0) & ! [X3] : (v5_pre_topc(k4_waybel_1(sK0,X3),sK0,sK0) | ~m1_subset_1(X3,u1_struct_0(sK0))) & l1_waybel_0(X2,sK0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : (k1_waybel_2(sK0,X2) != sK1 & r3_waybel_9(sK0,X2,sK1) & v10_waybel_0(X2,sK0) & ! [X3] : (v5_pre_topc(k4_waybel_1(sK0,X3),sK0,sK0) | ~m1_subset_1(X3,u1_struct_0(sK0))) & l1_waybel_0(X2,sK0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.23/0.51    introduced(choice_axiom,[])).
% 0.23/0.51  fof(f46,plain,(
% 0.23/0.51    ? [X2] : (k1_waybel_2(sK0,X2) != sK1 & r3_waybel_9(sK0,X2,sK1) & v10_waybel_0(X2,sK0) & ! [X3] : (v5_pre_topc(k4_waybel_1(sK0,X3),sK0,sK0) | ~m1_subset_1(X3,u1_struct_0(sK0))) & l1_waybel_0(X2,sK0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) => (sK1 != k1_waybel_2(sK0,sK2) & r3_waybel_9(sK0,sK2,sK1) & v10_waybel_0(sK2,sK0) & ! [X3] : (v5_pre_topc(k4_waybel_1(sK0,X3),sK0,sK0) | ~m1_subset_1(X3,u1_struct_0(sK0))) & l1_waybel_0(sK2,sK0) & v7_waybel_0(sK2) & v4_orders_2(sK2) & ~v2_struct_0(sK2))),
% 0.23/0.51    introduced(choice_axiom,[])).
% 0.23/0.51  fof(f21,plain,(
% 0.23/0.51    ? [X0] : (? [X1] : (? [X2] : (k1_waybel_2(X0,X2) != X1 & r3_waybel_9(X0,X2,X1) & v10_waybel_0(X2,X0) & ! [X3] : (v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0))) & l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0))),
% 0.23/0.51    inference(flattening,[],[f20])).
% 0.23/0.51  fof(f20,plain,(
% 0.23/0.51    ? [X0] : (? [X1] : (? [X2] : ((k1_waybel_2(X0,X2) != X1 & (r3_waybel_9(X0,X2,X1) & v10_waybel_0(X2,X0) & ! [X3] : (v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0))))) & (l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.23/0.51    inference(ennf_transformation,[],[f15])).
% 0.23/0.51  fof(f15,negated_conjecture,(
% 0.23/0.51    ~! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) => ((r3_waybel_9(X0,X2,X1) & v10_waybel_0(X2,X0) & ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X3),X0,X0))) => k1_waybel_2(X0,X2) = X1))))),
% 0.23/0.51    inference(negated_conjecture,[],[f14])).
% 0.23/0.51  fof(f14,conjecture,(
% 0.23/0.51    ! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) => ((r3_waybel_9(X0,X2,X1) & v10_waybel_0(X2,X0) & ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X3),X0,X0))) => k1_waybel_2(X0,X2) = X1))))),
% 0.23/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_waybel_9)).
% 0.23/0.51  fof(f253,plain,(
% 0.23/0.51    ~v5_pre_topc(k4_waybel_1(sK0,sK5(sK0)),sK0,sK0) | spl8_28),
% 0.23/0.51    inference(avatar_component_clause,[],[f252])).
% 0.23/0.51  fof(f257,plain,(
% 0.23/0.51    ~spl8_28 | ~spl8_4 | ~spl8_9 | spl8_29 | ~spl8_11 | ~spl8_12 | ~spl8_13 | ~spl8_14 | ~spl8_15 | ~spl8_16 | ~spl8_17 | ~spl8_10 | ~spl8_27),
% 0.23/0.51    inference(avatar_split_clause,[],[f250,f247,f154,f182,f178,f174,f170,f166,f162,f158,f255,f150,f130,f252])).
% 0.23/0.51  fof(f247,plain,(
% 0.23/0.51    spl8_27 <=> ! [X1,X0,X2] : (~r2_lattice3(X0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(X0),u1_waybel_0(X0,sK2)),X1) | ~v2_pre_topc(X0) | ~v8_pre_topc(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~v1_lattice3(X0) | ~v2_lattice3(X0) | ~v1_compts_1(X0) | ~l1_waybel_9(X0) | r3_orders_2(X0,X2,X1) | ~l1_waybel_0(sK2,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v5_pre_topc(k4_waybel_1(X0,sK5(X0)),X0,X0) | ~r3_waybel_9(X0,sK2,X2) | ~m1_subset_1(X1,u1_struct_0(X0)))),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).
% 0.23/0.51  fof(f250,plain,(
% 0.23/0.51    ( ! [X0,X1] : (~v2_pre_topc(sK0) | ~v8_pre_topc(sK0) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~v1_lattice3(sK0) | ~v2_lattice3(sK0) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | ~l1_waybel_9(sK0) | r3_orders_2(sK0,X1,X0) | ~l1_waybel_0(sK2,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v5_pre_topc(k4_waybel_1(sK0,sK5(sK0)),sK0,sK0) | ~r3_waybel_9(sK0,sK2,X1) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl8_10 | ~spl8_27)),
% 0.23/0.51    inference(resolution,[],[f248,f155])).
% 0.23/0.51  fof(f155,plain,(
% 0.23/0.51    v1_compts_1(sK0) | ~spl8_10),
% 0.23/0.51    inference(avatar_component_clause,[],[f154])).
% 0.23/0.51  fof(f248,plain,(
% 0.23/0.51    ( ! [X2,X0,X1] : (~v1_compts_1(X0) | ~v2_pre_topc(X0) | ~v8_pre_topc(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~v1_lattice3(X0) | ~v2_lattice3(X0) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(X0),u1_waybel_0(X0,sK2)),X1) | ~l1_waybel_9(X0) | r3_orders_2(X0,X2,X1) | ~l1_waybel_0(sK2,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v5_pre_topc(k4_waybel_1(X0,sK5(X0)),X0,X0) | ~r3_waybel_9(X0,sK2,X2) | ~m1_subset_1(X1,u1_struct_0(X0))) ) | ~spl8_27),
% 0.23/0.51    inference(avatar_component_clause,[],[f247])).
% 0.23/0.51  fof(f249,plain,(
% 0.23/0.51    spl8_7 | ~spl8_6 | spl8_27 | ~spl8_5),
% 0.23/0.51    inference(avatar_split_clause,[],[f245,f134,f247,f138,f142])).
% 0.23/0.51  fof(f245,plain,(
% 0.23/0.51    ( ! [X2,X0,X1] : (~r2_lattice3(X0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(X0),u1_waybel_0(X0,sK2)),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r3_waybel_9(X0,sK2,X2) | ~v5_pre_topc(k4_waybel_1(X0,sK5(X0)),X0,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(sK2,X0) | r3_orders_2(X0,X2,X1) | ~v4_orders_2(sK2) | v2_struct_0(sK2) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl8_5),
% 0.23/0.51    inference(resolution,[],[f114,f135])).
% 0.23/0.51  fof(f114,plain,(
% 0.23/0.51    ( ! [X4,X0,X3,X1] : (~v7_waybel_0(X1) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X3) | ~v5_pre_topc(k4_waybel_1(X0,sK5(X0)),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | r3_orders_2(X0,X3,X4) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.23/0.51    inference(duplicate_literal_removal,[],[f111])).
% 0.23/0.51  fof(f111,plain,(
% 0.23/0.51    ( ! [X4,X0,X3,X1] : (r3_orders_2(X0,X3,X4) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X3) | ~v5_pre_topc(k4_waybel_1(X0,sK5(X0)),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.23/0.51    inference(equality_resolution,[],[f95])).
% 0.23/0.51  fof(f95,plain,(
% 0.23/0.51    ( ! [X4,X2,X0,X3,X1] : (r3_orders_2(X0,X3,X4) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X2) | ~v5_pre_topc(k4_waybel_1(X0,sK5(X0)),X0,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f57])).
% 0.23/0.51  fof(f244,plain,(
% 0.23/0.51    ~spl8_9 | spl8_26),
% 0.23/0.51    inference(avatar_split_clause,[],[f243,f240,f150])).
% 0.23/0.51  fof(f243,plain,(
% 0.23/0.51    ~l1_waybel_9(sK0) | spl8_26),
% 0.23/0.51    inference(resolution,[],[f241,f82])).
% 0.23/0.51  fof(f82,plain,(
% 0.23/0.51    ( ! [X0] : (l1_orders_2(X0) | ~l1_waybel_9(X0)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f22])).
% 0.23/0.51  fof(f22,plain,(
% 0.23/0.51    ! [X0] : (l1_orders_2(X0) | ~l1_waybel_9(X0))),
% 0.23/0.51    inference(ennf_transformation,[],[f17])).
% 0.23/0.51  fof(f17,plain,(
% 0.23/0.51    ! [X0] : (l1_waybel_9(X0) => l1_orders_2(X0))),
% 0.23/0.51    inference(pure_predicate_removal,[],[f11])).
% 0.23/0.51  fof(f11,axiom,(
% 0.23/0.51    ! [X0] : (l1_waybel_9(X0) => (l1_orders_2(X0) & l1_pre_topc(X0)))),
% 0.23/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_waybel_9)).
% 0.23/0.51  fof(f241,plain,(
% 0.23/0.51    ~l1_orders_2(sK0) | spl8_26),
% 0.23/0.51    inference(avatar_component_clause,[],[f240])).
% 0.23/0.51  fof(f242,plain,(
% 0.23/0.51    ~spl8_26 | spl8_24),
% 0.23/0.51    inference(avatar_split_clause,[],[f238,f232,f240])).
% 0.23/0.51  fof(f238,plain,(
% 0.23/0.51    ~l1_orders_2(sK0) | spl8_24),
% 0.23/0.51    inference(resolution,[],[f233,f83])).
% 0.23/0.51  fof(f83,plain,(
% 0.23/0.51    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f23])).
% 0.23/0.51  fof(f23,plain,(
% 0.23/0.51    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 0.23/0.51    inference(ennf_transformation,[],[f3])).
% 0.23/0.51  fof(f3,axiom,(
% 0.23/0.51    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 0.23/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 0.23/0.51  fof(f233,plain,(
% 0.23/0.51    ~l1_struct_0(sK0) | spl8_24),
% 0.23/0.51    inference(avatar_component_clause,[],[f232])).
% 0.23/0.51  fof(f229,plain,(
% 0.23/0.51    ~spl8_8 | spl8_23 | ~spl8_2 | ~spl8_20),
% 0.23/0.51    inference(avatar_split_clause,[],[f224,f199,f122,f227,f146])).
% 0.23/0.51  fof(f199,plain,(
% 0.23/0.51    spl8_20 <=> ! [X0] : (r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | ~r3_waybel_9(sK0,sK2,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)))),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).
% 0.23/0.51  fof(f224,plain,(
% 0.23/0.51    r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | (~spl8_2 | ~spl8_20)),
% 0.23/0.51    inference(resolution,[],[f200,f123])).
% 0.23/0.51  fof(f200,plain,(
% 0.23/0.51    ( ! [X0] : (~r3_waybel_9(sK0,sK2,X0) | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl8_20),
% 0.23/0.51    inference(avatar_component_clause,[],[f199])).
% 0.23/0.51  fof(f223,plain,(
% 0.23/0.51    spl8_20 | ~spl8_4 | ~spl8_5 | ~spl8_6 | spl8_7 | ~spl8_3 | ~spl8_22),
% 0.23/0.51    inference(avatar_split_clause,[],[f221,f218,f126,f142,f138,f134,f130,f199])).
% 0.23/0.51  fof(f126,plain,(
% 0.23/0.51    spl8_3 <=> v10_waybel_0(sK2,sK0)),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.23/0.51  fof(f218,plain,(
% 0.23/0.51    spl8_22 <=> ! [X1,X0] : (~r3_waybel_9(sK0,X0,X1) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~l1_waybel_0(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1) | ~v10_waybel_0(X0,sK0))),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).
% 0.23/0.51  fof(f221,plain,(
% 0.23/0.51    ( ! [X0] : (v2_struct_0(sK2) | ~v4_orders_2(sK2) | ~v7_waybel_0(sK2) | ~l1_waybel_0(sK2,sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | ~r3_waybel_9(sK0,sK2,X0)) ) | (~spl8_3 | ~spl8_22)),
% 0.23/0.51    inference(resolution,[],[f219,f127])).
% 0.23/0.51  fof(f127,plain,(
% 0.23/0.51    v10_waybel_0(sK2,sK0) | ~spl8_3),
% 0.23/0.51    inference(avatar_component_clause,[],[f126])).
% 0.23/0.51  fof(f219,plain,(
% 0.23/0.51    ( ! [X0,X1] : (~v10_waybel_0(X0,sK0) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~l1_waybel_0(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1) | ~r3_waybel_9(sK0,X0,X1)) ) | ~spl8_22),
% 0.23/0.51    inference(avatar_component_clause,[],[f218])).
% 0.23/0.51  fof(f220,plain,(
% 0.23/0.51    ~spl8_17 | ~spl8_16 | ~spl8_15 | ~spl8_14 | ~spl8_13 | ~spl8_12 | ~spl8_11 | ~spl8_10 | ~spl8_9 | spl8_22 | spl8_21),
% 0.23/0.51    inference(avatar_split_clause,[],[f216,f213,f218,f150,f154,f158,f162,f166,f170,f174,f178,f182])).
% 0.23/0.51  fof(f213,plain,(
% 0.23/0.51    spl8_21 <=> m1_subset_1(sK4(sK0),u1_struct_0(sK0))),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).
% 0.23/0.51  fof(f216,plain,(
% 0.23/0.51    ( ! [X0,X1] : (~r3_waybel_9(sK0,X0,X1) | ~v10_waybel_0(X0,sK0) | r2_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_waybel_9(sK0) | ~v1_compts_1(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) ) | spl8_21),
% 0.23/0.51    inference(resolution,[],[f214,f115])).
% 0.23/0.51  fof(f115,plain,(
% 0.23/0.51    ( ! [X0,X3,X1] : (m1_subset_1(sK4(X0),u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X3) | ~v10_waybel_0(X1,X0) | r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.23/0.51    inference(duplicate_literal_removal,[],[f110])).
% 0.23/0.51  fof(f110,plain,(
% 0.23/0.51    ( ! [X0,X3,X1] : (r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X3) | ~v10_waybel_0(X1,X0) | m1_subset_1(sK4(X0),u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.23/0.51    inference(equality_resolution,[],[f92])).
% 0.23/0.51  fof(f92,plain,(
% 0.23/0.51    ( ! [X2,X0,X3,X1] : (r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X2) | ~v10_waybel_0(X1,X0) | m1_subset_1(sK4(X0),u1_struct_0(X0)) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f54])).
% 0.23/0.51  fof(f54,plain,(
% 0.23/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X2) | ~v10_waybel_0(X1,X0) | (~v5_pre_topc(k4_waybel_1(X0,sK4(X0)),X0,X0) & m1_subset_1(sK4(X0),u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.23/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f33,f53])).
% 0.23/0.51  fof(f53,plain,(
% 0.23/0.51    ! [X0] : (? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) => (~v5_pre_topc(k4_waybel_1(X0,sK4(X0)),X0,X0) & m1_subset_1(sK4(X0),u1_struct_0(X0))))),
% 0.23/0.51    introduced(choice_axiom,[])).
% 0.23/0.51  fof(f33,plain,(
% 0.23/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X2) | ~v10_waybel_0(X1,X0) | ? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.23/0.51    inference(flattening,[],[f32])).
% 0.23/0.51  fof(f32,plain,(
% 0.23/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | (~r3_waybel_9(X0,X1,X2) | ~v10_waybel_0(X1,X0) | ? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.23/0.51    inference(ennf_transformation,[],[f12])).
% 0.23/0.51  fof(f12,axiom,(
% 0.23/0.51    ! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r3_waybel_9(X0,X1,X2) & v10_waybel_0(X1,X0) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)) & X2 = X3) => r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3))))))),
% 0.23/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l48_waybel_9)).
% 0.23/0.51  fof(f214,plain,(
% 0.23/0.51    ~m1_subset_1(sK4(sK0),u1_struct_0(sK0)) | spl8_21),
% 0.23/0.51    inference(avatar_component_clause,[],[f213])).
% 0.23/0.51  fof(f215,plain,(
% 0.23/0.51    ~spl8_21 | spl8_19),
% 0.23/0.51    inference(avatar_split_clause,[],[f211,f195,f213])).
% 0.23/0.51  fof(f195,plain,(
% 0.23/0.51    spl8_19 <=> v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0)),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).
% 0.23/0.51  fof(f211,plain,(
% 0.23/0.51    ~m1_subset_1(sK4(sK0),u1_struct_0(sK0)) | spl8_19),
% 0.23/0.51    inference(resolution,[],[f196,f78])).
% 0.23/0.51  fof(f196,plain,(
% 0.23/0.51    ~v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0) | spl8_19),
% 0.23/0.51    inference(avatar_component_clause,[],[f195])).
% 0.23/0.51  fof(f210,plain,(
% 0.23/0.51    ~spl8_19 | ~spl8_4 | spl8_20 | ~spl8_9 | ~spl8_10 | ~spl8_11 | ~spl8_12 | ~spl8_13 | ~spl8_14 | ~spl8_15 | ~spl8_16 | ~spl8_17 | ~spl8_3 | ~spl8_18),
% 0.23/0.51    inference(avatar_split_clause,[],[f193,f190,f126,f182,f178,f174,f170,f166,f162,f158,f154,f150,f199,f130,f195])).
% 0.23/0.52  fof(f190,plain,(
% 0.23/0.52    spl8_18 <=> ! [X1,X0] : (~r3_waybel_9(X0,sK2,X1) | ~v2_pre_topc(X0) | ~v8_pre_topc(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~v1_lattice3(X0) | ~v2_lattice3(X0) | ~v1_compts_1(X0) | ~l1_waybel_9(X0) | r2_lattice3(X0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(X0),u1_waybel_0(X0,sK2)),X1) | ~l1_waybel_0(sK2,X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v5_pre_topc(k4_waybel_1(X0,sK4(X0)),X0,X0) | ~v10_waybel_0(sK2,X0))),
% 0.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).
% 0.23/0.52  fof(f193,plain,(
% 0.23/0.52    ( ! [X0] : (~v2_pre_topc(sK0) | ~v8_pre_topc(sK0) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~v1_lattice3(sK0) | ~v2_lattice3(sK0) | ~v1_compts_1(sK0) | ~l1_waybel_9(sK0) | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | ~l1_waybel_0(sK2,sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0) | ~r3_waybel_9(sK0,sK2,X0)) ) | (~spl8_3 | ~spl8_18)),
% 0.23/0.52    inference(resolution,[],[f191,f127])).
% 0.23/0.52  fof(f191,plain,(
% 0.23/0.52    ( ! [X0,X1] : (~v10_waybel_0(sK2,X0) | ~v2_pre_topc(X0) | ~v8_pre_topc(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~v1_lattice3(X0) | ~v2_lattice3(X0) | ~v1_compts_1(X0) | ~l1_waybel_9(X0) | r2_lattice3(X0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(X0),u1_waybel_0(X0,sK2)),X1) | ~l1_waybel_0(sK2,X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v5_pre_topc(k4_waybel_1(X0,sK4(X0)),X0,X0) | ~r3_waybel_9(X0,sK2,X1)) ) | ~spl8_18),
% 0.23/0.52    inference(avatar_component_clause,[],[f190])).
% 0.23/0.52  fof(f192,plain,(
% 0.23/0.52    spl8_7 | ~spl8_6 | spl8_18 | ~spl8_5),
% 0.23/0.52    inference(avatar_split_clause,[],[f186,f134,f190,f138,f142])).
% 0.23/0.52  fof(f186,plain,(
% 0.23/0.52    ( ! [X0,X1] : (~r3_waybel_9(X0,sK2,X1) | ~v10_waybel_0(sK2,X0) | ~v5_pre_topc(k4_waybel_1(X0,sK4(X0)),X0,X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_waybel_0(sK2,X0) | r2_lattice3(X0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(X0),u1_waybel_0(X0,sK2)),X1) | ~v4_orders_2(sK2) | v2_struct_0(sK2) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl8_5),
% 0.23/0.52    inference(resolution,[],[f116,f135])).
% 0.23/0.52  fof(f116,plain,(
% 0.23/0.52    ( ! [X0,X3,X1] : (~v7_waybel_0(X1) | ~r3_waybel_9(X0,X1,X3) | ~v10_waybel_0(X1,X0) | ~v5_pre_topc(k4_waybel_1(X0,sK4(X0)),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.23/0.52    inference(duplicate_literal_removal,[],[f109])).
% 0.23/0.52  fof(f109,plain,(
% 0.23/0.52    ( ! [X0,X3,X1] : (r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X3) | ~v10_waybel_0(X1,X0) | ~v5_pre_topc(k4_waybel_1(X0,sK4(X0)),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.23/0.52    inference(equality_resolution,[],[f93])).
% 0.23/0.52  fof(f93,plain,(
% 0.23/0.52    ( ! [X2,X0,X3,X1] : (r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X2) | ~v10_waybel_0(X1,X0) | ~v5_pre_topc(k4_waybel_1(X0,sK4(X0)),X0,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.23/0.52    inference(cnf_transformation,[],[f54])).
% 0.23/0.52  fof(f184,plain,(
% 0.23/0.52    spl8_17),
% 0.23/0.52    inference(avatar_split_clause,[],[f64,f182])).
% 0.23/0.52  fof(f64,plain,(
% 0.23/0.52    v2_pre_topc(sK0)),
% 0.23/0.52    inference(cnf_transformation,[],[f47])).
% 0.23/0.52  fof(f180,plain,(
% 0.23/0.52    spl8_16),
% 0.23/0.52    inference(avatar_split_clause,[],[f65,f178])).
% 0.23/0.52  fof(f65,plain,(
% 0.23/0.52    v8_pre_topc(sK0)),
% 0.23/0.52    inference(cnf_transformation,[],[f47])).
% 0.23/0.52  fof(f176,plain,(
% 0.23/0.52    spl8_15),
% 0.23/0.52    inference(avatar_split_clause,[],[f66,f174])).
% 0.23/0.52  fof(f66,plain,(
% 0.23/0.52    v3_orders_2(sK0)),
% 0.23/0.52    inference(cnf_transformation,[],[f47])).
% 0.23/0.52  fof(f172,plain,(
% 0.23/0.52    spl8_14),
% 0.23/0.52    inference(avatar_split_clause,[],[f67,f170])).
% 0.23/0.52  fof(f67,plain,(
% 0.23/0.52    v4_orders_2(sK0)),
% 0.23/0.52    inference(cnf_transformation,[],[f47])).
% 0.23/0.52  fof(f168,plain,(
% 0.23/0.52    spl8_13),
% 0.23/0.52    inference(avatar_split_clause,[],[f68,f166])).
% 0.23/0.52  fof(f68,plain,(
% 0.23/0.52    v5_orders_2(sK0)),
% 0.23/0.52    inference(cnf_transformation,[],[f47])).
% 0.23/0.52  fof(f164,plain,(
% 0.23/0.52    spl8_12),
% 0.23/0.52    inference(avatar_split_clause,[],[f69,f162])).
% 0.23/0.52  fof(f69,plain,(
% 0.23/0.52    v1_lattice3(sK0)),
% 0.23/0.52    inference(cnf_transformation,[],[f47])).
% 0.23/0.52  fof(f160,plain,(
% 0.23/0.52    spl8_11),
% 0.23/0.52    inference(avatar_split_clause,[],[f70,f158])).
% 0.23/0.52  fof(f70,plain,(
% 0.23/0.52    v2_lattice3(sK0)),
% 0.23/0.52    inference(cnf_transformation,[],[f47])).
% 0.23/0.52  fof(f156,plain,(
% 0.23/0.52    spl8_10),
% 0.23/0.52    inference(avatar_split_clause,[],[f71,f154])).
% 0.23/0.52  fof(f71,plain,(
% 0.23/0.52    v1_compts_1(sK0)),
% 0.23/0.52    inference(cnf_transformation,[],[f47])).
% 0.23/0.52  fof(f152,plain,(
% 0.23/0.52    spl8_9),
% 0.23/0.52    inference(avatar_split_clause,[],[f72,f150])).
% 0.23/0.52  fof(f72,plain,(
% 0.23/0.52    l1_waybel_9(sK0)),
% 0.23/0.52    inference(cnf_transformation,[],[f47])).
% 0.23/0.52  fof(f148,plain,(
% 0.23/0.52    spl8_8),
% 0.23/0.52    inference(avatar_split_clause,[],[f73,f146])).
% 0.23/0.52  fof(f73,plain,(
% 0.23/0.52    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.23/0.52    inference(cnf_transformation,[],[f47])).
% 0.23/0.52  fof(f144,plain,(
% 0.23/0.52    ~spl8_7),
% 0.23/0.52    inference(avatar_split_clause,[],[f74,f142])).
% 0.23/0.52  fof(f74,plain,(
% 0.23/0.52    ~v2_struct_0(sK2)),
% 0.23/0.52    inference(cnf_transformation,[],[f47])).
% 0.23/0.52  fof(f140,plain,(
% 0.23/0.52    spl8_6),
% 0.23/0.52    inference(avatar_split_clause,[],[f75,f138])).
% 0.23/0.52  fof(f75,plain,(
% 0.23/0.52    v4_orders_2(sK2)),
% 0.23/0.52    inference(cnf_transformation,[],[f47])).
% 0.23/0.52  fof(f136,plain,(
% 0.23/0.52    spl8_5),
% 0.23/0.52    inference(avatar_split_clause,[],[f76,f134])).
% 0.23/0.52  fof(f76,plain,(
% 0.23/0.52    v7_waybel_0(sK2)),
% 0.23/0.52    inference(cnf_transformation,[],[f47])).
% 0.23/0.52  fof(f132,plain,(
% 0.23/0.52    spl8_4),
% 0.23/0.52    inference(avatar_split_clause,[],[f77,f130])).
% 0.23/0.52  fof(f77,plain,(
% 0.23/0.52    l1_waybel_0(sK2,sK0)),
% 0.23/0.52    inference(cnf_transformation,[],[f47])).
% 0.23/0.52  fof(f128,plain,(
% 0.23/0.52    spl8_3),
% 0.23/0.52    inference(avatar_split_clause,[],[f79,f126])).
% 0.23/0.52  fof(f79,plain,(
% 0.23/0.52    v10_waybel_0(sK2,sK0)),
% 0.23/0.52    inference(cnf_transformation,[],[f47])).
% 0.23/0.52  fof(f124,plain,(
% 0.23/0.52    spl8_2),
% 0.23/0.52    inference(avatar_split_clause,[],[f80,f122])).
% 0.23/0.52  fof(f80,plain,(
% 0.23/0.52    r3_waybel_9(sK0,sK2,sK1)),
% 0.23/0.52    inference(cnf_transformation,[],[f47])).
% 0.23/0.52  fof(f120,plain,(
% 0.23/0.52    ~spl8_1),
% 0.23/0.52    inference(avatar_split_clause,[],[f81,f118])).
% 0.23/0.52  fof(f81,plain,(
% 0.23/0.52    sK1 != k1_waybel_2(sK0,sK2)),
% 0.23/0.52    inference(cnf_transformation,[],[f47])).
% 0.23/0.52  % SZS output end Proof for theBenchmark
% 0.23/0.52  % (9108)------------------------------
% 0.23/0.52  % (9108)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.52  % (9108)Termination reason: Refutation
% 0.23/0.52  
% 0.23/0.52  % (9108)Memory used [KB]: 11129
% 0.23/0.52  % (9108)Time elapsed: 0.026 s
% 0.23/0.52  % (9108)------------------------------
% 0.23/0.52  % (9108)------------------------------
% 0.23/0.52  % (9101)Success in time 0.151 s
%------------------------------------------------------------------------------
