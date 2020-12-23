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
% DateTime   : Thu Dec  3 13:23:17 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  226 ( 553 expanded)
%              Number of leaves         :   58 ( 279 expanded)
%              Depth                    :   11
%              Number of atoms          : 1442 (5363 expanded)
%              Number of equality atoms :   68 ( 310 expanded)
%              Maximal formula depth    :   27 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f371,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f101,f105,f109,f113,f117,f121,f125,f129,f133,f137,f141,f145,f149,f153,f157,f161,f165,f173,f191,f196,f201,f204,f210,f218,f223,f225,f230,f238,f243,f248,f250,f255,f261,f301,f306,f313,f336,f339,f341,f346,f370])).

fof(f370,plain,
    ( spl6_43
    | ~ spl6_40
    | ~ spl6_25
    | ~ spl6_41 ),
    inference(avatar_split_clause,[],[f369,f299,f216,f291,f311])).

fof(f311,plain,
    ( spl6_43
  <=> sK1 = k2_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).

fof(f291,plain,
    ( spl6_40
  <=> r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).

fof(f216,plain,
    ( spl6_25
  <=> r1_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f299,plain,
    ( spl6_41
  <=> ! [X0] :
        ( ~ r1_lattice3(sK0,X0,sK1)
        | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK5(sK0,sK1,X0))
        | sK1 = k2_yellow_0(sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).

fof(f369,plain,
    ( ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))))
    | sK1 = k2_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)))
    | ~ spl6_25
    | ~ spl6_41 ),
    inference(resolution,[],[f300,f217])).

fof(f217,plain,
    ( r1_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),sK1)
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f216])).

fof(f300,plain,
    ( ! [X0] :
        ( ~ r1_lattice3(sK0,X0,sK1)
        | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK5(sK0,sK1,X0))
        | sK1 = k2_yellow_0(sK0,X0) )
    | ~ spl6_41 ),
    inference(avatar_component_clause,[],[f299])).

fof(f346,plain,
    ( spl6_45
    | ~ spl6_26
    | ~ spl6_4
    | spl6_1
    | ~ spl6_47 ),
    inference(avatar_split_clause,[],[f343,f333,f99,f111,f221,f327])).

fof(f327,plain,
    ( spl6_45
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).

fof(f221,plain,
    ( spl6_26
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f111,plain,
    ( spl6_4
  <=> l1_waybel_0(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f99,plain,
    ( spl6_1
  <=> sK1 = k1_waybel_9(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f333,plain,
    ( spl6_47
  <=> sK1 = k5_yellow_2(sK0,u1_waybel_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_47])])).

fof(f343,plain,
    ( sK1 = k1_waybel_9(sK0,sK2)
    | ~ l1_waybel_0(sK2,sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_47 ),
    inference(superposition,[],[f72,f334])).

fof(f334,plain,
    ( sK1 = k5_yellow_2(sK0,u1_waybel_0(sK0,sK2))
    | ~ spl6_47 ),
    inference(avatar_component_clause,[],[f333])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k1_waybel_9(X0,X1) = k5_yellow_2(X0,u1_waybel_0(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_waybel_9(X0,X1) = k5_yellow_2(X0,u1_waybel_0(X0,X1))
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_waybel_9(X0,X1) = k5_yellow_2(X0,u1_waybel_0(X0,X1))
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => k1_waybel_9(X0,X1) = k5_yellow_2(X0,u1_waybel_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_waybel_9)).

fof(f341,plain,
    ( ~ spl6_26
    | ~ spl6_11
    | ~ spl6_45 ),
    inference(avatar_split_clause,[],[f340,f327,f139,f221])).

fof(f139,plain,
    ( spl6_11
  <=> v2_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f340,plain,
    ( ~ v2_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ spl6_45 ),
    inference(resolution,[],[f328,f70])).

fof(f70,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

% (18228)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_lattice3)).

fof(f328,plain,
    ( v2_struct_0(sK0)
    | ~ spl6_45 ),
    inference(avatar_component_clause,[],[f327])).

fof(f339,plain,
    ( ~ spl6_24
    | ~ spl6_4
    | spl6_46 ),
    inference(avatar_split_clause,[],[f338,f330,f111,f213])).

fof(f213,plain,
    ( spl6_24
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f330,plain,
    ( spl6_46
  <=> v1_relat_1(u1_waybel_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).

fof(f338,plain,
    ( ~ l1_waybel_0(sK2,sK0)
    | ~ l1_struct_0(sK0)
    | spl6_46 ),
    inference(resolution,[],[f337,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_1(u1_waybel_0(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(u1_waybel_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_waybel_0)).

fof(f337,plain,
    ( ! [X0,X1] : ~ m1_subset_1(u1_waybel_0(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl6_46 ),
    inference(resolution,[],[f331,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f331,plain,
    ( ~ v1_relat_1(u1_waybel_0(sK0,sK2))
    | spl6_46 ),
    inference(avatar_component_clause,[],[f330])).

fof(f336,plain,
    ( spl6_45
    | ~ spl6_26
    | ~ spl6_46
    | spl6_47
    | ~ spl6_43 ),
    inference(avatar_split_clause,[],[f325,f311,f333,f330,f221,f327])).

fof(f325,plain,
    ( sK1 = k5_yellow_2(sK0,u1_waybel_0(sK0,sK2))
    | ~ v1_relat_1(u1_waybel_0(sK0,sK2))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_43 ),
    inference(superposition,[],[f71,f312])).

fof(f312,plain,
    ( sK1 = k2_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)))
    | ~ spl6_43 ),
    inference(avatar_component_clause,[],[f311])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k5_yellow_2(X0,X1) = k2_yellow_0(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k5_yellow_2(X0,X1) = k2_yellow_0(X0,k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k5_yellow_2(X0,X1) = k2_yellow_0(X0,k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( v1_relat_1(X1)
         => k5_yellow_2(X0,X1) = k2_yellow_0(X0,k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_yellow_2)).

fof(f313,plain,
    ( ~ spl6_13
    | ~ spl6_26
    | ~ spl6_8
    | ~ spl6_25
    | spl6_43
    | spl6_42 ),
    inference(avatar_split_clause,[],[f307,f304,f311,f216,f127,f221,f147])).

fof(f147,plain,
    ( spl6_13
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f127,plain,
    ( spl6_8
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f304,plain,
    ( spl6_42
  <=> r1_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).

fof(f307,plain,
    ( sK1 = k2_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)))
    | ~ r1_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | spl6_42 ),
    inference(resolution,[],[f305,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X2,sK5(X0,X1,X2))
      | k2_yellow_0(X0,X2) = X1
      | ~ r1_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 )
                | ( ~ r1_orders_2(X0,sK5(X0,X1,X2),X1)
                  & r1_lattice3(X0,X2,sK5(X0,X1,X2))
                  & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X4,X1)
                      | ~ r1_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r1_lattice3(X0,X2,X1) )
                | ~ r2_yellow_0(X0,X2)
                | k2_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f34,f48])).

fof(f48,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X1)
          & r1_lattice3(X0,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK5(X0,X1,X2),X1)
        & r1_lattice3(X0,X2,sK5(X0,X1,X2))
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 )
                | ? [X3] :
                    ( ~ r1_orders_2(X0,X3,X1)
                    & r1_lattice3(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X4,X1)
                      | ~ r1_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r1_lattice3(X0,X2,X1) )
                | ~ r2_yellow_0(X0,X2)
                | k2_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 )
                | ? [X3] :
                    ( ~ r1_orders_2(X0,X3,X1)
                    & r1_lattice3(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X4,X1)
                      | ~ r1_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r1_lattice3(X0,X2,X1) )
                | ~ r2_yellow_0(X0,X2)
                | k2_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r1_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X3,X1) ) )
                  & r1_lattice3(X0,X2,X1) )
               => ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 ) )
              & ( ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 )
               => ( ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X0))
                     => ( r1_lattice3(X0,X2,X4)
                       => r1_orders_2(X0,X4,X1) ) )
                  & r1_lattice3(X0,X2,X1) ) ) ) ) ) ),
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
                     => ( r1_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X3,X1) ) )
                  & r1_lattice3(X0,X2,X1) )
               => ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 ) )
              & ( ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 )
               => ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r1_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X3,X1) ) )
                  & r1_lattice3(X0,X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_yellow_0)).

fof(f305,plain,
    ( ~ r1_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))))
    | spl6_42 ),
    inference(avatar_component_clause,[],[f304])).

fof(f306,plain,
    ( ~ spl6_4
    | ~ spl6_24
    | ~ spl6_42
    | spl6_40 ),
    inference(avatar_split_clause,[],[f302,f291,f304,f213,f111])).

fof(f302,plain,
    ( ~ r1_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))))
    | ~ l1_struct_0(sK0)
    | ~ l1_waybel_0(sK2,sK0)
    | spl6_40 ),
    inference(superposition,[],[f292,f166])).

fof(f166,plain,(
    ! [X0,X1] :
      ( k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),u1_waybel_0(X1,X0)) = k2_relat_1(u1_waybel_0(X1,X0))
      | ~ l1_struct_0(X1)
      | ~ l1_waybel_0(X0,X1) ) ),
    inference(resolution,[],[f85,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f292,plain,
    ( ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))))
    | spl6_40 ),
    inference(avatar_component_clause,[],[f291])).

fof(f301,plain,
    ( ~ spl6_13
    | ~ spl6_26
    | ~ spl6_8
    | spl6_41
    | ~ spl6_33 ),
    inference(avatar_split_clause,[],[f297,f259,f299,f127,f221,f147])).

fof(f259,plain,
    ( spl6_33
  <=> ! [X0] :
        ( ~ m1_subset_1(sK5(sK0,sK1,X0),u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,X0,sK1)
        | sK1 = k2_yellow_0(sK0,X0)
        | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK5(sK0,sK1,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f297,plain,
    ( ! [X0] :
        ( ~ r1_lattice3(sK0,X0,sK1)
        | sK1 = k2_yellow_0(sK0,X0)
        | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK5(sK0,sK1,X0))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0) )
    | ~ spl6_33 ),
    inference(duplicate_literal_removal,[],[f294])).

fof(f294,plain,
    ( ! [X0] :
        ( ~ r1_lattice3(sK0,X0,sK1)
        | sK1 = k2_yellow_0(sK0,X0)
        | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK5(sK0,sK1,X0))
        | sK1 = k2_yellow_0(sK0,X0)
        | ~ r1_lattice3(sK0,X0,sK1)
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0) )
    | ~ spl6_33 ),
    inference(resolution,[],[f260,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | k2_yellow_0(X0,X2) = X1
      | ~ r1_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f260,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK5(sK0,sK1,X0),u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,X0,sK1)
        | sK1 = k2_yellow_0(sK0,X0)
        | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK5(sK0,sK1,X0)) )
    | ~ spl6_33 ),
    inference(avatar_component_clause,[],[f259])).

fof(f261,plain,
    ( ~ spl6_13
    | ~ spl6_26
    | ~ spl6_8
    | spl6_33
    | ~ spl6_32 ),
    inference(avatar_split_clause,[],[f256,f253,f259,f127,f221,f147])).

fof(f253,plain,
    ( spl6_32
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,X0,sK1)
        | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f256,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK5(sK0,sK1,X0),u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK5(sK0,sK1,X0))
        | sK1 = k2_yellow_0(sK0,X0)
        | ~ r1_lattice3(sK0,X0,sK1)
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0) )
    | ~ spl6_32 ),
    inference(resolution,[],[f254,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,sK5(X0,X1,X2),X1)
      | k2_yellow_0(X0,X2) = X1
      | ~ r1_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f254,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) )
    | ~ spl6_32 ),
    inference(avatar_component_clause,[],[f253])).

fof(f255,plain,
    ( ~ spl6_8
    | spl6_32
    | ~ spl6_2
    | ~ spl6_29 ),
    inference(avatar_split_clause,[],[f251,f236,f103,f253,f127])).

fof(f103,plain,
    ( spl6_2
  <=> r3_waybel_9(sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f236,plain,
    ( spl6_29
  <=> ! [X1,X0] :
        ( ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_waybel_9(sK0,sK2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_orders_2(sK0,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f251,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | r1_orders_2(sK0,X0,sK1) )
    | ~ spl6_2
    | ~ spl6_29 ),
    inference(resolution,[],[f237,f104])).

fof(f104,plain,
    ( r3_waybel_9(sK0,sK2,sK1)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f103])).

fof(f237,plain,
    ( ! [X0,X1] :
        ( ~ r3_waybel_9(sK0,sK2,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_orders_2(sK0,X0,X1) )
    | ~ spl6_29 ),
    inference(avatar_component_clause,[],[f236])).

fof(f250,plain,
    ( ~ spl6_4
    | spl6_29
    | ~ spl6_6
    | spl6_7
    | ~ spl6_5
    | ~ spl6_31 ),
    inference(avatar_split_clause,[],[f249,f246,f115,f123,f119,f236,f111])).

fof(f119,plain,
    ( spl6_6
  <=> v4_orders_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f123,plain,
    ( spl6_7
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f115,plain,
    ( spl6_5
  <=> v7_waybel_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f246,plain,
    ( spl6_31
  <=> ! [X1,X0,X2] :
        ( ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r1_orders_2(sK0,X1,X2)
        | ~ r3_waybel_9(sK0,X0,X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f249,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(sK2)
        | ~ v4_orders_2(sK2)
        | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
        | ~ l1_waybel_0(sK2,sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_orders_2(sK0,X0,X1)
        | ~ r3_waybel_9(sK0,sK2,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl6_5
    | ~ spl6_31 ),
    inference(resolution,[],[f247,f116])).

fof(f116,plain,
    ( v7_waybel_0(sK2)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f115])).

fof(f247,plain,
    ( ! [X2,X0,X1] :
        ( ~ v7_waybel_0(X0)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1)
        | ~ l1_waybel_0(X0,sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r1_orders_2(sK0,X1,X2)
        | ~ r3_waybel_9(sK0,X0,X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl6_31 ),
    inference(avatar_component_clause,[],[f246])).

fof(f248,plain,
    ( ~ spl6_17
    | ~ spl6_16
    | ~ spl6_15
    | ~ spl6_14
    | ~ spl6_13
    | ~ spl6_12
    | ~ spl6_11
    | ~ spl6_10
    | ~ spl6_9
    | spl6_31
    | spl6_30 ),
    inference(avatar_split_clause,[],[f244,f241,f246,f131,f135,f139,f143,f147,f151,f155,f159,f163])).

fof(f163,plain,
    ( spl6_17
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f159,plain,
    ( spl6_16
  <=> v8_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f155,plain,
    ( spl6_15
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f151,plain,
    ( spl6_14
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f143,plain,
    ( spl6_12
  <=> v1_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f135,plain,
    ( spl6_10
  <=> v1_compts_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f131,plain,
    ( spl6_9
  <=> l1_waybel_9(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f241,plain,
    ( spl6_30
  <=> m1_subset_1(sK4(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f244,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r3_waybel_9(sK0,X0,X2)
        | r1_orders_2(sK0,X1,X2)
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
    | spl6_30 ),
    inference(resolution,[],[f242,f94])).

fof(f94,plain,(
    ! [X4,X0,X3,X1] :
      ( m1_subset_1(sK4(X0),u1_struct_0(X0))
      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X3)
      | r1_orders_2(X0,X4,X3)
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
    inference(duplicate_literal_removal,[],[f91])).

fof(f91,plain,(
    ! [X4,X0,X3,X1] :
      ( r1_orders_2(X0,X4,X3)
      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X3)
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
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r1_orders_2(X0,X4,X3)
      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X2)
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
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r1_orders_2(X0,X4,X3)
                      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r3_waybel_9(X0,X1,X2)
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f45,f46])).

% (18221)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
fof(f46,plain,(
    ! [X0] :
      ( ? [X5] :
          ( ~ v5_pre_topc(k4_waybel_1(X0,X5),X0,X0)
          & m1_subset_1(X5,u1_struct_0(X0)) )
     => ( ~ v5_pre_topc(k4_waybel_1(X0,sK4(X0)),X0,X0)
        & m1_subset_1(sK4(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r1_orders_2(X0,X4,X3)
                      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
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
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X5] :
                      ( r1_orders_2(X0,X5,X3)
                      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5)
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
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X5] :
                      ( r1_orders_2(X0,X5,X3)
                      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5)
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
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
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
                       => ( r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5)
                         => r1_orders_2(X0,X5,X3) ) ) ) ) ) ) ) ),
    inference(rectify,[],[f11])).

fof(f11,axiom,(
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
                       => ( r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
                         => r1_orders_2(X0,X4,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l52_waybel_9)).

fof(f242,plain,
    ( ~ m1_subset_1(sK4(sK0),u1_struct_0(sK0))
    | spl6_30 ),
    inference(avatar_component_clause,[],[f241])).

fof(f243,plain,
    ( ~ spl6_30
    | spl6_28 ),
    inference(avatar_split_clause,[],[f239,f233,f241])).

fof(f233,plain,
    ( spl6_28
  <=> v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f239,plain,
    ( ~ m1_subset_1(sK4(sK0),u1_struct_0(sK0))
    | spl6_28 ),
    inference(resolution,[],[f234,f64])).

fof(f64,plain,(
    ! [X3] :
      ( v5_pre_topc(k4_waybel_1(sK0,X3),sK0,sK0)
      | ~ m1_subset_1(X3,u1_struct_0(sK0)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,
    ( sK1 != k1_waybel_9(sK0,sK2)
    & r3_waybel_9(sK0,sK2,sK1)
    & v11_waybel_0(sK2,sK0)
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f41,f40,f39])).

fof(f39,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k1_waybel_9(X0,X2) != X1
                & r3_waybel_9(X0,X2,X1)
                & v11_waybel_0(X2,X0)
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
              ( k1_waybel_9(sK0,X2) != X1
              & r3_waybel_9(sK0,X2,X1)
              & v11_waybel_0(X2,sK0)
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

fof(f40,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k1_waybel_9(sK0,X2) != X1
            & r3_waybel_9(sK0,X2,X1)
            & v11_waybel_0(X2,sK0)
            & ! [X3] :
                ( v5_pre_topc(k4_waybel_1(sK0,X3),sK0,sK0)
                | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
            & l1_waybel_0(X2,sK0)
            & v7_waybel_0(X2)
            & v4_orders_2(X2)
            & ~ v2_struct_0(X2) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( k1_waybel_9(sK0,X2) != sK1
          & r3_waybel_9(sK0,X2,sK1)
          & v11_waybel_0(X2,sK0)
          & ! [X3] :
              ( v5_pre_topc(k4_waybel_1(sK0,X3),sK0,sK0)
              | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
          & l1_waybel_0(X2,sK0)
          & v7_waybel_0(X2)
          & v4_orders_2(X2)
          & ~ v2_struct_0(X2) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X2] :
        ( k1_waybel_9(sK0,X2) != sK1
        & r3_waybel_9(sK0,X2,sK1)
        & v11_waybel_0(X2,sK0)
        & ! [X3] :
            ( v5_pre_topc(k4_waybel_1(sK0,X3),sK0,sK0)
            | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
        & l1_waybel_0(X2,sK0)
        & v7_waybel_0(X2)
        & v4_orders_2(X2)
        & ~ v2_struct_0(X2) )
   => ( sK1 != k1_waybel_9(sK0,sK2)
      & r3_waybel_9(sK0,sK2,sK1)
      & v11_waybel_0(sK2,sK0)
      & ! [X3] :
          ( v5_pre_topc(k4_waybel_1(sK0,X3),sK0,sK0)
          | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
      & l1_waybel_0(sK2,sK0)
      & v7_waybel_0(sK2)
      & v4_orders_2(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_waybel_9(X0,X2) != X1
              & r3_waybel_9(X0,X2,X1)
              & v11_waybel_0(X2,X0)
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_waybel_9(X0,X2) != X1
              & r3_waybel_9(X0,X2,X1)
              & v11_waybel_0(X2,X0)
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
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
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
                    & v11_waybel_0(X2,X0)
                    & ! [X3] :
                        ( m1_subset_1(X3,u1_struct_0(X0))
                       => v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) ) )
                 => k1_waybel_9(X0,X2) = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
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
                  & v11_waybel_0(X2,X0)
                  & ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) ) )
               => k1_waybel_9(X0,X2) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_waybel_9)).

fof(f234,plain,
    ( ~ v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0)
    | spl6_28 ),
    inference(avatar_component_clause,[],[f233])).

fof(f238,plain,
    ( ~ spl6_28
    | ~ spl6_4
    | ~ spl6_9
    | spl6_29
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_17
    | ~ spl6_10
    | ~ spl6_27 ),
    inference(avatar_split_clause,[],[f231,f228,f135,f163,f159,f155,f151,f147,f143,f139,f236,f131,f111,f233])).

fof(f228,plain,
    ( spl6_27
  <=> ! [X1,X0,X2] :
        ( ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(X0),u1_waybel_0(X0,sK2)),X1)
        | ~ v2_pre_topc(X0)
        | ~ v8_pre_topc(X0)
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ v1_lattice3(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_compts_1(X0)
        | ~ l1_waybel_9(X0)
        | r1_orders_2(X0,X1,X2)
        | ~ l1_waybel_0(sK2,X0)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ v5_pre_topc(k4_waybel_1(X0,sK4(X0)),X0,X0)
        | ~ r3_waybel_9(X0,sK2,X2)
        | ~ m1_subset_1(X1,u1_struct_0(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f231,plain,
    ( ! [X0,X1] :
        ( ~ v2_pre_topc(sK0)
        | ~ v8_pre_topc(sK0)
        | ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v2_lattice3(sK0)
        | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
        | ~ l1_waybel_9(sK0)
        | r1_orders_2(sK0,X0,X1)
        | ~ l1_waybel_0(sK2,sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0)
        | ~ r3_waybel_9(sK0,sK2,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl6_10
    | ~ spl6_27 ),
    inference(resolution,[],[f229,f136])).

fof(f136,plain,
    ( v1_compts_1(sK0)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f135])).

fof(f229,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_compts_1(X0)
        | ~ v2_pre_topc(X0)
        | ~ v8_pre_topc(X0)
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ v1_lattice3(X0)
        | ~ v2_lattice3(X0)
        | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(X0),u1_waybel_0(X0,sK2)),X1)
        | ~ l1_waybel_9(X0)
        | r1_orders_2(X0,X1,X2)
        | ~ l1_waybel_0(sK2,X0)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ v5_pre_topc(k4_waybel_1(X0,sK4(X0)),X0,X0)
        | ~ r3_waybel_9(X0,sK2,X2)
        | ~ m1_subset_1(X1,u1_struct_0(X0)) )
    | ~ spl6_27 ),
    inference(avatar_component_clause,[],[f228])).

fof(f230,plain,
    ( spl6_7
    | ~ spl6_6
    | spl6_27
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f226,f115,f228,f119,f123])).

fof(f226,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(X0),u1_waybel_0(X0,sK2)),X1)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ r3_waybel_9(X0,sK2,X2)
        | ~ v5_pre_topc(k4_waybel_1(X0,sK4(X0)),X0,X0)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ l1_waybel_0(sK2,X0)
        | r1_orders_2(X0,X1,X2)
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
    | ~ spl6_5 ),
    inference(resolution,[],[f95,f116])).

fof(f95,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v7_waybel_0(X1)
      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X3)
      | ~ v5_pre_topc(k4_waybel_1(X0,sK4(X0)),X0,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | r1_orders_2(X0,X4,X3)
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
    inference(duplicate_literal_removal,[],[f90])).

fof(f90,plain,(
    ! [X4,X0,X3,X1] :
      ( r1_orders_2(X0,X4,X3)
      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X3)
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
    inference(equality_resolution,[],[f76])).

% (18221)Refutation not found, incomplete strategy% (18221)------------------------------
% (18221)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (18221)Termination reason: Refutation not found, incomplete strategy

% (18221)Memory used [KB]: 6140
% (18221)Time elapsed: 0.082 s
% (18221)------------------------------
% (18221)------------------------------
fof(f76,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r1_orders_2(X0,X4,X3)
      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X2)
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
    inference(cnf_transformation,[],[f47])).

fof(f225,plain,
    ( ~ spl6_9
    | spl6_26 ),
    inference(avatar_split_clause,[],[f224,f221,f131])).

fof(f224,plain,
    ( ~ l1_waybel_9(sK0)
    | spl6_26 ),
    inference(resolution,[],[f222,f68])).

fof(f68,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
      | ~ l1_waybel_9(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
      | ~ l1_waybel_9(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( l1_waybel_9(X0)
     => l1_orders_2(X0) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_waybel_9(X0)
     => ( l1_orders_2(X0)
        & l1_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_waybel_9)).

fof(f222,plain,
    ( ~ l1_orders_2(sK0)
    | spl6_26 ),
    inference(avatar_component_clause,[],[f221])).

fof(f223,plain,
    ( ~ spl6_26
    | spl6_24 ),
    inference(avatar_split_clause,[],[f219,f213,f221])).

fof(f219,plain,
    ( ~ l1_orders_2(sK0)
    | spl6_24 ),
    inference(resolution,[],[f214,f69])).

fof(f69,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f214,plain,
    ( ~ l1_struct_0(sK0)
    | spl6_24 ),
    inference(avatar_component_clause,[],[f213])).

fof(f218,plain,
    ( ~ spl6_4
    | ~ spl6_24
    | spl6_25
    | ~ spl6_23 ),
    inference(avatar_split_clause,[],[f211,f208,f216,f213,f111])).

fof(f208,plain,
    ( spl6_23
  <=> r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f211,plain,
    ( r1_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),sK1)
    | ~ l1_struct_0(sK0)
    | ~ l1_waybel_0(sK2,sK0)
    | ~ spl6_23 ),
    inference(superposition,[],[f209,f166])).

fof(f209,plain,
    ( r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1)
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f208])).

fof(f210,plain,
    ( ~ spl6_8
    | spl6_23
    | ~ spl6_2
    | ~ spl6_20 ),
    inference(avatar_split_clause,[],[f205,f180,f103,f208,f127])).

fof(f180,plain,
    ( spl6_20
  <=> ! [X0] :
        ( r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
        | ~ r3_waybel_9(sK0,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

% (18233)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f205,plain,
    ( r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl6_2
    | ~ spl6_20 ),
    inference(resolution,[],[f181,f104])).

fof(f181,plain,
    ( ! [X0] :
        ( ~ r3_waybel_9(sK0,sK2,X0)
        | r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f180])).

fof(f204,plain,
    ( spl6_20
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | ~ spl6_3
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f202,f199,f107,f123,f119,f115,f111,f180])).

fof(f107,plain,
    ( spl6_3
  <=> v11_waybel_0(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f199,plain,
    ( spl6_22
  <=> ! [X1,X0] :
        ( ~ r3_waybel_9(sK0,X0,X1)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1)
        | ~ v11_waybel_0(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f202,plain,
    ( ! [X0] :
        ( v2_struct_0(sK2)
        | ~ v4_orders_2(sK2)
        | ~ v7_waybel_0(sK2)
        | ~ l1_waybel_0(sK2,sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
        | ~ r3_waybel_9(sK0,sK2,X0) )
    | ~ spl6_3
    | ~ spl6_22 ),
    inference(resolution,[],[f200,f108])).

fof(f108,plain,
    ( v11_waybel_0(sK2,sK0)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f107])).

fof(f200,plain,
    ( ! [X0,X1] :
        ( ~ v11_waybel_0(X0,sK0)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1)
        | ~ r3_waybel_9(sK0,X0,X1) )
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f199])).

fof(f201,plain,
    ( ~ spl6_17
    | ~ spl6_16
    | ~ spl6_15
    | ~ spl6_14
    | ~ spl6_13
    | ~ spl6_12
    | ~ spl6_11
    | ~ spl6_10
    | ~ spl6_9
    | spl6_22
    | spl6_21 ),
    inference(avatar_split_clause,[],[f197,f194,f199,f131,f135,f139,f143,f147,f151,f155,f159,f163])).

fof(f194,plain,
    ( spl6_21
  <=> m1_subset_1(sK3(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f197,plain,
    ( ! [X0,X1] :
        ( ~ r3_waybel_9(sK0,X0,X1)
        | ~ v11_waybel_0(X0,sK0)
        | r1_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1)
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
    | spl6_21 ),
    inference(resolution,[],[f195,f96])).

fof(f96,plain,(
    ! [X0,X3,X1] :
      ( m1_subset_1(sK3(X0),u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X3)
      | ~ v11_waybel_0(X1,X0)
      | r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
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
    inference(duplicate_literal_removal,[],[f89])).

fof(f89,plain,(
    ! [X0,X3,X1] :
      ( r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
      | ~ r3_waybel_9(X0,X1,X3)
      | ~ v11_waybel_0(X1,X0)
      | m1_subset_1(sK3(X0),u1_struct_0(X0))
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
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ v11_waybel_0(X1,X0)
      | m1_subset_1(sK3(X0),u1_struct_0(X0))
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
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
                  | ~ r3_waybel_9(X0,X1,X2)
                  | ~ v11_waybel_0(X1,X0)
                  | ( ~ v5_pre_topc(k4_waybel_1(X0,sK3(X0)),X0,X0)
                    & m1_subset_1(sK3(X0),u1_struct_0(X0)) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ? [X4] :
          ( ~ v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ v5_pre_topc(k4_waybel_1(X0,sK3(X0)),X0,X0)
        & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
                  | ~ r3_waybel_9(X0,X1,X2)
                  | ~ v11_waybel_0(X1,X0)
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
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
                  | ~ r3_waybel_9(X0,X1,X2)
                  | ~ v11_waybel_0(X1,X0)
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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
                      & v11_waybel_0(X1,X0)
                      & ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) )
                      & X2 = X3 )
                   => r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_waybel_9)).

fof(f195,plain,
    ( ~ m1_subset_1(sK3(sK0),u1_struct_0(sK0))
    | spl6_21 ),
    inference(avatar_component_clause,[],[f194])).

fof(f196,plain,
    ( ~ spl6_21
    | spl6_19 ),
    inference(avatar_split_clause,[],[f192,f176,f194])).

fof(f176,plain,
    ( spl6_19
  <=> v5_pre_topc(k4_waybel_1(sK0,sK3(sK0)),sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f192,plain,
    ( ~ m1_subset_1(sK3(sK0),u1_struct_0(sK0))
    | spl6_19 ),
    inference(resolution,[],[f177,f64])).

fof(f177,plain,
    ( ~ v5_pre_topc(k4_waybel_1(sK0,sK3(sK0)),sK0,sK0)
    | spl6_19 ),
    inference(avatar_component_clause,[],[f176])).

fof(f191,plain,
    ( ~ spl6_19
    | ~ spl6_4
    | spl6_20
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_17
    | ~ spl6_3
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f174,f171,f107,f163,f159,f155,f151,f147,f143,f139,f135,f131,f180,f111,f176])).

fof(f171,plain,
    ( spl6_18
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
        | r1_lattice3(X0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(X0),u1_waybel_0(X0,sK2)),X1)
        | ~ l1_waybel_0(sK2,X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ v5_pre_topc(k4_waybel_1(X0,sK3(X0)),X0,X0)
        | ~ v11_waybel_0(sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f174,plain,
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
        | r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
        | ~ l1_waybel_0(sK2,sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v5_pre_topc(k4_waybel_1(sK0,sK3(sK0)),sK0,sK0)
        | ~ r3_waybel_9(sK0,sK2,X0) )
    | ~ spl6_3
    | ~ spl6_18 ),
    inference(resolution,[],[f172,f108])).

fof(f172,plain,
    ( ! [X0,X1] :
        ( ~ v11_waybel_0(sK2,X0)
        | ~ v2_pre_topc(X0)
        | ~ v8_pre_topc(X0)
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ v1_lattice3(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_compts_1(X0)
        | ~ l1_waybel_9(X0)
        | r1_lattice3(X0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(X0),u1_waybel_0(X0,sK2)),X1)
        | ~ l1_waybel_0(sK2,X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ v5_pre_topc(k4_waybel_1(X0,sK3(X0)),X0,X0)
        | ~ r3_waybel_9(X0,sK2,X1) )
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f171])).

fof(f173,plain,
    ( spl6_7
    | ~ spl6_6
    | spl6_18
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f167,f115,f171,f119,f123])).

fof(f167,plain,
    ( ! [X0,X1] :
        ( ~ r3_waybel_9(X0,sK2,X1)
        | ~ v11_waybel_0(sK2,X0)
        | ~ v5_pre_topc(k4_waybel_1(X0,sK3(X0)),X0,X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_waybel_0(sK2,X0)
        | r1_lattice3(X0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(X0),u1_waybel_0(X0,sK2)),X1)
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
    | ~ spl6_5 ),
    inference(resolution,[],[f97,f116])).

fof(f97,plain,(
    ! [X0,X3,X1] :
      ( ~ v7_waybel_0(X1)
      | ~ r3_waybel_9(X0,X1,X3)
      | ~ v11_waybel_0(X1,X0)
      | ~ v5_pre_topc(k4_waybel_1(X0,sK3(X0)),X0,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
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
    inference(duplicate_literal_removal,[],[f88])).

fof(f88,plain,(
    ! [X0,X3,X1] :
      ( r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
      | ~ r3_waybel_9(X0,X1,X3)
      | ~ v11_waybel_0(X1,X0)
      | ~ v5_pre_topc(k4_waybel_1(X0,sK3(X0)),X0,X0)
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
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ v11_waybel_0(X1,X0)
      | ~ v5_pre_topc(k4_waybel_1(X0,sK3(X0)),X0,X0)
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
    inference(cnf_transformation,[],[f44])).

fof(f165,plain,(
    spl6_17 ),
    inference(avatar_split_clause,[],[f50,f163])).

fof(f50,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f161,plain,(
    spl6_16 ),
    inference(avatar_split_clause,[],[f51,f159])).

fof(f51,plain,(
    v8_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f157,plain,(
    spl6_15 ),
    inference(avatar_split_clause,[],[f52,f155])).

fof(f52,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f153,plain,(
    spl6_14 ),
    inference(avatar_split_clause,[],[f53,f151])).

fof(f53,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f149,plain,(
    spl6_13 ),
    inference(avatar_split_clause,[],[f54,f147])).

fof(f54,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f145,plain,(
    spl6_12 ),
    inference(avatar_split_clause,[],[f55,f143])).

fof(f55,plain,(
    v1_lattice3(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f141,plain,(
    spl6_11 ),
    inference(avatar_split_clause,[],[f56,f139])).

fof(f56,plain,(
    v2_lattice3(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f137,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f57,f135])).

fof(f57,plain,(
    v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f133,plain,(
    spl6_9 ),
    inference(avatar_split_clause,[],[f58,f131])).

fof(f58,plain,(
    l1_waybel_9(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f129,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f59,f127])).

fof(f59,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f42])).

fof(f125,plain,(
    ~ spl6_7 ),
    inference(avatar_split_clause,[],[f60,f123])).

fof(f60,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f121,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f61,f119])).

fof(f61,plain,(
    v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f117,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f62,f115])).

fof(f62,plain,(
    v7_waybel_0(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f113,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f63,f111])).

fof(f63,plain,(
    l1_waybel_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f109,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f65,f107])).

fof(f65,plain,(
    v11_waybel_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f105,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f66,f103])).

fof(f66,plain,(
    r3_waybel_9(sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f101,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f67,f99])).

fof(f67,plain,(
    sK1 != k1_waybel_9(sK0,sK2) ),
    inference(cnf_transformation,[],[f42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:27:09 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.44  % (18234)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.45  % (18226)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.46  % (18227)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.47  % (18236)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.47  % (18227)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % (18235)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f371,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f101,f105,f109,f113,f117,f121,f125,f129,f133,f137,f141,f145,f149,f153,f157,f161,f165,f173,f191,f196,f201,f204,f210,f218,f223,f225,f230,f238,f243,f248,f250,f255,f261,f301,f306,f313,f336,f339,f341,f346,f370])).
% 0.20/0.47  fof(f370,plain,(
% 0.20/0.47    spl6_43 | ~spl6_40 | ~spl6_25 | ~spl6_41),
% 0.20/0.47    inference(avatar_split_clause,[],[f369,f299,f216,f291,f311])).
% 0.20/0.47  fof(f311,plain,(
% 0.20/0.47    spl6_43 <=> sK1 = k2_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).
% 0.20/0.47  fof(f291,plain,(
% 0.20/0.47    spl6_40 <=> r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).
% 0.20/0.47  fof(f216,plain,(
% 0.20/0.47    spl6_25 <=> r1_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).
% 0.20/0.47  fof(f299,plain,(
% 0.20/0.47    spl6_41 <=> ! [X0] : (~r1_lattice3(sK0,X0,sK1) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK5(sK0,sK1,X0)) | sK1 = k2_yellow_0(sK0,X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).
% 0.20/0.47  fof(f369,plain,(
% 0.20/0.47    ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2)))) | sK1 = k2_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2))) | (~spl6_25 | ~spl6_41)),
% 0.20/0.47    inference(resolution,[],[f300,f217])).
% 0.20/0.47  fof(f217,plain,(
% 0.20/0.47    r1_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),sK1) | ~spl6_25),
% 0.20/0.47    inference(avatar_component_clause,[],[f216])).
% 0.20/0.47  fof(f300,plain,(
% 0.20/0.47    ( ! [X0] : (~r1_lattice3(sK0,X0,sK1) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK5(sK0,sK1,X0)) | sK1 = k2_yellow_0(sK0,X0)) ) | ~spl6_41),
% 0.20/0.47    inference(avatar_component_clause,[],[f299])).
% 0.20/0.47  fof(f346,plain,(
% 0.20/0.47    spl6_45 | ~spl6_26 | ~spl6_4 | spl6_1 | ~spl6_47),
% 0.20/0.47    inference(avatar_split_clause,[],[f343,f333,f99,f111,f221,f327])).
% 0.20/0.47  fof(f327,plain,(
% 0.20/0.47    spl6_45 <=> v2_struct_0(sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).
% 0.20/0.47  fof(f221,plain,(
% 0.20/0.47    spl6_26 <=> l1_orders_2(sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 0.20/0.47  fof(f111,plain,(
% 0.20/0.47    spl6_4 <=> l1_waybel_0(sK2,sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.20/0.47  fof(f99,plain,(
% 0.20/0.47    spl6_1 <=> sK1 = k1_waybel_9(sK0,sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.20/0.47  fof(f333,plain,(
% 0.20/0.47    spl6_47 <=> sK1 = k5_yellow_2(sK0,u1_waybel_0(sK0,sK2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_47])])).
% 0.20/0.47  fof(f343,plain,(
% 0.20/0.47    sK1 = k1_waybel_9(sK0,sK2) | ~l1_waybel_0(sK2,sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | ~spl6_47),
% 0.20/0.47    inference(superposition,[],[f72,f334])).
% 0.20/0.47  fof(f334,plain,(
% 0.20/0.47    sK1 = k5_yellow_2(sK0,u1_waybel_0(sK0,sK2)) | ~spl6_47),
% 0.20/0.47    inference(avatar_component_clause,[],[f333])).
% 0.20/0.47  fof(f72,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k1_waybel_9(X0,X1) = k5_yellow_2(X0,u1_waybel_0(X0,X1)) | ~l1_waybel_0(X1,X0) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f28])).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (k1_waybel_9(X0,X1) = k5_yellow_2(X0,u1_waybel_0(X0,X1)) | ~l1_waybel_0(X1,X0)) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.47    inference(flattening,[],[f27])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (k1_waybel_9(X0,X1) = k5_yellow_2(X0,u1_waybel_0(X0,X1)) | ~l1_waybel_0(X1,X0)) | (~l1_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f7])).
% 0.20/0.47  fof(f7,axiom,(
% 0.20/0.47    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (l1_waybel_0(X1,X0) => k1_waybel_9(X0,X1) = k5_yellow_2(X0,u1_waybel_0(X0,X1))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_waybel_9)).
% 0.20/0.47  fof(f341,plain,(
% 0.20/0.47    ~spl6_26 | ~spl6_11 | ~spl6_45),
% 0.20/0.47    inference(avatar_split_clause,[],[f340,f327,f139,f221])).
% 0.20/0.48  fof(f139,plain,(
% 0.20/0.48    spl6_11 <=> v2_lattice3(sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.20/0.48  fof(f340,plain,(
% 0.20/0.48    ~v2_lattice3(sK0) | ~l1_orders_2(sK0) | ~spl6_45),
% 0.20/0.48    inference(resolution,[],[f328,f70])).
% 0.20/0.48  fof(f70,plain,(
% 0.20/0.48    ( ! [X0] : (~v2_struct_0(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f24])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    ! [X0] : (~v2_struct_0(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0))),
% 0.20/0.48    inference(flattening,[],[f23])).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    ! [X0] : ((~v2_struct_0(X0) | ~v2_lattice3(X0)) | ~l1_orders_2(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f4])).
% 0.20/0.48  % (18228)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0] : (l1_orders_2(X0) => (v2_lattice3(X0) => ~v2_struct_0(X0)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_lattice3)).
% 0.20/0.49  fof(f328,plain,(
% 0.20/0.49    v2_struct_0(sK0) | ~spl6_45),
% 0.20/0.49    inference(avatar_component_clause,[],[f327])).
% 0.20/0.49  fof(f339,plain,(
% 0.20/0.49    ~spl6_24 | ~spl6_4 | spl6_46),
% 0.20/0.49    inference(avatar_split_clause,[],[f338,f330,f111,f213])).
% 0.20/0.49  fof(f213,plain,(
% 0.20/0.49    spl6_24 <=> l1_struct_0(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 0.20/0.49  fof(f330,plain,(
% 0.20/0.49    spl6_46 <=> v1_relat_1(u1_waybel_0(sK0,sK2))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).
% 0.20/0.49  fof(f338,plain,(
% 0.20/0.49    ~l1_waybel_0(sK2,sK0) | ~l1_struct_0(sK0) | spl6_46),
% 0.20/0.49    inference(resolution,[],[f337,f85])).
% 0.20/0.49  fof(f85,plain,(
% 0.20/0.49    ( ! [X0,X1] : (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f36])).
% 0.20/0.49  fof(f36,plain,(
% 0.20/0.49    ! [X0,X1] : (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f35])).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    ! [X0,X1] : (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | (~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f18])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ! [X0,X1] : ((l1_waybel_0(X1,X0) & l1_struct_0(X0)) => m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))))),
% 0.20/0.49    inference(pure_predicate_removal,[],[f17])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ! [X0,X1] : ((l1_waybel_0(X1,X0) & l1_struct_0(X0)) => (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_1(u1_waybel_0(X0,X1))))),
% 0.20/0.49    inference(pure_predicate_removal,[],[f6])).
% 0.20/0.49  fof(f6,axiom,(
% 0.20/0.49    ! [X0,X1] : ((l1_waybel_0(X1,X0) & l1_struct_0(X0)) => (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(u1_waybel_0(X0,X1))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_waybel_0)).
% 0.20/0.49  fof(f337,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_subset_1(u1_waybel_0(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl6_46),
% 0.20/0.49    inference(resolution,[],[f331,f86])).
% 0.20/0.49  fof(f86,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f37])).
% 0.20/0.49  fof(f37,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.49    inference(ennf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.49  fof(f331,plain,(
% 0.20/0.49    ~v1_relat_1(u1_waybel_0(sK0,sK2)) | spl6_46),
% 0.20/0.49    inference(avatar_component_clause,[],[f330])).
% 0.20/0.49  fof(f336,plain,(
% 0.20/0.49    spl6_45 | ~spl6_26 | ~spl6_46 | spl6_47 | ~spl6_43),
% 0.20/0.49    inference(avatar_split_clause,[],[f325,f311,f333,f330,f221,f327])).
% 0.20/0.49  fof(f325,plain,(
% 0.20/0.49    sK1 = k5_yellow_2(sK0,u1_waybel_0(sK0,sK2)) | ~v1_relat_1(u1_waybel_0(sK0,sK2)) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | ~spl6_43),
% 0.20/0.49    inference(superposition,[],[f71,f312])).
% 0.20/0.49  fof(f312,plain,(
% 0.20/0.49    sK1 = k2_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2))) | ~spl6_43),
% 0.20/0.49    inference(avatar_component_clause,[],[f311])).
% 0.20/0.49  fof(f71,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k5_yellow_2(X0,X1) = k2_yellow_0(X0,k2_relat_1(X1)) | ~v1_relat_1(X1) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f26])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (k5_yellow_2(X0,X1) = k2_yellow_0(X0,k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f25])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (k5_yellow_2(X0,X1) = k2_yellow_0(X0,k2_relat_1(X1)) | ~v1_relat_1(X1)) | (~l1_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f8])).
% 0.20/0.49  fof(f8,axiom,(
% 0.20/0.49    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (v1_relat_1(X1) => k5_yellow_2(X0,X1) = k2_yellow_0(X0,k2_relat_1(X1))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_yellow_2)).
% 0.20/0.49  fof(f313,plain,(
% 0.20/0.49    ~spl6_13 | ~spl6_26 | ~spl6_8 | ~spl6_25 | spl6_43 | spl6_42),
% 0.20/0.49    inference(avatar_split_clause,[],[f307,f304,f311,f216,f127,f221,f147])).
% 0.20/0.49  fof(f147,plain,(
% 0.20/0.49    spl6_13 <=> v5_orders_2(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.20/0.49  fof(f127,plain,(
% 0.20/0.49    spl6_8 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.20/0.49  fof(f304,plain,(
% 0.20/0.49    spl6_42 <=> r1_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).
% 0.20/0.49  fof(f307,plain,(
% 0.20/0.49    sK1 = k2_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2))) | ~r1_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | spl6_42),
% 0.20/0.49    inference(resolution,[],[f305,f80])).
% 0.20/0.49  fof(f80,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (r1_lattice3(X0,X2,sK5(X0,X1,X2)) | k2_yellow_0(X0,X2) = X1 | ~r1_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f49])).
% 0.20/0.49  fof(f49,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (((r2_yellow_0(X0,X2) & k2_yellow_0(X0,X2) = X1) | (~r1_orders_2(X0,sK5(X0,X1,X2),X1) & r1_lattice3(X0,X2,sK5(X0,X1,X2)) & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))) | ~r1_lattice3(X0,X2,X1)) & ((! [X4] : (r1_orders_2(X0,X4,X1) | ~r1_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_lattice3(X0,X2,X1)) | ~r2_yellow_0(X0,X2) | k2_yellow_0(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f34,f48])).
% 0.20/0.49  fof(f48,plain,(
% 0.20/0.49    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X3,X1) & r1_lattice3(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,sK5(X0,X1,X2),X1) & r1_lattice3(X0,X2,sK5(X0,X1,X2)) & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f34,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (((r2_yellow_0(X0,X2) & k2_yellow_0(X0,X2) = X1) | ? [X3] : (~r1_orders_2(X0,X3,X1) & r1_lattice3(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X2,X1)) & ((! [X4] : (r1_orders_2(X0,X4,X1) | ~r1_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_lattice3(X0,X2,X1)) | ~r2_yellow_0(X0,X2) | k2_yellow_0(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 0.20/0.49    inference(flattening,[],[f33])).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (((r2_yellow_0(X0,X2) & k2_yellow_0(X0,X2) = X1) | (? [X3] : ((~r1_orders_2(X0,X3,X1) & r1_lattice3(X0,X2,X3)) & m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X2,X1))) & ((! [X4] : ((r1_orders_2(X0,X4,X1) | ~r1_lattice3(X0,X2,X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_lattice3(X0,X2,X1)) | (~r2_yellow_0(X0,X2) | k2_yellow_0(X0,X2) != X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f15])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (((! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattice3(X0,X2,X3) => r1_orders_2(X0,X3,X1))) & r1_lattice3(X0,X2,X1)) => (r2_yellow_0(X0,X2) & k2_yellow_0(X0,X2) = X1)) & ((r2_yellow_0(X0,X2) & k2_yellow_0(X0,X2) = X1) => (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (r1_lattice3(X0,X2,X4) => r1_orders_2(X0,X4,X1))) & r1_lattice3(X0,X2,X1))))))),
% 0.20/0.49    inference(rectify,[],[f5])).
% 0.20/0.49  fof(f5,axiom,(
% 0.20/0.49    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (((! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattice3(X0,X2,X3) => r1_orders_2(X0,X3,X1))) & r1_lattice3(X0,X2,X1)) => (r2_yellow_0(X0,X2) & k2_yellow_0(X0,X2) = X1)) & ((r2_yellow_0(X0,X2) & k2_yellow_0(X0,X2) = X1) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattice3(X0,X2,X3) => r1_orders_2(X0,X3,X1))) & r1_lattice3(X0,X2,X1))))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_yellow_0)).
% 0.20/0.49  fof(f305,plain,(
% 0.20/0.49    ~r1_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2)))) | spl6_42),
% 0.20/0.49    inference(avatar_component_clause,[],[f304])).
% 0.20/0.49  fof(f306,plain,(
% 0.20/0.49    ~spl6_4 | ~spl6_24 | ~spl6_42 | spl6_40),
% 0.20/0.49    inference(avatar_split_clause,[],[f302,f291,f304,f213,f111])).
% 0.20/0.49  fof(f302,plain,(
% 0.20/0.49    ~r1_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2)))) | ~l1_struct_0(sK0) | ~l1_waybel_0(sK2,sK0) | spl6_40),
% 0.20/0.49    inference(superposition,[],[f292,f166])).
% 0.20/0.49  fof(f166,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),u1_waybel_0(X1,X0)) = k2_relat_1(u1_waybel_0(X1,X0)) | ~l1_struct_0(X1) | ~l1_waybel_0(X0,X1)) )),
% 0.20/0.49    inference(resolution,[],[f85,f87])).
% 0.20/0.49  fof(f87,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f38])).
% 0.20/0.49  fof(f38,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.49    inference(ennf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.20/0.49  fof(f292,plain,(
% 0.20/0.49    ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2)))) | spl6_40),
% 0.20/0.49    inference(avatar_component_clause,[],[f291])).
% 0.20/0.49  fof(f301,plain,(
% 0.20/0.49    ~spl6_13 | ~spl6_26 | ~spl6_8 | spl6_41 | ~spl6_33),
% 0.20/0.49    inference(avatar_split_clause,[],[f297,f259,f299,f127,f221,f147])).
% 0.20/0.49  fof(f259,plain,(
% 0.20/0.49    spl6_33 <=> ! [X0] : (~m1_subset_1(sK5(sK0,sK1,X0),u1_struct_0(sK0)) | ~r1_lattice3(sK0,X0,sK1) | sK1 = k2_yellow_0(sK0,X0) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK5(sK0,sK1,X0)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).
% 0.20/0.49  fof(f297,plain,(
% 0.20/0.49    ( ! [X0] : (~r1_lattice3(sK0,X0,sK1) | sK1 = k2_yellow_0(sK0,X0) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK5(sK0,sK1,X0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0)) ) | ~spl6_33),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f294])).
% 0.20/0.49  fof(f294,plain,(
% 0.20/0.49    ( ! [X0] : (~r1_lattice3(sK0,X0,sK1) | sK1 = k2_yellow_0(sK0,X0) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK5(sK0,sK1,X0)) | sK1 = k2_yellow_0(sK0,X0) | ~r1_lattice3(sK0,X0,sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0)) ) | ~spl6_33),
% 0.20/0.49    inference(resolution,[],[f260,f79])).
% 0.20/0.49  fof(f79,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) | k2_yellow_0(X0,X2) = X1 | ~r1_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f49])).
% 0.20/0.49  fof(f260,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_subset_1(sK5(sK0,sK1,X0),u1_struct_0(sK0)) | ~r1_lattice3(sK0,X0,sK1) | sK1 = k2_yellow_0(sK0,X0) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK5(sK0,sK1,X0))) ) | ~spl6_33),
% 0.20/0.49    inference(avatar_component_clause,[],[f259])).
% 0.20/0.49  fof(f261,plain,(
% 0.20/0.49    ~spl6_13 | ~spl6_26 | ~spl6_8 | spl6_33 | ~spl6_32),
% 0.20/0.49    inference(avatar_split_clause,[],[f256,f253,f259,f127,f221,f147])).
% 0.20/0.49  fof(f253,plain,(
% 0.20/0.49    spl6_32 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,X0,sK1) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).
% 0.20/0.49  fof(f256,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_subset_1(sK5(sK0,sK1,X0),u1_struct_0(sK0)) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK5(sK0,sK1,X0)) | sK1 = k2_yellow_0(sK0,X0) | ~r1_lattice3(sK0,X0,sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0)) ) | ~spl6_32),
% 0.20/0.49    inference(resolution,[],[f254,f81])).
% 0.20/0.49  fof(f81,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~r1_orders_2(X0,sK5(X0,X1,X2),X1) | k2_yellow_0(X0,X2) = X1 | ~r1_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f49])).
% 0.20/0.49  fof(f254,plain,(
% 0.20/0.49    ( ! [X0] : (r1_orders_2(sK0,X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)) ) | ~spl6_32),
% 0.20/0.49    inference(avatar_component_clause,[],[f253])).
% 0.20/0.49  fof(f255,plain,(
% 0.20/0.49    ~spl6_8 | spl6_32 | ~spl6_2 | ~spl6_29),
% 0.20/0.49    inference(avatar_split_clause,[],[f251,f236,f103,f253,f127])).
% 0.20/0.49  fof(f103,plain,(
% 0.20/0.49    spl6_2 <=> r3_waybel_9(sK0,sK2,sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.20/0.49  fof(f236,plain,(
% 0.20/0.49    spl6_29 <=> ! [X1,X0] : (~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK2,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_orders_2(sK0,X0,X1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).
% 0.20/0.49  fof(f251,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | r1_orders_2(sK0,X0,sK1)) ) | (~spl6_2 | ~spl6_29)),
% 0.20/0.49    inference(resolution,[],[f237,f104])).
% 0.20/0.49  fof(f104,plain,(
% 0.20/0.49    r3_waybel_9(sK0,sK2,sK1) | ~spl6_2),
% 0.20/0.49    inference(avatar_component_clause,[],[f103])).
% 0.20/0.49  fof(f237,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r3_waybel_9(sK0,sK2,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_orders_2(sK0,X0,X1)) ) | ~spl6_29),
% 0.20/0.49    inference(avatar_component_clause,[],[f236])).
% 0.20/0.49  fof(f250,plain,(
% 0.20/0.49    ~spl6_4 | spl6_29 | ~spl6_6 | spl6_7 | ~spl6_5 | ~spl6_31),
% 0.20/0.49    inference(avatar_split_clause,[],[f249,f246,f115,f123,f119,f236,f111])).
% 0.20/0.49  fof(f119,plain,(
% 0.20/0.49    spl6_6 <=> v4_orders_2(sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.20/0.49  fof(f123,plain,(
% 0.20/0.49    spl6_7 <=> v2_struct_0(sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.20/0.49  fof(f115,plain,(
% 0.20/0.49    spl6_5 <=> v7_waybel_0(sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.20/0.49  fof(f246,plain,(
% 0.20/0.49    spl6_31 <=> ! [X1,X0,X2] : (~r1_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~l1_waybel_0(X0,sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | r1_orders_2(sK0,X1,X2) | ~r3_waybel_9(sK0,X0,X2) | ~m1_subset_1(X1,u1_struct_0(sK0)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).
% 0.20/0.49  fof(f249,plain,(
% 0.20/0.49    ( ! [X0,X1] : (v2_struct_0(sK2) | ~v4_orders_2(sK2) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | ~l1_waybel_0(sK2,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_orders_2(sK0,X0,X1) | ~r3_waybel_9(sK0,sK2,X1) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl6_5 | ~spl6_31)),
% 0.20/0.49    inference(resolution,[],[f247,f116])).
% 0.20/0.49  fof(f116,plain,(
% 0.20/0.49    v7_waybel_0(sK2) | ~spl6_5),
% 0.20/0.49    inference(avatar_component_clause,[],[f115])).
% 0.20/0.49  fof(f247,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~v7_waybel_0(X0) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1) | ~l1_waybel_0(X0,sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | r1_orders_2(sK0,X1,X2) | ~r3_waybel_9(sK0,X0,X2) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | ~spl6_31),
% 0.20/0.49    inference(avatar_component_clause,[],[f246])).
% 0.20/0.49  fof(f248,plain,(
% 0.20/0.49    ~spl6_17 | ~spl6_16 | ~spl6_15 | ~spl6_14 | ~spl6_13 | ~spl6_12 | ~spl6_11 | ~spl6_10 | ~spl6_9 | spl6_31 | spl6_30),
% 0.20/0.49    inference(avatar_split_clause,[],[f244,f241,f246,f131,f135,f139,f143,f147,f151,f155,f159,f163])).
% 0.20/0.49  fof(f163,plain,(
% 0.20/0.49    spl6_17 <=> v2_pre_topc(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.20/0.49  fof(f159,plain,(
% 0.20/0.49    spl6_16 <=> v8_pre_topc(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.20/0.49  fof(f155,plain,(
% 0.20/0.49    spl6_15 <=> v3_orders_2(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.20/0.49  fof(f151,plain,(
% 0.20/0.49    spl6_14 <=> v4_orders_2(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.20/0.49  fof(f143,plain,(
% 0.20/0.49    spl6_12 <=> v1_lattice3(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.20/0.49  fof(f135,plain,(
% 0.20/0.49    spl6_10 <=> v1_compts_1(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.20/0.49  fof(f131,plain,(
% 0.20/0.49    spl6_9 <=> l1_waybel_9(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.20/0.49  fof(f241,plain,(
% 0.20/0.49    spl6_30 <=> m1_subset_1(sK4(sK0),u1_struct_0(sK0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).
% 0.20/0.49  fof(f244,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~r1_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X0,X2) | r1_orders_2(sK0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_waybel_9(sK0) | ~v1_compts_1(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) ) | spl6_30),
% 0.20/0.49    inference(resolution,[],[f242,f94])).
% 0.20/0.49  fof(f94,plain,(
% 0.20/0.49    ( ! [X4,X0,X3,X1] : (m1_subset_1(sK4(X0),u1_struct_0(X0)) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X3) | r1_orders_2(X0,X4,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f91])).
% 0.20/0.49  fof(f91,plain,(
% 0.20/0.49    ( ! [X4,X0,X3,X1] : (r1_orders_2(X0,X4,X3) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X3) | m1_subset_1(sK4(X0),u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.49    inference(equality_resolution,[],[f75])).
% 0.20/0.49  fof(f75,plain,(
% 0.20/0.49    ( ! [X4,X2,X0,X3,X1] : (r1_orders_2(X0,X4,X3) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X2) | m1_subset_1(sK4(X0),u1_struct_0(X0)) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f47])).
% 0.20/0.49  fof(f47,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_waybel_9(X0,X1,X2) | (~v5_pre_topc(k4_waybel_1(X0,sK4(X0)),X0,X0) & m1_subset_1(sK4(X0),u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f45,f46])).
% 0.20/0.49  % (18221)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.49  fof(f46,plain,(
% 0.20/0.49    ! [X0] : (? [X5] : (~v5_pre_topc(k4_waybel_1(X0,X5),X0,X0) & m1_subset_1(X5,u1_struct_0(X0))) => (~v5_pre_topc(k4_waybel_1(X0,sK4(X0)),X0,X0) & m1_subset_1(sK4(X0),u1_struct_0(X0))))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f45,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_waybel_9(X0,X1,X2) | ? [X5] : (~v5_pre_topc(k4_waybel_1(X0,X5),X0,X0) & m1_subset_1(X5,u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.49    inference(rectify,[],[f32])).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X5] : (r1_orders_2(X0,X5,X3) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~r3_waybel_9(X0,X1,X2) | ? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.49    inference(flattening,[],[f31])).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((! [X5] : ((r1_orders_2(X0,X5,X3) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5)) | ~m1_subset_1(X5,u1_struct_0(X0))) | (~r3_waybel_9(X0,X1,X2) | ? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f14])).
% 0.20/0.49  fof(f14,plain,(
% 0.20/0.49    ! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r3_waybel_9(X0,X1,X2) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)) & X2 = X3) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X0)) => (r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5) => r1_orders_2(X0,X5,X3))))))))),
% 0.20/0.49    inference(rectify,[],[f11])).
% 0.20/0.49  fof(f11,axiom,(
% 0.20/0.49    ! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r3_waybel_9(X0,X1,X2) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)) & X2 = X3) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) => r1_orders_2(X0,X4,X3))))))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l52_waybel_9)).
% 0.20/0.49  fof(f242,plain,(
% 0.20/0.49    ~m1_subset_1(sK4(sK0),u1_struct_0(sK0)) | spl6_30),
% 0.20/0.49    inference(avatar_component_clause,[],[f241])).
% 0.20/0.49  fof(f243,plain,(
% 0.20/0.49    ~spl6_30 | spl6_28),
% 0.20/0.49    inference(avatar_split_clause,[],[f239,f233,f241])).
% 0.20/0.49  fof(f233,plain,(
% 0.20/0.49    spl6_28 <=> v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).
% 0.20/0.49  fof(f239,plain,(
% 0.20/0.49    ~m1_subset_1(sK4(sK0),u1_struct_0(sK0)) | spl6_28),
% 0.20/0.49    inference(resolution,[],[f234,f64])).
% 0.20/0.49  fof(f64,plain,(
% 0.20/0.49    ( ! [X3] : (v5_pre_topc(k4_waybel_1(sK0,X3),sK0,sK0) | ~m1_subset_1(X3,u1_struct_0(sK0))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f42])).
% 0.20/0.49  fof(f42,plain,(
% 0.20/0.49    ((sK1 != k1_waybel_9(sK0,sK2) & r3_waybel_9(sK0,sK2,sK1) & v11_waybel_0(sK2,sK0) & ! [X3] : (v5_pre_topc(k4_waybel_1(sK0,X3),sK0,sK0) | ~m1_subset_1(X3,u1_struct_0(sK0))) & l1_waybel_0(sK2,sK0) & v7_waybel_0(sK2) & v4_orders_2(sK2) & ~v2_struct_0(sK2)) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_waybel_9(sK0) & v1_compts_1(sK0) & v2_lattice3(sK0) & v1_lattice3(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & v8_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f41,f40,f39])).
% 0.20/0.49  fof(f39,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (? [X2] : (k1_waybel_9(X0,X2) != X1 & r3_waybel_9(X0,X2,X1) & v11_waybel_0(X2,X0) & ! [X3] : (v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0))) & l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (k1_waybel_9(sK0,X2) != X1 & r3_waybel_9(sK0,X2,X1) & v11_waybel_0(X2,sK0) & ! [X3] : (v5_pre_topc(k4_waybel_1(sK0,X3),sK0,sK0) | ~m1_subset_1(X3,u1_struct_0(sK0))) & l1_waybel_0(X2,sK0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_waybel_9(sK0) & v1_compts_1(sK0) & v2_lattice3(sK0) & v1_lattice3(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & v8_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f40,plain,(
% 0.20/0.49    ? [X1] : (? [X2] : (k1_waybel_9(sK0,X2) != X1 & r3_waybel_9(sK0,X2,X1) & v11_waybel_0(X2,sK0) & ! [X3] : (v5_pre_topc(k4_waybel_1(sK0,X3),sK0,sK0) | ~m1_subset_1(X3,u1_struct_0(sK0))) & l1_waybel_0(X2,sK0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : (k1_waybel_9(sK0,X2) != sK1 & r3_waybel_9(sK0,X2,sK1) & v11_waybel_0(X2,sK0) & ! [X3] : (v5_pre_topc(k4_waybel_1(sK0,X3),sK0,sK0) | ~m1_subset_1(X3,u1_struct_0(sK0))) & l1_waybel_0(X2,sK0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f41,plain,(
% 0.20/0.49    ? [X2] : (k1_waybel_9(sK0,X2) != sK1 & r3_waybel_9(sK0,X2,sK1) & v11_waybel_0(X2,sK0) & ! [X3] : (v5_pre_topc(k4_waybel_1(sK0,X3),sK0,sK0) | ~m1_subset_1(X3,u1_struct_0(sK0))) & l1_waybel_0(X2,sK0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) => (sK1 != k1_waybel_9(sK0,sK2) & r3_waybel_9(sK0,sK2,sK1) & v11_waybel_0(sK2,sK0) & ! [X3] : (v5_pre_topc(k4_waybel_1(sK0,X3),sK0,sK0) | ~m1_subset_1(X3,u1_struct_0(sK0))) & l1_waybel_0(sK2,sK0) & v7_waybel_0(sK2) & v4_orders_2(sK2) & ~v2_struct_0(sK2))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (? [X2] : (k1_waybel_9(X0,X2) != X1 & r3_waybel_9(X0,X2,X1) & v11_waybel_0(X2,X0) & ! [X3] : (v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0))) & l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0))),
% 0.20/0.49    inference(flattening,[],[f19])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (? [X2] : ((k1_waybel_9(X0,X2) != X1 & (r3_waybel_9(X0,X2,X1) & v11_waybel_0(X2,X0) & ! [X3] : (v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0))))) & (l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f13])).
% 0.20/0.49  fof(f13,negated_conjecture,(
% 0.20/0.49    ~! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) => ((r3_waybel_9(X0,X2,X1) & v11_waybel_0(X2,X0) & ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X3),X0,X0))) => k1_waybel_9(X0,X2) = X1))))),
% 0.20/0.49    inference(negated_conjecture,[],[f12])).
% 0.20/0.49  fof(f12,conjecture,(
% 0.20/0.49    ! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) => ((r3_waybel_9(X0,X2,X1) & v11_waybel_0(X2,X0) & ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X3),X0,X0))) => k1_waybel_9(X0,X2) = X1))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_waybel_9)).
% 0.20/0.49  fof(f234,plain,(
% 0.20/0.49    ~v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0) | spl6_28),
% 0.20/0.49    inference(avatar_component_clause,[],[f233])).
% 0.20/0.49  fof(f238,plain,(
% 0.20/0.49    ~spl6_28 | ~spl6_4 | ~spl6_9 | spl6_29 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_14 | ~spl6_15 | ~spl6_16 | ~spl6_17 | ~spl6_10 | ~spl6_27),
% 0.20/0.49    inference(avatar_split_clause,[],[f231,f228,f135,f163,f159,f155,f151,f147,f143,f139,f236,f131,f111,f233])).
% 0.20/0.49  fof(f228,plain,(
% 0.20/0.49    spl6_27 <=> ! [X1,X0,X2] : (~r1_lattice3(X0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(X0),u1_waybel_0(X0,sK2)),X1) | ~v2_pre_topc(X0) | ~v8_pre_topc(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~v1_lattice3(X0) | ~v2_lattice3(X0) | ~v1_compts_1(X0) | ~l1_waybel_9(X0) | r1_orders_2(X0,X1,X2) | ~l1_waybel_0(sK2,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v5_pre_topc(k4_waybel_1(X0,sK4(X0)),X0,X0) | ~r3_waybel_9(X0,sK2,X2) | ~m1_subset_1(X1,u1_struct_0(X0)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 0.20/0.49  fof(f231,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v2_pre_topc(sK0) | ~v8_pre_topc(sK0) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~v1_lattice3(sK0) | ~v2_lattice3(sK0) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | ~l1_waybel_9(sK0) | r1_orders_2(sK0,X0,X1) | ~l1_waybel_0(sK2,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0) | ~r3_waybel_9(sK0,sK2,X1) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl6_10 | ~spl6_27)),
% 0.20/0.49    inference(resolution,[],[f229,f136])).
% 0.20/0.49  fof(f136,plain,(
% 0.20/0.49    v1_compts_1(sK0) | ~spl6_10),
% 0.20/0.49    inference(avatar_component_clause,[],[f135])).
% 0.20/0.49  fof(f229,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~v1_compts_1(X0) | ~v2_pre_topc(X0) | ~v8_pre_topc(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~v1_lattice3(X0) | ~v2_lattice3(X0) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(X0),u1_waybel_0(X0,sK2)),X1) | ~l1_waybel_9(X0) | r1_orders_2(X0,X1,X2) | ~l1_waybel_0(sK2,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v5_pre_topc(k4_waybel_1(X0,sK4(X0)),X0,X0) | ~r3_waybel_9(X0,sK2,X2) | ~m1_subset_1(X1,u1_struct_0(X0))) ) | ~spl6_27),
% 0.20/0.49    inference(avatar_component_clause,[],[f228])).
% 0.20/0.49  fof(f230,plain,(
% 0.20/0.49    spl6_7 | ~spl6_6 | spl6_27 | ~spl6_5),
% 0.20/0.49    inference(avatar_split_clause,[],[f226,f115,f228,f119,f123])).
% 0.20/0.49  fof(f226,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~r1_lattice3(X0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(X0),u1_waybel_0(X0,sK2)),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r3_waybel_9(X0,sK2,X2) | ~v5_pre_topc(k4_waybel_1(X0,sK4(X0)),X0,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(sK2,X0) | r1_orders_2(X0,X1,X2) | ~v4_orders_2(sK2) | v2_struct_0(sK2) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl6_5),
% 0.20/0.49    inference(resolution,[],[f95,f116])).
% 0.20/0.49  fof(f95,plain,(
% 0.20/0.49    ( ! [X4,X0,X3,X1] : (~v7_waybel_0(X1) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X3) | ~v5_pre_topc(k4_waybel_1(X0,sK4(X0)),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | r1_orders_2(X0,X4,X3) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f90])).
% 0.20/0.49  fof(f90,plain,(
% 0.20/0.49    ( ! [X4,X0,X3,X1] : (r1_orders_2(X0,X4,X3) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X3) | ~v5_pre_topc(k4_waybel_1(X0,sK4(X0)),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.49    inference(equality_resolution,[],[f76])).
% 0.20/0.49  % (18221)Refutation not found, incomplete strategy% (18221)------------------------------
% 0.20/0.49  % (18221)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (18221)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (18221)Memory used [KB]: 6140
% 0.20/0.49  % (18221)Time elapsed: 0.082 s
% 0.20/0.49  % (18221)------------------------------
% 0.20/0.49  % (18221)------------------------------
% 0.20/0.49  fof(f76,plain,(
% 0.20/0.49    ( ! [X4,X2,X0,X3,X1] : (r1_orders_2(X0,X4,X3) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X2) | ~v5_pre_topc(k4_waybel_1(X0,sK4(X0)),X0,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f47])).
% 0.20/0.49  fof(f225,plain,(
% 0.20/0.49    ~spl6_9 | spl6_26),
% 0.20/0.49    inference(avatar_split_clause,[],[f224,f221,f131])).
% 0.20/0.49  fof(f224,plain,(
% 0.20/0.49    ~l1_waybel_9(sK0) | spl6_26),
% 0.20/0.49    inference(resolution,[],[f222,f68])).
% 0.20/0.49  fof(f68,plain,(
% 0.20/0.49    ( ! [X0] : (l1_orders_2(X0) | ~l1_waybel_9(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f21])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ! [X0] : (l1_orders_2(X0) | ~l1_waybel_9(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f16])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ! [X0] : (l1_waybel_9(X0) => l1_orders_2(X0))),
% 0.20/0.49    inference(pure_predicate_removal,[],[f9])).
% 0.20/0.49  fof(f9,axiom,(
% 0.20/0.49    ! [X0] : (l1_waybel_9(X0) => (l1_orders_2(X0) & l1_pre_topc(X0)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_waybel_9)).
% 0.20/0.49  fof(f222,plain,(
% 0.20/0.49    ~l1_orders_2(sK0) | spl6_26),
% 0.20/0.49    inference(avatar_component_clause,[],[f221])).
% 0.20/0.49  fof(f223,plain,(
% 0.20/0.49    ~spl6_26 | spl6_24),
% 0.20/0.49    inference(avatar_split_clause,[],[f219,f213,f221])).
% 0.20/0.49  fof(f219,plain,(
% 0.20/0.49    ~l1_orders_2(sK0) | spl6_24),
% 0.20/0.49    inference(resolution,[],[f214,f69])).
% 0.20/0.49  fof(f69,plain,(
% 0.20/0.49    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f22])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 0.20/0.49  fof(f214,plain,(
% 0.20/0.49    ~l1_struct_0(sK0) | spl6_24),
% 0.20/0.49    inference(avatar_component_clause,[],[f213])).
% 0.20/0.49  fof(f218,plain,(
% 0.20/0.49    ~spl6_4 | ~spl6_24 | spl6_25 | ~spl6_23),
% 0.20/0.49    inference(avatar_split_clause,[],[f211,f208,f216,f213,f111])).
% 0.20/0.49  fof(f208,plain,(
% 0.20/0.49    spl6_23 <=> r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 0.20/0.49  fof(f211,plain,(
% 0.20/0.49    r1_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),sK1) | ~l1_struct_0(sK0) | ~l1_waybel_0(sK2,sK0) | ~spl6_23),
% 0.20/0.49    inference(superposition,[],[f209,f166])).
% 0.20/0.49  fof(f209,plain,(
% 0.20/0.49    r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1) | ~spl6_23),
% 0.20/0.49    inference(avatar_component_clause,[],[f208])).
% 0.20/0.49  fof(f210,plain,(
% 0.20/0.49    ~spl6_8 | spl6_23 | ~spl6_2 | ~spl6_20),
% 0.20/0.49    inference(avatar_split_clause,[],[f205,f180,f103,f208,f127])).
% 0.20/0.49  fof(f180,plain,(
% 0.20/0.49    spl6_20 <=> ! [X0] : (r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | ~r3_waybel_9(sK0,sK2,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 0.20/0.49  % (18233)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.49  fof(f205,plain,(
% 0.20/0.49    r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | (~spl6_2 | ~spl6_20)),
% 0.20/0.49    inference(resolution,[],[f181,f104])).
% 0.20/0.49  fof(f181,plain,(
% 0.20/0.49    ( ! [X0] : (~r3_waybel_9(sK0,sK2,X0) | r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl6_20),
% 0.20/0.49    inference(avatar_component_clause,[],[f180])).
% 0.20/0.49  fof(f204,plain,(
% 0.20/0.49    spl6_20 | ~spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7 | ~spl6_3 | ~spl6_22),
% 0.20/0.49    inference(avatar_split_clause,[],[f202,f199,f107,f123,f119,f115,f111,f180])).
% 0.20/0.49  fof(f107,plain,(
% 0.20/0.49    spl6_3 <=> v11_waybel_0(sK2,sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.20/0.49  fof(f199,plain,(
% 0.20/0.49    spl6_22 <=> ! [X1,X0] : (~r3_waybel_9(sK0,X0,X1) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~l1_waybel_0(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1) | ~v11_waybel_0(X0,sK0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 0.20/0.49  fof(f202,plain,(
% 0.20/0.49    ( ! [X0] : (v2_struct_0(sK2) | ~v4_orders_2(sK2) | ~v7_waybel_0(sK2) | ~l1_waybel_0(sK2,sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | ~r3_waybel_9(sK0,sK2,X0)) ) | (~spl6_3 | ~spl6_22)),
% 0.20/0.49    inference(resolution,[],[f200,f108])).
% 0.20/0.49  fof(f108,plain,(
% 0.20/0.49    v11_waybel_0(sK2,sK0) | ~spl6_3),
% 0.20/0.49    inference(avatar_component_clause,[],[f107])).
% 0.20/0.49  fof(f200,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v11_waybel_0(X0,sK0) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~l1_waybel_0(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1) | ~r3_waybel_9(sK0,X0,X1)) ) | ~spl6_22),
% 0.20/0.49    inference(avatar_component_clause,[],[f199])).
% 0.20/0.49  fof(f201,plain,(
% 0.20/0.49    ~spl6_17 | ~spl6_16 | ~spl6_15 | ~spl6_14 | ~spl6_13 | ~spl6_12 | ~spl6_11 | ~spl6_10 | ~spl6_9 | spl6_22 | spl6_21),
% 0.20/0.49    inference(avatar_split_clause,[],[f197,f194,f199,f131,f135,f139,f143,f147,f151,f155,f159,f163])).
% 0.20/0.49  fof(f194,plain,(
% 0.20/0.49    spl6_21 <=> m1_subset_1(sK3(sK0),u1_struct_0(sK0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 0.20/0.49  fof(f197,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r3_waybel_9(sK0,X0,X1) | ~v11_waybel_0(X0,sK0) | r1_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_waybel_9(sK0) | ~v1_compts_1(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) ) | spl6_21),
% 0.20/0.49    inference(resolution,[],[f195,f96])).
% 0.20/0.49  fof(f96,plain,(
% 0.20/0.49    ( ! [X0,X3,X1] : (m1_subset_1(sK3(X0),u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X3) | ~v11_waybel_0(X1,X0) | r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f89])).
% 0.20/0.49  fof(f89,plain,(
% 0.20/0.49    ( ! [X0,X3,X1] : (r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X3) | ~v11_waybel_0(X1,X0) | m1_subset_1(sK3(X0),u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.49    inference(equality_resolution,[],[f73])).
% 0.20/0.49  fof(f73,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X2) | ~v11_waybel_0(X1,X0) | m1_subset_1(sK3(X0),u1_struct_0(X0)) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f44])).
% 0.20/0.49  fof(f44,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X2) | ~v11_waybel_0(X1,X0) | (~v5_pre_topc(k4_waybel_1(X0,sK3(X0)),X0,X0) & m1_subset_1(sK3(X0),u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f43])).
% 0.20/0.49  fof(f43,plain,(
% 0.20/0.49    ! [X0] : (? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) => (~v5_pre_topc(k4_waybel_1(X0,sK3(X0)),X0,X0) & m1_subset_1(sK3(X0),u1_struct_0(X0))))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X2) | ~v11_waybel_0(X1,X0) | ? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.49    inference(flattening,[],[f29])).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | (~r3_waybel_9(X0,X1,X2) | ~v11_waybel_0(X1,X0) | ? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f10])).
% 0.20/0.49  fof(f10,axiom,(
% 0.20/0.49    ! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r3_waybel_9(X0,X1,X2) & v11_waybel_0(X1,X0) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)) & X2 = X3) => r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3))))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_waybel_9)).
% 0.20/0.49  fof(f195,plain,(
% 0.20/0.49    ~m1_subset_1(sK3(sK0),u1_struct_0(sK0)) | spl6_21),
% 0.20/0.49    inference(avatar_component_clause,[],[f194])).
% 0.20/0.49  fof(f196,plain,(
% 0.20/0.49    ~spl6_21 | spl6_19),
% 0.20/0.49    inference(avatar_split_clause,[],[f192,f176,f194])).
% 0.20/0.49  fof(f176,plain,(
% 0.20/0.49    spl6_19 <=> v5_pre_topc(k4_waybel_1(sK0,sK3(sK0)),sK0,sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 0.20/0.49  fof(f192,plain,(
% 0.20/0.49    ~m1_subset_1(sK3(sK0),u1_struct_0(sK0)) | spl6_19),
% 0.20/0.49    inference(resolution,[],[f177,f64])).
% 0.20/0.49  fof(f177,plain,(
% 0.20/0.49    ~v5_pre_topc(k4_waybel_1(sK0,sK3(sK0)),sK0,sK0) | spl6_19),
% 0.20/0.49    inference(avatar_component_clause,[],[f176])).
% 0.20/0.49  fof(f191,plain,(
% 0.20/0.49    ~spl6_19 | ~spl6_4 | spl6_20 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_14 | ~spl6_15 | ~spl6_16 | ~spl6_17 | ~spl6_3 | ~spl6_18),
% 0.20/0.49    inference(avatar_split_clause,[],[f174,f171,f107,f163,f159,f155,f151,f147,f143,f139,f135,f131,f180,f111,f176])).
% 0.20/0.49  fof(f171,plain,(
% 0.20/0.49    spl6_18 <=> ! [X1,X0] : (~r3_waybel_9(X0,sK2,X1) | ~v2_pre_topc(X0) | ~v8_pre_topc(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~v1_lattice3(X0) | ~v2_lattice3(X0) | ~v1_compts_1(X0) | ~l1_waybel_9(X0) | r1_lattice3(X0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(X0),u1_waybel_0(X0,sK2)),X1) | ~l1_waybel_0(sK2,X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v5_pre_topc(k4_waybel_1(X0,sK3(X0)),X0,X0) | ~v11_waybel_0(sK2,X0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 0.20/0.49  fof(f174,plain,(
% 0.20/0.49    ( ! [X0] : (~v2_pre_topc(sK0) | ~v8_pre_topc(sK0) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~v1_lattice3(sK0) | ~v2_lattice3(sK0) | ~v1_compts_1(sK0) | ~l1_waybel_9(sK0) | r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | ~l1_waybel_0(sK2,sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v5_pre_topc(k4_waybel_1(sK0,sK3(sK0)),sK0,sK0) | ~r3_waybel_9(sK0,sK2,X0)) ) | (~spl6_3 | ~spl6_18)),
% 0.20/0.49    inference(resolution,[],[f172,f108])).
% 0.20/0.49  fof(f172,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v11_waybel_0(sK2,X0) | ~v2_pre_topc(X0) | ~v8_pre_topc(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~v1_lattice3(X0) | ~v2_lattice3(X0) | ~v1_compts_1(X0) | ~l1_waybel_9(X0) | r1_lattice3(X0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(X0),u1_waybel_0(X0,sK2)),X1) | ~l1_waybel_0(sK2,X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v5_pre_topc(k4_waybel_1(X0,sK3(X0)),X0,X0) | ~r3_waybel_9(X0,sK2,X1)) ) | ~spl6_18),
% 0.20/0.49    inference(avatar_component_clause,[],[f171])).
% 0.20/0.49  fof(f173,plain,(
% 0.20/0.49    spl6_7 | ~spl6_6 | spl6_18 | ~spl6_5),
% 0.20/0.49    inference(avatar_split_clause,[],[f167,f115,f171,f119,f123])).
% 0.20/0.49  fof(f167,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r3_waybel_9(X0,sK2,X1) | ~v11_waybel_0(sK2,X0) | ~v5_pre_topc(k4_waybel_1(X0,sK3(X0)),X0,X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_waybel_0(sK2,X0) | r1_lattice3(X0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(X0),u1_waybel_0(X0,sK2)),X1) | ~v4_orders_2(sK2) | v2_struct_0(sK2) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl6_5),
% 0.20/0.49    inference(resolution,[],[f97,f116])).
% 0.20/0.49  fof(f97,plain,(
% 0.20/0.49    ( ! [X0,X3,X1] : (~v7_waybel_0(X1) | ~r3_waybel_9(X0,X1,X3) | ~v11_waybel_0(X1,X0) | ~v5_pre_topc(k4_waybel_1(X0,sK3(X0)),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f88])).
% 0.20/0.49  fof(f88,plain,(
% 0.20/0.49    ( ! [X0,X3,X1] : (r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X3) | ~v11_waybel_0(X1,X0) | ~v5_pre_topc(k4_waybel_1(X0,sK3(X0)),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.49    inference(equality_resolution,[],[f74])).
% 0.20/0.49  fof(f74,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X2) | ~v11_waybel_0(X1,X0) | ~v5_pre_topc(k4_waybel_1(X0,sK3(X0)),X0,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f44])).
% 0.20/0.49  fof(f165,plain,(
% 0.20/0.49    spl6_17),
% 0.20/0.49    inference(avatar_split_clause,[],[f50,f163])).
% 0.20/0.49  fof(f50,plain,(
% 0.20/0.49    v2_pre_topc(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f42])).
% 0.20/0.49  fof(f161,plain,(
% 0.20/0.49    spl6_16),
% 0.20/0.49    inference(avatar_split_clause,[],[f51,f159])).
% 0.20/0.49  fof(f51,plain,(
% 0.20/0.49    v8_pre_topc(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f42])).
% 0.20/0.49  fof(f157,plain,(
% 0.20/0.49    spl6_15),
% 0.20/0.49    inference(avatar_split_clause,[],[f52,f155])).
% 0.20/0.49  fof(f52,plain,(
% 0.20/0.49    v3_orders_2(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f42])).
% 0.20/0.49  fof(f153,plain,(
% 0.20/0.49    spl6_14),
% 0.20/0.49    inference(avatar_split_clause,[],[f53,f151])).
% 0.20/0.49  fof(f53,plain,(
% 0.20/0.49    v4_orders_2(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f42])).
% 0.20/0.49  fof(f149,plain,(
% 0.20/0.49    spl6_13),
% 0.20/0.49    inference(avatar_split_clause,[],[f54,f147])).
% 0.20/0.49  fof(f54,plain,(
% 0.20/0.49    v5_orders_2(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f42])).
% 0.20/0.49  fof(f145,plain,(
% 0.20/0.49    spl6_12),
% 0.20/0.49    inference(avatar_split_clause,[],[f55,f143])).
% 0.20/0.49  fof(f55,plain,(
% 0.20/0.49    v1_lattice3(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f42])).
% 0.20/0.49  fof(f141,plain,(
% 0.20/0.49    spl6_11),
% 0.20/0.49    inference(avatar_split_clause,[],[f56,f139])).
% 0.20/0.49  fof(f56,plain,(
% 0.20/0.49    v2_lattice3(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f42])).
% 0.20/0.49  fof(f137,plain,(
% 0.20/0.49    spl6_10),
% 0.20/0.49    inference(avatar_split_clause,[],[f57,f135])).
% 0.20/0.49  fof(f57,plain,(
% 0.20/0.49    v1_compts_1(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f42])).
% 0.20/0.49  fof(f133,plain,(
% 0.20/0.49    spl6_9),
% 0.20/0.49    inference(avatar_split_clause,[],[f58,f131])).
% 0.20/0.49  fof(f58,plain,(
% 0.20/0.49    l1_waybel_9(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f42])).
% 0.20/0.49  fof(f129,plain,(
% 0.20/0.49    spl6_8),
% 0.20/0.49    inference(avatar_split_clause,[],[f59,f127])).
% 0.20/0.49  fof(f59,plain,(
% 0.20/0.49    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.49    inference(cnf_transformation,[],[f42])).
% 0.20/0.49  fof(f125,plain,(
% 0.20/0.49    ~spl6_7),
% 0.20/0.49    inference(avatar_split_clause,[],[f60,f123])).
% 0.20/0.49  fof(f60,plain,(
% 0.20/0.49    ~v2_struct_0(sK2)),
% 0.20/0.49    inference(cnf_transformation,[],[f42])).
% 0.20/0.49  fof(f121,plain,(
% 0.20/0.49    spl6_6),
% 0.20/0.49    inference(avatar_split_clause,[],[f61,f119])).
% 0.20/0.49  fof(f61,plain,(
% 0.20/0.49    v4_orders_2(sK2)),
% 0.20/0.49    inference(cnf_transformation,[],[f42])).
% 0.20/0.49  fof(f117,plain,(
% 0.20/0.49    spl6_5),
% 0.20/0.49    inference(avatar_split_clause,[],[f62,f115])).
% 0.20/0.49  fof(f62,plain,(
% 0.20/0.49    v7_waybel_0(sK2)),
% 0.20/0.49    inference(cnf_transformation,[],[f42])).
% 0.20/0.49  fof(f113,plain,(
% 0.20/0.49    spl6_4),
% 0.20/0.49    inference(avatar_split_clause,[],[f63,f111])).
% 0.20/0.49  fof(f63,plain,(
% 0.20/0.49    l1_waybel_0(sK2,sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f42])).
% 0.20/0.49  fof(f109,plain,(
% 0.20/0.49    spl6_3),
% 0.20/0.49    inference(avatar_split_clause,[],[f65,f107])).
% 0.20/0.49  fof(f65,plain,(
% 0.20/0.49    v11_waybel_0(sK2,sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f42])).
% 0.20/0.49  fof(f105,plain,(
% 0.20/0.49    spl6_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f66,f103])).
% 0.20/0.49  fof(f66,plain,(
% 0.20/0.49    r3_waybel_9(sK0,sK2,sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f42])).
% 0.20/0.49  fof(f101,plain,(
% 0.20/0.49    ~spl6_1),
% 0.20/0.49    inference(avatar_split_clause,[],[f67,f99])).
% 0.20/0.49  fof(f67,plain,(
% 0.20/0.49    sK1 != k1_waybel_9(sK0,sK2)),
% 0.20/0.49    inference(cnf_transformation,[],[f42])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (18227)------------------------------
% 0.20/0.49  % (18227)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (18227)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (18227)Memory used [KB]: 11001
% 0.20/0.49  % (18227)Time elapsed: 0.061 s
% 0.20/0.49  % (18227)------------------------------
% 0.20/0.49  % (18227)------------------------------
% 0.20/0.49  % (18233)Refutation not found, incomplete strategy% (18233)------------------------------
% 0.20/0.49  % (18233)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (18233)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (18233)Memory used [KB]: 6140
% 0.20/0.49  % (18233)Time elapsed: 0.002 s
% 0.20/0.49  % (18233)------------------------------
% 0.20/0.49  % (18233)------------------------------
% 0.20/0.49  % (18220)Success in time 0.136 s
%------------------------------------------------------------------------------
