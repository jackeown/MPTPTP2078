%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:53 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  202 ( 356 expanded)
%              Number of leaves         :   52 ( 142 expanded)
%              Depth                    :   16
%              Number of atoms          :  875 (2156 expanded)
%              Number of equality atoms :   41 (  57 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f545,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f107,f122,f127,f132,f137,f142,f152,f157,f167,f169,f175,f188,f224,f242,f243,f258,f319,f334,f342,f348,f354,f358,f398,f432,f433,f434,f493,f535,f543,f544])).

fof(f544,plain,
    ( u1_struct_0(sK0) != sK1
    | m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f543,plain,
    ( ~ spl8_16
    | ~ spl8_17 ),
    inference(avatar_contradiction_clause,[],[f542])).

fof(f542,plain,
    ( $false
    | ~ spl8_16
    | ~ spl8_17 ),
    inference(unit_resulting_resolution,[],[f197,f191,f102])).

fof(f102,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X1))
      | ~ v1_subset_1(X1,X1) ) ),
    inference(equality_resolution,[],[f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

fof(f191,plain,
    ( v1_subset_1(sK1,sK1)
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f190])).

fof(f190,plain,
    ( spl8_16
  <=> v1_subset_1(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f197,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ spl8_17 ),
    inference(avatar_component_clause,[],[f195])).

fof(f195,plain,
    ( spl8_17
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f535,plain,
    ( spl8_15
    | ~ spl8_11
    | ~ spl8_50 ),
    inference(avatar_split_clause,[],[f500,f490,f154,f185])).

fof(f185,plain,
    ( spl8_15
  <=> u1_struct_0(sK0) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f154,plain,
    ( spl8_11
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f490,plain,
    ( spl8_50
  <=> r2_hidden(sK7(u1_struct_0(sK0),sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_50])])).

fof(f500,plain,
    ( u1_struct_0(sK0) = sK1
    | ~ spl8_11
    | ~ spl8_50 ),
    inference(subsumption_resolution,[],[f498,f156])).

fof(f156,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f154])).

fof(f498,plain,
    ( u1_struct_0(sK0) = sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_50 ),
    inference(resolution,[],[f492,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK7(X0,X1),X1)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ~ r2_hidden(sK7(X0,X1),X1)
        & m1_subset_1(sK7(X0,X1),X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f30,f57])).

fof(f57,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
     => ( ~ r2_hidden(sK7(X0,X1),X1)
        & m1_subset_1(sK7(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( ! [X2] :
            ( m1_subset_1(X2,X0)
           => r2_hidden(X2,X1) )
       => X0 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_subset_1)).

fof(f492,plain,
    ( r2_hidden(sK7(u1_struct_0(sK0),sK1),sK1)
    | ~ spl8_50 ),
    inference(avatar_component_clause,[],[f490])).

fof(f493,plain,
    ( spl8_50
    | ~ spl8_22
    | ~ spl8_43 ),
    inference(avatar_split_clause,[],[f470,f430,f239,f490])).

fof(f239,plain,
    ( spl8_22
  <=> m1_subset_1(sK7(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f430,plain,
    ( spl8_43
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_43])])).

fof(f470,plain,
    ( r2_hidden(sK7(u1_struct_0(sK0),sK1),sK1)
    | ~ spl8_22
    | ~ spl8_43 ),
    inference(resolution,[],[f431,f241])).

fof(f241,plain,
    ( m1_subset_1(sK7(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ spl8_22 ),
    inference(avatar_component_clause,[],[f239])).

fof(f431,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,sK1) )
    | ~ spl8_43 ),
    inference(avatar_component_clause,[],[f430])).

fof(f434,plain,
    ( u1_struct_0(sK0) != sK1
    | r2_hidden(k3_yellow_0(sK0),sK1)
    | ~ r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f433,plain,
    ( u1_struct_0(sK0) != sK1
    | v1_xboole_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f432,plain,
    ( spl8_43
    | ~ spl8_13
    | ~ spl8_37
    | ~ spl8_40 ),
    inference(avatar_split_clause,[],[f422,f396,f356,f164,f430])).

fof(f164,plain,
    ( spl8_13
  <=> r2_hidden(k3_yellow_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f356,plain,
    ( spl8_37
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X1)
        | r2_hidden(X1,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_37])])).

fof(f396,plain,
    ( spl8_40
  <=> ! [X0] :
        ( r1_orders_2(sK0,k3_yellow_0(sK0),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_40])])).

fof(f422,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,sK1) )
    | ~ spl8_13
    | ~ spl8_37
    | ~ spl8_40 ),
    inference(subsumption_resolution,[],[f421,f165])).

fof(f165,plain,
    ( r2_hidden(k3_yellow_0(sK0),sK1)
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f164])).

fof(f421,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(k3_yellow_0(sK0),sK1)
        | r2_hidden(X0,sK1) )
    | ~ spl8_37
    | ~ spl8_40 ),
    inference(duplicate_literal_removal,[],[f419])).

fof(f419,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(k3_yellow_0(sK0),sK1)
        | r2_hidden(X0,sK1) )
    | ~ spl8_37
    | ~ spl8_40 ),
    inference(resolution,[],[f397,f357])).

fof(f357,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK1)
        | r2_hidden(X1,sK1) )
    | ~ spl8_37 ),
    inference(avatar_component_clause,[],[f356])).

fof(f397,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,k3_yellow_0(sK0),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl8_40 ),
    inference(avatar_component_clause,[],[f396])).

fof(f398,plain,
    ( spl8_40
    | ~ spl8_6
    | ~ spl8_14
    | ~ spl8_29
    | ~ spl8_36 ),
    inference(avatar_split_clause,[],[f369,f352,f302,f172,f129,f396])).

fof(f129,plain,
    ( spl8_6
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f172,plain,
    ( spl8_14
  <=> k3_yellow_0(sK0) = k1_yellow_0(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f302,plain,
    ( spl8_29
  <=> r1_yellow_0(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).

fof(f352,plain,
    ( spl8_36
  <=> ! [X0] :
        ( r2_lattice3(sK0,k1_xboole_0,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_36])])).

fof(f369,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,k3_yellow_0(sK0),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl8_6
    | ~ spl8_14
    | ~ spl8_29
    | ~ spl8_36 ),
    inference(forward_demodulation,[],[f368,f174])).

fof(f174,plain,
    ( k3_yellow_0(sK0) = k1_yellow_0(sK0,k1_xboole_0)
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f172])).

fof(f368,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,k1_yellow_0(sK0,k1_xboole_0),X0) )
    | ~ spl8_6
    | ~ spl8_29
    | ~ spl8_36 ),
    inference(subsumption_resolution,[],[f367,f131])).

fof(f131,plain,
    ( l1_orders_2(sK0)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f129])).

fof(f367,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,k1_yellow_0(sK0,k1_xboole_0),X0)
        | ~ l1_orders_2(sK0) )
    | ~ spl8_29
    | ~ spl8_36 ),
    inference(subsumption_resolution,[],[f366,f303])).

fof(f303,plain,
    ( r1_yellow_0(sK0,k1_xboole_0)
    | ~ spl8_29 ),
    inference(avatar_component_clause,[],[f302])).

fof(f366,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,k1_yellow_0(sK0,k1_xboole_0),X0)
        | ~ r1_yellow_0(sK0,k1_xboole_0)
        | ~ l1_orders_2(sK0) )
    | ~ spl8_36 ),
    inference(duplicate_literal_removal,[],[f359])).

fof(f359,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,k1_yellow_0(sK0,k1_xboole_0),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_yellow_0(sK0,k1_xboole_0)
        | ~ l1_orders_2(sK0) )
    | ~ spl8_36 ),
    inference(resolution,[],[f353,f274])).

fof(f274,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_lattice3(X0,X1,X4)
      | r1_orders_2(X0,k1_yellow_0(X0,X1),X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f100,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_0)).

fof(f100,plain,(
    ! [X4,X0,X1] :
      ( r1_orders_2(X0,k1_yellow_0(X0,X1),X4)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X2,X4)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | k1_yellow_0(X0,X1) != X2
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ( ~ r1_orders_2(X0,X2,sK4(X0,X1,X2))
                & r2_lattice3(X0,X1,sK4(X0,X1,X2))
                & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f46,f47])).

fof(f47,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK4(X0,X1,X2))
        & r2_lattice3(X0,X1,sK4(X0,X1,X2))
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
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
    inference(rectify,[],[f45])).

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f353,plain,
    ( ! [X0] :
        ( r2_lattice3(sK0,k1_xboole_0,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl8_36 ),
    inference(avatar_component_clause,[],[f352])).

fof(f358,plain,
    ( spl8_37
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_34 ),
    inference(avatar_split_clause,[],[f344,f340,f154,f149,f356])).

fof(f149,plain,
    ( spl8_10
  <=> v13_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f340,plain,
    ( spl8_34
  <=> ! [X1,X0,X2] :
        ( ~ r1_orders_2(sK0,X0,X1)
        | ~ r2_hidden(X0,X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v13_waybel_0(X2,sK0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_34])])).

fof(f344,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X1)
        | r2_hidden(X1,sK1) )
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_34 ),
    inference(subsumption_resolution,[],[f343,f156])).

fof(f343,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X1,sK1) )
    | ~ spl8_10
    | ~ spl8_34 ),
    inference(resolution,[],[f341,f151])).

fof(f151,plain,
    ( v13_waybel_0(sK1,sK0)
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f149])).

fof(f341,plain,
    ( ! [X2,X0,X1] :
        ( ~ v13_waybel_0(X2,sK0)
        | ~ r2_hidden(X0,X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X1,X2) )
    | ~ spl8_34 ),
    inference(avatar_component_clause,[],[f340])).

fof(f354,plain,
    ( spl8_36
    | ~ spl8_8
    | ~ spl8_35 ),
    inference(avatar_split_clause,[],[f349,f346,f139,f352])).

fof(f139,plain,
    ( spl8_8
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f346,plain,
    ( spl8_35
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_lattice3(sK0,X1,X0)
        | ~ v1_xboole_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_35])])).

fof(f349,plain,
    ( ! [X0] :
        ( r2_lattice3(sK0,k1_xboole_0,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl8_8
    | ~ spl8_35 ),
    inference(resolution,[],[f347,f141])).

fof(f141,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f139])).

fof(f347,plain,
    ( ! [X0,X1] :
        ( ~ v1_xboole_0(X1)
        | r2_lattice3(sK0,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl8_35 ),
    inference(avatar_component_clause,[],[f346])).

fof(f348,plain,
    ( spl8_35
    | ~ spl8_33 ),
    inference(avatar_split_clause,[],[f335,f332,f346])).

fof(f332,plain,
    ( spl8_33
  <=> ! [X1,X0] :
        ( r2_hidden(sK5(sK0,X0,X1),X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_lattice3(sK0,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_33])])).

fof(f335,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_lattice3(sK0,X1,X0)
        | ~ v1_xboole_0(X1) )
    | ~ spl8_33 ),
    inference(resolution,[],[f333,f91])).

fof(f91,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK6(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f54,f55])).

fof(f55,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK6(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f333,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK5(sK0,X0,X1),X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_lattice3(sK0,X0,X1) )
    | ~ spl8_33 ),
    inference(avatar_component_clause,[],[f332])).

fof(f342,plain,
    ( spl8_34
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f291,f129,f340])).

fof(f291,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_orders_2(sK0,X0,X1)
        | ~ r2_hidden(X0,X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v13_waybel_0(X2,sK0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X1,X2) )
    | ~ spl8_6 ),
    inference(resolution,[],[f285,f131])).

fof(f285,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_orders_2(X0,X4,X5)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X5,X1) ) ),
    inference(subsumption_resolution,[],[f74,f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f74,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r1_orders_2(X0,X4,X5)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v13_waybel_0(X1,X0)
              | ( ~ r2_hidden(sK3(X0,X1),X1)
                & r1_orders_2(X0,sK2(X0,X1),sK3(X0,X1))
                & r2_hidden(sK2(X0,X1),X1)
                & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | ~ r1_orders_2(X0,X4,X5)
                      | ~ r2_hidden(X4,X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v13_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f40,f42,f41])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(X3,X1)
              & r1_orders_2(X0,X2,X3)
              & r2_hidden(X2,X1)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ~ r2_hidden(X3,X1)
            & r1_orders_2(X0,sK2(X0,X1),X3)
            & r2_hidden(sK2(X0,X1),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X1)
          & r1_orders_2(X0,sK2(X0,X1),X3)
          & r2_hidden(sK2(X0,X1),X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r1_orders_2(X0,sK2(X0,X1),sK3(X0,X1))
        & r2_hidden(sK2(X0,X1),X1)
        & m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v13_waybel_0(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & r1_orders_2(X0,X2,X3)
                      & r2_hidden(X2,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | ~ r1_orders_2(X0,X4,X5)
                      | ~ r2_hidden(X4,X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v13_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v13_waybel_0(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & r1_orders_2(X0,X2,X3)
                      & r2_hidden(X2,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ! [X3] :
                      ( r2_hidden(X3,X1)
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r2_hidden(X2,X1)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v13_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X2,X3)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X2,X3)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r1_orders_2(X0,X2,X3)
                        & r2_hidden(X2,X1) )
                     => r2_hidden(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_waybel_0)).

fof(f334,plain,
    ( spl8_33
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f248,f129,f332])).

fof(f248,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK5(sK0,X0,X1),X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_lattice3(sK0,X0,X1) )
    | ~ spl8_6 ),
    inference(resolution,[],[f87,f131])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | r2_hidden(sK5(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,sK5(X0,X1,X2),X2)
                & r2_hidden(sK5(X0,X1,X2),X1)
                & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f50,f51])).

fof(f51,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK5(X0,X1,X2),X2)
        & r2_hidden(sK5(X0,X1,X2),X1)
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
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
    inference(rectify,[],[f49])).

fof(f49,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X3,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattice3)).

fof(f319,plain,
    ( spl8_1
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | spl8_29 ),
    inference(avatar_contradiction_clause,[],[f318])).

fof(f318,plain,
    ( $false
    | spl8_1
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | spl8_29 ),
    inference(subsumption_resolution,[],[f317,f106])).

fof(f106,plain,
    ( ~ v2_struct_0(sK0)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl8_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f317,plain,
    ( v2_struct_0(sK0)
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | spl8_29 ),
    inference(subsumption_resolution,[],[f316,f121])).

fof(f121,plain,
    ( v5_orders_2(sK0)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl8_4
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f316,plain,
    ( ~ v5_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_5
    | ~ spl8_6
    | spl8_29 ),
    inference(subsumption_resolution,[],[f315,f126])).

fof(f126,plain,
    ( v1_yellow_0(sK0)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl8_5
  <=> v1_yellow_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f315,plain,
    ( ~ v1_yellow_0(sK0)
    | ~ v5_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_6
    | spl8_29 ),
    inference(subsumption_resolution,[],[f313,f131])).

fof(f313,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v1_yellow_0(sK0)
    | ~ v5_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl8_29 ),
    inference(resolution,[],[f304,f89])).

fof(f89,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( r2_yellow_0(X0,u1_struct_0(X0))
        & r1_yellow_0(X0,k1_xboole_0) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( r2_yellow_0(X0,u1_struct_0(X0))
        & r1_yellow_0(X0,k1_xboole_0) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r2_yellow_0(X0,u1_struct_0(X0))
        & r1_yellow_0(X0,k1_xboole_0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_yellow_0)).

fof(f304,plain,
    ( ~ r1_yellow_0(sK0,k1_xboole_0)
    | spl8_29 ),
    inference(avatar_component_clause,[],[f302])).

fof(f258,plain,
    ( spl8_23
    | spl8_24
    | ~ spl8_19 ),
    inference(avatar_split_clause,[],[f228,f221,f255,f251])).

fof(f251,plain,
    ( spl8_23
  <=> r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).

fof(f255,plain,
    ( spl8_24
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f221,plain,
    ( spl8_19
  <=> m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f228,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0))
    | ~ spl8_19 ),
    inference(resolution,[],[f223,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f223,plain,
    ( m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))
    | ~ spl8_19 ),
    inference(avatar_component_clause,[],[f221])).

fof(f243,plain,
    ( u1_struct_0(sK0) != sK1
    | v1_subset_1(sK1,sK1)
    | ~ v1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f242,plain,
    ( spl8_22
    | ~ spl8_11
    | spl8_15 ),
    inference(avatar_split_clause,[],[f227,f185,f154,f239])).

fof(f227,plain,
    ( m1_subset_1(sK7(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ spl8_11
    | spl8_15 ),
    inference(subsumption_resolution,[],[f226,f186])).

fof(f186,plain,
    ( u1_struct_0(sK0) != sK1
    | spl8_15 ),
    inference(avatar_component_clause,[],[f185])).

fof(f226,plain,
    ( m1_subset_1(sK7(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | u1_struct_0(sK0) = sK1
    | ~ spl8_11 ),
    inference(resolution,[],[f95,f156])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | m1_subset_1(sK7(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f58])).

fof(f224,plain,
    ( spl8_19
    | ~ spl8_6
    | ~ spl8_14 ),
    inference(avatar_split_clause,[],[f179,f172,f129,f221])).

fof(f179,plain,
    ( m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))
    | ~ spl8_6
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f178,f131])).

fof(f178,plain,
    ( m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl8_14 ),
    inference(superposition,[],[f93,f174])).

fof(f188,plain,
    ( spl8_15
    | ~ spl8_11
    | spl8_12 ),
    inference(avatar_split_clause,[],[f181,f160,f154,f185])).

fof(f160,plain,
    ( spl8_12
  <=> v1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f181,plain,
    ( u1_struct_0(sK0) = sK1
    | ~ spl8_11
    | spl8_12 ),
    inference(subsumption_resolution,[],[f180,f161])).

fof(f161,plain,
    ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
    | spl8_12 ),
    inference(avatar_component_clause,[],[f160])).

fof(f180,plain,
    ( u1_struct_0(sK0) = sK1
    | v1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl8_11 ),
    inference(resolution,[],[f98,f156])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f175,plain,
    ( spl8_14
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f170,f129,f172])).

fof(f170,plain,
    ( k3_yellow_0(sK0) = k1_yellow_0(sK0,k1_xboole_0)
    | ~ spl8_6 ),
    inference(resolution,[],[f73,f131])).

fof(f73,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_yellow_0)).

fof(f169,plain,
    ( ~ spl8_12
    | spl8_13 ),
    inference(avatar_split_clause,[],[f168,f164,f160])).

fof(f168,plain,
    ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
    | spl8_13 ),
    inference(subsumption_resolution,[],[f71,f166])).

fof(f166,plain,
    ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
    | spl8_13 ),
    inference(avatar_component_clause,[],[f164])).

fof(f71,plain,
    ( r2_hidden(k3_yellow_0(sK0),sK1)
    | ~ v1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( ( r2_hidden(k3_yellow_0(sK0),sK1)
      | ~ v1_subset_1(sK1,u1_struct_0(sK0)) )
    & ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
      | v1_subset_1(sK1,u1_struct_0(sK0)) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & v13_waybel_0(sK1,sK0)
    & v2_waybel_0(sK1,sK0)
    & ~ v1_xboole_0(sK1)
    & l1_orders_2(sK0)
    & v1_yellow_0(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f35,f37,f36])).

fof(f36,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( r2_hidden(k3_yellow_0(X0),X1)
              | ~ v1_subset_1(X1,u1_struct_0(X0)) )
            & ( ~ r2_hidden(k3_yellow_0(X0),X1)
              | v1_subset_1(X1,u1_struct_0(X0)) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
        & l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( r2_hidden(k3_yellow_0(sK0),X1)
            | ~ v1_subset_1(X1,u1_struct_0(sK0)) )
          & ( ~ r2_hidden(k3_yellow_0(sK0),X1)
            | v1_subset_1(X1,u1_struct_0(sK0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
          & v13_waybel_0(X1,sK0)
          & v2_waybel_0(X1,sK0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(sK0)
      & v1_yellow_0(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X1] :
        ( ( r2_hidden(k3_yellow_0(sK0),X1)
          | ~ v1_subset_1(X1,u1_struct_0(sK0)) )
        & ( ~ r2_hidden(k3_yellow_0(sK0),X1)
          | v1_subset_1(X1,u1_struct_0(sK0)) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        & v13_waybel_0(X1,sK0)
        & v2_waybel_0(X1,sK0)
        & ~ v1_xboole_0(X1) )
   => ( ( r2_hidden(k3_yellow_0(sK0),sK1)
        | ~ v1_subset_1(sK1,u1_struct_0(sK0)) )
      & ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
        | v1_subset_1(sK1,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      & v13_waybel_0(sK1,sK0)
      & v2_waybel_0(sK1,sK0)
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(k3_yellow_0(X0),X1)
            | ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & ( ~ r2_hidden(k3_yellow_0(X0),X1)
            | v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & v2_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(k3_yellow_0(X0),X1)
            | ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & ( ~ r2_hidden(k3_yellow_0(X0),X1)
            | v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & v2_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
          <~> ~ r2_hidden(k3_yellow_0(X0),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & v2_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
          <~> ~ r2_hidden(k3_yellow_0(X0),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & v2_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_yellow_0(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(X1,X0)
              & v2_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ( v1_subset_1(X1,u1_struct_0(X0))
            <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ( v1_subset_1(X1,u1_struct_0(X0))
          <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_waybel_7)).

fof(f167,plain,
    ( spl8_12
    | ~ spl8_13 ),
    inference(avatar_split_clause,[],[f70,f164,f160])).

fof(f70,plain,
    ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
    | v1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f38])).

fof(f157,plain,(
    spl8_11 ),
    inference(avatar_split_clause,[],[f69,f154])).

fof(f69,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f38])).

fof(f152,plain,(
    spl8_10 ),
    inference(avatar_split_clause,[],[f68,f149])).

fof(f68,plain,(
    v13_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f142,plain,(
    spl8_8 ),
    inference(avatar_split_clause,[],[f72,f139])).

fof(f72,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f137,plain,(
    ~ spl8_7 ),
    inference(avatar_split_clause,[],[f66,f134])).

fof(f134,plain,
    ( spl8_7
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f66,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f132,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f65,f129])).

fof(f65,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f127,plain,(
    spl8_5 ),
    inference(avatar_split_clause,[],[f64,f124])).

fof(f64,plain,(
    v1_yellow_0(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f122,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f63,f119])).

fof(f63,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f107,plain,(
    ~ spl8_1 ),
    inference(avatar_split_clause,[],[f60,f104])).

fof(f60,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:49:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (1399)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.48  % (1399)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % (1418)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f545,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(avatar_sat_refutation,[],[f107,f122,f127,f132,f137,f142,f152,f157,f167,f169,f175,f188,f224,f242,f243,f258,f319,f334,f342,f348,f354,f358,f398,f432,f433,f434,f493,f535,f543,f544])).
% 0.20/0.49  fof(f544,plain,(
% 0.20/0.49    u1_struct_0(sK0) != sK1 | m1_subset_1(sK1,k1_zfmisc_1(sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.49  fof(f543,plain,(
% 0.20/0.49    ~spl8_16 | ~spl8_17),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f542])).
% 0.20/0.49  fof(f542,plain,(
% 0.20/0.49    $false | (~spl8_16 | ~spl8_17)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f197,f191,f102])).
% 0.20/0.49  fof(f102,plain,(
% 0.20/0.49    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(X1)) | ~v1_subset_1(X1,X1)) )),
% 0.20/0.49    inference(equality_resolution,[],[f97])).
% 0.20/0.49  fof(f97,plain,(
% 0.20/0.49    ( ! [X0,X1] : (X0 != X1 | ~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f59])).
% 0.20/0.49  fof(f59,plain,(
% 0.20/0.49    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.49    inference(nnf_transformation,[],[f31])).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f12])).
% 0.20/0.49  fof(f12,axiom,(
% 0.20/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).
% 0.20/0.49  fof(f191,plain,(
% 0.20/0.49    v1_subset_1(sK1,sK1) | ~spl8_16),
% 0.20/0.49    inference(avatar_component_clause,[],[f190])).
% 0.20/0.49  fof(f190,plain,(
% 0.20/0.49    spl8_16 <=> v1_subset_1(sK1,sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).
% 0.20/0.49  fof(f197,plain,(
% 0.20/0.49    m1_subset_1(sK1,k1_zfmisc_1(sK1)) | ~spl8_17),
% 0.20/0.49    inference(avatar_component_clause,[],[f195])).
% 0.20/0.49  fof(f195,plain,(
% 0.20/0.49    spl8_17 <=> m1_subset_1(sK1,k1_zfmisc_1(sK1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).
% 0.20/0.49  fof(f535,plain,(
% 0.20/0.49    spl8_15 | ~spl8_11 | ~spl8_50),
% 0.20/0.49    inference(avatar_split_clause,[],[f500,f490,f154,f185])).
% 0.20/0.49  fof(f185,plain,(
% 0.20/0.49    spl8_15 <=> u1_struct_0(sK0) = sK1),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).
% 0.20/0.49  fof(f154,plain,(
% 0.20/0.49    spl8_11 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 0.20/0.49  fof(f490,plain,(
% 0.20/0.49    spl8_50 <=> r2_hidden(sK7(u1_struct_0(sK0),sK1),sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_50])])).
% 0.20/0.49  fof(f500,plain,(
% 0.20/0.49    u1_struct_0(sK0) = sK1 | (~spl8_11 | ~spl8_50)),
% 0.20/0.49    inference(subsumption_resolution,[],[f498,f156])).
% 0.20/0.49  fof(f156,plain,(
% 0.20/0.49    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl8_11),
% 0.20/0.49    inference(avatar_component_clause,[],[f154])).
% 0.20/0.49  fof(f498,plain,(
% 0.20/0.49    u1_struct_0(sK0) = sK1 | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl8_50),
% 0.20/0.49    inference(resolution,[],[f492,f96])).
% 0.20/0.49  fof(f96,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r2_hidden(sK7(X0,X1),X1) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f58])).
% 0.20/0.49  fof(f58,plain,(
% 0.20/0.49    ! [X0,X1] : (X0 = X1 | (~r2_hidden(sK7(X0,X1),X1) & m1_subset_1(sK7(X0,X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f30,f57])).
% 0.20/0.49  fof(f57,plain,(
% 0.20/0.49    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & m1_subset_1(X2,X0)) => (~r2_hidden(sK7(X0,X1),X1) & m1_subset_1(sK7(X0,X1),X0)))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    ! [X0,X1] : (X0 = X1 | ? [X2] : (~r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.49    inference(flattening,[],[f29])).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    ! [X0,X1] : ((X0 = X1 | ? [X2] : (~r2_hidden(X2,X1) & m1_subset_1(X2,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (! [X2] : (m1_subset_1(X2,X0) => r2_hidden(X2,X1)) => X0 = X1))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_subset_1)).
% 0.20/0.49  fof(f492,plain,(
% 0.20/0.49    r2_hidden(sK7(u1_struct_0(sK0),sK1),sK1) | ~spl8_50),
% 0.20/0.49    inference(avatar_component_clause,[],[f490])).
% 0.20/0.49  fof(f493,plain,(
% 0.20/0.49    spl8_50 | ~spl8_22 | ~spl8_43),
% 0.20/0.49    inference(avatar_split_clause,[],[f470,f430,f239,f490])).
% 0.20/0.49  fof(f239,plain,(
% 0.20/0.49    spl8_22 <=> m1_subset_1(sK7(u1_struct_0(sK0),sK1),u1_struct_0(sK0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).
% 0.20/0.49  fof(f430,plain,(
% 0.20/0.49    spl8_43 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,sK1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_43])])).
% 0.20/0.49  fof(f470,plain,(
% 0.20/0.49    r2_hidden(sK7(u1_struct_0(sK0),sK1),sK1) | (~spl8_22 | ~spl8_43)),
% 0.20/0.49    inference(resolution,[],[f431,f241])).
% 0.20/0.49  fof(f241,plain,(
% 0.20/0.49    m1_subset_1(sK7(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~spl8_22),
% 0.20/0.49    inference(avatar_component_clause,[],[f239])).
% 0.20/0.49  fof(f431,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,sK1)) ) | ~spl8_43),
% 0.20/0.49    inference(avatar_component_clause,[],[f430])).
% 0.20/0.49  fof(f434,plain,(
% 0.20/0.49    u1_struct_0(sK0) != sK1 | r2_hidden(k3_yellow_0(sK0),sK1) | ~r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0))),
% 0.20/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.49  fof(f433,plain,(
% 0.20/0.49    u1_struct_0(sK0) != sK1 | v1_xboole_0(sK1) | ~v1_xboole_0(u1_struct_0(sK0))),
% 0.20/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.49  fof(f432,plain,(
% 0.20/0.49    spl8_43 | ~spl8_13 | ~spl8_37 | ~spl8_40),
% 0.20/0.49    inference(avatar_split_clause,[],[f422,f396,f356,f164,f430])).
% 0.20/0.49  fof(f164,plain,(
% 0.20/0.49    spl8_13 <=> r2_hidden(k3_yellow_0(sK0),sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 0.20/0.49  fof(f356,plain,(
% 0.20/0.49    spl8_37 <=> ! [X1,X0] : (~r2_hidden(X0,sK1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,X1) | r2_hidden(X1,sK1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_37])])).
% 0.20/0.49  fof(f396,plain,(
% 0.20/0.49    spl8_40 <=> ! [X0] : (r1_orders_2(sK0,k3_yellow_0(sK0),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_40])])).
% 0.20/0.49  fof(f422,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,sK1)) ) | (~spl8_13 | ~spl8_37 | ~spl8_40)),
% 0.20/0.49    inference(subsumption_resolution,[],[f421,f165])).
% 0.20/0.49  fof(f165,plain,(
% 0.20/0.49    r2_hidden(k3_yellow_0(sK0),sK1) | ~spl8_13),
% 0.20/0.49    inference(avatar_component_clause,[],[f164])).
% 0.20/0.49  fof(f421,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(k3_yellow_0(sK0),sK1) | r2_hidden(X0,sK1)) ) | (~spl8_37 | ~spl8_40)),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f419])).
% 0.20/0.49  fof(f419,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(k3_yellow_0(sK0),sK1) | r2_hidden(X0,sK1)) ) | (~spl8_37 | ~spl8_40)),
% 0.20/0.49    inference(resolution,[],[f397,f357])).
% 0.20/0.49  fof(f357,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r1_orders_2(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X0,sK1) | r2_hidden(X1,sK1)) ) | ~spl8_37),
% 0.20/0.49    inference(avatar_component_clause,[],[f356])).
% 0.20/0.49  fof(f397,plain,(
% 0.20/0.49    ( ! [X0] : (r1_orders_2(sK0,k3_yellow_0(sK0),X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl8_40),
% 0.20/0.49    inference(avatar_component_clause,[],[f396])).
% 0.20/0.49  fof(f398,plain,(
% 0.20/0.49    spl8_40 | ~spl8_6 | ~spl8_14 | ~spl8_29 | ~spl8_36),
% 0.20/0.49    inference(avatar_split_clause,[],[f369,f352,f302,f172,f129,f396])).
% 0.20/0.49  fof(f129,plain,(
% 0.20/0.49    spl8_6 <=> l1_orders_2(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.20/0.49  fof(f172,plain,(
% 0.20/0.49    spl8_14 <=> k3_yellow_0(sK0) = k1_yellow_0(sK0,k1_xboole_0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 0.20/0.49  fof(f302,plain,(
% 0.20/0.49    spl8_29 <=> r1_yellow_0(sK0,k1_xboole_0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).
% 0.20/0.49  fof(f352,plain,(
% 0.20/0.49    spl8_36 <=> ! [X0] : (r2_lattice3(sK0,k1_xboole_0,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_36])])).
% 0.20/0.49  fof(f369,plain,(
% 0.20/0.49    ( ! [X0] : (r1_orders_2(sK0,k3_yellow_0(sK0),X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl8_6 | ~spl8_14 | ~spl8_29 | ~spl8_36)),
% 0.20/0.49    inference(forward_demodulation,[],[f368,f174])).
% 0.20/0.49  fof(f174,plain,(
% 0.20/0.49    k3_yellow_0(sK0) = k1_yellow_0(sK0,k1_xboole_0) | ~spl8_14),
% 0.20/0.49    inference(avatar_component_clause,[],[f172])).
% 0.20/0.49  fof(f368,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,k1_yellow_0(sK0,k1_xboole_0),X0)) ) | (~spl8_6 | ~spl8_29 | ~spl8_36)),
% 0.20/0.49    inference(subsumption_resolution,[],[f367,f131])).
% 0.20/0.49  fof(f131,plain,(
% 0.20/0.49    l1_orders_2(sK0) | ~spl8_6),
% 0.20/0.49    inference(avatar_component_clause,[],[f129])).
% 0.20/0.49  fof(f367,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,k1_yellow_0(sK0,k1_xboole_0),X0) | ~l1_orders_2(sK0)) ) | (~spl8_29 | ~spl8_36)),
% 0.20/0.49    inference(subsumption_resolution,[],[f366,f303])).
% 0.20/0.49  fof(f303,plain,(
% 0.20/0.49    r1_yellow_0(sK0,k1_xboole_0) | ~spl8_29),
% 0.20/0.49    inference(avatar_component_clause,[],[f302])).
% 0.20/0.49  fof(f366,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,k1_yellow_0(sK0,k1_xboole_0),X0) | ~r1_yellow_0(sK0,k1_xboole_0) | ~l1_orders_2(sK0)) ) | ~spl8_36),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f359])).
% 0.20/0.49  fof(f359,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,k1_yellow_0(sK0,k1_xboole_0),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_yellow_0(sK0,k1_xboole_0) | ~l1_orders_2(sK0)) ) | ~spl8_36),
% 0.20/0.49    inference(resolution,[],[f353,f274])).
% 0.20/0.49  fof(f274,plain,(
% 0.20/0.49    ( ! [X4,X0,X1] : (~r2_lattice3(X0,X1,X4) | r1_orders_2(X0,k1_yellow_0(X0,X1),X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r1_yellow_0(X0,X1) | ~l1_orders_2(X0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f100,f93])).
% 0.20/0.49  fof(f93,plain,(
% 0.20/0.49    ( ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f26])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f9])).
% 0.20/0.49  fof(f9,axiom,(
% 0.20/0.49    ! [X0,X1] : (l1_orders_2(X0) => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_0)).
% 0.20/0.49  fof(f100,plain,(
% 0.20/0.49    ( ! [X4,X0,X1] : (r1_orders_2(X0,k1_yellow_0(X0,X1),X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.20/0.49    inference(equality_resolution,[],[f81])).
% 0.20/0.49  fof(f81,plain,(
% 0.20/0.49    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X2,X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | k1_yellow_0(X0,X1) != X2 | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f48])).
% 0.20/0.49  fof(f48,plain,(
% 0.20/0.49    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | (~r1_orders_2(X0,X2,sK4(X0,X1,X2)) & r2_lattice3(X0,X1,sK4(X0,X1,X2)) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f46,f47])).
% 0.20/0.49  fof(f47,plain,(
% 0.20/0.49    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X2,sK4(X0,X1,X2)) & r2_lattice3(X0,X1,sK4(X0,X1,X2)) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f46,plain,(
% 0.20/0.49    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.20/0.49    inference(rectify,[],[f45])).
% 0.20/0.49  fof(f45,plain,(
% 0.20/0.49    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.20/0.49    inference(flattening,[],[f44])).
% 0.20/0.49  fof(f44,plain,(
% 0.20/0.49    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) & ((! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.20/0.49    inference(nnf_transformation,[],[f21])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ! [X0] : (! [X1,X2] : ((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.20/0.49    inference(flattening,[],[f20])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f8])).
% 0.20/0.49  fof(f8,axiom,(
% 0.20/0.49    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_yellow_0(X0,X1) => (k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X3) => r1_orders_2(X0,X2,X3))) & r2_lattice3(X0,X1,X2))))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_yellow_0)).
% 0.20/0.49  fof(f353,plain,(
% 0.20/0.49    ( ! [X0] : (r2_lattice3(sK0,k1_xboole_0,X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl8_36),
% 0.20/0.49    inference(avatar_component_clause,[],[f352])).
% 0.20/0.49  fof(f358,plain,(
% 0.20/0.49    spl8_37 | ~spl8_10 | ~spl8_11 | ~spl8_34),
% 0.20/0.49    inference(avatar_split_clause,[],[f344,f340,f154,f149,f356])).
% 0.20/0.49  fof(f149,plain,(
% 0.20/0.49    spl8_10 <=> v13_waybel_0(sK1,sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 0.20/0.49  fof(f340,plain,(
% 0.20/0.49    spl8_34 <=> ! [X1,X0,X2] : (~r1_orders_2(sK0,X0,X1) | ~r2_hidden(X0,X2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v13_waybel_0(X2,sK0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X1,X2))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_34])])).
% 0.20/0.49  fof(f344,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r2_hidden(X0,sK1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,X1) | r2_hidden(X1,sK1)) ) | (~spl8_10 | ~spl8_11 | ~spl8_34)),
% 0.20/0.49    inference(subsumption_resolution,[],[f343,f156])).
% 0.20/0.49  fof(f343,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r2_hidden(X0,sK1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,X1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X1,sK1)) ) | (~spl8_10 | ~spl8_34)),
% 0.20/0.49    inference(resolution,[],[f341,f151])).
% 0.20/0.49  fof(f151,plain,(
% 0.20/0.49    v13_waybel_0(sK1,sK0) | ~spl8_10),
% 0.20/0.49    inference(avatar_component_clause,[],[f149])).
% 0.20/0.49  fof(f341,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~v13_waybel_0(X2,sK0) | ~r2_hidden(X0,X2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X1,X2)) ) | ~spl8_34),
% 0.20/0.49    inference(avatar_component_clause,[],[f340])).
% 0.20/0.49  fof(f354,plain,(
% 0.20/0.49    spl8_36 | ~spl8_8 | ~spl8_35),
% 0.20/0.49    inference(avatar_split_clause,[],[f349,f346,f139,f352])).
% 0.20/0.49  fof(f139,plain,(
% 0.20/0.49    spl8_8 <=> v1_xboole_0(k1_xboole_0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.20/0.49  fof(f346,plain,(
% 0.20/0.49    spl8_35 <=> ! [X1,X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r2_lattice3(sK0,X1,X0) | ~v1_xboole_0(X1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_35])])).
% 0.20/0.49  fof(f349,plain,(
% 0.20/0.49    ( ! [X0] : (r2_lattice3(sK0,k1_xboole_0,X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl8_8 | ~spl8_35)),
% 0.20/0.49    inference(resolution,[],[f347,f141])).
% 0.20/0.49  fof(f141,plain,(
% 0.20/0.49    v1_xboole_0(k1_xboole_0) | ~spl8_8),
% 0.20/0.49    inference(avatar_component_clause,[],[f139])).
% 0.20/0.49  fof(f347,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v1_xboole_0(X1) | r2_lattice3(sK0,X1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl8_35),
% 0.20/0.49    inference(avatar_component_clause,[],[f346])).
% 0.20/0.49  fof(f348,plain,(
% 0.20/0.49    spl8_35 | ~spl8_33),
% 0.20/0.49    inference(avatar_split_clause,[],[f335,f332,f346])).
% 0.20/0.49  fof(f332,plain,(
% 0.20/0.49    spl8_33 <=> ! [X1,X0] : (r2_hidden(sK5(sK0,X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_lattice3(sK0,X0,X1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_33])])).
% 0.20/0.49  fof(f335,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r2_lattice3(sK0,X1,X0) | ~v1_xboole_0(X1)) ) | ~spl8_33),
% 0.20/0.49    inference(resolution,[],[f333,f91])).
% 0.20/0.49  fof(f91,plain,(
% 0.20/0.49    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f56])).
% 0.20/0.49  fof(f56,plain,(
% 0.20/0.49    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK6(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f54,f55])).
% 0.20/0.49  fof(f55,plain,(
% 0.20/0.49    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK6(X0),X0))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f54,plain,(
% 0.20/0.49    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.49    inference(rectify,[],[f53])).
% 0.20/0.49  fof(f53,plain,(
% 0.20/0.49    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.49    inference(nnf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.49  fof(f333,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r2_hidden(sK5(sK0,X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_lattice3(sK0,X0,X1)) ) | ~spl8_33),
% 0.20/0.49    inference(avatar_component_clause,[],[f332])).
% 0.20/0.49  fof(f342,plain,(
% 0.20/0.49    spl8_34 | ~spl8_6),
% 0.20/0.49    inference(avatar_split_clause,[],[f291,f129,f340])).
% 0.20/0.49  fof(f291,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~r1_orders_2(sK0,X0,X1) | ~r2_hidden(X0,X2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v13_waybel_0(X2,sK0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X1,X2)) ) | ~spl8_6),
% 0.20/0.49    inference(resolution,[],[f285,f131])).
% 0.20/0.49  fof(f285,plain,(
% 0.20/0.49    ( ! [X4,X0,X5,X1] : (~l1_orders_2(X0) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~v13_waybel_0(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(X5,X1)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f74,f99])).
% 0.20/0.49  fof(f99,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f33])).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.20/0.49    inference(flattening,[],[f32])).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.20/0.49    inference(ennf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 0.20/0.49  fof(f74,plain,(
% 0.20/0.49    ( ! [X4,X0,X5,X1] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v13_waybel_0(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f43])).
% 0.20/0.49  fof(f43,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ((~r2_hidden(sK3(X0,X1),X1) & r1_orders_2(X0,sK2(X0,X1),sK3(X0,X1)) & r2_hidden(sK2(X0,X1),X1) & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f40,f42,f41])).
% 0.20/0.49  fof(f41,plain,(
% 0.20/0.49    ! [X1,X0] : (? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,sK2(X0,X1),X3) & r2_hidden(sK2(X0,X1),X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f42,plain,(
% 0.20/0.49    ! [X1,X0] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,sK2(X0,X1),X3) & r2_hidden(sK2(X0,X1),X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r2_hidden(sK3(X0,X1),X1) & r1_orders_2(X0,sK2(X0,X1),sK3(X0,X1)) & r2_hidden(sK2(X0,X1),X1) & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f40,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.20/0.49    inference(rectify,[],[f39])).
% 0.20/0.49  fof(f39,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.20/0.49    inference(nnf_transformation,[],[f19])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.20/0.49    inference(flattening,[],[f18])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : ((r2_hidden(X3,X1) | (~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f11])).
% 0.20/0.49  fof(f11,axiom,(
% 0.20/0.49    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v13_waybel_0(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1)) => r2_hidden(X3,X1)))))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_waybel_0)).
% 0.20/0.49  fof(f334,plain,(
% 0.20/0.49    spl8_33 | ~spl8_6),
% 0.20/0.49    inference(avatar_split_clause,[],[f248,f129,f332])).
% 0.20/0.49  fof(f248,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r2_hidden(sK5(sK0,X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_lattice3(sK0,X0,X1)) ) | ~spl8_6),
% 0.20/0.49    inference(resolution,[],[f87,f131])).
% 0.20/0.49  fof(f87,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | r2_hidden(sK5(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | r2_lattice3(X0,X1,X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f52])).
% 0.20/0.49  fof(f52,plain,(
% 0.20/0.49    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | (~r1_orders_2(X0,sK5(X0,X1,X2),X2) & r2_hidden(sK5(X0,X1,X2),X1) & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f50,f51])).
% 0.20/0.49  fof(f51,plain,(
% 0.20/0.49    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,sK5(X0,X1,X2),X2) & r2_hidden(sK5(X0,X1,X2),X1) & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f50,plain,(
% 0.20/0.49    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.20/0.49    inference(rectify,[],[f49])).
% 0.20/0.49  fof(f49,plain,(
% 0.20/0.49    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.20/0.49    inference(nnf_transformation,[],[f23])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.20/0.49    inference(flattening,[],[f22])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,axiom,(
% 0.20/0.49    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X3,X2))))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattice3)).
% 0.20/0.49  fof(f319,plain,(
% 0.20/0.49    spl8_1 | ~spl8_4 | ~spl8_5 | ~spl8_6 | spl8_29),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f318])).
% 0.20/0.49  fof(f318,plain,(
% 0.20/0.49    $false | (spl8_1 | ~spl8_4 | ~spl8_5 | ~spl8_6 | spl8_29)),
% 0.20/0.49    inference(subsumption_resolution,[],[f317,f106])).
% 0.20/0.49  fof(f106,plain,(
% 0.20/0.49    ~v2_struct_0(sK0) | spl8_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f104])).
% 0.20/0.49  fof(f104,plain,(
% 0.20/0.49    spl8_1 <=> v2_struct_0(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.20/0.49  fof(f317,plain,(
% 0.20/0.49    v2_struct_0(sK0) | (~spl8_4 | ~spl8_5 | ~spl8_6 | spl8_29)),
% 0.20/0.49    inference(subsumption_resolution,[],[f316,f121])).
% 0.20/0.49  fof(f121,plain,(
% 0.20/0.49    v5_orders_2(sK0) | ~spl8_4),
% 0.20/0.49    inference(avatar_component_clause,[],[f119])).
% 0.20/0.49  fof(f119,plain,(
% 0.20/0.49    spl8_4 <=> v5_orders_2(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.20/0.49  fof(f316,plain,(
% 0.20/0.49    ~v5_orders_2(sK0) | v2_struct_0(sK0) | (~spl8_5 | ~spl8_6 | spl8_29)),
% 0.20/0.49    inference(subsumption_resolution,[],[f315,f126])).
% 0.20/0.49  fof(f126,plain,(
% 0.20/0.49    v1_yellow_0(sK0) | ~spl8_5),
% 0.20/0.49    inference(avatar_component_clause,[],[f124])).
% 0.20/0.49  fof(f124,plain,(
% 0.20/0.49    spl8_5 <=> v1_yellow_0(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.20/0.49  fof(f315,plain,(
% 0.20/0.49    ~v1_yellow_0(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | (~spl8_6 | spl8_29)),
% 0.20/0.49    inference(subsumption_resolution,[],[f313,f131])).
% 0.20/0.49  fof(f313,plain,(
% 0.20/0.49    ~l1_orders_2(sK0) | ~v1_yellow_0(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | spl8_29),
% 0.20/0.49    inference(resolution,[],[f304,f89])).
% 0.20/0.49  fof(f89,plain,(
% 0.20/0.49    ( ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f25])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    ! [X0] : ((r2_yellow_0(X0,u1_struct_0(X0)) & r1_yellow_0(X0,k1_xboole_0)) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f24])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    ! [X0] : ((r2_yellow_0(X0,u1_struct_0(X0)) & r1_yellow_0(X0,k1_xboole_0)) | (~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f10])).
% 0.20/0.49  fof(f10,axiom,(
% 0.20/0.49    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => (r2_yellow_0(X0,u1_struct_0(X0)) & r1_yellow_0(X0,k1_xboole_0)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_yellow_0)).
% 0.20/0.49  fof(f304,plain,(
% 0.20/0.49    ~r1_yellow_0(sK0,k1_xboole_0) | spl8_29),
% 0.20/0.49    inference(avatar_component_clause,[],[f302])).
% 0.20/0.49  fof(f258,plain,(
% 0.20/0.49    spl8_23 | spl8_24 | ~spl8_19),
% 0.20/0.49    inference(avatar_split_clause,[],[f228,f221,f255,f251])).
% 0.20/0.49  fof(f251,plain,(
% 0.20/0.49    spl8_23 <=> r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).
% 0.20/0.49  fof(f255,plain,(
% 0.20/0.49    spl8_24 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).
% 0.20/0.49  fof(f221,plain,(
% 0.20/0.49    spl8_19 <=> m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).
% 0.20/0.49  fof(f228,plain,(
% 0.20/0.49    v1_xboole_0(u1_struct_0(sK0)) | r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0)) | ~spl8_19),
% 0.20/0.49    inference(resolution,[],[f223,f94])).
% 0.20/0.49  fof(f94,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f28])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.20/0.49    inference(flattening,[],[f27])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.20/0.49  fof(f223,plain,(
% 0.20/0.49    m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) | ~spl8_19),
% 0.20/0.49    inference(avatar_component_clause,[],[f221])).
% 0.20/0.49  fof(f243,plain,(
% 0.20/0.49    u1_struct_0(sK0) != sK1 | v1_subset_1(sK1,sK1) | ~v1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.49  fof(f242,plain,(
% 0.20/0.49    spl8_22 | ~spl8_11 | spl8_15),
% 0.20/0.49    inference(avatar_split_clause,[],[f227,f185,f154,f239])).
% 0.20/0.49  fof(f227,plain,(
% 0.20/0.49    m1_subset_1(sK7(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | (~spl8_11 | spl8_15)),
% 0.20/0.49    inference(subsumption_resolution,[],[f226,f186])).
% 0.20/0.49  fof(f186,plain,(
% 0.20/0.49    u1_struct_0(sK0) != sK1 | spl8_15),
% 0.20/0.49    inference(avatar_component_clause,[],[f185])).
% 0.20/0.49  fof(f226,plain,(
% 0.20/0.49    m1_subset_1(sK7(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | u1_struct_0(sK0) = sK1 | ~spl8_11),
% 0.20/0.49    inference(resolution,[],[f95,f156])).
% 0.20/0.49  fof(f95,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | m1_subset_1(sK7(X0,X1),X0) | X0 = X1) )),
% 0.20/0.49    inference(cnf_transformation,[],[f58])).
% 0.20/0.49  fof(f224,plain,(
% 0.20/0.49    spl8_19 | ~spl8_6 | ~spl8_14),
% 0.20/0.49    inference(avatar_split_clause,[],[f179,f172,f129,f221])).
% 0.20/0.49  fof(f179,plain,(
% 0.20/0.49    m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) | (~spl8_6 | ~spl8_14)),
% 0.20/0.49    inference(subsumption_resolution,[],[f178,f131])).
% 0.20/0.49  fof(f178,plain,(
% 0.20/0.49    m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~spl8_14),
% 0.20/0.49    inference(superposition,[],[f93,f174])).
% 0.20/0.49  fof(f188,plain,(
% 0.20/0.49    spl8_15 | ~spl8_11 | spl8_12),
% 0.20/0.49    inference(avatar_split_clause,[],[f181,f160,f154,f185])).
% 0.20/0.49  fof(f160,plain,(
% 0.20/0.49    spl8_12 <=> v1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 0.20/0.49  fof(f181,plain,(
% 0.20/0.49    u1_struct_0(sK0) = sK1 | (~spl8_11 | spl8_12)),
% 0.20/0.49    inference(subsumption_resolution,[],[f180,f161])).
% 0.20/0.49  fof(f161,plain,(
% 0.20/0.49    ~v1_subset_1(sK1,u1_struct_0(sK0)) | spl8_12),
% 0.20/0.49    inference(avatar_component_clause,[],[f160])).
% 0.20/0.49  fof(f180,plain,(
% 0.20/0.49    u1_struct_0(sK0) = sK1 | v1_subset_1(sK1,u1_struct_0(sK0)) | ~spl8_11),
% 0.20/0.49    inference(resolution,[],[f98,f156])).
% 0.20/0.49  fof(f98,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f59])).
% 0.20/0.49  fof(f175,plain,(
% 0.20/0.49    spl8_14 | ~spl8_6),
% 0.20/0.49    inference(avatar_split_clause,[],[f170,f129,f172])).
% 0.20/0.49  fof(f170,plain,(
% 0.20/0.49    k3_yellow_0(sK0) = k1_yellow_0(sK0,k1_xboole_0) | ~spl8_6),
% 0.20/0.49    inference(resolution,[],[f73,f131])).
% 0.20/0.49  fof(f73,plain,(
% 0.20/0.49    ( ! [X0] : (~l1_orders_2(X0) | k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f17])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f7])).
% 0.20/0.49  fof(f7,axiom,(
% 0.20/0.49    ! [X0] : (l1_orders_2(X0) => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_yellow_0)).
% 0.20/0.49  fof(f169,plain,(
% 0.20/0.49    ~spl8_12 | spl8_13),
% 0.20/0.49    inference(avatar_split_clause,[],[f168,f164,f160])).
% 0.20/0.49  fof(f168,plain,(
% 0.20/0.49    ~v1_subset_1(sK1,u1_struct_0(sK0)) | spl8_13),
% 0.20/0.49    inference(subsumption_resolution,[],[f71,f166])).
% 0.20/0.49  fof(f166,plain,(
% 0.20/0.49    ~r2_hidden(k3_yellow_0(sK0),sK1) | spl8_13),
% 0.20/0.49    inference(avatar_component_clause,[],[f164])).
% 0.20/0.49  fof(f71,plain,(
% 0.20/0.49    r2_hidden(k3_yellow_0(sK0),sK1) | ~v1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.49    inference(cnf_transformation,[],[f38])).
% 0.20/0.49  fof(f38,plain,(
% 0.20/0.49    ((r2_hidden(k3_yellow_0(sK0),sK1) | ~v1_subset_1(sK1,u1_struct_0(sK0))) & (~r2_hidden(k3_yellow_0(sK0),sK1) | v1_subset_1(sK1,u1_struct_0(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & v13_waybel_0(sK1,sK0) & v2_waybel_0(sK1,sK0) & ~v1_xboole_0(sK1)) & l1_orders_2(sK0) & v1_yellow_0(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0)),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f35,f37,f36])).
% 0.20/0.49  fof(f36,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : ((r2_hidden(k3_yellow_0(sK0),X1) | ~v1_subset_1(X1,u1_struct_0(sK0))) & (~r2_hidden(k3_yellow_0(sK0),X1) | v1_subset_1(X1,u1_struct_0(sK0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & v13_waybel_0(X1,sK0) & v2_waybel_0(X1,sK0) & ~v1_xboole_0(X1)) & l1_orders_2(sK0) & v1_yellow_0(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f37,plain,(
% 0.20/0.49    ? [X1] : ((r2_hidden(k3_yellow_0(sK0),X1) | ~v1_subset_1(X1,u1_struct_0(sK0))) & (~r2_hidden(k3_yellow_0(sK0),X1) | v1_subset_1(X1,u1_struct_0(sK0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & v13_waybel_0(X1,sK0) & v2_waybel_0(X1,sK0) & ~v1_xboole_0(X1)) => ((r2_hidden(k3_yellow_0(sK0),sK1) | ~v1_subset_1(sK1,u1_struct_0(sK0))) & (~r2_hidden(k3_yellow_0(sK0),sK1) | v1_subset_1(sK1,u1_struct_0(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & v13_waybel_0(sK1,sK0) & v2_waybel_0(sK1,sK0) & ~v1_xboole_0(sK1))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f34])).
% 0.20/0.49  fof(f34,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.20/0.49    inference(nnf_transformation,[],[f16])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f15])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1))) & (l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f14])).
% 0.20/0.49  fof(f14,negated_conjecture,(
% 0.20/0.49    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 0.20/0.49    inference(negated_conjecture,[],[f13])).
% 0.20/0.49  fof(f13,conjecture,(
% 0.20/0.49    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_waybel_7)).
% 0.20/0.49  fof(f167,plain,(
% 0.20/0.49    spl8_12 | ~spl8_13),
% 0.20/0.49    inference(avatar_split_clause,[],[f70,f164,f160])).
% 0.20/0.49  fof(f70,plain,(
% 0.20/0.49    ~r2_hidden(k3_yellow_0(sK0),sK1) | v1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.49    inference(cnf_transformation,[],[f38])).
% 0.20/0.49  fof(f157,plain,(
% 0.20/0.49    spl8_11),
% 0.20/0.49    inference(avatar_split_clause,[],[f69,f154])).
% 0.20/0.49  fof(f69,plain,(
% 0.20/0.49    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.49    inference(cnf_transformation,[],[f38])).
% 0.20/0.49  fof(f152,plain,(
% 0.20/0.49    spl8_10),
% 0.20/0.49    inference(avatar_split_clause,[],[f68,f149])).
% 0.20/0.49  fof(f68,plain,(
% 0.20/0.49    v13_waybel_0(sK1,sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f38])).
% 0.20/0.49  fof(f142,plain,(
% 0.20/0.49    spl8_8),
% 0.20/0.49    inference(avatar_split_clause,[],[f72,f139])).
% 0.20/0.49  fof(f72,plain,(
% 0.20/0.49    v1_xboole_0(k1_xboole_0)),
% 0.20/0.49    inference(cnf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    v1_xboole_0(k1_xboole_0)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.49  fof(f137,plain,(
% 0.20/0.49    ~spl8_7),
% 0.20/0.49    inference(avatar_split_clause,[],[f66,f134])).
% 0.20/0.49  fof(f134,plain,(
% 0.20/0.49    spl8_7 <=> v1_xboole_0(sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.20/0.49  fof(f66,plain,(
% 0.20/0.49    ~v1_xboole_0(sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f38])).
% 0.20/0.49  fof(f132,plain,(
% 0.20/0.49    spl8_6),
% 0.20/0.49    inference(avatar_split_clause,[],[f65,f129])).
% 0.20/0.49  fof(f65,plain,(
% 0.20/0.49    l1_orders_2(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f38])).
% 0.20/0.49  fof(f127,plain,(
% 0.20/0.49    spl8_5),
% 0.20/0.49    inference(avatar_split_clause,[],[f64,f124])).
% 0.20/0.49  fof(f64,plain,(
% 0.20/0.49    v1_yellow_0(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f38])).
% 0.20/0.49  fof(f122,plain,(
% 0.20/0.49    spl8_4),
% 0.20/0.49    inference(avatar_split_clause,[],[f63,f119])).
% 0.20/0.49  fof(f63,plain,(
% 0.20/0.49    v5_orders_2(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f38])).
% 0.20/0.49  fof(f107,plain,(
% 0.20/0.49    ~spl8_1),
% 0.20/0.49    inference(avatar_split_clause,[],[f60,f104])).
% 0.20/0.49  fof(f60,plain,(
% 0.20/0.49    ~v2_struct_0(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f38])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (1399)------------------------------
% 0.20/0.49  % (1399)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (1399)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (1399)Memory used [KB]: 6524
% 0.20/0.49  % (1399)Time elapsed: 0.068 s
% 0.20/0.49  % (1399)------------------------------
% 0.20/0.49  % (1399)------------------------------
% 0.20/0.50  % (1393)Success in time 0.137 s
%------------------------------------------------------------------------------
