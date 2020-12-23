%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tops_2__t23_tops_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:37 EDT 2019

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 213 expanded)
%              Number of leaves         :   19 (  81 expanded)
%              Depth                    :   13
%              Number of atoms          :  349 ( 707 expanded)
%              Number of equality atoms :   17 (  32 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f348,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f93,f97,f101,f105,f109,f135,f163,f177,f211,f245,f272,f295,f327,f346])).

fof(f346,plain,
    ( ~ spl8_0
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | spl8_37
    | ~ spl8_42
    | ~ spl8_54 ),
    inference(avatar_contradiction_clause,[],[f345])).

fof(f345,plain,
    ( $false
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_37
    | ~ spl8_42
    | ~ spl8_54 ),
    inference(subsumption_resolution,[],[f344,f244])).

fof(f244,plain,
    ( ~ v4_pre_topc(sK3(sK0,k2_xboole_0(sK1,sK2)),sK0)
    | ~ spl8_37 ),
    inference(avatar_component_clause,[],[f243])).

fof(f243,plain,
    ( spl8_37
  <=> ~ v4_pre_topc(sK3(sK0,k2_xboole_0(sK1,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_37])])).

fof(f344,plain,
    ( v4_pre_topc(sK3(sK0,k2_xboole_0(sK1,sK2)),sK0)
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_37
    | ~ spl8_42
    | ~ spl8_54 ),
    inference(subsumption_resolution,[],[f336,f343])).

fof(f343,plain,
    ( r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK2)
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_8
    | ~ spl8_37
    | ~ spl8_42
    | ~ spl8_54 ),
    inference(subsumption_resolution,[],[f333,f342])).

fof(f342,plain,
    ( ~ r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK1)
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_8
    | ~ spl8_37
    | ~ spl8_42 ),
    inference(subsumption_resolution,[],[f335,f244])).

fof(f335,plain,
    ( ~ r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK1)
    | v4_pre_topc(sK3(sK0,k2_xboole_0(sK1,sK2)),sK0)
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_8
    | ~ spl8_42 ),
    inference(resolution,[],[f294,f131])).

fof(f131,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,sK1)
        | v4_pre_topc(X0,sK0) )
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f130,f96])).

fof(f96,plain,
    ( v2_tops_2(sK1,sK0)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl8_2
  <=> v2_tops_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f130,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,sK1)
        | v4_pre_topc(X0,sK0)
        | ~ v2_tops_2(sK1,sK0) )
    | ~ spl8_0
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f121,f92])).

fof(f92,plain,
    ( l1_pre_topc(sK0)
    | ~ spl8_0 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl8_0
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_0])])).

fof(f121,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,sK1)
        | v4_pre_topc(X0,sK0)
        | ~ v2_tops_2(sK1,sK0) )
    | ~ spl8_8 ),
    inference(resolution,[],[f108,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X2,X1)
      | v4_pre_topc(X2,X0)
      | ~ v2_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_2(X1,X0)
          <=> ! [X2] :
                ( v4_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_2(X1,X0)
          <=> ! [X2] :
                ( v4_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v2_tops_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r2_hidden(X2,X1)
                 => v4_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t23_tops_2.p',d2_tops_2)).

fof(f108,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl8_8
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f294,plain,
    ( m1_subset_1(sK3(sK0,k2_xboole_0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_42 ),
    inference(avatar_component_clause,[],[f293])).

fof(f293,plain,
    ( spl8_42
  <=> m1_subset_1(sK3(sK0,k2_xboole_0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_42])])).

fof(f333,plain,
    ( r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK2)
    | r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK1)
    | ~ spl8_54 ),
    inference(resolution,[],[f326,f76])).

fof(f76,plain,(
    ! [X0,X3,X1] :
      ( ~ sP7(X3,X1,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t23_tops_2.p',d3_xboole_0)).

fof(f326,plain,
    ( sP7(sK3(sK0,k2_xboole_0(sK1,sK2)),sK2,sK1)
    | ~ spl8_54 ),
    inference(avatar_component_clause,[],[f325])).

fof(f325,plain,
    ( spl8_54
  <=> sP7(sK3(sK0,k2_xboole_0(sK1,sK2)),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_54])])).

fof(f336,plain,
    ( ~ r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK2)
    | v4_pre_topc(sK3(sK0,k2_xboole_0(sK1,sK2)),sK0)
    | ~ spl8_0
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_42 ),
    inference(resolution,[],[f294,f120])).

fof(f120,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,sK2)
        | v4_pre_topc(X0,sK0) )
    | ~ spl8_0
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f119,f100])).

fof(f100,plain,
    ( v2_tops_2(sK2,sK0)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl8_4
  <=> v2_tops_2(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f119,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,sK2)
        | v4_pre_topc(X0,sK0)
        | ~ v2_tops_2(sK2,sK0) )
    | ~ spl8_0
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f110,f92])).

fof(f110,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,sK2)
        | v4_pre_topc(X0,sK0)
        | ~ v2_tops_2(sK2,sK0) )
    | ~ spl8_6 ),
    inference(resolution,[],[f104,f65])).

fof(f104,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl8_6
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f327,plain,
    ( spl8_54
    | ~ spl8_40 ),
    inference(avatar_split_clause,[],[f300,f270,f325])).

fof(f270,plain,
    ( spl8_40
  <=> r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_40])])).

fof(f300,plain,
    ( sP7(sK3(sK0,k2_xboole_0(sK1,sK2)),sK2,sK1)
    | ~ spl8_40 ),
    inference(resolution,[],[f271,f87])).

fof(f87,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k2_xboole_0(X0,X1))
      | sP7(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( sP7(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f271,plain,
    ( r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,sK2))
    | ~ spl8_40 ),
    inference(avatar_component_clause,[],[f270])).

fof(f295,plain,
    ( spl8_42
    | ~ spl8_0
    | spl8_11
    | ~ spl8_22
    | ~ spl8_24 ),
    inference(avatar_split_clause,[],[f222,f209,f175,f133,f91,f293])).

fof(f133,plain,
    ( spl8_11
  <=> ~ v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f175,plain,
    ( spl8_22
  <=> m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f209,plain,
    ( spl8_24
  <=> k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2) = k2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f222,plain,
    ( m1_subset_1(sK3(sK0,k2_xboole_0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_0
    | ~ spl8_11
    | ~ spl8_22
    | ~ spl8_24 ),
    inference(subsumption_resolution,[],[f198,f219])).

fof(f219,plain,
    ( ~ v2_tops_2(k2_xboole_0(sK1,sK2),sK0)
    | ~ spl8_11
    | ~ spl8_24 ),
    inference(superposition,[],[f134,f210])).

fof(f210,plain,
    ( k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2) = k2_xboole_0(sK1,sK2)
    | ~ spl8_24 ),
    inference(avatar_component_clause,[],[f209])).

fof(f134,plain,
    ( ~ v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f133])).

fof(f198,plain,
    ( m1_subset_1(sK3(sK0,k2_xboole_0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_tops_2(k2_xboole_0(sK1,sK2),sK0)
    | ~ spl8_0
    | ~ spl8_22 ),
    inference(subsumption_resolution,[],[f189,f92])).

fof(f189,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_subset_1(sK3(sK0,k2_xboole_0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_tops_2(k2_xboole_0(sK1,sK2),sK0)
    | ~ spl8_22 ),
    inference(resolution,[],[f176,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f176,plain,
    ( m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl8_22 ),
    inference(avatar_component_clause,[],[f175])).

fof(f272,plain,
    ( spl8_40
    | ~ spl8_0
    | spl8_11
    | ~ spl8_22
    | ~ spl8_24 ),
    inference(avatar_split_clause,[],[f221,f209,f175,f133,f91,f270])).

fof(f221,plain,
    ( r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,sK2))
    | ~ spl8_0
    | ~ spl8_11
    | ~ spl8_22
    | ~ spl8_24 ),
    inference(subsumption_resolution,[],[f199,f219])).

fof(f199,plain,
    ( r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,sK2))
    | v2_tops_2(k2_xboole_0(sK1,sK2),sK0)
    | ~ spl8_0
    | ~ spl8_22 ),
    inference(subsumption_resolution,[],[f190,f92])).

fof(f190,plain,
    ( ~ l1_pre_topc(sK0)
    | r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,sK2))
    | v2_tops_2(k2_xboole_0(sK1,sK2),sK0)
    | ~ spl8_22 ),
    inference(resolution,[],[f176,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | r2_hidden(sK3(X0,X1),X1)
      | v2_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f245,plain,
    ( ~ spl8_37
    | ~ spl8_0
    | spl8_11
    | ~ spl8_22
    | ~ spl8_24 ),
    inference(avatar_split_clause,[],[f220,f209,f175,f133,f91,f243])).

fof(f220,plain,
    ( ~ v4_pre_topc(sK3(sK0,k2_xboole_0(sK1,sK2)),sK0)
    | ~ spl8_0
    | ~ spl8_11
    | ~ spl8_22
    | ~ spl8_24 ),
    inference(subsumption_resolution,[],[f200,f219])).

fof(f200,plain,
    ( ~ v4_pre_topc(sK3(sK0,k2_xboole_0(sK1,sK2)),sK0)
    | v2_tops_2(k2_xboole_0(sK1,sK2),sK0)
    | ~ spl8_0
    | ~ spl8_22 ),
    inference(subsumption_resolution,[],[f191,f92])).

fof(f191,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v4_pre_topc(sK3(sK0,k2_xboole_0(sK1,sK2)),sK0)
    | v2_tops_2(k2_xboole_0(sK1,sK2),sK0)
    | ~ spl8_22 ),
    inference(resolution,[],[f176,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(sK3(X0,X1),X0)
      | v2_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f211,plain,
    ( spl8_24
    | ~ spl8_6
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f165,f107,f103,f209])).

fof(f165,plain,
    ( k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2) = k2_xboole_0(sK1,sK2)
    | ~ spl8_6
    | ~ spl8_8 ),
    inference(resolution,[],[f127,f104])).

fof(f127,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2) = k2_xboole_0(sK1,X2) )
    | ~ spl8_8 ),
    inference(resolution,[],[f108,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t23_tops_2.p',redefinition_k4_subset_1)).

fof(f177,plain,
    ( spl8_22
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_20 ),
    inference(avatar_split_clause,[],[f173,f161,f107,f103,f175])).

fof(f161,plain,
    ( spl8_20
  <=> k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2,sK1) = k2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f173,plain,
    ( m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_20 ),
    inference(forward_demodulation,[],[f170,f162])).

fof(f162,plain,
    ( k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2,sK1) = k2_xboole_0(sK1,sK2)
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f161])).

fof(f170,plain,
    ( m1_subset_1(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl8_6
    | ~ spl8_8 ),
    inference(resolution,[],[f115,f108])).

fof(f115,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | m1_subset_1(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
    | ~ spl8_6 ),
    inference(resolution,[],[f104,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t23_tops_2.p',dt_k4_subset_1)).

fof(f163,plain,
    ( spl8_20
    | ~ spl8_6
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f159,f107,f103,f161])).

fof(f159,plain,
    ( k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2,sK1) = k2_xboole_0(sK1,sK2)
    | ~ spl8_6
    | ~ spl8_8 ),
    inference(forward_demodulation,[],[f157,f82])).

fof(f82,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t23_tops_2.p',commutativity_k2_xboole_0)).

fof(f157,plain,
    ( k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2,sK1) = k2_xboole_0(sK2,sK1)
    | ~ spl8_6
    | ~ spl8_8 ),
    inference(resolution,[],[f116,f108])).

fof(f116,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2,X2) = k2_xboole_0(sK2,X2) )
    | ~ spl8_6 ),
    inference(resolution,[],[f104,f62])).

fof(f135,plain,(
    ~ spl8_11 ),
    inference(avatar_split_clause,[],[f58,f133])).

fof(f58,plain,(
    ~ v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v2_tops_2(X2,X0)
              & v2_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v2_tops_2(X2,X0)
              & v2_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ( ( v2_tops_2(X2,X0)
                    & v2_tops_2(X1,X0) )
                 => v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( ( v2_tops_2(X2,X0)
                  & v2_tops_2(X1,X0) )
               => v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t23_tops_2.p',t23_tops_2)).

fof(f109,plain,(
    spl8_8 ),
    inference(avatar_split_clause,[],[f59,f107])).

fof(f59,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f35])).

fof(f105,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f55,f103])).

fof(f55,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f35])).

fof(f101,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f57,f99])).

fof(f57,plain,(
    v2_tops_2(sK2,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f97,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f56,f95])).

fof(f56,plain,(
    v2_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f93,plain,(
    spl8_0 ),
    inference(avatar_split_clause,[],[f60,f91])).

fof(f60,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
