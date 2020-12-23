%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:54 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  157 ( 318 expanded)
%              Number of leaves         :   37 ( 141 expanded)
%              Depth                    :   11
%              Number of atoms          :  649 (2014 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f771,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f79,f84,f104,f109,f114,f119,f128,f137,f142,f151,f156,f161,f225,f268,f367,f473,f580,f656,f697,f719,f728,f743,f765,f770])).

fof(f770,plain,
    ( spl5_13
    | ~ spl5_14
    | ~ spl5_17
    | ~ spl5_18 ),
    inference(avatar_contradiction_clause,[],[f769])).

fof(f769,plain,
    ( $false
    | spl5_13
    | ~ spl5_14
    | ~ spl5_17
    | ~ spl5_18 ),
    inference(unit_resulting_resolution,[],[f155,f160,f136,f131,f207])).

fof(f207,plain,(
    ! [X0,X1] :
      ( ~ r1_tsep_1(X0,X1)
      | r1_tsep_1(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f176,f53])).

fof(f53,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f176,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X1)
      | ~ r1_tsep_1(X0,X1)
      | r1_tsep_1(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f62,f53])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( r1_tsep_1(X0,X1)
       => r1_tsep_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

fof(f131,plain,
    ( ~ r1_tsep_1(sK2,sK3)
    | spl5_13 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl5_13
  <=> r1_tsep_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f136,plain,
    ( r1_tsep_1(sK3,sK2)
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl5_14
  <=> r1_tsep_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f160,plain,
    ( l1_pre_topc(sK3)
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f158])).

fof(f158,plain,
    ( spl5_18
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f155,plain,
    ( l1_pre_topc(sK2)
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f153])).

fof(f153,plain,
    ( spl5_17
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f765,plain,
    ( ~ spl5_11
    | spl5_12
    | ~ spl5_93
    | ~ spl5_94 ),
    inference(avatar_contradiction_clause,[],[f762])).

fof(f762,plain,
    ( $false
    | ~ spl5_11
    | spl5_12
    | ~ spl5_93
    | ~ spl5_94 ),
    inference(unit_resulting_resolution,[],[f713,f717,f122,f127,f62])).

fof(f127,plain,
    ( ~ r1_tsep_1(sK3,sK1)
    | spl5_12 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl5_12
  <=> r1_tsep_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f122,plain,
    ( r1_tsep_1(sK1,sK3)
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl5_11
  <=> r1_tsep_1(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f717,plain,
    ( l1_struct_0(sK3)
    | ~ spl5_94 ),
    inference(avatar_component_clause,[],[f716])).

fof(f716,plain,
    ( spl5_94
  <=> l1_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_94])])).

fof(f713,plain,
    ( l1_struct_0(sK1)
    | ~ spl5_93 ),
    inference(avatar_component_clause,[],[f712])).

fof(f712,plain,
    ( spl5_93
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_93])])).

fof(f743,plain,
    ( ~ spl5_18
    | spl5_94 ),
    inference(avatar_contradiction_clause,[],[f742])).

fof(f742,plain,
    ( $false
    | ~ spl5_18
    | spl5_94 ),
    inference(subsumption_resolution,[],[f740,f160])).

fof(f740,plain,
    ( ~ l1_pre_topc(sK3)
    | spl5_94 ),
    inference(resolution,[],[f718,f53])).

fof(f718,plain,
    ( ~ l1_struct_0(sK3)
    | spl5_94 ),
    inference(avatar_component_clause,[],[f716])).

fof(f728,plain,
    ( ~ spl5_16
    | spl5_93 ),
    inference(avatar_contradiction_clause,[],[f727])).

fof(f727,plain,
    ( $false
    | ~ spl5_16
    | spl5_93 ),
    inference(subsumption_resolution,[],[f725,f150])).

fof(f150,plain,
    ( l1_pre_topc(sK1)
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl5_16
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f725,plain,
    ( ~ l1_pre_topc(sK1)
    | spl5_93 ),
    inference(resolution,[],[f714,f53])).

fof(f714,plain,
    ( ~ l1_struct_0(sK1)
    | spl5_93 ),
    inference(avatar_component_clause,[],[f712])).

fof(f719,plain,
    ( ~ spl5_93
    | ~ spl5_94
    | spl5_11
    | ~ spl5_92 ),
    inference(avatar_split_clause,[],[f701,f694,f121,f716,f712])).

fof(f694,plain,
    ( spl5_92
  <=> r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_92])])).

fof(f701,plain,
    ( ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK1)
    | spl5_11
    | ~ spl5_92 ),
    inference(subsumption_resolution,[],[f699,f123])).

fof(f123,plain,
    ( ~ r1_tsep_1(sK1,sK3)
    | spl5_11 ),
    inference(avatar_component_clause,[],[f121])).

fof(f699,plain,
    ( r1_tsep_1(sK1,sK3)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK1)
    | ~ spl5_92 ),
    inference(resolution,[],[f696,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_tsep_1(X0,X1)
              | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
            & ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
              | ~ r1_tsep_1(X0,X1) ) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tsep_1)).

fof(f696,plain,
    ( r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3))
    | ~ spl5_92 ),
    inference(avatar_component_clause,[],[f694])).

fof(f697,plain,
    ( spl5_92
    | ~ spl5_88 ),
    inference(avatar_split_clause,[],[f685,f654,f694])).

fof(f654,plain,
    ( spl5_88
  <=> ! [X0] :
        ( r1_xboole_0(u1_struct_0(sK1),X0)
        | ~ r2_hidden(sK4(u1_struct_0(sK1),X0),u1_struct_0(sK3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_88])])).

fof(f685,plain,
    ( r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3))
    | ~ spl5_88 ),
    inference(duplicate_literal_removal,[],[f682])).

fof(f682,plain,
    ( r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3))
    | r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3))
    | ~ spl5_88 ),
    inference(resolution,[],[f655,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f23,f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
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

fof(f655,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(u1_struct_0(sK1),X0),u1_struct_0(sK3))
        | r1_xboole_0(u1_struct_0(sK1),X0) )
    | ~ spl5_88 ),
    inference(avatar_component_clause,[],[f654])).

fof(f656,plain,
    ( spl5_88
    | ~ spl5_7
    | ~ spl5_10
    | ~ spl5_73 ),
    inference(avatar_split_clause,[],[f605,f578,f116,f101,f654])).

fof(f101,plain,
    ( spl5_7
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f116,plain,
    ( spl5_10
  <=> m1_pre_topc(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f578,plain,
    ( spl5_73
  <=> ! [X1,X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | r1_xboole_0(u1_struct_0(X0),X1)
        | ~ r2_hidden(sK4(u1_struct_0(X0),X1),u1_struct_0(sK3))
        | ~ m1_pre_topc(X0,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_73])])).

fof(f605,plain,
    ( ! [X0] :
        ( r1_xboole_0(u1_struct_0(sK1),X0)
        | ~ r2_hidden(sK4(u1_struct_0(sK1),X0),u1_struct_0(sK3)) )
    | ~ spl5_7
    | ~ spl5_10
    | ~ spl5_73 ),
    inference(subsumption_resolution,[],[f603,f103])).

fof(f103,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f101])).

fof(f603,plain,
    ( ! [X0] :
        ( r1_xboole_0(u1_struct_0(sK1),X0)
        | ~ r2_hidden(sK4(u1_struct_0(sK1),X0),u1_struct_0(sK3))
        | ~ m1_pre_topc(sK1,sK0) )
    | ~ spl5_10
    | ~ spl5_73 ),
    inference(resolution,[],[f579,f118])).

fof(f118,plain,
    ( m1_pre_topc(sK1,sK2)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f116])).

fof(f579,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X0,sK2)
        | r1_xboole_0(u1_struct_0(X0),X1)
        | ~ r2_hidden(sK4(u1_struct_0(X0),X1),u1_struct_0(sK3))
        | ~ m1_pre_topc(X0,sK0) )
    | ~ spl5_73 ),
    inference(avatar_component_clause,[],[f578])).

fof(f580,plain,
    ( spl5_73
    | ~ spl5_8
    | ~ spl5_13
    | ~ spl5_18
    | ~ spl5_61 ),
    inference(avatar_split_clause,[],[f489,f471,f158,f130,f106,f578])).

fof(f106,plain,
    ( spl5_8
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f471,plain,
    ( spl5_61
  <=> ! [X1,X3,X0,X2] :
        ( ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X1,sK0)
        | r1_xboole_0(u1_struct_0(X0),X2)
        | ~ r2_hidden(sK4(u1_struct_0(X0),X2),u1_struct_0(X3))
        | ~ r1_tsep_1(X1,X3)
        | ~ l1_pre_topc(X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_61])])).

fof(f489,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X0,sK0)
        | r1_xboole_0(u1_struct_0(X0),X1)
        | ~ r2_hidden(sK4(u1_struct_0(X0),X1),u1_struct_0(sK3))
        | ~ m1_pre_topc(X0,sK2) )
    | ~ spl5_8
    | ~ spl5_13
    | ~ spl5_18
    | ~ spl5_61 ),
    inference(subsumption_resolution,[],[f488,f160])).

fof(f488,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X0,sK0)
        | r1_xboole_0(u1_struct_0(X0),X1)
        | ~ r2_hidden(sK4(u1_struct_0(X0),X1),u1_struct_0(sK3))
        | ~ m1_pre_topc(X0,sK2)
        | ~ l1_pre_topc(sK3) )
    | ~ spl5_8
    | ~ spl5_13
    | ~ spl5_61 ),
    inference(subsumption_resolution,[],[f486,f108])).

fof(f108,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f106])).

fof(f486,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(sK2,sK0)
        | r1_xboole_0(u1_struct_0(X0),X1)
        | ~ r2_hidden(sK4(u1_struct_0(X0),X1),u1_struct_0(sK3))
        | ~ m1_pre_topc(X0,sK2)
        | ~ l1_pre_topc(sK3) )
    | ~ spl5_13
    | ~ spl5_61 ),
    inference(resolution,[],[f472,f132])).

fof(f132,plain,
    ( r1_tsep_1(sK2,sK3)
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f130])).

fof(f472,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r1_tsep_1(X1,X3)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X1,sK0)
        | r1_xboole_0(u1_struct_0(X0),X2)
        | ~ r2_hidden(sK4(u1_struct_0(X0),X2),u1_struct_0(X3))
        | ~ m1_pre_topc(X0,X1)
        | ~ l1_pre_topc(X3) )
    | ~ spl5_61 ),
    inference(avatar_component_clause,[],[f471])).

fof(f473,plain,
    ( spl5_61
    | ~ spl5_15
    | ~ spl5_47 ),
    inference(avatar_split_clause,[],[f386,f365,f140,f471])).

fof(f140,plain,
    ( spl5_15
  <=> ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f365,plain,
    ( spl5_47
  <=> ! [X1,X0,X2] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X0,X1)
        | r2_hidden(sK4(u1_struct_0(X0),X2),u1_struct_0(X1))
        | ~ m1_pre_topc(X1,sK0)
        | r1_xboole_0(u1_struct_0(X0),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_47])])).

fof(f386,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X1,sK0)
        | r1_xboole_0(u1_struct_0(X0),X2)
        | ~ r2_hidden(sK4(u1_struct_0(X0),X2),u1_struct_0(X3))
        | ~ r1_tsep_1(X1,X3)
        | ~ l1_pre_topc(X3) )
    | ~ spl5_15
    | ~ spl5_47 ),
    inference(subsumption_resolution,[],[f383,f141])).

fof(f141,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | l1_pre_topc(X0) )
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f140])).

fof(f383,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X1,sK0)
        | r1_xboole_0(u1_struct_0(X0),X2)
        | ~ r2_hidden(sK4(u1_struct_0(X0),X2),u1_struct_0(X3))
        | ~ r1_tsep_1(X1,X3)
        | ~ l1_pre_topc(X1)
        | ~ l1_pre_topc(X3) )
    | ~ spl5_47 ),
    inference(resolution,[],[f366,f259])).

fof(f259,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,u1_struct_0(X0))
      | ~ r2_hidden(X2,u1_struct_0(X1))
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f237,f53])).

fof(f237,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ r1_tsep_1(X1,X0)
      | ~ r2_hidden(X2,u1_struct_0(X0))
      | ~ r2_hidden(X2,u1_struct_0(X1))
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f180,f53])).

fof(f180,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ l1_struct_0(X1)
      | ~ r1_tsep_1(X0,X1)
      | ~ r2_hidden(X2,u1_struct_0(X1))
      | ~ r2_hidden(X2,u1_struct_0(X0)) ) ),
    inference(resolution,[],[f51,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f366,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(sK4(u1_struct_0(X0),X2),u1_struct_0(X1))
        | ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X1,sK0)
        | r1_xboole_0(u1_struct_0(X0),X2) )
    | ~ spl5_47 ),
    inference(avatar_component_clause,[],[f365])).

fof(f367,plain,
    ( spl5_47
    | ~ spl5_31 ),
    inference(avatar_split_clause,[],[f270,f266,f365])).

fof(f266,plain,
    ( spl5_31
  <=> ! [X3,X5,X4] :
        ( ~ m1_pre_topc(X3,sK0)
        | ~ m1_pre_topc(X4,sK0)
        | ~ m1_pre_topc(X4,X3)
        | r2_hidden(X5,u1_struct_0(X3))
        | ~ r2_hidden(X5,u1_struct_0(X4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f270,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X0,X1)
        | r2_hidden(sK4(u1_struct_0(X0),X2),u1_struct_0(X1))
        | ~ m1_pre_topc(X1,sK0)
        | r1_xboole_0(u1_struct_0(X0),X2) )
    | ~ spl5_31 ),
    inference(resolution,[],[f267,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f267,plain,
    ( ! [X4,X5,X3] :
        ( ~ r2_hidden(X5,u1_struct_0(X4))
        | ~ m1_pre_topc(X4,sK0)
        | ~ m1_pre_topc(X4,X3)
        | r2_hidden(X5,u1_struct_0(X3))
        | ~ m1_pre_topc(X3,sK0) )
    | ~ spl5_31 ),
    inference(avatar_component_clause,[],[f266])).

fof(f268,plain,
    ( spl5_31
    | ~ spl5_24 ),
    inference(avatar_split_clause,[],[f231,f223,f266])).

fof(f223,plain,
    ( spl5_24
  <=> ! [X1,X0] :
        ( ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X0,sK0)
        | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f231,plain,
    ( ! [X4,X5,X3] :
        ( ~ m1_pre_topc(X3,sK0)
        | ~ m1_pre_topc(X4,sK0)
        | ~ m1_pre_topc(X4,X3)
        | r2_hidden(X5,u1_struct_0(X3))
        | ~ r2_hidden(X5,u1_struct_0(X4)) )
    | ~ spl5_24 ),
    inference(resolution,[],[f224,f171])).

fof(f171,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f61,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f224,plain,
    ( ! [X0,X1] :
        ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X0,X1) )
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f223])).

fof(f225,plain,
    ( spl5_24
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f201,f81,f76,f223])).

fof(f76,plain,
    ( spl5_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f81,plain,
    ( spl5_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f201,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X0,sK0)
        | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) )
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f200,f83])).

fof(f83,plain,
    ( l1_pre_topc(sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f81])).

fof(f200,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ l1_pre_topc(sK0)
        | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) )
    | ~ spl5_2 ),
    inference(resolution,[],[f57,f78])).

fof(f78,plain,
    ( v2_pre_topc(sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f76])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
                  | ~ m1_pre_topc(X1,X2) )
                & ( m1_pre_topc(X1,X2)
                  | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).

fof(f161,plain,
    ( spl5_18
    | ~ spl5_9
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f145,f140,f111,f158])).

fof(f111,plain,
    ( spl5_9
  <=> m1_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f145,plain,
    ( l1_pre_topc(sK3)
    | ~ spl5_9
    | ~ spl5_15 ),
    inference(resolution,[],[f141,f113])).

fof(f113,plain,
    ( m1_pre_topc(sK3,sK0)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f111])).

fof(f156,plain,
    ( spl5_17
    | ~ spl5_8
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f144,f140,f106,f153])).

fof(f144,plain,
    ( l1_pre_topc(sK2)
    | ~ spl5_8
    | ~ spl5_15 ),
    inference(resolution,[],[f141,f108])).

fof(f151,plain,
    ( spl5_16
    | ~ spl5_7
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f143,f140,f101,f148])).

fof(f143,plain,
    ( l1_pre_topc(sK1)
    | ~ spl5_7
    | ~ spl5_15 ),
    inference(resolution,[],[f141,f103])).

fof(f142,plain,
    ( spl5_15
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f138,f81,f140])).

fof(f138,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | l1_pre_topc(X0) )
    | ~ spl5_3 ),
    inference(resolution,[],[f54,f83])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f137,plain,
    ( spl5_13
    | spl5_14 ),
    inference(avatar_split_clause,[],[f50,f134,f130])).

fof(f50,plain,
    ( r1_tsep_1(sK3,sK2)
    | r1_tsep_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ( r1_tsep_1(sK3,sK2)
      | r1_tsep_1(sK2,sK3) )
    & ( ~ r1_tsep_1(sK3,sK1)
      | ~ r1_tsep_1(sK1,sK3) )
    & m1_pre_topc(sK1,sK2)
    & m1_pre_topc(sK3,sK0)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f30,f29,f28,f27])).

fof(f27,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( r1_tsep_1(X3,X2)
                      | r1_tsep_1(X2,X3) )
                    & ( ~ r1_tsep_1(X3,X1)
                      | ~ r1_tsep_1(X1,X3) )
                    & m1_pre_topc(X1,X2)
                    & m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,sK0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( r1_tsep_1(X3,X2)
                  | r1_tsep_1(X2,X3) )
                & ( ~ r1_tsep_1(X3,X1)
                  | ~ r1_tsep_1(X1,X3) )
                & m1_pre_topc(X1,X2)
                & m1_pre_topc(X3,sK0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( r1_tsep_1(X3,X2)
                | r1_tsep_1(X2,X3) )
              & ( ~ r1_tsep_1(X3,sK1)
                | ~ r1_tsep_1(sK1,X3) )
              & m1_pre_topc(sK1,X2)
              & m1_pre_topc(X3,sK0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK0)
          & ~ v2_struct_0(X2) )
      & m1_pre_topc(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( r1_tsep_1(X3,X2)
              | r1_tsep_1(X2,X3) )
            & ( ~ r1_tsep_1(X3,sK1)
              | ~ r1_tsep_1(sK1,X3) )
            & m1_pre_topc(sK1,X2)
            & m1_pre_topc(X3,sK0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK0)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ( r1_tsep_1(X3,sK2)
            | r1_tsep_1(sK2,X3) )
          & ( ~ r1_tsep_1(X3,sK1)
            | ~ r1_tsep_1(sK1,X3) )
          & m1_pre_topc(sK1,sK2)
          & m1_pre_topc(X3,sK0)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X3] :
        ( ( r1_tsep_1(X3,sK2)
          | r1_tsep_1(sK2,X3) )
        & ( ~ r1_tsep_1(X3,sK1)
          | ~ r1_tsep_1(sK1,X3) )
        & m1_pre_topc(sK1,sK2)
        & m1_pre_topc(X3,sK0)
        & ~ v2_struct_0(X3) )
   => ( ( r1_tsep_1(sK3,sK2)
        | r1_tsep_1(sK2,sK3) )
      & ( ~ r1_tsep_1(sK3,sK1)
        | ~ r1_tsep_1(sK1,sK3) )
      & m1_pre_topc(sK1,sK2)
      & m1_pre_topc(sK3,sK0)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ( m1_pre_topc(X1,X2)
                     => ( ( ~ r1_tsep_1(X3,X2)
                          & ~ r1_tsep_1(X2,X3) )
                        | ( r1_tsep_1(X3,X1)
                          & r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( m1_pre_topc(X1,X2)
                   => ( ( ~ r1_tsep_1(X3,X2)
                        & ~ r1_tsep_1(X2,X3) )
                      | ( r1_tsep_1(X3,X1)
                        & r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_tmap_1)).

fof(f128,plain,
    ( ~ spl5_11
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f49,f125,f121])).

fof(f49,plain,
    ( ~ r1_tsep_1(sK3,sK1)
    | ~ r1_tsep_1(sK1,sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f119,plain,(
    spl5_10 ),
    inference(avatar_split_clause,[],[f48,f116])).

fof(f48,plain,(
    m1_pre_topc(sK1,sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f114,plain,(
    spl5_9 ),
    inference(avatar_split_clause,[],[f47,f111])).

fof(f47,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f109,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f45,f106])).

fof(f45,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f104,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f43,f101])).

fof(f43,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f84,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f41,f81])).

fof(f41,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f79,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f40,f76])).

fof(f40,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:09:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.22/0.45  % (14517)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.45  % (14528)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.47  % (14535)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.47  % (14519)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.47  % (14517)Refutation not found, incomplete strategy% (14517)------------------------------
% 0.22/0.47  % (14517)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (14517)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.47  
% 0.22/0.47  % (14517)Memory used [KB]: 10618
% 0.22/0.47  % (14517)Time elapsed: 0.071 s
% 0.22/0.47  % (14517)------------------------------
% 0.22/0.47  % (14517)------------------------------
% 0.22/0.48  % (14540)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.50  % (14518)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.50  % (14527)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.50  % (14519)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f771,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f79,f84,f104,f109,f114,f119,f128,f137,f142,f151,f156,f161,f225,f268,f367,f473,f580,f656,f697,f719,f728,f743,f765,f770])).
% 0.22/0.50  fof(f770,plain,(
% 0.22/0.50    spl5_13 | ~spl5_14 | ~spl5_17 | ~spl5_18),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f769])).
% 0.22/0.50  fof(f769,plain,(
% 0.22/0.50    $false | (spl5_13 | ~spl5_14 | ~spl5_17 | ~spl5_18)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f155,f160,f136,f131,f207])).
% 0.22/0.50  fof(f207,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r1_tsep_1(X0,X1) | r1_tsep_1(X1,X0) | ~l1_pre_topc(X0) | ~l1_pre_topc(X1)) )),
% 0.22/0.50    inference(resolution,[],[f176,f53])).
% 0.22/0.50  fof(f53,plain,(
% 0.22/0.50    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f17])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.50  fof(f176,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~l1_struct_0(X1) | ~r1_tsep_1(X0,X1) | r1_tsep_1(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.50    inference(resolution,[],[f62,f53])).
% 0.22/0.50  fof(f62,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~l1_struct_0(X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | r1_tsep_1(X1,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f26])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ! [X0,X1] : (r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f25])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ! [X0,X1] : ((r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1)) | (~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f9])).
% 0.22/0.50  fof(f9,axiom,(
% 0.22/0.50    ! [X0,X1] : ((l1_struct_0(X1) & l1_struct_0(X0)) => (r1_tsep_1(X0,X1) => r1_tsep_1(X1,X0)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).
% 0.22/0.50  fof(f131,plain,(
% 0.22/0.50    ~r1_tsep_1(sK2,sK3) | spl5_13),
% 0.22/0.50    inference(avatar_component_clause,[],[f130])).
% 0.22/0.50  fof(f130,plain,(
% 0.22/0.50    spl5_13 <=> r1_tsep_1(sK2,sK3)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.22/0.50  fof(f136,plain,(
% 0.22/0.50    r1_tsep_1(sK3,sK2) | ~spl5_14),
% 0.22/0.50    inference(avatar_component_clause,[],[f134])).
% 0.22/0.50  fof(f134,plain,(
% 0.22/0.50    spl5_14 <=> r1_tsep_1(sK3,sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.22/0.50  fof(f160,plain,(
% 0.22/0.50    l1_pre_topc(sK3) | ~spl5_18),
% 0.22/0.50    inference(avatar_component_clause,[],[f158])).
% 0.22/0.50  fof(f158,plain,(
% 0.22/0.50    spl5_18 <=> l1_pre_topc(sK3)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.22/0.50  fof(f155,plain,(
% 0.22/0.50    l1_pre_topc(sK2) | ~spl5_17),
% 0.22/0.50    inference(avatar_component_clause,[],[f153])).
% 0.22/0.50  fof(f153,plain,(
% 0.22/0.50    spl5_17 <=> l1_pre_topc(sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.22/0.50  fof(f765,plain,(
% 0.22/0.50    ~spl5_11 | spl5_12 | ~spl5_93 | ~spl5_94),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f762])).
% 0.22/0.50  fof(f762,plain,(
% 0.22/0.50    $false | (~spl5_11 | spl5_12 | ~spl5_93 | ~spl5_94)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f713,f717,f122,f127,f62])).
% 0.22/0.50  fof(f127,plain,(
% 0.22/0.50    ~r1_tsep_1(sK3,sK1) | spl5_12),
% 0.22/0.50    inference(avatar_component_clause,[],[f125])).
% 0.22/0.50  fof(f125,plain,(
% 0.22/0.50    spl5_12 <=> r1_tsep_1(sK3,sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.22/0.50  fof(f122,plain,(
% 0.22/0.50    r1_tsep_1(sK1,sK3) | ~spl5_11),
% 0.22/0.50    inference(avatar_component_clause,[],[f121])).
% 0.22/0.50  fof(f121,plain,(
% 0.22/0.50    spl5_11 <=> r1_tsep_1(sK1,sK3)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.22/0.50  fof(f717,plain,(
% 0.22/0.50    l1_struct_0(sK3) | ~spl5_94),
% 0.22/0.50    inference(avatar_component_clause,[],[f716])).
% 0.22/0.50  fof(f716,plain,(
% 0.22/0.50    spl5_94 <=> l1_struct_0(sK3)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_94])])).
% 0.22/0.50  fof(f713,plain,(
% 0.22/0.50    l1_struct_0(sK1) | ~spl5_93),
% 0.22/0.50    inference(avatar_component_clause,[],[f712])).
% 0.22/0.50  fof(f712,plain,(
% 0.22/0.50    spl5_93 <=> l1_struct_0(sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_93])])).
% 0.22/0.50  fof(f743,plain,(
% 0.22/0.50    ~spl5_18 | spl5_94),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f742])).
% 0.22/0.50  fof(f742,plain,(
% 0.22/0.50    $false | (~spl5_18 | spl5_94)),
% 0.22/0.50    inference(subsumption_resolution,[],[f740,f160])).
% 0.22/0.50  fof(f740,plain,(
% 0.22/0.50    ~l1_pre_topc(sK3) | spl5_94),
% 0.22/0.50    inference(resolution,[],[f718,f53])).
% 0.22/0.50  fof(f718,plain,(
% 0.22/0.50    ~l1_struct_0(sK3) | spl5_94),
% 0.22/0.50    inference(avatar_component_clause,[],[f716])).
% 0.22/0.50  fof(f728,plain,(
% 0.22/0.50    ~spl5_16 | spl5_93),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f727])).
% 0.22/0.50  fof(f727,plain,(
% 0.22/0.50    $false | (~spl5_16 | spl5_93)),
% 0.22/0.50    inference(subsumption_resolution,[],[f725,f150])).
% 0.22/0.50  fof(f150,plain,(
% 0.22/0.50    l1_pre_topc(sK1) | ~spl5_16),
% 0.22/0.50    inference(avatar_component_clause,[],[f148])).
% 0.22/0.50  fof(f148,plain,(
% 0.22/0.50    spl5_16 <=> l1_pre_topc(sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.22/0.50  fof(f725,plain,(
% 0.22/0.50    ~l1_pre_topc(sK1) | spl5_93),
% 0.22/0.50    inference(resolution,[],[f714,f53])).
% 0.22/0.50  fof(f714,plain,(
% 0.22/0.50    ~l1_struct_0(sK1) | spl5_93),
% 0.22/0.50    inference(avatar_component_clause,[],[f712])).
% 0.22/0.50  fof(f719,plain,(
% 0.22/0.50    ~spl5_93 | ~spl5_94 | spl5_11 | ~spl5_92),
% 0.22/0.50    inference(avatar_split_clause,[],[f701,f694,f121,f716,f712])).
% 0.22/0.50  fof(f694,plain,(
% 0.22/0.50    spl5_92 <=> r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_92])])).
% 0.22/0.50  fof(f701,plain,(
% 0.22/0.50    ~l1_struct_0(sK3) | ~l1_struct_0(sK1) | (spl5_11 | ~spl5_92)),
% 0.22/0.50    inference(subsumption_resolution,[],[f699,f123])).
% 0.22/0.50  fof(f123,plain,(
% 0.22/0.50    ~r1_tsep_1(sK1,sK3) | spl5_11),
% 0.22/0.50    inference(avatar_component_clause,[],[f121])).
% 0.22/0.50  fof(f699,plain,(
% 0.22/0.50    r1_tsep_1(sK1,sK3) | ~l1_struct_0(sK3) | ~l1_struct_0(sK1) | ~spl5_92),
% 0.22/0.50    inference(resolution,[],[f696,f52])).
% 0.22/0.50  fof(f52,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f32])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (((r1_tsep_1(X0,X1) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) & (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 0.22/0.50    inference(nnf_transformation,[],[f16])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : ((r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f8])).
% 0.22/0.50  fof(f8,axiom,(
% 0.22/0.50    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => (r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tsep_1)).
% 0.22/0.50  fof(f696,plain,(
% 0.22/0.50    r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) | ~spl5_92),
% 0.22/0.50    inference(avatar_component_clause,[],[f694])).
% 0.22/0.50  fof(f697,plain,(
% 0.22/0.50    spl5_92 | ~spl5_88),
% 0.22/0.50    inference(avatar_split_clause,[],[f685,f654,f694])).
% 0.22/0.50  fof(f654,plain,(
% 0.22/0.50    spl5_88 <=> ! [X0] : (r1_xboole_0(u1_struct_0(sK1),X0) | ~r2_hidden(sK4(u1_struct_0(sK1),X0),u1_struct_0(sK3)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_88])])).
% 0.22/0.50  fof(f685,plain,(
% 0.22/0.50    r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) | ~spl5_88),
% 0.22/0.50    inference(duplicate_literal_removal,[],[f682])).
% 0.22/0.50  fof(f682,plain,(
% 0.22/0.50    r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) | r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) | ~spl5_88),
% 0.22/0.50    inference(resolution,[],[f655,f59])).
% 0.22/0.50  fof(f59,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f35])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f23,f34])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.22/0.50    inference(ennf_transformation,[],[f13])).
% 0.22/0.50  fof(f13,plain,(
% 0.22/0.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.50    inference(rectify,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.22/0.50  fof(f655,plain,(
% 0.22/0.50    ( ! [X0] : (~r2_hidden(sK4(u1_struct_0(sK1),X0),u1_struct_0(sK3)) | r1_xboole_0(u1_struct_0(sK1),X0)) ) | ~spl5_88),
% 0.22/0.50    inference(avatar_component_clause,[],[f654])).
% 0.22/0.50  fof(f656,plain,(
% 0.22/0.50    spl5_88 | ~spl5_7 | ~spl5_10 | ~spl5_73),
% 0.22/0.50    inference(avatar_split_clause,[],[f605,f578,f116,f101,f654])).
% 0.22/0.50  fof(f101,plain,(
% 0.22/0.50    spl5_7 <=> m1_pre_topc(sK1,sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.22/0.50  fof(f116,plain,(
% 0.22/0.50    spl5_10 <=> m1_pre_topc(sK1,sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.22/0.50  fof(f578,plain,(
% 0.22/0.50    spl5_73 <=> ! [X1,X0] : (~m1_pre_topc(X0,sK0) | r1_xboole_0(u1_struct_0(X0),X1) | ~r2_hidden(sK4(u1_struct_0(X0),X1),u1_struct_0(sK3)) | ~m1_pre_topc(X0,sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_73])])).
% 0.22/0.50  fof(f605,plain,(
% 0.22/0.50    ( ! [X0] : (r1_xboole_0(u1_struct_0(sK1),X0) | ~r2_hidden(sK4(u1_struct_0(sK1),X0),u1_struct_0(sK3))) ) | (~spl5_7 | ~spl5_10 | ~spl5_73)),
% 0.22/0.50    inference(subsumption_resolution,[],[f603,f103])).
% 0.22/0.50  fof(f103,plain,(
% 0.22/0.50    m1_pre_topc(sK1,sK0) | ~spl5_7),
% 0.22/0.50    inference(avatar_component_clause,[],[f101])).
% 0.22/0.50  fof(f603,plain,(
% 0.22/0.50    ( ! [X0] : (r1_xboole_0(u1_struct_0(sK1),X0) | ~r2_hidden(sK4(u1_struct_0(sK1),X0),u1_struct_0(sK3)) | ~m1_pre_topc(sK1,sK0)) ) | (~spl5_10 | ~spl5_73)),
% 0.22/0.50    inference(resolution,[],[f579,f118])).
% 0.22/0.50  fof(f118,plain,(
% 0.22/0.50    m1_pre_topc(sK1,sK2) | ~spl5_10),
% 0.22/0.50    inference(avatar_component_clause,[],[f116])).
% 0.22/0.50  fof(f579,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_pre_topc(X0,sK2) | r1_xboole_0(u1_struct_0(X0),X1) | ~r2_hidden(sK4(u1_struct_0(X0),X1),u1_struct_0(sK3)) | ~m1_pre_topc(X0,sK0)) ) | ~spl5_73),
% 0.22/0.50    inference(avatar_component_clause,[],[f578])).
% 0.22/0.50  fof(f580,plain,(
% 0.22/0.50    spl5_73 | ~spl5_8 | ~spl5_13 | ~spl5_18 | ~spl5_61),
% 0.22/0.50    inference(avatar_split_clause,[],[f489,f471,f158,f130,f106,f578])).
% 0.22/0.50  fof(f106,plain,(
% 0.22/0.50    spl5_8 <=> m1_pre_topc(sK2,sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.22/0.50  fof(f471,plain,(
% 0.22/0.50    spl5_61 <=> ! [X1,X3,X0,X2] : (~m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(X1,sK0) | r1_xboole_0(u1_struct_0(X0),X2) | ~r2_hidden(sK4(u1_struct_0(X0),X2),u1_struct_0(X3)) | ~r1_tsep_1(X1,X3) | ~l1_pre_topc(X3))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_61])])).
% 0.22/0.50  fof(f489,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_pre_topc(X0,sK0) | r1_xboole_0(u1_struct_0(X0),X1) | ~r2_hidden(sK4(u1_struct_0(X0),X1),u1_struct_0(sK3)) | ~m1_pre_topc(X0,sK2)) ) | (~spl5_8 | ~spl5_13 | ~spl5_18 | ~spl5_61)),
% 0.22/0.50    inference(subsumption_resolution,[],[f488,f160])).
% 0.22/0.50  fof(f488,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_pre_topc(X0,sK0) | r1_xboole_0(u1_struct_0(X0),X1) | ~r2_hidden(sK4(u1_struct_0(X0),X1),u1_struct_0(sK3)) | ~m1_pre_topc(X0,sK2) | ~l1_pre_topc(sK3)) ) | (~spl5_8 | ~spl5_13 | ~spl5_61)),
% 0.22/0.50    inference(subsumption_resolution,[],[f486,f108])).
% 0.22/0.50  fof(f108,plain,(
% 0.22/0.50    m1_pre_topc(sK2,sK0) | ~spl5_8),
% 0.22/0.50    inference(avatar_component_clause,[],[f106])).
% 0.22/0.50  fof(f486,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_pre_topc(X0,sK0) | ~m1_pre_topc(sK2,sK0) | r1_xboole_0(u1_struct_0(X0),X1) | ~r2_hidden(sK4(u1_struct_0(X0),X1),u1_struct_0(sK3)) | ~m1_pre_topc(X0,sK2) | ~l1_pre_topc(sK3)) ) | (~spl5_13 | ~spl5_61)),
% 0.22/0.50    inference(resolution,[],[f472,f132])).
% 0.22/0.50  fof(f132,plain,(
% 0.22/0.50    r1_tsep_1(sK2,sK3) | ~spl5_13),
% 0.22/0.50    inference(avatar_component_clause,[],[f130])).
% 0.22/0.50  fof(f472,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (~r1_tsep_1(X1,X3) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(X1,sK0) | r1_xboole_0(u1_struct_0(X0),X2) | ~r2_hidden(sK4(u1_struct_0(X0),X2),u1_struct_0(X3)) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X3)) ) | ~spl5_61),
% 0.22/0.50    inference(avatar_component_clause,[],[f471])).
% 0.22/0.50  fof(f473,plain,(
% 0.22/0.50    spl5_61 | ~spl5_15 | ~spl5_47),
% 0.22/0.50    inference(avatar_split_clause,[],[f386,f365,f140,f471])).
% 0.22/0.50  fof(f140,plain,(
% 0.22/0.50    spl5_15 <=> ! [X0] : (~m1_pre_topc(X0,sK0) | l1_pre_topc(X0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.22/0.50  fof(f365,plain,(
% 0.22/0.50    spl5_47 <=> ! [X1,X0,X2] : (~m1_pre_topc(X0,sK0) | ~m1_pre_topc(X0,X1) | r2_hidden(sK4(u1_struct_0(X0),X2),u1_struct_0(X1)) | ~m1_pre_topc(X1,sK0) | r1_xboole_0(u1_struct_0(X0),X2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_47])])).
% 0.22/0.50  fof(f386,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (~m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(X1,sK0) | r1_xboole_0(u1_struct_0(X0),X2) | ~r2_hidden(sK4(u1_struct_0(X0),X2),u1_struct_0(X3)) | ~r1_tsep_1(X1,X3) | ~l1_pre_topc(X3)) ) | (~spl5_15 | ~spl5_47)),
% 0.22/0.50    inference(subsumption_resolution,[],[f383,f141])).
% 0.22/0.50  fof(f141,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_pre_topc(X0,sK0) | l1_pre_topc(X0)) ) | ~spl5_15),
% 0.22/0.50    inference(avatar_component_clause,[],[f140])).
% 0.22/0.50  fof(f383,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (~m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(X1,sK0) | r1_xboole_0(u1_struct_0(X0),X2) | ~r2_hidden(sK4(u1_struct_0(X0),X2),u1_struct_0(X3)) | ~r1_tsep_1(X1,X3) | ~l1_pre_topc(X1) | ~l1_pre_topc(X3)) ) | ~spl5_47),
% 0.22/0.50    inference(resolution,[],[f366,f259])).
% 0.22/0.50  fof(f259,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~r2_hidden(X2,u1_struct_0(X0)) | ~r2_hidden(X2,u1_struct_0(X1)) | ~r1_tsep_1(X0,X1) | ~l1_pre_topc(X0) | ~l1_pre_topc(X1)) )),
% 0.22/0.50    inference(resolution,[],[f237,f53])).
% 0.22/0.50  fof(f237,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~l1_struct_0(X0) | ~r1_tsep_1(X1,X0) | ~r2_hidden(X2,u1_struct_0(X0)) | ~r2_hidden(X2,u1_struct_0(X1)) | ~l1_pre_topc(X1)) )),
% 0.22/0.50    inference(resolution,[],[f180,f53])).
% 0.22/0.50  fof(f180,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~l1_struct_0(X0) | ~l1_struct_0(X1) | ~r1_tsep_1(X0,X1) | ~r2_hidden(X2,u1_struct_0(X1)) | ~r2_hidden(X2,u1_struct_0(X0))) )),
% 0.22/0.50    inference(resolution,[],[f51,f60])).
% 0.22/0.50  fof(f60,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f35])).
% 0.22/0.50  fof(f51,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f32])).
% 0.22/0.50  fof(f366,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (r2_hidden(sK4(u1_struct_0(X0),X2),u1_struct_0(X1)) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(X1,sK0) | r1_xboole_0(u1_struct_0(X0),X2)) ) | ~spl5_47),
% 0.22/0.50    inference(avatar_component_clause,[],[f365])).
% 0.22/0.50  fof(f367,plain,(
% 0.22/0.50    spl5_47 | ~spl5_31),
% 0.22/0.50    inference(avatar_split_clause,[],[f270,f266,f365])).
% 0.22/0.50  fof(f266,plain,(
% 0.22/0.50    spl5_31 <=> ! [X3,X5,X4] : (~m1_pre_topc(X3,sK0) | ~m1_pre_topc(X4,sK0) | ~m1_pre_topc(X4,X3) | r2_hidden(X5,u1_struct_0(X3)) | ~r2_hidden(X5,u1_struct_0(X4)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).
% 0.22/0.50  fof(f270,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_pre_topc(X0,sK0) | ~m1_pre_topc(X0,X1) | r2_hidden(sK4(u1_struct_0(X0),X2),u1_struct_0(X1)) | ~m1_pre_topc(X1,sK0) | r1_xboole_0(u1_struct_0(X0),X2)) ) | ~spl5_31),
% 0.22/0.50    inference(resolution,[],[f267,f58])).
% 0.22/0.50  fof(f58,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f35])).
% 0.22/0.50  fof(f267,plain,(
% 0.22/0.50    ( ! [X4,X5,X3] : (~r2_hidden(X5,u1_struct_0(X4)) | ~m1_pre_topc(X4,sK0) | ~m1_pre_topc(X4,X3) | r2_hidden(X5,u1_struct_0(X3)) | ~m1_pre_topc(X3,sK0)) ) | ~spl5_31),
% 0.22/0.50    inference(avatar_component_clause,[],[f266])).
% 0.22/0.50  fof(f268,plain,(
% 0.22/0.50    spl5_31 | ~spl5_24),
% 0.22/0.50    inference(avatar_split_clause,[],[f231,f223,f266])).
% 0.22/0.50  fof(f223,plain,(
% 0.22/0.50    spl5_24 <=> ! [X1,X0] : (~m1_pre_topc(X0,X1) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X0,sK0) | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 0.22/0.50  fof(f231,plain,(
% 0.22/0.50    ( ! [X4,X5,X3] : (~m1_pre_topc(X3,sK0) | ~m1_pre_topc(X4,sK0) | ~m1_pre_topc(X4,X3) | r2_hidden(X5,u1_struct_0(X3)) | ~r2_hidden(X5,u1_struct_0(X4))) ) | ~spl5_24),
% 0.22/0.50    inference(resolution,[],[f224,f171])).
% 0.22/0.50  fof(f171,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) )),
% 0.22/0.50    inference(resolution,[],[f61,f67])).
% 0.22/0.50  fof(f67,plain,(
% 0.22/0.50    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f38])).
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.50    inference(nnf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.50  fof(f61,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f24])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 0.22/0.50  fof(f224,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(X0,X1)) ) | ~spl5_24),
% 0.22/0.50    inference(avatar_component_clause,[],[f223])).
% 0.22/0.50  fof(f225,plain,(
% 0.22/0.50    spl5_24 | ~spl5_2 | ~spl5_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f201,f81,f76,f223])).
% 0.22/0.50  fof(f76,plain,(
% 0.22/0.50    spl5_2 <=> v2_pre_topc(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.22/0.50  fof(f81,plain,(
% 0.22/0.50    spl5_3 <=> l1_pre_topc(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.22/0.50  fof(f201,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_pre_topc(X0,X1) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X0,sK0) | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))) ) | (~spl5_2 | ~spl5_3)),
% 0.22/0.50    inference(subsumption_resolution,[],[f200,f83])).
% 0.22/0.50  fof(f83,plain,(
% 0.22/0.50    l1_pre_topc(sK0) | ~spl5_3),
% 0.22/0.50    inference(avatar_component_clause,[],[f81])).
% 0.22/0.50  fof(f200,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_pre_topc(X0,X1) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X0,sK0) | ~l1_pre_topc(sK0) | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))) ) | ~spl5_2),
% 0.22/0.50    inference(resolution,[],[f57,f78])).
% 0.22/0.50  fof(f78,plain,(
% 0.22/0.50    v2_pre_topc(sK0) | ~spl5_2),
% 0.22/0.50    inference(avatar_component_clause,[],[f76])).
% 0.22/0.50  fof(f57,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | r1_tarski(u1_struct_0(X1),u1_struct_0(X2))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f33])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.50    inference(nnf_transformation,[],[f22])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.50    inference(flattening,[],[f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f10])).
% 0.22/0.50  fof(f10,axiom,(
% 0.22/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).
% 0.22/0.50  fof(f161,plain,(
% 0.22/0.50    spl5_18 | ~spl5_9 | ~spl5_15),
% 0.22/0.50    inference(avatar_split_clause,[],[f145,f140,f111,f158])).
% 0.22/0.50  fof(f111,plain,(
% 0.22/0.50    spl5_9 <=> m1_pre_topc(sK3,sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.22/0.50  fof(f145,plain,(
% 0.22/0.50    l1_pre_topc(sK3) | (~spl5_9 | ~spl5_15)),
% 0.22/0.50    inference(resolution,[],[f141,f113])).
% 0.22/0.50  fof(f113,plain,(
% 0.22/0.50    m1_pre_topc(sK3,sK0) | ~spl5_9),
% 0.22/0.50    inference(avatar_component_clause,[],[f111])).
% 0.22/0.50  fof(f156,plain,(
% 0.22/0.50    spl5_17 | ~spl5_8 | ~spl5_15),
% 0.22/0.50    inference(avatar_split_clause,[],[f144,f140,f106,f153])).
% 0.22/0.50  fof(f144,plain,(
% 0.22/0.50    l1_pre_topc(sK2) | (~spl5_8 | ~spl5_15)),
% 0.22/0.50    inference(resolution,[],[f141,f108])).
% 0.22/0.50  fof(f151,plain,(
% 0.22/0.50    spl5_16 | ~spl5_7 | ~spl5_15),
% 0.22/0.50    inference(avatar_split_clause,[],[f143,f140,f101,f148])).
% 0.22/0.50  fof(f143,plain,(
% 0.22/0.50    l1_pre_topc(sK1) | (~spl5_7 | ~spl5_15)),
% 0.22/0.50    inference(resolution,[],[f141,f103])).
% 0.22/0.50  fof(f142,plain,(
% 0.22/0.50    spl5_15 | ~spl5_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f138,f81,f140])).
% 0.22/0.50  fof(f138,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_pre_topc(X0,sK0) | l1_pre_topc(X0)) ) | ~spl5_3),
% 0.22/0.50    inference(resolution,[],[f54,f83])).
% 0.22/0.50  fof(f54,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f18])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,axiom,(
% 0.22/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.22/0.50  fof(f137,plain,(
% 0.22/0.50    spl5_13 | spl5_14),
% 0.22/0.50    inference(avatar_split_clause,[],[f50,f134,f130])).
% 0.22/0.50  fof(f50,plain,(
% 0.22/0.50    r1_tsep_1(sK3,sK2) | r1_tsep_1(sK2,sK3)),
% 0.22/0.50    inference(cnf_transformation,[],[f31])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ((((r1_tsep_1(sK3,sK2) | r1_tsep_1(sK2,sK3)) & (~r1_tsep_1(sK3,sK1) | ~r1_tsep_1(sK1,sK3)) & m1_pre_topc(sK1,sK2) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f30,f29,f28,f27])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ? [X1] : (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,sK1) | ~r1_tsep_1(sK1,X3)) & m1_pre_topc(sK1,X2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,sK1) | ~r1_tsep_1(sK1,X3)) & m1_pre_topc(sK1,X2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) => (? [X3] : ((r1_tsep_1(X3,sK2) | r1_tsep_1(sK2,X3)) & (~r1_tsep_1(X3,sK1) | ~r1_tsep_1(sK1,X3)) & m1_pre_topc(sK1,sK2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ? [X3] : ((r1_tsep_1(X3,sK2) | r1_tsep_1(sK2,X3)) & (~r1_tsep_1(X3,sK1) | ~r1_tsep_1(sK1,X3)) & m1_pre_topc(sK1,sK2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) => ((r1_tsep_1(sK3,sK2) | r1_tsep_1(sK2,sK3)) & (~r1_tsep_1(sK3,sK1) | ~r1_tsep_1(sK1,sK3)) & m1_pre_topc(sK1,sK2) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f14])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3))) & m1_pre_topc(X1,X2)) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f12])).
% 0.22/0.50  fof(f12,negated_conjecture,(
% 0.22/0.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | (r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3))))))))),
% 0.22/0.50    inference(negated_conjecture,[],[f11])).
% 0.22/0.50  fof(f11,conjecture,(
% 0.22/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | (r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3))))))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_tmap_1)).
% 0.22/0.50  fof(f128,plain,(
% 0.22/0.50    ~spl5_11 | ~spl5_12),
% 0.22/0.50    inference(avatar_split_clause,[],[f49,f125,f121])).
% 0.22/0.50  fof(f49,plain,(
% 0.22/0.50    ~r1_tsep_1(sK3,sK1) | ~r1_tsep_1(sK1,sK3)),
% 0.22/0.50    inference(cnf_transformation,[],[f31])).
% 0.22/0.50  fof(f119,plain,(
% 0.22/0.50    spl5_10),
% 0.22/0.50    inference(avatar_split_clause,[],[f48,f116])).
% 0.22/0.50  fof(f48,plain,(
% 0.22/0.50    m1_pre_topc(sK1,sK2)),
% 0.22/0.50    inference(cnf_transformation,[],[f31])).
% 0.22/0.50  fof(f114,plain,(
% 0.22/0.50    spl5_9),
% 0.22/0.50    inference(avatar_split_clause,[],[f47,f111])).
% 0.22/0.50  fof(f47,plain,(
% 0.22/0.50    m1_pre_topc(sK3,sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f31])).
% 0.22/0.50  fof(f109,plain,(
% 0.22/0.50    spl5_8),
% 0.22/0.50    inference(avatar_split_clause,[],[f45,f106])).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    m1_pre_topc(sK2,sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f31])).
% 0.22/0.50  fof(f104,plain,(
% 0.22/0.50    spl5_7),
% 0.22/0.50    inference(avatar_split_clause,[],[f43,f101])).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    m1_pre_topc(sK1,sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f31])).
% 0.22/0.50  fof(f84,plain,(
% 0.22/0.50    spl5_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f41,f81])).
% 0.22/0.50  fof(f41,plain,(
% 0.22/0.50    l1_pre_topc(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f31])).
% 0.22/0.50  fof(f79,plain,(
% 0.22/0.50    spl5_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f40,f76])).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    v2_pre_topc(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f31])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (14519)------------------------------
% 0.22/0.50  % (14519)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (14519)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (14519)Memory used [KB]: 6652
% 0.22/0.50  % (14519)Time elapsed: 0.095 s
% 0.22/0.50  % (14519)------------------------------
% 0.22/0.50  % (14519)------------------------------
% 0.22/0.51  % (14536)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.51  % (14532)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.51  % (14516)Success in time 0.149 s
%------------------------------------------------------------------------------
