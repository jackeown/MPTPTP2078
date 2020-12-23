%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:45 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.26s
% Verified   : 
% Statistics : Number of formulae       :  161 ( 460 expanded)
%              Number of leaves         :   42 ( 233 expanded)
%              Depth                    :    9
%              Number of atoms          :  740 (1881 expanded)
%              Number of equality atoms :   60 (  69 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (9929)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
fof(f1400,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f79,f84,f89,f94,f99,f104,f109,f114,f120,f126,f132,f138,f144,f150,f157,f162,f172,f193,f248,f277,f299,f599,f668,f774,f893,f1399])).

fof(f1399,plain,
    ( ~ spl5_123
    | ~ spl5_5
    | spl5_8
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_15
    | ~ spl5_16
    | spl5_92 ),
    inference(avatar_split_clause,[],[f1396,f665,f159,f154,f147,f141,f111,f96,f824])).

fof(f824,plain,
    ( spl5_123
  <=> k7_lattices(sK0,sK2) = k2_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_123])])).

fof(f96,plain,
    ( spl5_5
  <=> l3_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

% (9934)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
fof(f111,plain,
    ( spl5_8
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f141,plain,
    ( spl5_13
  <=> v8_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f147,plain,
    ( spl5_14
  <=> v9_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f154,plain,
    ( spl5_15
  <=> m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f159,plain,
    ( spl5_16
  <=> m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f665,plain,
    ( spl5_92
  <=> r1_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_92])])).

fof(f1396,plain,
    ( k7_lattices(sK0,sK2) != k2_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1))
    | ~ spl5_5
    | spl5_8
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_15
    | ~ spl5_16
    | spl5_92 ),
    inference(unit_resulting_resolution,[],[f113,f143,f149,f98,f161,f156,f667,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k2_lattices(X0,X1,X2) != X1
      | r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_lattices(X0,X1,X2)
                  | k2_lattices(X0,X1,X2) != X1 )
                & ( k2_lattices(X0,X1,X2) = X1
                  | ~ r1_lattices(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k2_lattices(X0,X1,X2) = X1 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k2_lattices(X0,X1,X2) = X1 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_lattices(X0,X1,X2)
              <=> k2_lattices(X0,X1,X2) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_lattices)).

fof(f667,plain,
    ( ~ r1_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1))
    | spl5_92 ),
    inference(avatar_component_clause,[],[f665])).

fof(f156,plain,
    ( m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f154])).

% (9937)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
fof(f161,plain,
    ( m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f159])).

fof(f98,plain,
    ( l3_lattices(sK0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f96])).

fof(f149,plain,
    ( v9_lattices(sK0)
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f147])).

fof(f143,plain,
    ( v8_lattices(sK0)
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f141])).

fof(f113,plain,
    ( ~ v2_struct_0(sK0)
    | spl5_8 ),
    inference(avatar_component_clause,[],[f111])).

fof(f893,plain,
    ( sK1 != k2_lattices(sK0,sK1,sK2)
    | k3_lattices(sK0,sK1,sK2) != k1_lattices(sK0,sK1,sK2)
    | sK2 != k1_lattices(sK0,k2_lattices(sK0,sK1,sK2),sK2)
    | k7_lattices(sK0,k3_lattices(sK0,sK1,sK2)) != k2_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1))
    | k7_lattices(sK0,sK2) = k2_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f774,plain,
    ( spl5_110
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | spl5_8
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_37 ),
    inference(avatar_split_clause,[],[f768,f296,f147,f141,f111,f96,f91,f86,f771])).

fof(f771,plain,
    ( spl5_110
  <=> sK1 = k2_lattices(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_110])])).

fof(f86,plain,
    ( spl5_3
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f91,plain,
    ( spl5_4
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f296,plain,
    ( spl5_37
  <=> r1_lattices(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).

fof(f768,plain,
    ( sK1 = k2_lattices(sK0,sK1,sK2)
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | spl5_8
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_37 ),
    inference(unit_resulting_resolution,[],[f113,f143,f149,f98,f93,f88,f298,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ v9_lattices(X0)
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | k2_lattices(X0,X1,X2) = X1
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f298,plain,
    ( r1_lattices(sK0,sK1,sK2)
    | ~ spl5_37 ),
    inference(avatar_component_clause,[],[f296])).

fof(f88,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f86])).

fof(f93,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f91])).

fof(f668,plain,
    ( ~ spl5_92
    | spl5_1
    | ~ spl5_5
    | spl5_8
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_15
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f501,f159,f154,f147,f141,f135,f111,f96,f76,f665])).

fof(f76,plain,
    ( spl5_1
  <=> r3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f135,plain,
    ( spl5_12
  <=> v6_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f501,plain,
    ( ~ r1_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1))
    | spl5_1
    | ~ spl5_5
    | spl5_8
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_15
    | ~ spl5_16 ),
    inference(unit_resulting_resolution,[],[f113,f137,f143,f149,f98,f156,f78,f161,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ v9_lattices(X0)
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r3_lattices(X0,X1,X2)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_lattices(X0,X1,X2)
          | ~ r1_lattices(X0,X1,X2) )
        & ( r1_lattices(X0,X1,X2)
          | ~ r3_lattices(X0,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_lattices)).

fof(f78,plain,
    ( ~ r3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f76])).

fof(f137,plain,
    ( v6_lattices(sK0)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f135])).

fof(f599,plain,
    ( spl5_79
    | spl5_8
    | ~ spl5_9
    | ~ spl5_12
    | ~ spl5_15
    | ~ spl5_16
    | ~ spl5_28 ),
    inference(avatar_split_clause,[],[f594,f245,f159,f154,f135,f117,f111,f596])).

fof(f596,plain,
    ( spl5_79
  <=> k7_lattices(sK0,k3_lattices(sK0,sK1,sK2)) = k2_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_79])])).

fof(f117,plain,
    ( spl5_9
  <=> l1_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f245,plain,
    ( spl5_28
  <=> k7_lattices(sK0,k3_lattices(sK0,sK1,sK2)) = k4_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f594,plain,
    ( k7_lattices(sK0,k3_lattices(sK0,sK1,sK2)) = k2_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1))
    | spl5_8
    | ~ spl5_9
    | ~ spl5_12
    | ~ spl5_15
    | ~ spl5_16
    | ~ spl5_28 ),
    inference(forward_demodulation,[],[f520,f247])).

fof(f247,plain,
    ( k7_lattices(sK0,k3_lattices(sK0,sK1,sK2)) = k4_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1))
    | ~ spl5_28 ),
    inference(avatar_component_clause,[],[f245])).

fof(f520,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) = k2_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1))
    | spl5_8
    | ~ spl5_9
    | ~ spl5_12
    | ~ spl5_15
    | ~ spl5_16 ),
    inference(unit_resulting_resolution,[],[f113,f137,f119,f156,f161,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_lattices)).

fof(f119,plain,
    ( l1_lattices(sK0)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f117])).

fof(f299,plain,
    ( spl5_37
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | spl5_8
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f292,f147,f141,f135,f111,f96,f91,f86,f81,f296])).

fof(f81,plain,
    ( spl5_2
  <=> r3_lattices(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f292,plain,
    ( r1_lattices(sK0,sK1,sK2)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | spl5_8
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_14 ),
    inference(unit_resulting_resolution,[],[f113,f137,f143,f98,f93,f83,f88,f149,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r1_lattices(X0,X1,X2)
      | ~ r3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f83,plain,
    ( r3_lattices(sK0,sK1,sK2)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f81])).

fof(f277,plain,
    ( spl5_33
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | spl5_8
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f265,f141,f111,f96,f91,f86,f274])).

fof(f274,plain,
    ( spl5_33
  <=> sK2 = k1_lattices(sK0,k2_lattices(sK0,sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).

fof(f265,plain,
    ( sK2 = k1_lattices(sK0,k2_lattices(sK0,sK1,sK2),sK2)
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | spl5_8
    | ~ spl5_13 ),
    inference(unit_resulting_resolution,[],[f113,f98,f88,f93,f143,f62])).

fof(f62,plain,(
    ! [X4,X0,X3] :
      ( ~ v8_lattices(X0)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ( ( v8_lattices(X0)
          | ( sK4(X0) != k1_lattices(X0,k2_lattices(X0,sK3(X0),sK4(X0)),sK4(X0))
            & m1_subset_1(sK4(X0),u1_struct_0(X0))
            & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v8_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f42,f44,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k1_lattices(X0,k2_lattices(X0,sK3(X0),X2),X2) != X2
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k1_lattices(X0,k2_lattices(X0,sK3(X0),X2),X2) != X2
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( sK4(X0) != k1_lattices(X0,k2_lattices(X0,sK3(X0),sK4(X0)),sK4(X0))
        & m1_subset_1(sK4(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( ( ( v8_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v8_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ( ( v8_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v8_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v8_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_lattices)).

fof(f248,plain,
    ( spl5_28
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | spl5_8
    | ~ spl5_17 ),
    inference(avatar_split_clause,[],[f243,f168,f111,f106,f101,f96,f91,f86,f245])).

fof(f101,plain,
    ( spl5_6
  <=> v17_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f106,plain,
    ( spl5_7
  <=> v10_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f168,plain,
    ( spl5_17
  <=> k3_lattices(sK0,sK1,sK2) = k3_lattices(sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f243,plain,
    ( k7_lattices(sK0,k3_lattices(sK0,sK1,sK2)) = k4_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1))
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | spl5_8
    | ~ spl5_17 ),
    inference(forward_demodulation,[],[f235,f170])).

fof(f170,plain,
    ( k3_lattices(sK0,sK1,sK2) = k3_lattices(sK0,sK2,sK1)
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f168])).

fof(f235,plain,
    ( k7_lattices(sK0,k3_lattices(sK0,sK2,sK1)) = k4_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1))
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | spl5_8 ),
    inference(unit_resulting_resolution,[],[f113,f108,f103,f98,f88,f93,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ v17_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | k7_lattices(X0,k3_lattices(X0,X1,X2)) = k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2))
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k7_lattices(X0,k3_lattices(X0,X1,X2)) = k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k7_lattices(X0,k3_lattices(X0,X1,X2)) = k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => k7_lattices(X0,k3_lattices(X0,X1,X2)) = k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_lattices)).

fof(f103,plain,
    ( v17_lattices(sK0)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f101])).

fof(f108,plain,
    ( v10_lattices(sK0)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f106])).

fof(f193,plain,
    ( spl5_20
    | ~ spl5_3
    | ~ spl5_4
    | spl5_8
    | ~ spl5_10
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f174,f129,f123,f111,f91,f86,f190])).

fof(f190,plain,
    ( spl5_20
  <=> k3_lattices(sK0,sK1,sK2) = k1_lattices(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f123,plain,
    ( spl5_10
  <=> l2_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f129,plain,
    ( spl5_11
  <=> v4_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f174,plain,
    ( k3_lattices(sK0,sK1,sK2) = k1_lattices(sK0,sK1,sK2)
    | ~ spl5_3
    | ~ spl5_4
    | spl5_8
    | ~ spl5_10
    | ~ spl5_11 ),
    inference(unit_resulting_resolution,[],[f113,f131,f125,f93,f88,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_lattices)).

fof(f125,plain,
    ( l2_lattices(sK0)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f123])).

fof(f131,plain,
    ( v4_lattices(sK0)
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f129])).

fof(f172,plain,
    ( spl5_17
    | ~ spl5_3
    | ~ spl5_4
    | spl5_8
    | ~ spl5_10
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f164,f129,f123,f111,f91,f86,f168])).

fof(f164,plain,
    ( k3_lattices(sK0,sK1,sK2) = k3_lattices(sK0,sK2,sK1)
    | ~ spl5_3
    | ~ spl5_4
    | spl5_8
    | ~ spl5_10
    | ~ spl5_11 ),
    inference(unit_resulting_resolution,[],[f113,f125,f93,f88,f131,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_lattices)).

fof(f162,plain,
    ( spl5_16
    | ~ spl5_3
    | ~ spl5_5
    | spl5_8 ),
    inference(avatar_split_clause,[],[f151,f111,f96,f86,f159])).

fof(f151,plain,
    ( m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
    | ~ spl5_3
    | ~ spl5_5
    | spl5_8 ),
    inference(unit_resulting_resolution,[],[f113,f98,f88,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_lattices)).

fof(f157,plain,
    ( spl5_15
    | ~ spl5_4
    | ~ spl5_5
    | spl5_8 ),
    inference(avatar_split_clause,[],[f152,f111,f96,f91,f154])).

fof(f152,plain,
    ( m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | ~ spl5_4
    | ~ spl5_5
    | spl5_8 ),
    inference(unit_resulting_resolution,[],[f113,f98,f93,f55])).

fof(f150,plain,
    ( spl5_14
    | ~ spl5_5
    | ~ spl5_7
    | spl5_8 ),
    inference(avatar_split_clause,[],[f145,f111,f106,f96,f147])).

fof(f145,plain,
    ( v9_lattices(sK0)
    | ~ spl5_5
    | ~ spl5_7
    | spl5_8 ),
    inference(unit_resulting_resolution,[],[f98,f113,f108,f74])).

fof(f74,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v7_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).

fof(f144,plain,
    ( spl5_13
    | ~ spl5_5
    | ~ spl5_7
    | spl5_8 ),
    inference(avatar_split_clause,[],[f139,f111,f106,f96,f141])).

fof(f139,plain,
    ( v8_lattices(sK0)
    | ~ spl5_5
    | ~ spl5_7
    | spl5_8 ),
    inference(unit_resulting_resolution,[],[f98,f113,f108,f73])).

fof(f73,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f138,plain,
    ( spl5_12
    | ~ spl5_5
    | ~ spl5_7
    | spl5_8 ),
    inference(avatar_split_clause,[],[f133,f111,f106,f96,f135])).

fof(f133,plain,
    ( v6_lattices(sK0)
    | ~ spl5_5
    | ~ spl5_7
    | spl5_8 ),
    inference(unit_resulting_resolution,[],[f98,f113,f108,f72])).

fof(f72,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f132,plain,
    ( spl5_11
    | ~ spl5_5
    | ~ spl5_7
    | spl5_8 ),
    inference(avatar_split_clause,[],[f127,f111,f106,f96,f129])).

fof(f127,plain,
    ( v4_lattices(sK0)
    | ~ spl5_5
    | ~ spl5_7
    | spl5_8 ),
    inference(unit_resulting_resolution,[],[f98,f113,f108,f71])).

fof(f71,plain,(
    ! [X0] :
      ( v4_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f126,plain,
    ( spl5_10
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f121,f96,f123])).

fof(f121,plain,
    ( l2_lattices(sK0)
    | ~ spl5_5 ),
    inference(unit_resulting_resolution,[],[f98,f69])).

fof(f69,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f120,plain,
    ( spl5_9
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f115,f96,f117])).

fof(f115,plain,
    ( l1_lattices(sK0)
    | ~ spl5_5 ),
    inference(unit_resulting_resolution,[],[f98,f68])).

% (9940)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
fof(f68,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f114,plain,(
    ~ spl5_8 ),
    inference(avatar_split_clause,[],[f47,f111])).

fof(f47,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( ~ r3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1))
    & r3_lattices(sK0,sK1,sK2)
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l3_lattices(sK0)
    & v17_lattices(sK0)
    & v10_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f38,f37,f36])).

fof(f36,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1))
                & r3_lattices(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r3_lattices(sK0,k7_lattices(sK0,X2),k7_lattices(sK0,X1))
              & r3_lattices(sK0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l3_lattices(sK0)
      & v17_lattices(sK0)
      & v10_lattices(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

% (9941)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
fof(f37,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r3_lattices(sK0,k7_lattices(sK0,X2),k7_lattices(sK0,X1))
            & r3_lattices(sK0,X1,X2)
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ~ r3_lattices(sK0,k7_lattices(sK0,X2),k7_lattices(sK0,sK1))
          & r3_lattices(sK0,sK1,X2)
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X2] :
        ( ~ r3_lattices(sK0,k7_lattices(sK0,X2),k7_lattices(sK0,sK1))
        & r3_lattices(sK0,sK1,X2)
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ~ r3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1))
      & r3_lattices(sK0,sK1,sK2)
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1))
              & r3_lattices(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v17_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

% (9947)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% (9936)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1))
              & r3_lattices(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v17_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v17_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r3_lattices(X0,X1,X2)
                 => r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r3_lattices(X0,X1,X2)
               => r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_lattices)).

fof(f109,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f48,f106])).

% (9938)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
fof(f48,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f104,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f49,f101])).

fof(f49,plain,(
    v17_lattices(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f99,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f50,f96])).

fof(f50,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f94,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f51,f91])).

fof(f51,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f39])).

fof(f89,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f52,f86])).

fof(f52,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f39])).

fof(f84,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f53,f81])).

fof(f53,plain,(
    r3_lattices(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f79,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f54,f76])).

fof(f54,plain,(
    ~ r3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) ),
    inference(cnf_transformation,[],[f39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n021.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 20:56:49 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.21/0.47  % (9931)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.48  % (9943)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.21/0.50  % (9933)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.21/0.50  % (9944)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.21/0.50  % (9932)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (9945)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.21/0.50  % (9928)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.50  % (9927)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.50  % (9928)Refutation not found, incomplete strategy% (9928)------------------------------
% 0.21/0.50  % (9928)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (9928)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (9928)Memory used [KB]: 10618
% 0.21/0.50  % (9928)Time elapsed: 0.093 s
% 0.21/0.50  % (9928)------------------------------
% 0.21/0.50  % (9928)------------------------------
% 0.21/0.51  % (9925)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.51  % (9931)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % (9926)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.52  % (9935)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.21/0.52  % (9942)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  % (9929)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.52  fof(f1400,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f79,f84,f89,f94,f99,f104,f109,f114,f120,f126,f132,f138,f144,f150,f157,f162,f172,f193,f248,f277,f299,f599,f668,f774,f893,f1399])).
% 0.21/0.52  fof(f1399,plain,(
% 0.21/0.52    ~spl5_123 | ~spl5_5 | spl5_8 | ~spl5_13 | ~spl5_14 | ~spl5_15 | ~spl5_16 | spl5_92),
% 0.21/0.52    inference(avatar_split_clause,[],[f1396,f665,f159,f154,f147,f141,f111,f96,f824])).
% 1.26/0.52  fof(f824,plain,(
% 1.26/0.52    spl5_123 <=> k7_lattices(sK0,sK2) = k2_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1))),
% 1.26/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_123])])).
% 1.26/0.52  fof(f96,plain,(
% 1.26/0.52    spl5_5 <=> l3_lattices(sK0)),
% 1.26/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.26/0.52  % (9934)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 1.26/0.52  fof(f111,plain,(
% 1.26/0.52    spl5_8 <=> v2_struct_0(sK0)),
% 1.26/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 1.26/0.52  fof(f141,plain,(
% 1.26/0.52    spl5_13 <=> v8_lattices(sK0)),
% 1.26/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 1.26/0.52  fof(f147,plain,(
% 1.26/0.52    spl5_14 <=> v9_lattices(sK0)),
% 1.26/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 1.26/0.52  fof(f154,plain,(
% 1.26/0.52    spl5_15 <=> m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))),
% 1.26/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 1.26/0.52  fof(f159,plain,(
% 1.26/0.52    spl5_16 <=> m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))),
% 1.26/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 1.26/0.52  fof(f665,plain,(
% 1.26/0.52    spl5_92 <=> r1_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1))),
% 1.26/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_92])])).
% 1.26/0.52  fof(f1396,plain,(
% 1.26/0.52    k7_lattices(sK0,sK2) != k2_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) | (~spl5_5 | spl5_8 | ~spl5_13 | ~spl5_14 | ~spl5_15 | ~spl5_16 | spl5_92)),
% 1.26/0.52    inference(unit_resulting_resolution,[],[f113,f143,f149,f98,f161,f156,f667,f67])).
% 1.26/0.52  fof(f67,plain,(
% 1.26/0.52    ( ! [X2,X0,X1] : (k2_lattices(X0,X1,X2) != X1 | r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)) )),
% 1.26/0.52    inference(cnf_transformation,[],[f46])).
% 1.26/0.52  fof(f46,plain,(
% 1.26/0.52    ! [X0] : (! [X1] : (! [X2] : (((r1_lattices(X0,X1,X2) | k2_lattices(X0,X1,X2) != X1) & (k2_lattices(X0,X1,X2) = X1 | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 1.26/0.52    inference(nnf_transformation,[],[f32])).
% 1.26/0.52  fof(f32,plain,(
% 1.26/0.52    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 1.26/0.52    inference(flattening,[],[f31])).
% 1.26/0.52  fof(f31,plain,(
% 1.26/0.52    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)))),
% 1.26/0.52    inference(ennf_transformation,[],[f9])).
% 1.26/0.52  fof(f9,axiom,(
% 1.26/0.52    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1))))),
% 1.26/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_lattices)).
% 1.26/0.52  fof(f667,plain,(
% 1.26/0.52    ~r1_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) | spl5_92),
% 1.26/0.52    inference(avatar_component_clause,[],[f665])).
% 1.26/0.52  fof(f156,plain,(
% 1.26/0.52    m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0)) | ~spl5_15),
% 1.26/0.52    inference(avatar_component_clause,[],[f154])).
% 1.26/0.52  % (9937)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 1.26/0.52  fof(f161,plain,(
% 1.26/0.52    m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0)) | ~spl5_16),
% 1.26/0.52    inference(avatar_component_clause,[],[f159])).
% 1.26/0.52  fof(f98,plain,(
% 1.26/0.52    l3_lattices(sK0) | ~spl5_5),
% 1.26/0.52    inference(avatar_component_clause,[],[f96])).
% 1.26/0.52  fof(f149,plain,(
% 1.26/0.52    v9_lattices(sK0) | ~spl5_14),
% 1.26/0.52    inference(avatar_component_clause,[],[f147])).
% 1.26/0.52  fof(f143,plain,(
% 1.26/0.52    v8_lattices(sK0) | ~spl5_13),
% 1.26/0.52    inference(avatar_component_clause,[],[f141])).
% 1.26/0.52  fof(f113,plain,(
% 1.26/0.52    ~v2_struct_0(sK0) | spl5_8),
% 1.26/0.52    inference(avatar_component_clause,[],[f111])).
% 1.26/0.52  fof(f893,plain,(
% 1.26/0.52    sK1 != k2_lattices(sK0,sK1,sK2) | k3_lattices(sK0,sK1,sK2) != k1_lattices(sK0,sK1,sK2) | sK2 != k1_lattices(sK0,k2_lattices(sK0,sK1,sK2),sK2) | k7_lattices(sK0,k3_lattices(sK0,sK1,sK2)) != k2_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) | k7_lattices(sK0,sK2) = k2_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1))),
% 1.26/0.52    introduced(theory_tautology_sat_conflict,[])).
% 1.26/0.52  fof(f774,plain,(
% 1.26/0.52    spl5_110 | ~spl5_3 | ~spl5_4 | ~spl5_5 | spl5_8 | ~spl5_13 | ~spl5_14 | ~spl5_37),
% 1.26/0.52    inference(avatar_split_clause,[],[f768,f296,f147,f141,f111,f96,f91,f86,f771])).
% 1.26/0.52  fof(f771,plain,(
% 1.26/0.52    spl5_110 <=> sK1 = k2_lattices(sK0,sK1,sK2)),
% 1.26/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_110])])).
% 1.26/0.52  fof(f86,plain,(
% 1.26/0.52    spl5_3 <=> m1_subset_1(sK2,u1_struct_0(sK0))),
% 1.26/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.26/0.52  fof(f91,plain,(
% 1.26/0.52    spl5_4 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 1.26/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.26/0.52  fof(f296,plain,(
% 1.26/0.52    spl5_37 <=> r1_lattices(sK0,sK1,sK2)),
% 1.26/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).
% 1.26/0.52  fof(f768,plain,(
% 1.26/0.52    sK1 = k2_lattices(sK0,sK1,sK2) | (~spl5_3 | ~spl5_4 | ~spl5_5 | spl5_8 | ~spl5_13 | ~spl5_14 | ~spl5_37)),
% 1.26/0.52    inference(unit_resulting_resolution,[],[f113,f143,f149,f98,f93,f88,f298,f66])).
% 1.26/0.52  fof(f66,plain,(
% 1.26/0.52    ( ! [X2,X0,X1] : (~v9_lattices(X0) | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | k2_lattices(X0,X1,X2) = X1 | ~v8_lattices(X0) | v2_struct_0(X0)) )),
% 1.26/0.52    inference(cnf_transformation,[],[f46])).
% 1.26/0.52  fof(f298,plain,(
% 1.26/0.52    r1_lattices(sK0,sK1,sK2) | ~spl5_37),
% 1.26/0.52    inference(avatar_component_clause,[],[f296])).
% 1.26/0.52  fof(f88,plain,(
% 1.26/0.52    m1_subset_1(sK2,u1_struct_0(sK0)) | ~spl5_3),
% 1.26/0.52    inference(avatar_component_clause,[],[f86])).
% 1.26/0.52  fof(f93,plain,(
% 1.26/0.52    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl5_4),
% 1.26/0.52    inference(avatar_component_clause,[],[f91])).
% 1.26/0.52  fof(f668,plain,(
% 1.26/0.52    ~spl5_92 | spl5_1 | ~spl5_5 | spl5_8 | ~spl5_12 | ~spl5_13 | ~spl5_14 | ~spl5_15 | ~spl5_16),
% 1.26/0.52    inference(avatar_split_clause,[],[f501,f159,f154,f147,f141,f135,f111,f96,f76,f665])).
% 1.26/0.52  fof(f76,plain,(
% 1.26/0.52    spl5_1 <=> r3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1))),
% 1.26/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.26/0.52  fof(f135,plain,(
% 1.26/0.52    spl5_12 <=> v6_lattices(sK0)),
% 1.26/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 1.26/0.52  fof(f501,plain,(
% 1.26/0.52    ~r1_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) | (spl5_1 | ~spl5_5 | spl5_8 | ~spl5_12 | ~spl5_13 | ~spl5_14 | ~spl5_15 | ~spl5_16)),
% 1.26/0.52    inference(unit_resulting_resolution,[],[f113,f137,f143,f149,f98,f156,f78,f161,f58])).
% 1.26/0.52  fof(f58,plain,(
% 1.26/0.52    ( ! [X2,X0,X1] : (~v9_lattices(X0) | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | r3_lattices(X0,X1,X2) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 1.26/0.52    inference(cnf_transformation,[],[f40])).
% 1.26/0.52  fof(f40,plain,(
% 1.26/0.52    ! [X0,X1,X2] : (((r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2)) & (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 1.26/0.52    inference(nnf_transformation,[],[f22])).
% 1.26/0.52  fof(f22,plain,(
% 1.26/0.52    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 1.26/0.52    inference(flattening,[],[f21])).
% 1.26/0.52  fof(f21,plain,(
% 1.26/0.52    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 1.26/0.52    inference(ennf_transformation,[],[f8])).
% 1.26/0.52  fof(f8,axiom,(
% 1.26/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)))),
% 1.26/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_lattices)).
% 1.26/0.52  fof(f78,plain,(
% 1.26/0.52    ~r3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) | spl5_1),
% 1.26/0.52    inference(avatar_component_clause,[],[f76])).
% 1.26/0.52  fof(f137,plain,(
% 1.26/0.52    v6_lattices(sK0) | ~spl5_12),
% 1.26/0.52    inference(avatar_component_clause,[],[f135])).
% 1.26/0.52  fof(f599,plain,(
% 1.26/0.52    spl5_79 | spl5_8 | ~spl5_9 | ~spl5_12 | ~spl5_15 | ~spl5_16 | ~spl5_28),
% 1.26/0.52    inference(avatar_split_clause,[],[f594,f245,f159,f154,f135,f117,f111,f596])).
% 1.26/0.52  fof(f596,plain,(
% 1.26/0.52    spl5_79 <=> k7_lattices(sK0,k3_lattices(sK0,sK1,sK2)) = k2_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1))),
% 1.26/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_79])])).
% 1.26/0.52  fof(f117,plain,(
% 1.26/0.52    spl5_9 <=> l1_lattices(sK0)),
% 1.26/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 1.26/0.52  fof(f245,plain,(
% 1.26/0.52    spl5_28 <=> k7_lattices(sK0,k3_lattices(sK0,sK1,sK2)) = k4_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1))),
% 1.26/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).
% 1.26/0.52  fof(f594,plain,(
% 1.26/0.52    k7_lattices(sK0,k3_lattices(sK0,sK1,sK2)) = k2_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) | (spl5_8 | ~spl5_9 | ~spl5_12 | ~spl5_15 | ~spl5_16 | ~spl5_28)),
% 1.26/0.52    inference(forward_demodulation,[],[f520,f247])).
% 1.26/0.52  fof(f247,plain,(
% 1.26/0.52    k7_lattices(sK0,k3_lattices(sK0,sK1,sK2)) = k4_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) | ~spl5_28),
% 1.26/0.52    inference(avatar_component_clause,[],[f245])).
% 1.26/0.52  fof(f520,plain,(
% 1.26/0.52    k4_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) = k2_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) | (spl5_8 | ~spl5_9 | ~spl5_12 | ~spl5_15 | ~spl5_16)),
% 1.26/0.52    inference(unit_resulting_resolution,[],[f113,f137,f119,f156,f161,f61])).
% 1.26/0.52  fof(f61,plain,(
% 1.26/0.52    ( ! [X2,X0,X1] : (k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 1.26/0.52    inference(cnf_transformation,[],[f28])).
% 1.26/0.52  fof(f28,plain,(
% 1.26/0.52    ! [X0,X1,X2] : (k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 1.26/0.52    inference(flattening,[],[f27])).
% 1.26/0.52  fof(f27,plain,(
% 1.26/0.52    ! [X0,X1,X2] : (k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 1.26/0.52    inference(ennf_transformation,[],[f7])).
% 1.26/0.52  fof(f7,axiom,(
% 1.26/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2))),
% 1.26/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_lattices)).
% 1.26/0.52  fof(f119,plain,(
% 1.26/0.52    l1_lattices(sK0) | ~spl5_9),
% 1.26/0.52    inference(avatar_component_clause,[],[f117])).
% 1.26/0.52  fof(f299,plain,(
% 1.26/0.52    spl5_37 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | spl5_8 | ~spl5_12 | ~spl5_13 | ~spl5_14),
% 1.26/0.52    inference(avatar_split_clause,[],[f292,f147,f141,f135,f111,f96,f91,f86,f81,f296])).
% 1.26/0.52  fof(f81,plain,(
% 1.26/0.52    spl5_2 <=> r3_lattices(sK0,sK1,sK2)),
% 1.26/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.26/0.52  fof(f292,plain,(
% 1.26/0.52    r1_lattices(sK0,sK1,sK2) | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | spl5_8 | ~spl5_12 | ~spl5_13 | ~spl5_14)),
% 1.26/0.52    inference(unit_resulting_resolution,[],[f113,f137,f143,f98,f93,f83,f88,f149,f57])).
% 1.26/0.52  fof(f57,plain,(
% 1.26/0.52    ( ! [X2,X0,X1] : (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 1.26/0.52    inference(cnf_transformation,[],[f40])).
% 1.26/0.52  fof(f83,plain,(
% 1.26/0.52    r3_lattices(sK0,sK1,sK2) | ~spl5_2),
% 1.26/0.52    inference(avatar_component_clause,[],[f81])).
% 1.26/0.52  fof(f277,plain,(
% 1.26/0.52    spl5_33 | ~spl5_3 | ~spl5_4 | ~spl5_5 | spl5_8 | ~spl5_13),
% 1.26/0.52    inference(avatar_split_clause,[],[f265,f141,f111,f96,f91,f86,f274])).
% 1.26/0.52  fof(f274,plain,(
% 1.26/0.52    spl5_33 <=> sK2 = k1_lattices(sK0,k2_lattices(sK0,sK1,sK2),sK2)),
% 1.26/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).
% 1.26/0.52  fof(f265,plain,(
% 1.26/0.52    sK2 = k1_lattices(sK0,k2_lattices(sK0,sK1,sK2),sK2) | (~spl5_3 | ~spl5_4 | ~spl5_5 | spl5_8 | ~spl5_13)),
% 1.26/0.52    inference(unit_resulting_resolution,[],[f113,f98,f88,f93,f143,f62])).
% 1.26/0.52  fof(f62,plain,(
% 1.26/0.52    ( ! [X4,X0,X3] : (~v8_lattices(X0) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.26/0.52    inference(cnf_transformation,[],[f45])).
% 1.26/0.52  fof(f45,plain,(
% 1.26/0.52    ! [X0] : (((v8_lattices(X0) | ((sK4(X0) != k1_lattices(X0,k2_lattices(X0,sK3(X0),sK4(X0)),sK4(X0)) & m1_subset_1(sK4(X0),u1_struct_0(X0))) & m1_subset_1(sK3(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.26/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f42,f44,f43])).
% 1.26/0.52  fof(f43,plain,(
% 1.26/0.52    ! [X0] : (? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k1_lattices(X0,k2_lattices(X0,sK3(X0),X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK3(X0),u1_struct_0(X0))))),
% 1.26/0.52    introduced(choice_axiom,[])).
% 1.26/0.52  fof(f44,plain,(
% 1.26/0.52    ! [X0] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,sK3(X0),X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) => (sK4(X0) != k1_lattices(X0,k2_lattices(X0,sK3(X0),sK4(X0)),sK4(X0)) & m1_subset_1(sK4(X0),u1_struct_0(X0))))),
% 1.26/0.52    introduced(choice_axiom,[])).
% 1.26/0.52  fof(f42,plain,(
% 1.26/0.52    ! [X0] : (((v8_lattices(X0) | ? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.26/0.52    inference(rectify,[],[f41])).
% 1.26/0.52  fof(f41,plain,(
% 1.26/0.52    ! [X0] : (((v8_lattices(X0) | ? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.26/0.52    inference(nnf_transformation,[],[f30])).
% 1.26/0.52  fof(f30,plain,(
% 1.26/0.52    ! [X0] : ((v8_lattices(X0) <=> ! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.26/0.52    inference(flattening,[],[f29])).
% 1.26/0.52  fof(f29,plain,(
% 1.26/0.52    ! [X0] : ((v8_lattices(X0) <=> ! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 1.26/0.52    inference(ennf_transformation,[],[f3])).
% 1.26/0.52  fof(f3,axiom,(
% 1.26/0.52    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v8_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2))))),
% 1.26/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_lattices)).
% 1.26/0.52  fof(f248,plain,(
% 1.26/0.52    spl5_28 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_7 | spl5_8 | ~spl5_17),
% 1.26/0.52    inference(avatar_split_clause,[],[f243,f168,f111,f106,f101,f96,f91,f86,f245])).
% 1.26/0.52  fof(f101,plain,(
% 1.26/0.52    spl5_6 <=> v17_lattices(sK0)),
% 1.26/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 1.26/0.52  fof(f106,plain,(
% 1.26/0.52    spl5_7 <=> v10_lattices(sK0)),
% 1.26/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 1.26/0.52  fof(f168,plain,(
% 1.26/0.52    spl5_17 <=> k3_lattices(sK0,sK1,sK2) = k3_lattices(sK0,sK2,sK1)),
% 1.26/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 1.26/0.52  fof(f243,plain,(
% 1.26/0.52    k7_lattices(sK0,k3_lattices(sK0,sK1,sK2)) = k4_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) | (~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_7 | spl5_8 | ~spl5_17)),
% 1.26/0.52    inference(forward_demodulation,[],[f235,f170])).
% 1.26/0.52  fof(f170,plain,(
% 1.26/0.52    k3_lattices(sK0,sK1,sK2) = k3_lattices(sK0,sK2,sK1) | ~spl5_17),
% 1.26/0.52    inference(avatar_component_clause,[],[f168])).
% 1.26/0.52  fof(f235,plain,(
% 1.26/0.52    k7_lattices(sK0,k3_lattices(sK0,sK2,sK1)) = k4_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) | (~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_7 | spl5_8)),
% 1.26/0.52    inference(unit_resulting_resolution,[],[f113,f108,f103,f98,f88,f93,f56])).
% 1.26/0.52  fof(f56,plain,(
% 1.26/0.52    ( ! [X2,X0,X1] : (~v17_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | k7_lattices(X0,k3_lattices(X0,X1,X2)) = k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 1.26/0.52    inference(cnf_transformation,[],[f20])).
% 1.26/0.52  fof(f20,plain,(
% 1.26/0.52    ! [X0] : (! [X1] : (! [X2] : (k7_lattices(X0,k3_lattices(X0,X1,X2)) = k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 1.26/0.52    inference(flattening,[],[f19])).
% 1.26/0.52  fof(f19,plain,(
% 1.26/0.52    ! [X0] : (! [X1] : (! [X2] : (k7_lattices(X0,k3_lattices(X0,X1,X2)) = k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 1.26/0.52    inference(ennf_transformation,[],[f10])).
% 1.26/0.52  fof(f10,axiom,(
% 1.26/0.52    ! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k7_lattices(X0,k3_lattices(X0,X1,X2)) = k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)))))),
% 1.26/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_lattices)).
% 1.26/0.52  fof(f103,plain,(
% 1.26/0.52    v17_lattices(sK0) | ~spl5_6),
% 1.26/0.52    inference(avatar_component_clause,[],[f101])).
% 1.26/0.52  fof(f108,plain,(
% 1.26/0.52    v10_lattices(sK0) | ~spl5_7),
% 1.26/0.52    inference(avatar_component_clause,[],[f106])).
% 1.26/0.52  fof(f193,plain,(
% 1.26/0.52    spl5_20 | ~spl5_3 | ~spl5_4 | spl5_8 | ~spl5_10 | ~spl5_11),
% 1.26/0.52    inference(avatar_split_clause,[],[f174,f129,f123,f111,f91,f86,f190])).
% 1.26/0.52  fof(f190,plain,(
% 1.26/0.52    spl5_20 <=> k3_lattices(sK0,sK1,sK2) = k1_lattices(sK0,sK1,sK2)),
% 1.26/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 1.26/0.52  fof(f123,plain,(
% 1.26/0.52    spl5_10 <=> l2_lattices(sK0)),
% 1.26/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 1.26/0.52  fof(f129,plain,(
% 1.26/0.52    spl5_11 <=> v4_lattices(sK0)),
% 1.26/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 1.26/0.52  fof(f174,plain,(
% 1.26/0.52    k3_lattices(sK0,sK1,sK2) = k1_lattices(sK0,sK1,sK2) | (~spl5_3 | ~spl5_4 | spl5_8 | ~spl5_10 | ~spl5_11)),
% 1.26/0.52    inference(unit_resulting_resolution,[],[f113,f131,f125,f93,f88,f60])).
% 1.26/0.52  fof(f60,plain,(
% 1.26/0.52    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)) )),
% 1.26/0.52    inference(cnf_transformation,[],[f26])).
% 1.26/0.52  fof(f26,plain,(
% 1.26/0.52    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 1.26/0.52    inference(flattening,[],[f25])).
% 1.26/0.52  fof(f25,plain,(
% 1.26/0.52    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 1.26/0.52    inference(ennf_transformation,[],[f6])).
% 1.26/0.52  fof(f6,axiom,(
% 1.26/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2))),
% 1.26/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_lattices)).
% 1.26/0.52  fof(f125,plain,(
% 1.26/0.52    l2_lattices(sK0) | ~spl5_10),
% 1.26/0.52    inference(avatar_component_clause,[],[f123])).
% 1.26/0.52  fof(f131,plain,(
% 1.26/0.52    v4_lattices(sK0) | ~spl5_11),
% 1.26/0.52    inference(avatar_component_clause,[],[f129])).
% 1.26/0.52  fof(f172,plain,(
% 1.26/0.52    spl5_17 | ~spl5_3 | ~spl5_4 | spl5_8 | ~spl5_10 | ~spl5_11),
% 1.26/0.52    inference(avatar_split_clause,[],[f164,f129,f123,f111,f91,f86,f168])).
% 1.26/0.52  fof(f164,plain,(
% 1.26/0.52    k3_lattices(sK0,sK1,sK2) = k3_lattices(sK0,sK2,sK1) | (~spl5_3 | ~spl5_4 | spl5_8 | ~spl5_10 | ~spl5_11)),
% 1.26/0.52    inference(unit_resulting_resolution,[],[f113,f125,f93,f88,f131,f59])).
% 1.26/0.52  fof(f59,plain,(
% 1.26/0.52    ( ! [X2,X0,X1] : (k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)) )),
% 1.26/0.52    inference(cnf_transformation,[],[f24])).
% 1.26/0.52  fof(f24,plain,(
% 1.26/0.52    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 1.26/0.52    inference(flattening,[],[f23])).
% 1.26/0.52  fof(f23,plain,(
% 1.26/0.52    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 1.26/0.52    inference(ennf_transformation,[],[f2])).
% 1.26/0.52  fof(f2,axiom,(
% 1.26/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1))),
% 1.26/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_lattices)).
% 1.26/0.52  fof(f162,plain,(
% 1.26/0.52    spl5_16 | ~spl5_3 | ~spl5_5 | spl5_8),
% 1.26/0.52    inference(avatar_split_clause,[],[f151,f111,f96,f86,f159])).
% 1.26/0.52  fof(f151,plain,(
% 1.26/0.52    m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0)) | (~spl5_3 | ~spl5_5 | spl5_8)),
% 1.26/0.52    inference(unit_resulting_resolution,[],[f113,f98,f88,f55])).
% 1.26/0.52  fof(f55,plain,(
% 1.26/0.52    ( ! [X0,X1] : (m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.26/0.52    inference(cnf_transformation,[],[f18])).
% 1.26/0.52  fof(f18,plain,(
% 1.26/0.52    ! [X0,X1] : (m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.26/0.52    inference(flattening,[],[f17])).
% 1.26/0.52  fof(f17,plain,(
% 1.26/0.52    ! [X0,X1] : (m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)))),
% 1.26/0.52    inference(ennf_transformation,[],[f4])).
% 1.26/0.52  fof(f4,axiom,(
% 1.26/0.52    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)))),
% 1.26/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_lattices)).
% 1.26/0.52  fof(f157,plain,(
% 1.26/0.52    spl5_15 | ~spl5_4 | ~spl5_5 | spl5_8),
% 1.26/0.52    inference(avatar_split_clause,[],[f152,f111,f96,f91,f154])).
% 1.26/0.52  fof(f152,plain,(
% 1.26/0.52    m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0)) | (~spl5_4 | ~spl5_5 | spl5_8)),
% 1.26/0.52    inference(unit_resulting_resolution,[],[f113,f98,f93,f55])).
% 1.26/0.52  fof(f150,plain,(
% 1.26/0.52    spl5_14 | ~spl5_5 | ~spl5_7 | spl5_8),
% 1.26/0.52    inference(avatar_split_clause,[],[f145,f111,f106,f96,f147])).
% 1.26/0.52  fof(f145,plain,(
% 1.26/0.52    v9_lattices(sK0) | (~spl5_5 | ~spl5_7 | spl5_8)),
% 1.26/0.52    inference(unit_resulting_resolution,[],[f98,f113,f108,f74])).
% 1.26/0.52  fof(f74,plain,(
% 1.26/0.52    ( ! [X0] : (v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.26/0.52    inference(cnf_transformation,[],[f35])).
% 1.26/0.52  fof(f35,plain,(
% 1.26/0.52    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 1.26/0.52    inference(flattening,[],[f34])).
% 1.26/0.52  fof(f34,plain,(
% 1.26/0.52    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 1.26/0.52    inference(ennf_transformation,[],[f14])).
% 1.26/0.52  fof(f14,plain,(
% 1.26/0.52    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 1.26/0.52    inference(pure_predicate_removal,[],[f13])).
% 1.26/0.52  fof(f13,plain,(
% 1.26/0.52    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 1.26/0.52    inference(pure_predicate_removal,[],[f1])).
% 1.26/0.52  fof(f1,axiom,(
% 1.26/0.52    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 1.26/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).
% 1.26/0.52  fof(f144,plain,(
% 1.26/0.52    spl5_13 | ~spl5_5 | ~spl5_7 | spl5_8),
% 1.26/0.52    inference(avatar_split_clause,[],[f139,f111,f106,f96,f141])).
% 1.26/0.52  fof(f139,plain,(
% 1.26/0.52    v8_lattices(sK0) | (~spl5_5 | ~spl5_7 | spl5_8)),
% 1.26/0.52    inference(unit_resulting_resolution,[],[f98,f113,f108,f73])).
% 1.26/0.52  fof(f73,plain,(
% 1.26/0.52    ( ! [X0] : (v8_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.26/0.52    inference(cnf_transformation,[],[f35])).
% 1.26/0.52  fof(f138,plain,(
% 1.26/0.52    spl5_12 | ~spl5_5 | ~spl5_7 | spl5_8),
% 1.26/0.52    inference(avatar_split_clause,[],[f133,f111,f106,f96,f135])).
% 1.26/0.52  fof(f133,plain,(
% 1.26/0.52    v6_lattices(sK0) | (~spl5_5 | ~spl5_7 | spl5_8)),
% 1.26/0.52    inference(unit_resulting_resolution,[],[f98,f113,f108,f72])).
% 1.26/0.52  fof(f72,plain,(
% 1.26/0.52    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.26/0.52    inference(cnf_transformation,[],[f35])).
% 1.26/0.52  fof(f132,plain,(
% 1.26/0.52    spl5_11 | ~spl5_5 | ~spl5_7 | spl5_8),
% 1.26/0.52    inference(avatar_split_clause,[],[f127,f111,f106,f96,f129])).
% 1.26/0.52  fof(f127,plain,(
% 1.26/0.52    v4_lattices(sK0) | (~spl5_5 | ~spl5_7 | spl5_8)),
% 1.26/0.52    inference(unit_resulting_resolution,[],[f98,f113,f108,f71])).
% 1.26/0.52  fof(f71,plain,(
% 1.26/0.52    ( ! [X0] : (v4_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.26/0.52    inference(cnf_transformation,[],[f35])).
% 1.26/0.52  fof(f126,plain,(
% 1.26/0.52    spl5_10 | ~spl5_5),
% 1.26/0.52    inference(avatar_split_clause,[],[f121,f96,f123])).
% 1.26/0.52  fof(f121,plain,(
% 1.26/0.52    l2_lattices(sK0) | ~spl5_5),
% 1.26/0.52    inference(unit_resulting_resolution,[],[f98,f69])).
% 1.26/0.52  fof(f69,plain,(
% 1.26/0.52    ( ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0)) )),
% 1.26/0.52    inference(cnf_transformation,[],[f33])).
% 1.26/0.52  fof(f33,plain,(
% 1.26/0.52    ! [X0] : ((l2_lattices(X0) & l1_lattices(X0)) | ~l3_lattices(X0))),
% 1.26/0.52    inference(ennf_transformation,[],[f5])).
% 1.26/0.52  fof(f5,axiom,(
% 1.26/0.52    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 1.26/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).
% 1.26/0.52  fof(f120,plain,(
% 1.26/0.52    spl5_9 | ~spl5_5),
% 1.26/0.52    inference(avatar_split_clause,[],[f115,f96,f117])).
% 1.26/0.52  fof(f115,plain,(
% 1.26/0.52    l1_lattices(sK0) | ~spl5_5),
% 1.26/0.52    inference(unit_resulting_resolution,[],[f98,f68])).
% 1.26/0.52  % (9940)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 1.26/0.52  fof(f68,plain,(
% 1.26/0.52    ( ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0)) )),
% 1.26/0.52    inference(cnf_transformation,[],[f33])).
% 1.26/0.52  fof(f114,plain,(
% 1.26/0.52    ~spl5_8),
% 1.26/0.52    inference(avatar_split_clause,[],[f47,f111])).
% 1.26/0.52  fof(f47,plain,(
% 1.26/0.52    ~v2_struct_0(sK0)),
% 1.26/0.52    inference(cnf_transformation,[],[f39])).
% 1.26/0.52  fof(f39,plain,(
% 1.26/0.52    ((~r3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) & r3_lattices(sK0,sK1,sK2) & m1_subset_1(sK2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l3_lattices(sK0) & v17_lattices(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0)),
% 1.26/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f38,f37,f36])).
% 1.26/0.52  fof(f36,plain,(
% 1.26/0.52    ? [X0] : (? [X1] : (? [X2] : (~r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1)) & r3_lattices(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (~r3_lattices(sK0,k7_lattices(sK0,X2),k7_lattices(sK0,X1)) & r3_lattices(sK0,X1,X2) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) & l3_lattices(sK0) & v17_lattices(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0))),
% 1.26/0.52    introduced(choice_axiom,[])).
% 1.26/0.52  % (9941)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 1.26/0.52  fof(f37,plain,(
% 1.26/0.52    ? [X1] : (? [X2] : (~r3_lattices(sK0,k7_lattices(sK0,X2),k7_lattices(sK0,X1)) & r3_lattices(sK0,X1,X2) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : (~r3_lattices(sK0,k7_lattices(sK0,X2),k7_lattices(sK0,sK1)) & r3_lattices(sK0,sK1,X2) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 1.26/0.52    introduced(choice_axiom,[])).
% 1.26/0.52  fof(f38,plain,(
% 1.26/0.52    ? [X2] : (~r3_lattices(sK0,k7_lattices(sK0,X2),k7_lattices(sK0,sK1)) & r3_lattices(sK0,sK1,X2) & m1_subset_1(X2,u1_struct_0(sK0))) => (~r3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) & r3_lattices(sK0,sK1,sK2) & m1_subset_1(sK2,u1_struct_0(sK0)))),
% 1.26/0.52    introduced(choice_axiom,[])).
% 1.26/0.52  fof(f16,plain,(
% 1.26/0.52    ? [X0] : (? [X1] : (? [X2] : (~r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1)) & r3_lattices(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 1.26/0.52    inference(flattening,[],[f15])).
% 1.26/0.53  % (9947)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 1.26/0.53  % (9936)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 1.26/0.53  fof(f15,plain,(
% 1.26/0.53    ? [X0] : (? [X1] : (? [X2] : ((~r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1)) & r3_lattices(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 1.26/0.53    inference(ennf_transformation,[],[f12])).
% 1.26/0.53  fof(f12,negated_conjecture,(
% 1.26/0.53    ~! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_lattices(X0,X1,X2) => r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1))))))),
% 1.26/0.53    inference(negated_conjecture,[],[f11])).
% 1.26/0.53  fof(f11,conjecture,(
% 1.26/0.53    ! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_lattices(X0,X1,X2) => r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1))))))),
% 1.26/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_lattices)).
% 1.26/0.53  fof(f109,plain,(
% 1.26/0.53    spl5_7),
% 1.26/0.53    inference(avatar_split_clause,[],[f48,f106])).
% 1.26/0.53  % (9938)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 1.26/0.53  fof(f48,plain,(
% 1.26/0.53    v10_lattices(sK0)),
% 1.26/0.53    inference(cnf_transformation,[],[f39])).
% 1.26/0.53  fof(f104,plain,(
% 1.26/0.53    spl5_6),
% 1.26/0.53    inference(avatar_split_clause,[],[f49,f101])).
% 1.26/0.53  fof(f49,plain,(
% 1.26/0.53    v17_lattices(sK0)),
% 1.26/0.53    inference(cnf_transformation,[],[f39])).
% 1.26/0.53  fof(f99,plain,(
% 1.26/0.53    spl5_5),
% 1.26/0.53    inference(avatar_split_clause,[],[f50,f96])).
% 1.26/0.53  fof(f50,plain,(
% 1.26/0.53    l3_lattices(sK0)),
% 1.26/0.53    inference(cnf_transformation,[],[f39])).
% 1.26/0.53  fof(f94,plain,(
% 1.26/0.53    spl5_4),
% 1.26/0.53    inference(avatar_split_clause,[],[f51,f91])).
% 1.26/0.53  fof(f51,plain,(
% 1.26/0.53    m1_subset_1(sK1,u1_struct_0(sK0))),
% 1.26/0.53    inference(cnf_transformation,[],[f39])).
% 1.26/0.53  fof(f89,plain,(
% 1.26/0.53    spl5_3),
% 1.26/0.53    inference(avatar_split_clause,[],[f52,f86])).
% 1.26/0.53  fof(f52,plain,(
% 1.26/0.53    m1_subset_1(sK2,u1_struct_0(sK0))),
% 1.26/0.53    inference(cnf_transformation,[],[f39])).
% 1.26/0.53  fof(f84,plain,(
% 1.26/0.53    spl5_2),
% 1.26/0.53    inference(avatar_split_clause,[],[f53,f81])).
% 1.26/0.53  fof(f53,plain,(
% 1.26/0.53    r3_lattices(sK0,sK1,sK2)),
% 1.26/0.53    inference(cnf_transformation,[],[f39])).
% 1.26/0.53  fof(f79,plain,(
% 1.26/0.53    ~spl5_1),
% 1.26/0.53    inference(avatar_split_clause,[],[f54,f76])).
% 1.26/0.53  fof(f54,plain,(
% 1.26/0.53    ~r3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1))),
% 1.26/0.53    inference(cnf_transformation,[],[f39])).
% 1.26/0.53  % SZS output end Proof for theBenchmark
% 1.26/0.53  % (9931)------------------------------
% 1.26/0.53  % (9931)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.53  % (9931)Termination reason: Refutation
% 1.26/0.53  
% 1.26/0.53  % (9931)Memory used [KB]: 11897
% 1.26/0.53  % (9931)Time elapsed: 0.107 s
% 1.26/0.53  % (9931)------------------------------
% 1.26/0.53  % (9931)------------------------------
% 1.26/0.53  % (9924)Success in time 0.175 s
%------------------------------------------------------------------------------
