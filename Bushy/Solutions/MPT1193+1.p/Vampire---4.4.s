%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : lattices__t18_lattices.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:00 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  285 ( 717 expanded)
%              Number of leaves         :   80 ( 292 expanded)
%              Depth                    :   12
%              Number of atoms          :  762 (1945 expanded)
%              Number of equality atoms :   47 ( 119 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f788,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f135,f142,f149,f156,f163,f170,f177,f184,f191,f202,f209,f216,f223,f236,f243,f250,f257,f264,f271,f278,f304,f322,f329,f364,f383,f390,f408,f414,f421,f476,f487,f500,f509,f518,f529,f580,f590,f609,f618,f631,f643,f655,f662,f668,f671,f673,f675,f677,f678,f710,f717,f728,f745,f770,f781])).

fof(f781,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_16
    | ~ spl8_18
    | spl8_39 ),
    inference(avatar_contradiction_clause,[],[f780])).

fof(f780,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_16
    | ~ spl8_18
    | ~ spl8_39 ),
    inference(subsumption_resolution,[],[f779,f277])).

fof(f277,plain,
    ( k4_lattices(sK0,sK1,sK1) != sK1
    | ~ spl8_39 ),
    inference(avatar_component_clause,[],[f276])).

fof(f276,plain,
    ( spl8_39
  <=> k4_lattices(sK0,sK1,sK1) != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_39])])).

fof(f779,plain,
    ( k4_lattices(sK0,sK1,sK1) = sK1
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_16
    | ~ spl8_18 ),
    inference(forward_demodulation,[],[f777,f751])).

fof(f751,plain,
    ( k2_lattices(sK0,sK1,sK1) = sK1
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_16 ),
    inference(forward_demodulation,[],[f749,f687])).

fof(f687,plain,
    ( k1_lattices(sK0,sK1,sK1) = sK1
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_16 ),
    inference(unit_resulting_resolution,[],[f134,f141,f148,f155,f162,f190,f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( ~ v8_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | k1_lattices(X0,X1,X1) = X1
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_lattices(X0,X1,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_lattices(X0,X1,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k1_lattices(X0,X1,X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/lattices__t18_lattices.p',t17_lattices)).

fof(f190,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f189])).

fof(f189,plain,
    ( spl8_16
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f162,plain,
    ( l3_lattices(sK0)
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f161])).

fof(f161,plain,
    ( spl8_8
  <=> l3_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f155,plain,
    ( v9_lattices(sK0)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl8_6
  <=> v9_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f148,plain,
    ( v8_lattices(sK0)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl8_4
  <=> v8_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f141,plain,
    ( v6_lattices(sK0)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl8_2
  <=> v6_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f134,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl8_1
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f749,plain,
    ( k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK1)) = sK1
    | ~ spl8_1
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_16 ),
    inference(unit_resulting_resolution,[],[f134,f162,f155,f190,f190,f107])).

fof(f107,plain,(
    ! [X4,X0,X3] :
      ( v2_struct_0(X0)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v9_lattices(X0)
      | ~ l3_lattices(X0)
      | k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 ) ),
    inference(cnf_transformation,[],[f81])).

fof(f81,plain,(
    ! [X0] :
      ( ( ( v9_lattices(X0)
          | ( k2_lattices(X0,sK2(X0),k1_lattices(X0,sK2(X0),sK3(X0))) != sK2(X0)
            & m1_subset_1(sK3(X0),u1_struct_0(X0))
            & m1_subset_1(sK2(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v9_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f78,f80,f79])).

fof(f79,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k2_lattices(X0,sK2(X0),k1_lattices(X0,sK2(X0),X2)) != sK2(X0)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK2(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f80,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k2_lattices(X0,X1,k1_lattices(X0,X1,sK3(X0))) != X1
        & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f78,plain,(
    ! [X0] :
      ( ( ( v9_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v9_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f77])).

fof(f77,plain,(
    ! [X0] :
      ( ( ( v9_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v9_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v9_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/lattices__t18_lattices.p',d9_lattices)).

fof(f777,plain,
    ( k4_lattices(sK0,sK1,sK1) = k2_lattices(sK0,sK1,sK1)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_16
    | ~ spl8_18 ),
    inference(unit_resulting_resolution,[],[f134,f141,f201,f190,f190,f118])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( ~ v6_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/lattices__t18_lattices.p',redefinition_k4_lattices)).

fof(f201,plain,
    ( l1_lattices(sK0)
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f200])).

fof(f200,plain,
    ( spl8_18
  <=> l1_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f770,plain,
    ( ~ spl8_93
    | spl8_59
    | ~ spl8_64 ),
    inference(avatar_split_clause,[],[f699,f504,f474,f768])).

fof(f768,plain,
    ( spl8_93
  <=> ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_93])])).

fof(f474,plain,
    ( spl8_59
  <=> ~ m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_59])])).

fof(f504,plain,
    ( spl8_64
  <=> r2_hidden(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_64])])).

fof(f699,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl8_59
    | ~ spl8_64 ),
    inference(unit_resulting_resolution,[],[f475,f505,f122])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f67])).

fof(f67,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/lattices__t18_lattices.p',t4_subset)).

fof(f505,plain,
    ( r2_hidden(sK1,k1_xboole_0)
    | ~ spl8_64 ),
    inference(avatar_component_clause,[],[f504])).

fof(f475,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0))
    | ~ spl8_59 ),
    inference(avatar_component_clause,[],[f474])).

fof(f745,plain,
    ( ~ spl8_91
    | spl8_87 ),
    inference(avatar_split_clause,[],[f718,f708,f743])).

fof(f743,plain,
    ( spl8_91
  <=> ~ r2_hidden(k1_xboole_0,sK4(k1_zfmisc_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_91])])).

fof(f708,plain,
    ( spl8_87
  <=> ~ m1_subset_1(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_87])])).

fof(f718,plain,
    ( ~ r2_hidden(k1_xboole_0,sK4(k1_zfmisc_1(sK1)))
    | ~ spl8_87 ),
    inference(unit_resulting_resolution,[],[f111,f709,f122])).

fof(f709,plain,
    ( ~ m1_subset_1(k1_xboole_0,sK1)
    | ~ spl8_87 ),
    inference(avatar_component_clause,[],[f708])).

fof(f111,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(cnf_transformation,[],[f83])).

fof(f83,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f26,f82])).

fof(f82,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f26,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/lattices__t18_lattices.p',existence_m1_subset_1)).

fof(f728,plain,
    ( ~ spl8_45
    | ~ spl8_54 ),
    inference(avatar_split_clause,[],[f460,f388,f299])).

fof(f299,plain,
    ( spl8_45
  <=> ~ v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_45])])).

fof(f388,plain,
    ( spl8_54
  <=> r2_hidden(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_54])])).

fof(f460,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl8_54 ),
    inference(unit_resulting_resolution,[],[f389,f116])).

fof(f116,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/lattices__t18_lattices.p',t7_boole)).

fof(f389,plain,
    ( r2_hidden(sK1,u1_struct_0(sK0))
    | ~ spl8_54 ),
    inference(avatar_component_clause,[],[f388])).

fof(f717,plain,
    ( ~ spl8_89
    | spl8_51
    | ~ spl8_56 ),
    inference(avatar_split_clause,[],[f683,f419,f359,f715])).

fof(f715,plain,
    ( spl8_89
  <=> ~ r2_hidden(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_89])])).

fof(f359,plain,
    ( spl8_51
  <=> ~ v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_51])])).

fof(f419,plain,
    ( spl8_56
  <=> m1_subset_1(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_56])])).

fof(f683,plain,
    ( ~ r2_hidden(k1_xboole_0,sK1)
    | ~ spl8_51
    | ~ spl8_56 ),
    inference(unit_resulting_resolution,[],[f360,f420,f280])).

fof(f280,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,X3)
      | ~ m1_subset_1(X3,X2)
      | v1_xboole_0(X2) ) ),
    inference(resolution,[],[f114,f112])).

fof(f112,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/lattices__t18_lattices.p',antisymmetry_r2_hidden)).

fof(f114,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/lattices__t18_lattices.p',t2_subset)).

fof(f420,plain,
    ( m1_subset_1(sK1,k1_xboole_0)
    | ~ spl8_56 ),
    inference(avatar_component_clause,[],[f419])).

fof(f360,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl8_51 ),
    inference(avatar_component_clause,[],[f359])).

fof(f710,plain,
    ( ~ spl8_87
    | spl8_43
    | spl8_51
    | ~ spl8_56 ),
    inference(avatar_split_clause,[],[f682,f419,f359,f293,f708])).

fof(f293,plain,
    ( spl8_43
  <=> ~ v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_43])])).

fof(f682,plain,
    ( ~ m1_subset_1(k1_xboole_0,sK1)
    | ~ spl8_43
    | ~ spl8_51
    | ~ spl8_56 ),
    inference(unit_resulting_resolution,[],[f360,f294,f420,f281])).

fof(f281,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(resolution,[],[f280,f114])).

fof(f294,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl8_43 ),
    inference(avatar_component_clause,[],[f293])).

fof(f678,plain,
    ( ~ spl8_51
    | ~ spl8_68 ),
    inference(avatar_split_clause,[],[f597,f527,f359])).

fof(f527,plain,
    ( spl8_68
  <=> r2_hidden(sK4(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_68])])).

fof(f597,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl8_68 ),
    inference(unit_resulting_resolution,[],[f528,f116])).

fof(f528,plain,
    ( r2_hidden(sK4(k1_xboole_0),k1_xboole_0)
    | ~ spl8_68 ),
    inference(avatar_component_clause,[],[f527])).

fof(f677,plain,
    ( ~ spl8_44
    | ~ spl8_54 ),
    inference(avatar_contradiction_clause,[],[f676])).

fof(f676,plain,
    ( $false
    | ~ spl8_44
    | ~ spl8_54 ),
    inference(subsumption_resolution,[],[f303,f460])).

fof(f303,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl8_44 ),
    inference(avatar_component_clause,[],[f302])).

fof(f302,plain,
    ( spl8_44
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_44])])).

fof(f675,plain,
    ( ~ spl8_50
    | ~ spl8_68 ),
    inference(avatar_contradiction_clause,[],[f674])).

fof(f674,plain,
    ( $false
    | ~ spl8_50
    | ~ spl8_68 ),
    inference(subsumption_resolution,[],[f363,f597])).

fof(f363,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl8_50 ),
    inference(avatar_component_clause,[],[f362])).

fof(f362,plain,
    ( spl8_50
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_50])])).

fof(f673,plain,
    ( ~ spl8_56
    | spl8_65
    | ~ spl8_68 ),
    inference(avatar_contradiction_clause,[],[f672])).

fof(f672,plain,
    ( $false
    | ~ spl8_56
    | ~ spl8_65
    | ~ spl8_68 ),
    inference(subsumption_resolution,[],[f420,f663])).

fof(f663,plain,
    ( ~ m1_subset_1(sK1,k1_xboole_0)
    | ~ spl8_65
    | ~ spl8_68 ),
    inference(subsumption_resolution,[],[f511,f597])).

fof(f511,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ m1_subset_1(sK1,k1_xboole_0)
    | ~ spl8_65 ),
    inference(resolution,[],[f508,f114])).

fof(f508,plain,
    ( ~ r2_hidden(sK1,k1_xboole_0)
    | ~ spl8_65 ),
    inference(avatar_component_clause,[],[f507])).

fof(f507,plain,
    ( spl8_65
  <=> ~ r2_hidden(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_65])])).

fof(f671,plain,
    ( ~ spl8_62
    | ~ spl8_68
    | ~ spl8_72 ),
    inference(avatar_contradiction_clause,[],[f670])).

fof(f670,plain,
    ( $false
    | ~ spl8_62
    | ~ spl8_68
    | ~ spl8_72 ),
    inference(subsumption_resolution,[],[f669,f597])).

fof(f669,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl8_62
    | ~ spl8_72 ),
    inference(forward_demodulation,[],[f499,f589])).

fof(f589,plain,
    ( k1_xboole_0 = sK4(k1_zfmisc_1(k1_xboole_0))
    | ~ spl8_72 ),
    inference(avatar_component_clause,[],[f588])).

fof(f588,plain,
    ( spl8_72
  <=> k1_xboole_0 = sK4(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_72])])).

fof(f499,plain,
    ( v1_xboole_0(sK4(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl8_62 ),
    inference(avatar_component_clause,[],[f498])).

fof(f498,plain,
    ( spl8_62
  <=> v1_xboole_0(sK4(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_62])])).

fof(f668,plain,
    ( spl8_65
    | ~ spl8_68
    | ~ spl8_72
    | ~ spl8_78 ),
    inference(avatar_contradiction_clause,[],[f667])).

fof(f667,plain,
    ( $false
    | ~ spl8_65
    | ~ spl8_68
    | ~ spl8_72
    | ~ spl8_78 ),
    inference(subsumption_resolution,[],[f666,f663])).

fof(f666,plain,
    ( m1_subset_1(sK1,k1_xboole_0)
    | ~ spl8_72
    | ~ spl8_78 ),
    inference(backward_demodulation,[],[f589,f627])).

fof(f627,plain,
    ( m1_subset_1(sK1,sK4(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl8_78 ),
    inference(avatar_component_clause,[],[f626])).

fof(f626,plain,
    ( spl8_78
  <=> m1_subset_1(sK1,sK4(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_78])])).

fof(f662,plain,
    ( spl8_84
    | spl8_45 ),
    inference(avatar_split_clause,[],[f435,f299,f660])).

fof(f660,plain,
    ( spl8_84
  <=> r2_hidden(sK4(u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_84])])).

fof(f435,plain,
    ( r2_hidden(sK4(u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl8_45 ),
    inference(unit_resulting_resolution,[],[f111,f300,f114])).

fof(f300,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl8_45 ),
    inference(avatar_component_clause,[],[f299])).

fof(f655,plain,
    ( ~ spl8_83
    | spl8_45 ),
    inference(avatar_split_clause,[],[f434,f299,f653])).

fof(f653,plain,
    ( spl8_83
  <=> ~ r2_hidden(u1_struct_0(sK0),sK4(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_83])])).

fof(f434,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK4(u1_struct_0(sK0)))
    | ~ spl8_45 ),
    inference(unit_resulting_resolution,[],[f111,f300,f280])).

fof(f643,plain,
    ( ~ spl8_81
    | spl8_41 ),
    inference(avatar_split_clause,[],[f313,f290,f641])).

fof(f641,plain,
    ( spl8_81
  <=> ~ r2_hidden(u1_struct_0(sK0),sK4(k1_zfmisc_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_81])])).

fof(f290,plain,
    ( spl8_41
  <=> ~ m1_subset_1(u1_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_41])])).

fof(f313,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK4(k1_zfmisc_1(sK1)))
    | ~ spl8_41 ),
    inference(unit_resulting_resolution,[],[f111,f291,f122])).

fof(f291,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),sK1)
    | ~ spl8_41 ),
    inference(avatar_component_clause,[],[f290])).

fof(f631,plain,
    ( ~ spl8_79
    | spl8_63
    | spl8_75 ),
    inference(avatar_split_clause,[],[f610,f607,f495,f629])).

fof(f629,plain,
    ( spl8_79
  <=> ~ m1_subset_1(sK1,sK4(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_79])])).

fof(f495,plain,
    ( spl8_63
  <=> ~ v1_xboole_0(sK4(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_63])])).

fof(f607,plain,
    ( spl8_75
  <=> ~ r2_hidden(sK1,sK4(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_75])])).

fof(f610,plain,
    ( ~ m1_subset_1(sK1,sK4(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl8_63
    | ~ spl8_75 ),
    inference(unit_resulting_resolution,[],[f496,f608,f114])).

fof(f608,plain,
    ( ~ r2_hidden(sK1,sK4(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl8_75 ),
    inference(avatar_component_clause,[],[f607])).

fof(f496,plain,
    ( ~ v1_xboole_0(sK4(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl8_63 ),
    inference(avatar_component_clause,[],[f495])).

fof(f618,plain,
    ( ~ spl8_77
    | spl8_71 ),
    inference(avatar_split_clause,[],[f582,f578,f616])).

fof(f616,plain,
    ( spl8_77
  <=> ~ r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_77])])).

fof(f578,plain,
    ( spl8_71
  <=> ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_71])])).

fof(f582,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl8_71 ),
    inference(unit_resulting_resolution,[],[f579,f113])).

fof(f113,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/lattices__t18_lattices.p',t1_subset)).

fof(f579,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl8_71 ),
    inference(avatar_component_clause,[],[f578])).

fof(f609,plain,
    ( ~ spl8_75
    | spl8_57 ),
    inference(avatar_split_clause,[],[f431,f416,f607])).

fof(f416,plain,
    ( spl8_57
  <=> ~ m1_subset_1(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_57])])).

fof(f431,plain,
    ( ~ r2_hidden(sK1,sK4(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl8_57 ),
    inference(unit_resulting_resolution,[],[f111,f417,f122])).

fof(f417,plain,
    ( ~ m1_subset_1(sK1,k1_xboole_0)
    | ~ spl8_57 ),
    inference(avatar_component_clause,[],[f416])).

fof(f590,plain,
    ( spl8_72
    | ~ spl8_62 ),
    inference(avatar_split_clause,[],[f558,f498,f588])).

fof(f558,plain,
    ( k1_xboole_0 = sK4(k1_zfmisc_1(k1_xboole_0))
    | ~ spl8_62 ),
    inference(unit_resulting_resolution,[],[f499,f97])).

fof(f97,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/lattices__t18_lattices.p',t6_boole)).

fof(f580,plain,
    ( ~ spl8_71
    | ~ spl8_54
    | spl8_57 ),
    inference(avatar_split_clause,[],[f461,f416,f388,f578])).

fof(f461,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl8_54
    | ~ spl8_57 ),
    inference(unit_resulting_resolution,[],[f417,f389,f122])).

fof(f529,plain,
    ( spl8_68
    | spl8_51 ),
    inference(avatar_split_clause,[],[f502,f359,f527])).

fof(f502,plain,
    ( r2_hidden(sK4(k1_xboole_0),k1_xboole_0)
    | ~ spl8_51 ),
    inference(unit_resulting_resolution,[],[f111,f360,f114])).

fof(f518,plain,
    ( ~ spl8_67
    | spl8_51 ),
    inference(avatar_split_clause,[],[f501,f359,f516])).

fof(f516,plain,
    ( spl8_67
  <=> ~ r2_hidden(k1_xboole_0,sK4(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_67])])).

fof(f501,plain,
    ( ~ r2_hidden(k1_xboole_0,sK4(k1_xboole_0))
    | ~ spl8_51 ),
    inference(unit_resulting_resolution,[],[f111,f360,f280])).

fof(f509,plain,
    ( ~ spl8_65
    | spl8_57 ),
    inference(avatar_split_clause,[],[f432,f416,f507])).

fof(f432,plain,
    ( ~ r2_hidden(sK1,k1_xboole_0)
    | ~ spl8_57 ),
    inference(unit_resulting_resolution,[],[f417,f113])).

fof(f500,plain,
    ( spl8_62
    | ~ spl8_50 ),
    inference(avatar_split_clause,[],[f489,f362,f498])).

fof(f489,plain,
    ( v1_xboole_0(sK4(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl8_50 ),
    inference(unit_resulting_resolution,[],[f111,f422,f114])).

fof(f422,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK4(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl8_50 ),
    inference(unit_resulting_resolution,[],[f111,f363,f123])).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/lattices__t18_lattices.p',t5_subset)).

fof(f487,plain,
    ( ~ spl8_61
    | spl8_59 ),
    inference(avatar_split_clause,[],[f479,f474,f485])).

fof(f485,plain,
    ( spl8_61
  <=> ~ r2_hidden(sK1,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_61])])).

fof(f479,plain,
    ( ~ r2_hidden(sK1,k1_zfmisc_1(k1_xboole_0))
    | ~ spl8_59 ),
    inference(unit_resulting_resolution,[],[f475,f113])).

fof(f476,plain,
    ( ~ spl8_59
    | ~ spl8_48
    | ~ spl8_50 ),
    inference(avatar_split_clause,[],[f451,f362,f327,f474])).

fof(f327,plain,
    ( spl8_48
  <=> r2_hidden(sK4(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_48])])).

fof(f451,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0))
    | ~ spl8_48
    | ~ spl8_50 ),
    inference(unit_resulting_resolution,[],[f363,f328,f123])).

fof(f328,plain,
    ( r2_hidden(sK4(sK1),sK1)
    | ~ spl8_48 ),
    inference(avatar_component_clause,[],[f327])).

fof(f421,plain,
    ( spl8_56
    | ~ spl8_16
    | ~ spl8_44 ),
    inference(avatar_split_clause,[],[f400,f302,f189,f419])).

fof(f400,plain,
    ( m1_subset_1(sK1,k1_xboole_0)
    | ~ spl8_16
    | ~ spl8_44 ),
    inference(backward_demodulation,[],[f395,f190])).

fof(f395,plain,
    ( u1_struct_0(sK0) = k1_xboole_0
    | ~ spl8_44 ),
    inference(unit_resulting_resolution,[],[f303,f97])).

fof(f414,plain,
    ( spl8_50
    | ~ spl8_44 ),
    inference(avatar_split_clause,[],[f402,f302,f362])).

fof(f402,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl8_44 ),
    inference(backward_demodulation,[],[f395,f303])).

fof(f408,plain,
    ( ~ spl8_44
    | spl8_51 ),
    inference(avatar_contradiction_clause,[],[f407])).

fof(f407,plain,
    ( $false
    | ~ spl8_44
    | ~ spl8_51 ),
    inference(subsumption_resolution,[],[f402,f360])).

fof(f390,plain,
    ( spl8_54
    | ~ spl8_16
    | spl8_45 ),
    inference(avatar_split_clause,[],[f311,f299,f189,f388])).

fof(f311,plain,
    ( r2_hidden(sK1,u1_struct_0(sK0))
    | ~ spl8_16
    | ~ spl8_45 ),
    inference(unit_resulting_resolution,[],[f190,f300,f114])).

fof(f383,plain,
    ( ~ spl8_53
    | ~ spl8_16
    | spl8_45 ),
    inference(avatar_split_clause,[],[f309,f299,f189,f381])).

fof(f381,plain,
    ( spl8_53
  <=> ~ r2_hidden(u1_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_53])])).

fof(f309,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK1)
    | ~ spl8_16
    | ~ spl8_45 ),
    inference(unit_resulting_resolution,[],[f190,f300,f280])).

fof(f364,plain,
    ( spl8_50
    | ~ spl8_42 ),
    inference(avatar_split_clause,[],[f344,f296,f362])).

fof(f296,plain,
    ( spl8_42
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_42])])).

fof(f344,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl8_42 ),
    inference(backward_demodulation,[],[f336,f297])).

fof(f297,plain,
    ( v1_xboole_0(sK1)
    | ~ spl8_42 ),
    inference(avatar_component_clause,[],[f296])).

fof(f336,plain,
    ( k1_xboole_0 = sK1
    | ~ spl8_42 ),
    inference(unit_resulting_resolution,[],[f297,f97])).

fof(f329,plain,
    ( spl8_48
    | spl8_43 ),
    inference(avatar_split_clause,[],[f306,f293,f327])).

fof(f306,plain,
    ( r2_hidden(sK4(sK1),sK1)
    | ~ spl8_43 ),
    inference(unit_resulting_resolution,[],[f111,f294,f114])).

fof(f322,plain,
    ( ~ spl8_47
    | spl8_43 ),
    inference(avatar_split_clause,[],[f305,f293,f320])).

fof(f320,plain,
    ( spl8_47
  <=> ~ r2_hidden(sK1,sK4(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_47])])).

fof(f305,plain,
    ( ~ r2_hidden(sK1,sK4(sK1))
    | ~ spl8_43 ),
    inference(unit_resulting_resolution,[],[f111,f294,f280])).

fof(f304,plain,
    ( ~ spl8_41
    | spl8_42
    | spl8_44
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f282,f189,f302,f296,f290])).

fof(f282,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(u1_struct_0(sK0),sK1)
    | ~ spl8_16 ),
    inference(resolution,[],[f281,f190])).

fof(f278,plain,(
    ~ spl8_39 ),
    inference(avatar_split_clause,[],[f96,f276])).

fof(f96,plain,(
    k4_lattices(sK0,sK1,sK1) != sK1 ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,
    ( k4_lattices(sK0,sK1,sK1) != sK1
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l3_lattices(sK0)
    & v9_lattices(sK0)
    & v8_lattices(sK0)
    & v6_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f42,f75,f74])).

fof(f74,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k4_lattices(X0,X1,X1) != X1
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k4_lattices(sK0,X1,X1) != X1
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l3_lattices(sK0)
      & v9_lattices(sK0)
      & v8_lattices(sK0)
      & v6_lattices(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f75,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k4_lattices(X0,X1,X1) != X1
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( k4_lattices(X0,sK1,sK1) != sK1
        & m1_subset_1(sK1,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k4_lattices(X0,X1,X1) != X1
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v9_lattices(X0)
      & v8_lattices(X0)
      & v6_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k4_lattices(X0,X1,X1) != X1
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v9_lattices(X0)
      & v8_lattices(X0)
      & v6_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => k4_lattices(X0,X1,X1) = X1 ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k4_lattices(X0,X1,X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/lattices__t18_lattices.p',t18_lattices)).

fof(f271,plain,
    ( spl8_36
    | ~ spl8_22 ),
    inference(avatar_split_clause,[],[f229,f214,f269])).

fof(f269,plain,
    ( spl8_36
  <=> v1_funct_1(u1_lattices(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_36])])).

fof(f214,plain,
    ( spl8_22
  <=> l1_lattices(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f229,plain,
    ( v1_funct_1(u1_lattices(sK6))
    | ~ spl8_22 ),
    inference(unit_resulting_resolution,[],[f215,f103])).

fof(f103,plain,(
    ! [X0] :
      ( v1_funct_1(u1_lattices(X0))
      | ~ l1_lattices(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ( m1_subset_1(u1_lattices(X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))))
        & v1_funct_2(u1_lattices(X0),k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
        & v1_funct_1(u1_lattices(X0)) )
      | ~ l1_lattices(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_lattices(X0)
     => ( m1_subset_1(u1_lattices(X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))))
        & v1_funct_2(u1_lattices(X0),k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
        & v1_funct_1(u1_lattices(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/lattices__t18_lattices.p',dt_u1_lattices)).

fof(f215,plain,
    ( l1_lattices(sK6)
    | ~ spl8_22 ),
    inference(avatar_component_clause,[],[f214])).

fof(f264,plain,
    ( spl8_34
    | ~ spl8_24 ),
    inference(avatar_split_clause,[],[f226,f221,f262])).

fof(f262,plain,
    ( spl8_34
  <=> v1_funct_1(u2_lattices(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_34])])).

fof(f221,plain,
    ( spl8_24
  <=> l2_lattices(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f226,plain,
    ( v1_funct_1(u2_lattices(sK6))
    | ~ spl8_24 ),
    inference(unit_resulting_resolution,[],[f222,f100])).

fof(f100,plain,(
    ! [X0] :
      ( v1_funct_1(u2_lattices(X0))
      | ~ l2_lattices(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ( m1_subset_1(u2_lattices(X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))))
        & v1_funct_2(u2_lattices(X0),k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
        & v1_funct_1(u2_lattices(X0)) )
      | ~ l2_lattices(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( l2_lattices(X0)
     => ( m1_subset_1(u2_lattices(X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))))
        & v1_funct_2(u2_lattices(X0),k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
        & v1_funct_1(u2_lattices(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/lattices__t18_lattices.p',dt_u2_lattices)).

fof(f222,plain,
    ( l2_lattices(sK6)
    | ~ spl8_24 ),
    inference(avatar_component_clause,[],[f221])).

fof(f257,plain,
    ( spl8_32
    | ~ spl8_18 ),
    inference(avatar_split_clause,[],[f228,f200,f255])).

fof(f255,plain,
    ( spl8_32
  <=> v1_funct_1(u1_lattices(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).

fof(f228,plain,
    ( v1_funct_1(u1_lattices(sK0))
    | ~ spl8_18 ),
    inference(unit_resulting_resolution,[],[f201,f103])).

fof(f250,plain,
    ( spl8_30
    | ~ spl8_20 ),
    inference(avatar_split_clause,[],[f225,f207,f248])).

fof(f248,plain,
    ( spl8_30
  <=> v1_funct_1(u2_lattices(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).

fof(f207,plain,
    ( spl8_20
  <=> l2_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f225,plain,
    ( v1_funct_1(u2_lattices(sK0))
    | ~ spl8_20 ),
    inference(unit_resulting_resolution,[],[f208,f100])).

fof(f208,plain,
    ( l2_lattices(sK0)
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f207])).

fof(f243,plain,
    ( spl8_28
    | ~ spl8_14 ),
    inference(avatar_split_clause,[],[f227,f182,f241])).

fof(f241,plain,
    ( spl8_28
  <=> v1_funct_1(u1_lattices(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).

fof(f182,plain,
    ( spl8_14
  <=> l1_lattices(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f227,plain,
    ( v1_funct_1(u1_lattices(sK7))
    | ~ spl8_14 ),
    inference(unit_resulting_resolution,[],[f183,f103])).

fof(f183,plain,
    ( l1_lattices(sK7)
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f182])).

fof(f236,plain,
    ( spl8_26
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f224,f168,f234])).

fof(f234,plain,
    ( spl8_26
  <=> v1_funct_1(u2_lattices(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).

fof(f168,plain,
    ( spl8_10
  <=> l2_lattices(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f224,plain,
    ( v1_funct_1(u2_lattices(sK5))
    | ~ spl8_10 ),
    inference(unit_resulting_resolution,[],[f169,f100])).

fof(f169,plain,
    ( l2_lattices(sK5)
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f168])).

fof(f223,plain,
    ( spl8_24
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f195,f175,f221])).

fof(f175,plain,
    ( spl8_12
  <=> l3_lattices(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f195,plain,
    ( l2_lattices(sK6)
    | ~ spl8_12 ),
    inference(unit_resulting_resolution,[],[f176,f99])).

fof(f99,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/lattices__t18_lattices.p',dt_l3_lattices)).

fof(f176,plain,
    ( l3_lattices(sK6)
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f175])).

fof(f216,plain,
    ( spl8_22
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f193,f175,f214])).

fof(f193,plain,
    ( l1_lattices(sK6)
    | ~ spl8_12 ),
    inference(unit_resulting_resolution,[],[f176,f98])).

fof(f98,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f209,plain,
    ( spl8_20
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f194,f161,f207])).

fof(f194,plain,
    ( l2_lattices(sK0)
    | ~ spl8_8 ),
    inference(unit_resulting_resolution,[],[f162,f99])).

fof(f202,plain,
    ( spl8_18
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f192,f161,f200])).

fof(f192,plain,
    ( l1_lattices(sK0)
    | ~ spl8_8 ),
    inference(unit_resulting_resolution,[],[f162,f98])).

fof(f191,plain,(
    spl8_16 ),
    inference(avatar_split_clause,[],[f95,f189])).

fof(f95,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f76])).

fof(f184,plain,(
    spl8_14 ),
    inference(avatar_split_clause,[],[f128,f182])).

fof(f128,plain,(
    l1_lattices(sK7) ),
    inference(cnf_transformation,[],[f89])).

fof(f89,plain,(
    l1_lattices(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f22,f88])).

fof(f88,plain,
    ( ? [X0] : l1_lattices(X0)
   => l1_lattices(sK7) ),
    introduced(choice_axiom,[])).

fof(f22,axiom,(
    ? [X0] : l1_lattices(X0) ),
    file('/export/starexec/sandbox2/benchmark/lattices__t18_lattices.p',existence_l1_lattices)).

fof(f177,plain,(
    spl8_12 ),
    inference(avatar_split_clause,[],[f127,f175])).

fof(f127,plain,(
    l3_lattices(sK6) ),
    inference(cnf_transformation,[],[f87])).

fof(f87,plain,(
    l3_lattices(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f25,f86])).

fof(f86,plain,
    ( ? [X0] : l3_lattices(X0)
   => l3_lattices(sK6) ),
    introduced(choice_axiom,[])).

fof(f25,axiom,(
    ? [X0] : l3_lattices(X0) ),
    file('/export/starexec/sandbox2/benchmark/lattices__t18_lattices.p',existence_l3_lattices)).

fof(f170,plain,(
    spl8_10 ),
    inference(avatar_split_clause,[],[f126,f168])).

fof(f126,plain,(
    l2_lattices(sK5) ),
    inference(cnf_transformation,[],[f85])).

fof(f85,plain,(
    l2_lattices(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f24,f84])).

fof(f84,plain,
    ( ? [X0] : l2_lattices(X0)
   => l2_lattices(sK5) ),
    introduced(choice_axiom,[])).

fof(f24,axiom,(
    ? [X0] : l2_lattices(X0) ),
    file('/export/starexec/sandbox2/benchmark/lattices__t18_lattices.p',existence_l2_lattices)).

fof(f163,plain,(
    spl8_8 ),
    inference(avatar_split_clause,[],[f94,f161])).

fof(f94,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f76])).

fof(f156,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f93,f154])).

fof(f93,plain,(
    v9_lattices(sK0) ),
    inference(cnf_transformation,[],[f76])).

fof(f149,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f92,f147])).

fof(f92,plain,(
    v8_lattices(sK0) ),
    inference(cnf_transformation,[],[f76])).

fof(f142,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f91,f140])).

fof(f91,plain,(
    v6_lattices(sK0) ),
    inference(cnf_transformation,[],[f76])).

fof(f135,plain,(
    ~ spl8_1 ),
    inference(avatar_split_clause,[],[f90,f133])).

fof(f90,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f76])).
%------------------------------------------------------------------------------
