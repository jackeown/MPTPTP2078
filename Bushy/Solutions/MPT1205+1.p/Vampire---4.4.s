%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : lattices__t39_lattices.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:02 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 192 expanded)
%              Number of leaves         :   19 (  70 expanded)
%              Depth                    :   12
%              Number of atoms          :  425 ( 717 expanded)
%              Number of equality atoms :   46 (  68 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6947,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f126,f130,f134,f138,f156,f160,f164,f211,f215,f223,f229,f6814,f6946])).

fof(f6946,plain,
    ( spl9_258
    | spl9_1
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_20
    | ~ spl9_22 ),
    inference(avatar_split_clause,[],[f6940,f227,f221,f158,f154,f136,f132,f124,f4091])).

fof(f4091,plain,
    ( spl9_258
  <=> k1_lattices(sK0,k5_lattices(sK0),sK1) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_258])])).

fof(f124,plain,
    ( spl9_1
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f132,plain,
    ( spl9_4
  <=> v13_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f136,plain,
    ( spl9_6
  <=> l3_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f154,plain,
    ( spl9_8
  <=> l1_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f158,plain,
    ( spl9_10
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f221,plain,
    ( spl9_20
  <=> v8_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).

fof(f227,plain,
    ( spl9_22
  <=> m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).

fof(f6940,plain,
    ( k1_lattices(sK0,k5_lattices(sK0),sK1) = sK1
    | ~ spl9_1
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_20
    | ~ spl9_22 ),
    inference(forward_demodulation,[],[f4026,f2341])).

fof(f2341,plain,
    ( k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),sK1)
    | ~ spl9_1
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_22 ),
    inference(resolution,[],[f278,f159])).

fof(f159,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl9_10 ),
    inference(avatar_component_clause,[],[f158])).

fof(f278,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),X0) )
    | ~ spl9_1
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f277,f125])).

fof(f125,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f124])).

fof(f277,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),X0) )
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f276,f133])).

fof(f133,plain,
    ( v13_lattices(sK0)
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f132])).

fof(f276,plain,
    ( ! [X0] :
        ( ~ v13_lattices(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),X0) )
    | ~ spl9_8
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f260,f155])).

fof(f155,plain,
    ( l1_lattices(sK0)
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f154])).

fof(f260,plain,
    ( ! [X0] :
        ( ~ l1_lattices(sK0)
        | ~ v13_lattices(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),X0) )
    | ~ spl9_22 ),
    inference(resolution,[],[f228,f122])).

fof(f122,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v13_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k5_lattices(X0) = k2_lattices(X0,k5_lattices(X0),X2) ) ),
    inference(equality_resolution,[],[f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_lattices(X0)
      | ~ v13_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k2_lattices(X0,X1,X2) = X1
      | k5_lattices(X0) != X1 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k5_lattices(X0) = X1
          <=> ! [X2] :
                ( ( k2_lattices(X0,X2,X1) = X1
                  & k2_lattices(X0,X1,X2) = X1 )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k5_lattices(X0) = X1
          <=> ! [X2] :
                ( ( k2_lattices(X0,X2,X1) = X1
                  & k2_lattices(X0,X1,X2) = X1 )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v13_lattices(X0)
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( k5_lattices(X0) = X1
            <=> ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ( k2_lattices(X0,X2,X1) = X1
                    & k2_lattices(X0,X1,X2) = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t39_lattices.p',d16_lattices)).

fof(f228,plain,
    ( m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ spl9_22 ),
    inference(avatar_component_clause,[],[f227])).

fof(f4026,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,k5_lattices(sK0),sK1),sK1) = sK1
    | ~ spl9_1
    | ~ spl9_6
    | ~ spl9_10
    | ~ spl9_20
    | ~ spl9_22 ),
    inference(resolution,[],[f302,f159])).

fof(f302,plain,
    ( ! [X6] :
        ( ~ m1_subset_1(X6,u1_struct_0(sK0))
        | k1_lattices(sK0,k2_lattices(sK0,k5_lattices(sK0),X6),X6) = X6 )
    | ~ spl9_1
    | ~ spl9_6
    | ~ spl9_20
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f301,f222])).

fof(f222,plain,
    ( v8_lattices(sK0)
    | ~ spl9_20 ),
    inference(avatar_component_clause,[],[f221])).

fof(f301,plain,
    ( ! [X6] :
        ( ~ m1_subset_1(X6,u1_struct_0(sK0))
        | k1_lattices(sK0,k2_lattices(sK0,k5_lattices(sK0),X6),X6) = X6
        | ~ v8_lattices(sK0) )
    | ~ spl9_1
    | ~ spl9_6
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f300,f125])).

fof(f300,plain,
    ( ! [X6] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | k1_lattices(sK0,k2_lattices(sK0,k5_lattices(sK0),X6),X6) = X6
        | ~ v8_lattices(sK0) )
    | ~ spl9_6
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f269,f137])).

fof(f137,plain,
    ( l3_lattices(sK0)
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f136])).

fof(f269,plain,
    ( ! [X6] :
        ( ~ l3_lattices(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | k1_lattices(sK0,k2_lattices(sK0,k5_lattices(sK0),X6),X6) = X6
        | ~ v8_lattices(sK0) )
    | ~ spl9_22 ),
    inference(resolution,[],[f228,f111])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
      | ~ v8_lattices(X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v8_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t39_lattices.p',d8_lattices)).

fof(f6814,plain,
    ( spl9_1
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_14
    | spl9_17
    | ~ spl9_22
    | ~ spl9_258 ),
    inference(avatar_contradiction_clause,[],[f6813])).

fof(f6813,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_14
    | ~ spl9_17
    | ~ spl9_22
    | ~ spl9_258 ),
    inference(subsumption_resolution,[],[f6812,f214])).

fof(f214,plain,
    ( k3_lattices(sK0,k5_lattices(sK0),sK1) != sK1
    | ~ spl9_17 ),
    inference(avatar_component_clause,[],[f213])).

fof(f213,plain,
    ( spl9_17
  <=> k3_lattices(sK0,k5_lattices(sK0),sK1) != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).

fof(f6812,plain,
    ( k3_lattices(sK0,k5_lattices(sK0),sK1) = sK1
    | ~ spl9_1
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_14
    | ~ spl9_22
    | ~ spl9_258 ),
    inference(forward_demodulation,[],[f6728,f4092])).

fof(f4092,plain,
    ( k1_lattices(sK0,k5_lattices(sK0),sK1) = sK1
    | ~ spl9_258 ),
    inference(avatar_component_clause,[],[f4091])).

fof(f6728,plain,
    ( k3_lattices(sK0,k5_lattices(sK0),sK1) = k1_lattices(sK0,k5_lattices(sK0),sK1)
    | ~ spl9_1
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_14
    | ~ spl9_22 ),
    inference(resolution,[],[f291,f159])).

fof(f291,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | k3_lattices(sK0,k5_lattices(sK0),X3) = k1_lattices(sK0,k5_lattices(sK0),X3) )
    | ~ spl9_1
    | ~ spl9_12
    | ~ spl9_14
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f290,f125])).

fof(f290,plain,
    ( ! [X3] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | k3_lattices(sK0,k5_lattices(sK0),X3) = k1_lattices(sK0,k5_lattices(sK0),X3) )
    | ~ spl9_12
    | ~ spl9_14
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f289,f163])).

fof(f163,plain,
    ( l2_lattices(sK0)
    | ~ spl9_12 ),
    inference(avatar_component_clause,[],[f162])).

fof(f162,plain,
    ( spl9_12
  <=> l2_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f289,plain,
    ( ! [X3] :
        ( ~ l2_lattices(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | k3_lattices(sK0,k5_lattices(sK0),X3) = k1_lattices(sK0,k5_lattices(sK0),X3) )
    | ~ spl9_14
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f264,f210])).

fof(f210,plain,
    ( v4_lattices(sK0)
    | ~ spl9_14 ),
    inference(avatar_component_clause,[],[f209])).

fof(f209,plain,
    ( spl9_14
  <=> v4_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f264,plain,
    ( ! [X3] :
        ( ~ v4_lattices(sK0)
        | ~ l2_lattices(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | k3_lattices(sK0,k5_lattices(sK0),X3) = k1_lattices(sK0,k5_lattices(sK0),X3) )
    | ~ spl9_22 ),
    inference(resolution,[],[f228,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v4_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t39_lattices.p',redefinition_k3_lattices)).

fof(f229,plain,
    ( spl9_22
    | spl9_1
    | ~ spl9_8 ),
    inference(avatar_split_clause,[],[f225,f154,f124,f227])).

fof(f225,plain,
    ( m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ spl9_1
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f224,f125])).

fof(f224,plain,
    ( v2_struct_0(sK0)
    | m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ spl9_8 ),
    inference(resolution,[],[f155,f96])).

fof(f96,plain,(
    ! [X0] :
      ( ~ l1_lattices(X0)
      | v2_struct_0(X0)
      | m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t39_lattices.p',dt_k5_lattices)).

fof(f223,plain,
    ( spl9_20
    | spl9_1
    | ~ spl9_2
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f152,f136,f128,f124,f221])).

fof(f128,plain,
    ( spl9_2
  <=> v10_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f152,plain,
    ( v8_lattices(sK0)
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f151,f129])).

fof(f129,plain,
    ( v10_lattices(sK0)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f128])).

fof(f151,plain,
    ( ~ v10_lattices(sK0)
    | v8_lattices(sK0)
    | ~ spl9_1
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f143,f125])).

fof(f143,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | v8_lattices(sK0)
    | ~ spl9_6 ),
    inference(resolution,[],[f137,f103])).

fof(f103,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | v8_lattices(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
        & v6_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
        & v6_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v8_lattices(X0)
          & v6_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v8_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v8_lattices(X0)
          & v7_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f42])).

fof(f42,axiom,(
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
    file('/export/starexec/sandbox/benchmark/lattices__t39_lattices.p',cc1_lattices)).

fof(f215,plain,(
    ~ spl9_17 ),
    inference(avatar_split_clause,[],[f83,f213])).

fof(f83,plain,(
    k3_lattices(sK0,k5_lattices(sK0),sK1) != sK1 ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k3_lattices(X0,k5_lattices(X0),X1) != X1
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v13_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k3_lattices(X0,k5_lattices(X0),X1) != X1
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v13_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v13_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => k3_lattices(X0,k5_lattices(X0),X1) = X1 ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v13_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k3_lattices(X0,k5_lattices(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t39_lattices.p',t39_lattices)).

fof(f211,plain,
    ( spl9_14
    | spl9_1
    | ~ spl9_2
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f148,f136,f128,f124,f209])).

fof(f148,plain,
    ( v4_lattices(sK0)
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f147,f129])).

fof(f147,plain,
    ( ~ v10_lattices(sK0)
    | v4_lattices(sK0)
    | ~ spl9_1
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f141,f125])).

fof(f141,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | v4_lattices(sK0)
    | ~ spl9_6 ),
    inference(resolution,[],[f137,f101])).

fof(f101,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | v4_lattices(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f164,plain,
    ( spl9_12
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f140,f136,f162])).

fof(f140,plain,
    ( l2_lattices(sK0)
    | ~ spl9_6 ),
    inference(resolution,[],[f137,f100])).

fof(f100,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | l2_lattices(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t39_lattices.p',dt_l3_lattices)).

fof(f160,plain,(
    spl9_10 ),
    inference(avatar_split_clause,[],[f82,f158])).

fof(f82,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f47])).

fof(f156,plain,
    ( spl9_8
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f139,f136,f154])).

fof(f139,plain,
    ( l1_lattices(sK0)
    | ~ spl9_6 ),
    inference(resolution,[],[f137,f99])).

fof(f99,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | l1_lattices(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f138,plain,(
    spl9_6 ),
    inference(avatar_split_clause,[],[f87,f136])).

fof(f87,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f134,plain,(
    spl9_4 ),
    inference(avatar_split_clause,[],[f86,f132])).

fof(f86,plain,(
    v13_lattices(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f130,plain,(
    spl9_2 ),
    inference(avatar_split_clause,[],[f85,f128])).

fof(f85,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f126,plain,(
    ~ spl9_1 ),
    inference(avatar_split_clause,[],[f84,f124])).

fof(f84,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f47])).
%------------------------------------------------------------------------------
