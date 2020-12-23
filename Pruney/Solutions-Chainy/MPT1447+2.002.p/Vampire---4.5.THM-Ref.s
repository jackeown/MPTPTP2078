%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:32 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  177 ( 449 expanded)
%              Number of leaves         :   42 ( 229 expanded)
%              Depth                    :    9
%              Number of atoms          : 1015 (2798 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   15 (   7 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f487,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f57,f62,f67,f72,f77,f82,f91,f95,f99,f103,f109,f118,f122,f126,f130,f134,f140,f144,f150,f161,f175,f179,f183,f185,f193,f198,f208,f215,f220,f227,f242,f252,f259,f326,f352,f413,f453,f455,f457,f465,f486])).

fof(f486,plain,
    ( spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | spl2_4
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_28
    | ~ spl2_31
    | ~ spl2_20
    | spl2_46 ),
    inference(avatar_split_clause,[],[f466,f349,f142,f217,f190,f79,f74,f69,f64,f59,f54])).

fof(f54,plain,
    ( spl2_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f59,plain,
    ( spl2_2
  <=> v10_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f64,plain,
    ( spl2_3
  <=> l3_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f69,plain,
    ( spl2_4
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f74,plain,
    ( spl2_5
  <=> v10_lattices(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f79,plain,
    ( spl2_6
  <=> l3_lattices(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f190,plain,
    ( spl2_28
  <=> v13_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).

fof(f217,plain,
    ( spl2_31
  <=> v13_lattices(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).

fof(f142,plain,
    ( spl2_20
  <=> ! [X1,X0] :
        ( v13_lattices(k7_filter_1(X0,X1))
        | ~ v13_lattices(X1)
        | ~ v13_lattices(X0)
        | ~ l3_lattices(X1)
        | ~ v10_lattices(X1)
        | v2_struct_0(X1)
        | ~ l3_lattices(X0)
        | ~ v10_lattices(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f349,plain,
    ( spl2_46
  <=> v13_lattices(k7_filter_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_46])])).

fof(f466,plain,
    ( ~ v13_lattices(sK1)
    | ~ v13_lattices(sK0)
    | ~ l3_lattices(sK1)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl2_20
    | spl2_46 ),
    inference(resolution,[],[f351,f143])).

fof(f143,plain,
    ( ! [X0,X1] :
        ( v13_lattices(k7_filter_1(X0,X1))
        | ~ v13_lattices(X1)
        | ~ v13_lattices(X0)
        | ~ l3_lattices(X1)
        | ~ v10_lattices(X1)
        | v2_struct_0(X1)
        | ~ l3_lattices(X0)
        | ~ v10_lattices(X0)
        | v2_struct_0(X0) )
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f142])).

fof(f351,plain,
    ( ~ v13_lattices(k7_filter_1(sK0,sK1))
    | spl2_46 ),
    inference(avatar_component_clause,[],[f349])).

fof(f465,plain,
    ( spl2_24
    | ~ spl2_25
    | ~ spl2_46
    | spl2_8
    | ~ spl2_11
    | ~ spl2_35 ),
    inference(avatar_split_clause,[],[f266,f256,f101,f88,f349,f168,f164])).

fof(f164,plain,
    ( spl2_24
  <=> v2_struct_0(k7_filter_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).

fof(f168,plain,
    ( spl2_25
  <=> l3_lattices(k7_filter_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).

fof(f88,plain,
    ( spl2_8
  <=> v15_lattices(k7_filter_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f101,plain,
    ( spl2_11
  <=> ! [X0] :
        ( v15_lattices(X0)
        | ~ v14_lattices(X0)
        | ~ v13_lattices(X0)
        | ~ l3_lattices(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f256,plain,
    ( spl2_35
  <=> v14_lattices(k7_filter_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_35])])).

fof(f266,plain,
    ( v15_lattices(k7_filter_1(sK0,sK1))
    | ~ v13_lattices(k7_filter_1(sK0,sK1))
    | ~ l3_lattices(k7_filter_1(sK0,sK1))
    | v2_struct_0(k7_filter_1(sK0,sK1))
    | ~ spl2_11
    | ~ spl2_35 ),
    inference(resolution,[],[f258,f102])).

fof(f102,plain,
    ( ! [X0] :
        ( ~ v14_lattices(X0)
        | v15_lattices(X0)
        | ~ v13_lattices(X0)
        | ~ l3_lattices(X0)
        | v2_struct_0(X0) )
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f101])).

fof(f258,plain,
    ( v14_lattices(k7_filter_1(sK0,sK1))
    | ~ spl2_35 ),
    inference(avatar_component_clause,[],[f256])).

fof(f457,plain,
    ( ~ spl2_7
    | ~ spl2_30
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f39,f88,f205,f84])).

fof(f84,plain,
    ( spl2_7
  <=> v15_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f205,plain,
    ( spl2_30
  <=> v15_lattices(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).

fof(f39,plain,
    ( ~ v15_lattices(k7_filter_1(sK0,sK1))
    | ~ v15_lattices(sK1)
    | ~ v15_lattices(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ( ~ v15_lattices(k7_filter_1(sK0,sK1))
      | ~ v15_lattices(sK1)
      | ~ v15_lattices(sK0) )
    & ( v15_lattices(k7_filter_1(sK0,sK1))
      | ( v15_lattices(sK1)
        & v15_lattices(sK0) ) )
    & l3_lattices(sK1)
    & v10_lattices(sK1)
    & ~ v2_struct_0(sK1)
    & l3_lattices(sK0)
    & v10_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f23,f22])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v15_lattices(k7_filter_1(X0,X1))
              | ~ v15_lattices(X1)
              | ~ v15_lattices(X0) )
            & ( v15_lattices(k7_filter_1(X0,X1))
              | ( v15_lattices(X1)
                & v15_lattices(X0) ) )
            & l3_lattices(X1)
            & v10_lattices(X1)
            & ~ v2_struct_0(X1) )
        & l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ v15_lattices(k7_filter_1(sK0,X1))
            | ~ v15_lattices(X1)
            | ~ v15_lattices(sK0) )
          & ( v15_lattices(k7_filter_1(sK0,X1))
            | ( v15_lattices(X1)
              & v15_lattices(sK0) ) )
          & l3_lattices(X1)
          & v10_lattices(X1)
          & ~ v2_struct_0(X1) )
      & l3_lattices(sK0)
      & v10_lattices(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X1] :
        ( ( ~ v15_lattices(k7_filter_1(sK0,X1))
          | ~ v15_lattices(X1)
          | ~ v15_lattices(sK0) )
        & ( v15_lattices(k7_filter_1(sK0,X1))
          | ( v15_lattices(X1)
            & v15_lattices(sK0) ) )
        & l3_lattices(X1)
        & v10_lattices(X1)
        & ~ v2_struct_0(X1) )
   => ( ( ~ v15_lattices(k7_filter_1(sK0,sK1))
        | ~ v15_lattices(sK1)
        | ~ v15_lattices(sK0) )
      & ( v15_lattices(k7_filter_1(sK0,sK1))
        | ( v15_lattices(sK1)
          & v15_lattices(sK0) ) )
      & l3_lattices(sK1)
      & v10_lattices(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v15_lattices(k7_filter_1(X0,X1))
            | ~ v15_lattices(X1)
            | ~ v15_lattices(X0) )
          & ( v15_lattices(k7_filter_1(X0,X1))
            | ( v15_lattices(X1)
              & v15_lattices(X0) ) )
          & l3_lattices(X1)
          & v10_lattices(X1)
          & ~ v2_struct_0(X1) )
      & l3_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v15_lattices(k7_filter_1(X0,X1))
            | ~ v15_lattices(X1)
            | ~ v15_lattices(X0) )
          & ( v15_lattices(k7_filter_1(X0,X1))
            | ( v15_lattices(X1)
              & v15_lattices(X0) ) )
          & l3_lattices(X1)
          & v10_lattices(X1)
          & ~ v2_struct_0(X1) )
      & l3_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( v15_lattices(X1)
              & v15_lattices(X0) )
          <~> v15_lattices(k7_filter_1(X0,X1)) )
          & l3_lattices(X1)
          & v10_lattices(X1)
          & ~ v2_struct_0(X1) )
      & l3_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( v15_lattices(X1)
              & v15_lattices(X0) )
          <~> v15_lattices(k7_filter_1(X0,X1)) )
          & l3_lattices(X1)
          & v10_lattices(X1)
          & ~ v2_struct_0(X1) )
      & l3_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l3_lattices(X1)
              & v10_lattices(X1)
              & ~ v2_struct_0(X1) )
           => ( ( v15_lattices(X1)
                & v15_lattices(X0) )
            <=> v15_lattices(k7_filter_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l3_lattices(X1)
            & v10_lattices(X1)
            & ~ v2_struct_0(X1) )
         => ( ( v15_lattices(X1)
              & v15_lattices(X0) )
          <=> v15_lattices(k7_filter_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_filter_1)).

fof(f455,plain,
    ( ~ spl2_3
    | ~ spl2_46
    | spl2_1
    | ~ spl2_2
    | ~ spl2_56 ),
    inference(avatar_split_clause,[],[f414,f411,f59,f54,f349,f64])).

fof(f411,plain,
    ( spl2_56
  <=> ! [X0] :
        ( ~ v13_lattices(k7_filter_1(X0,sK1))
        | v2_struct_0(X0)
        | ~ v10_lattices(X0)
        | ~ l3_lattices(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_56])])).

fof(f414,plain,
    ( v2_struct_0(sK0)
    | ~ v13_lattices(k7_filter_1(sK0,sK1))
    | ~ l3_lattices(sK0)
    | ~ spl2_2
    | ~ spl2_56 ),
    inference(resolution,[],[f412,f61])).

fof(f61,plain,
    ( v10_lattices(sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f59])).

fof(f412,plain,
    ( ! [X0] :
        ( ~ v10_lattices(X0)
        | v2_struct_0(X0)
        | ~ v13_lattices(k7_filter_1(X0,sK1))
        | ~ l3_lattices(X0) )
    | ~ spl2_56 ),
    inference(avatar_component_clause,[],[f411])).

fof(f453,plain,
    ( spl2_24
    | ~ spl2_25
    | ~ spl2_8
    | ~ spl2_9
    | spl2_46 ),
    inference(avatar_split_clause,[],[f356,f349,f93,f88,f168,f164])).

fof(f93,plain,
    ( spl2_9
  <=> ! [X0] :
        ( v13_lattices(X0)
        | ~ v15_lattices(X0)
        | ~ l3_lattices(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f356,plain,
    ( ~ v15_lattices(k7_filter_1(sK0,sK1))
    | ~ l3_lattices(k7_filter_1(sK0,sK1))
    | v2_struct_0(k7_filter_1(sK0,sK1))
    | ~ spl2_9
    | spl2_46 ),
    inference(resolution,[],[f351,f94])).

fof(f94,plain,
    ( ! [X0] :
        ( v13_lattices(X0)
        | ~ v15_lattices(X0)
        | ~ l3_lattices(X0)
        | v2_struct_0(X0) )
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f93])).

fof(f413,plain,
    ( spl2_4
    | ~ spl2_5
    | ~ spl2_6
    | spl2_56
    | ~ spl2_18
    | spl2_31 ),
    inference(avatar_split_clause,[],[f407,f217,f132,f411,f79,f74,f69])).

fof(f132,plain,
    ( spl2_18
  <=> ! [X1,X0] :
        ( v13_lattices(X1)
        | ~ v13_lattices(k7_filter_1(X0,X1))
        | ~ l3_lattices(X1)
        | ~ v10_lattices(X1)
        | v2_struct_0(X1)
        | ~ l3_lattices(X0)
        | ~ v10_lattices(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f407,plain,
    ( ! [X0] :
        ( ~ v13_lattices(k7_filter_1(X0,sK1))
        | ~ l3_lattices(sK1)
        | ~ v10_lattices(sK1)
        | v2_struct_0(sK1)
        | ~ l3_lattices(X0)
        | ~ v10_lattices(X0)
        | v2_struct_0(X0) )
    | ~ spl2_18
    | spl2_31 ),
    inference(resolution,[],[f219,f133])).

fof(f133,plain,
    ( ! [X0,X1] :
        ( v13_lattices(X1)
        | ~ v13_lattices(k7_filter_1(X0,X1))
        | ~ l3_lattices(X1)
        | ~ v10_lattices(X1)
        | v2_struct_0(X1)
        | ~ l3_lattices(X0)
        | ~ v10_lattices(X0)
        | v2_struct_0(X0) )
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f132])).

fof(f219,plain,
    ( ~ v13_lattices(sK1)
    | spl2_31 ),
    inference(avatar_component_clause,[],[f217])).

fof(f352,plain,
    ( ~ spl2_6
    | ~ spl2_46
    | spl2_4
    | ~ spl2_5
    | ~ spl2_43 ),
    inference(avatar_split_clause,[],[f333,f324,f74,f69,f349,f79])).

fof(f324,plain,
    ( spl2_43
  <=> ! [X1] :
        ( ~ v13_lattices(k7_filter_1(sK0,X1))
        | v2_struct_0(X1)
        | ~ v10_lattices(X1)
        | ~ l3_lattices(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_43])])).

fof(f333,plain,
    ( v2_struct_0(sK1)
    | ~ v13_lattices(k7_filter_1(sK0,sK1))
    | ~ l3_lattices(sK1)
    | ~ spl2_5
    | ~ spl2_43 ),
    inference(resolution,[],[f325,f76])).

fof(f76,plain,
    ( v10_lattices(sK1)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f74])).

fof(f325,plain,
    ( ! [X1] :
        ( ~ v10_lattices(X1)
        | v2_struct_0(X1)
        | ~ v13_lattices(k7_filter_1(sK0,X1))
        | ~ l3_lattices(X1) )
    | ~ spl2_43 ),
    inference(avatar_component_clause,[],[f324])).

fof(f326,plain,
    ( spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | spl2_43
    | ~ spl2_17
    | spl2_28 ),
    inference(avatar_split_clause,[],[f250,f190,f128,f324,f64,f59,f54])).

fof(f128,plain,
    ( spl2_17
  <=> ! [X1,X0] :
        ( v13_lattices(X0)
        | ~ v13_lattices(k7_filter_1(X0,X1))
        | ~ l3_lattices(X1)
        | ~ v10_lattices(X1)
        | v2_struct_0(X1)
        | ~ l3_lattices(X0)
        | ~ v10_lattices(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f250,plain,
    ( ! [X1] :
        ( ~ v13_lattices(k7_filter_1(sK0,X1))
        | ~ l3_lattices(X1)
        | ~ v10_lattices(X1)
        | v2_struct_0(X1)
        | ~ l3_lattices(sK0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl2_17
    | spl2_28 ),
    inference(resolution,[],[f192,f129])).

fof(f129,plain,
    ( ! [X0,X1] :
        ( v13_lattices(X0)
        | ~ v13_lattices(k7_filter_1(X0,X1))
        | ~ l3_lattices(X1)
        | ~ v10_lattices(X1)
        | v2_struct_0(X1)
        | ~ l3_lattices(X0)
        | ~ v10_lattices(X0)
        | v2_struct_0(X0) )
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f128])).

fof(f192,plain,
    ( ~ v13_lattices(sK0)
    | spl2_28 ),
    inference(avatar_component_clause,[],[f190])).

fof(f259,plain,
    ( ~ spl2_6
    | spl2_35
    | spl2_4
    | ~ spl2_30
    | ~ spl2_5
    | ~ spl2_32 ),
    inference(avatar_split_clause,[],[f254,f225,f74,f205,f69,f256,f79])).

fof(f225,plain,
    ( spl2_32
  <=> ! [X0] :
        ( v14_lattices(k7_filter_1(sK0,X0))
        | ~ v15_lattices(X0)
        | v2_struct_0(X0)
        | ~ v10_lattices(X0)
        | ~ l3_lattices(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).

fof(f254,plain,
    ( ~ v15_lattices(sK1)
    | v2_struct_0(sK1)
    | v14_lattices(k7_filter_1(sK0,sK1))
    | ~ l3_lattices(sK1)
    | ~ spl2_5
    | ~ spl2_32 ),
    inference(resolution,[],[f226,f76])).

% (20952)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
fof(f226,plain,
    ( ! [X0] :
        ( ~ v10_lattices(X0)
        | ~ v15_lattices(X0)
        | v2_struct_0(X0)
        | v14_lattices(k7_filter_1(sK0,X0))
        | ~ l3_lattices(X0) )
    | ~ spl2_32 ),
    inference(avatar_component_clause,[],[f225])).

fof(f252,plain,
    ( spl2_4
    | ~ spl2_6
    | ~ spl2_30
    | ~ spl2_9
    | spl2_31 ),
    inference(avatar_split_clause,[],[f223,f217,f93,f205,f79,f69])).

fof(f223,plain,
    ( ~ v15_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ spl2_9
    | spl2_31 ),
    inference(resolution,[],[f219,f94])).

fof(f242,plain,
    ( spl2_1
    | ~ spl2_3
    | ~ spl2_7
    | ~ spl2_10
    | spl2_26 ),
    inference(avatar_split_clause,[],[f240,f172,f97,f84,f64,f54])).

fof(f97,plain,
    ( spl2_10
  <=> ! [X0] :
        ( v14_lattices(X0)
        | ~ v15_lattices(X0)
        | ~ l3_lattices(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f172,plain,
    ( spl2_26
  <=> v14_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).

fof(f240,plain,
    ( ~ v15_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl2_10
    | spl2_26 ),
    inference(resolution,[],[f173,f98])).

fof(f98,plain,
    ( ! [X0] :
        ( v14_lattices(X0)
        | ~ v15_lattices(X0)
        | ~ l3_lattices(X0)
        | v2_struct_0(X0) )
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f97])).

fof(f173,plain,
    ( ~ v14_lattices(sK0)
    | spl2_26 ),
    inference(avatar_component_clause,[],[f172])).

fof(f227,plain,
    ( spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | spl2_32
    | ~ spl2_21
    | ~ spl2_26 ),
    inference(avatar_split_clause,[],[f186,f172,f148,f225,f64,f59,f54])).

fof(f148,plain,
    ( spl2_21
  <=> ! [X1,X0] :
        ( v14_lattices(k7_filter_1(X0,X1))
        | ~ v14_lattices(X0)
        | ~ l3_lattices(X1)
        | ~ v10_lattices(X1)
        | v2_struct_0(X1)
        | ~ l3_lattices(X0)
        | ~ v10_lattices(X0)
        | v2_struct_0(X0)
        | ~ v15_lattices(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).

fof(f186,plain,
    ( ! [X0] :
        ( v14_lattices(k7_filter_1(sK0,X0))
        | ~ l3_lattices(X0)
        | ~ v10_lattices(X0)
        | v2_struct_0(X0)
        | ~ l3_lattices(sK0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0)
        | ~ v15_lattices(X0) )
    | ~ spl2_21
    | ~ spl2_26 ),
    inference(resolution,[],[f174,f149])).

fof(f149,plain,
    ( ! [X0,X1] :
        ( ~ v14_lattices(X0)
        | v14_lattices(k7_filter_1(X0,X1))
        | ~ l3_lattices(X1)
        | ~ v10_lattices(X1)
        | v2_struct_0(X1)
        | ~ l3_lattices(X0)
        | ~ v10_lattices(X0)
        | v2_struct_0(X0)
        | ~ v15_lattices(X1) )
    | ~ spl2_21 ),
    inference(avatar_component_clause,[],[f148])).

fof(f174,plain,
    ( v14_lattices(sK0)
    | ~ spl2_26 ),
    inference(avatar_component_clause,[],[f172])).

fof(f220,plain,
    ( spl2_4
    | ~ spl2_6
    | ~ spl2_31
    | spl2_30
    | ~ spl2_11
    | ~ spl2_29 ),
    inference(avatar_split_clause,[],[f214,f195,f101,f205,f217,f79,f69])).

fof(f195,plain,
    ( spl2_29
  <=> v14_lattices(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).

fof(f214,plain,
    ( v15_lattices(sK1)
    | ~ v13_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ spl2_11
    | ~ spl2_29 ),
    inference(resolution,[],[f197,f102])).

fof(f197,plain,
    ( v14_lattices(sK1)
    | ~ spl2_29 ),
    inference(avatar_component_clause,[],[f195])).

fof(f215,plain,
    ( spl2_1
    | ~ spl2_3
    | ~ spl2_7
    | ~ spl2_9
    | spl2_28 ),
    inference(avatar_split_clause,[],[f203,f190,f93,f84,f64,f54])).

fof(f203,plain,
    ( ~ v15_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl2_9
    | spl2_28 ),
    inference(resolution,[],[f192,f94])).

fof(f208,plain,
    ( spl2_30
    | spl2_8 ),
    inference(avatar_split_clause,[],[f38,f88,f205])).

fof(f38,plain,
    ( v15_lattices(k7_filter_1(sK0,sK1))
    | v15_lattices(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f198,plain,
    ( spl2_24
    | ~ spl2_25
    | spl2_29
    | spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | spl2_4
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_8
    | ~ spl2_27 ),
    inference(avatar_split_clause,[],[f181,f177,f88,f79,f74,f69,f64,f59,f54,f195,f168,f164])).

fof(f177,plain,
    ( spl2_27
  <=> ! [X1,X0] :
        ( v14_lattices(X0)
        | ~ l3_lattices(X0)
        | ~ v10_lattices(X0)
        | v2_struct_0(X0)
        | ~ l3_lattices(X1)
        | ~ v10_lattices(X1)
        | v2_struct_0(X1)
        | ~ v15_lattices(k7_filter_1(X1,X0))
        | ~ l3_lattices(k7_filter_1(X1,X0))
        | v2_struct_0(k7_filter_1(X1,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).

fof(f181,plain,
    ( ~ l3_lattices(sK1)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | v14_lattices(sK1)
    | ~ l3_lattices(k7_filter_1(sK0,sK1))
    | v2_struct_0(k7_filter_1(sK0,sK1))
    | ~ spl2_8
    | ~ spl2_27 ),
    inference(resolution,[],[f178,f90])).

fof(f90,plain,
    ( v15_lattices(k7_filter_1(sK0,sK1))
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f88])).

fof(f178,plain,
    ( ! [X0,X1] :
        ( ~ v15_lattices(k7_filter_1(X1,X0))
        | ~ l3_lattices(X0)
        | ~ v10_lattices(X0)
        | v2_struct_0(X0)
        | ~ l3_lattices(X1)
        | ~ v10_lattices(X1)
        | v2_struct_0(X1)
        | v14_lattices(X0)
        | ~ l3_lattices(k7_filter_1(X1,X0))
        | v2_struct_0(k7_filter_1(X1,X0)) )
    | ~ spl2_27 ),
    inference(avatar_component_clause,[],[f177])).

fof(f193,plain,
    ( spl2_1
    | ~ spl2_3
    | ~ spl2_28
    | spl2_7
    | ~ spl2_11
    | ~ spl2_26 ),
    inference(avatar_split_clause,[],[f188,f172,f101,f84,f190,f64,f54])).

fof(f188,plain,
    ( v15_lattices(sK0)
    | ~ v13_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl2_11
    | ~ spl2_26 ),
    inference(resolution,[],[f174,f102])).

fof(f185,plain,
    ( spl2_1
    | ~ spl2_3
    | spl2_4
    | ~ spl2_6
    | ~ spl2_12
    | ~ spl2_24 ),
    inference(avatar_split_clause,[],[f184,f164,f107,f79,f69,f64,f54])).

fof(f107,plain,
    ( spl2_12
  <=> ! [X1,X0] :
        ( ~ v2_struct_0(k7_filter_1(X0,X1))
        | ~ l3_lattices(X1)
        | v2_struct_0(X1)
        | ~ l3_lattices(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f184,plain,
    ( ~ l3_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl2_12
    | ~ spl2_24 ),
    inference(resolution,[],[f166,f108])).

fof(f108,plain,
    ( ! [X0,X1] :
        ( ~ v2_struct_0(k7_filter_1(X0,X1))
        | ~ l3_lattices(X1)
        | v2_struct_0(X1)
        | ~ l3_lattices(X0)
        | v2_struct_0(X0) )
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f107])).

fof(f166,plain,
    ( v2_struct_0(k7_filter_1(sK0,sK1))
    | ~ spl2_24 ),
    inference(avatar_component_clause,[],[f164])).

fof(f183,plain,
    ( spl2_1
    | ~ spl2_3
    | spl2_4
    | ~ spl2_6
    | ~ spl2_14
    | spl2_25 ),
    inference(avatar_split_clause,[],[f182,f168,f116,f79,f69,f64,f54])).

fof(f116,plain,
    ( spl2_14
  <=> ! [X1,X0] :
        ( l3_lattices(k7_filter_1(X0,X1))
        | ~ l3_lattices(X1)
        | v2_struct_0(X1)
        | ~ l3_lattices(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f182,plain,
    ( ~ l3_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl2_14
    | spl2_25 ),
    inference(resolution,[],[f170,f117])).

fof(f117,plain,
    ( ! [X0,X1] :
        ( l3_lattices(k7_filter_1(X0,X1))
        | ~ l3_lattices(X1)
        | v2_struct_0(X1)
        | ~ l3_lattices(X0)
        | v2_struct_0(X0) )
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f116])).

fof(f170,plain,
    ( ~ l3_lattices(k7_filter_1(sK0,sK1))
    | spl2_25 ),
    inference(avatar_component_clause,[],[f168])).

fof(f179,plain,
    ( spl2_27
    | ~ spl2_10
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f136,f124,f97,f177])).

fof(f124,plain,
    ( spl2_16
  <=> ! [X1,X0] :
        ( v14_lattices(X1)
        | ~ v14_lattices(k7_filter_1(X0,X1))
        | ~ l3_lattices(X1)
        | ~ v10_lattices(X1)
        | v2_struct_0(X1)
        | ~ l3_lattices(X0)
        | ~ v10_lattices(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f136,plain,
    ( ! [X0,X1] :
        ( v14_lattices(X0)
        | ~ l3_lattices(X0)
        | ~ v10_lattices(X0)
        | v2_struct_0(X0)
        | ~ l3_lattices(X1)
        | ~ v10_lattices(X1)
        | v2_struct_0(X1)
        | ~ v15_lattices(k7_filter_1(X1,X0))
        | ~ l3_lattices(k7_filter_1(X1,X0))
        | v2_struct_0(k7_filter_1(X1,X0)) )
    | ~ spl2_10
    | ~ spl2_16 ),
    inference(resolution,[],[f125,f98])).

fof(f125,plain,
    ( ! [X0,X1] :
        ( ~ v14_lattices(k7_filter_1(X0,X1))
        | v14_lattices(X1)
        | ~ l3_lattices(X1)
        | ~ v10_lattices(X1)
        | v2_struct_0(X1)
        | ~ l3_lattices(X0)
        | ~ v10_lattices(X0)
        | v2_struct_0(X0) )
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f124])).

fof(f175,plain,
    ( spl2_24
    | ~ spl2_25
    | spl2_26
    | spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | spl2_4
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_8
    | ~ spl2_23 ),
    inference(avatar_split_clause,[],[f162,f159,f88,f79,f74,f69,f64,f59,f54,f172,f168,f164])).

fof(f159,plain,
    ( spl2_23
  <=> ! [X1,X0] :
        ( v14_lattices(X0)
        | ~ l3_lattices(X1)
        | ~ v10_lattices(X1)
        | v2_struct_0(X1)
        | ~ l3_lattices(X0)
        | ~ v10_lattices(X0)
        | v2_struct_0(X0)
        | ~ v15_lattices(k7_filter_1(X0,X1))
        | ~ l3_lattices(k7_filter_1(X0,X1))
        | v2_struct_0(k7_filter_1(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f162,plain,
    ( ~ l3_lattices(sK1)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | v14_lattices(sK0)
    | ~ l3_lattices(k7_filter_1(sK0,sK1))
    | v2_struct_0(k7_filter_1(sK0,sK1))
    | ~ spl2_8
    | ~ spl2_23 ),
    inference(resolution,[],[f160,f90])).

fof(f160,plain,
    ( ! [X0,X1] :
        ( ~ v15_lattices(k7_filter_1(X0,X1))
        | ~ l3_lattices(X1)
        | ~ v10_lattices(X1)
        | v2_struct_0(X1)
        | ~ l3_lattices(X0)
        | ~ v10_lattices(X0)
        | v2_struct_0(X0)
        | v14_lattices(X0)
        | ~ l3_lattices(k7_filter_1(X0,X1))
        | v2_struct_0(k7_filter_1(X0,X1)) )
    | ~ spl2_23 ),
    inference(avatar_component_clause,[],[f159])).

fof(f161,plain,
    ( spl2_23
    | ~ spl2_10
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f135,f120,f97,f159])).

fof(f120,plain,
    ( spl2_15
  <=> ! [X1,X0] :
        ( v14_lattices(X0)
        | ~ v14_lattices(k7_filter_1(X0,X1))
        | ~ l3_lattices(X1)
        | ~ v10_lattices(X1)
        | v2_struct_0(X1)
        | ~ l3_lattices(X0)
        | ~ v10_lattices(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f135,plain,
    ( ! [X0,X1] :
        ( v14_lattices(X0)
        | ~ l3_lattices(X1)
        | ~ v10_lattices(X1)
        | v2_struct_0(X1)
        | ~ l3_lattices(X0)
        | ~ v10_lattices(X0)
        | v2_struct_0(X0)
        | ~ v15_lattices(k7_filter_1(X0,X1))
        | ~ l3_lattices(k7_filter_1(X0,X1))
        | v2_struct_0(k7_filter_1(X0,X1)) )
    | ~ spl2_10
    | ~ spl2_15 ),
    inference(resolution,[],[f121,f98])).

fof(f121,plain,
    ( ! [X0,X1] :
        ( ~ v14_lattices(k7_filter_1(X0,X1))
        | v14_lattices(X0)
        | ~ l3_lattices(X1)
        | ~ v10_lattices(X1)
        | v2_struct_0(X1)
        | ~ l3_lattices(X0)
        | ~ v10_lattices(X0)
        | v2_struct_0(X0) )
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f120])).

fof(f150,plain,
    ( spl2_21
    | ~ spl2_10
    | ~ spl2_19 ),
    inference(avatar_split_clause,[],[f146,f138,f97,f148])).

fof(f138,plain,
    ( spl2_19
  <=> ! [X1,X0] :
        ( v14_lattices(k7_filter_1(X0,X1))
        | ~ v14_lattices(X1)
        | ~ v14_lattices(X0)
        | ~ l3_lattices(X1)
        | ~ v10_lattices(X1)
        | v2_struct_0(X1)
        | ~ l3_lattices(X0)
        | ~ v10_lattices(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f146,plain,
    ( ! [X0,X1] :
        ( v14_lattices(k7_filter_1(X0,X1))
        | ~ v14_lattices(X0)
        | ~ l3_lattices(X1)
        | ~ v10_lattices(X1)
        | v2_struct_0(X1)
        | ~ l3_lattices(X0)
        | ~ v10_lattices(X0)
        | v2_struct_0(X0)
        | ~ v15_lattices(X1) )
    | ~ spl2_10
    | ~ spl2_19 ),
    inference(duplicate_literal_removal,[],[f145])).

fof(f145,plain,
    ( ! [X0,X1] :
        ( v14_lattices(k7_filter_1(X0,X1))
        | ~ v14_lattices(X0)
        | ~ l3_lattices(X1)
        | ~ v10_lattices(X1)
        | v2_struct_0(X1)
        | ~ l3_lattices(X0)
        | ~ v10_lattices(X0)
        | v2_struct_0(X0)
        | ~ v15_lattices(X1)
        | ~ l3_lattices(X1)
        | v2_struct_0(X1) )
    | ~ spl2_10
    | ~ spl2_19 ),
    inference(resolution,[],[f139,f98])).

fof(f139,plain,
    ( ! [X0,X1] :
        ( ~ v14_lattices(X1)
        | v14_lattices(k7_filter_1(X0,X1))
        | ~ v14_lattices(X0)
        | ~ l3_lattices(X1)
        | ~ v10_lattices(X1)
        | v2_struct_0(X1)
        | ~ l3_lattices(X0)
        | ~ v10_lattices(X0)
        | v2_struct_0(X0) )
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f138])).

fof(f144,plain,(
    spl2_20 ),
    inference(avatar_split_clause,[],[f43,f142])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v13_lattices(k7_filter_1(X0,X1))
      | ~ v13_lattices(X1)
      | ~ v13_lattices(X0)
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( ( v13_lattices(X1)
                & v13_lattices(X0) )
              | ~ v13_lattices(k7_filter_1(X0,X1)) )
            & ( v13_lattices(k7_filter_1(X0,X1))
              | ~ v13_lattices(X1)
              | ~ v13_lattices(X0) ) )
          | ~ l3_lattices(X1)
          | ~ v10_lattices(X1)
          | v2_struct_0(X1) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( ( v13_lattices(X1)
                & v13_lattices(X0) )
              | ~ v13_lattices(k7_filter_1(X0,X1)) )
            & ( v13_lattices(k7_filter_1(X0,X1))
              | ~ v13_lattices(X1)
              | ~ v13_lattices(X0) ) )
          | ~ l3_lattices(X1)
          | ~ v10_lattices(X1)
          | v2_struct_0(X1) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v13_lattices(X1)
              & v13_lattices(X0) )
          <=> v13_lattices(k7_filter_1(X0,X1)) )
          | ~ l3_lattices(X1)
          | ~ v10_lattices(X1)
          | v2_struct_0(X1) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v13_lattices(X1)
              & v13_lattices(X0) )
          <=> v13_lattices(k7_filter_1(X0,X1)) )
          | ~ l3_lattices(X1)
          | ~ v10_lattices(X1)
          | v2_struct_0(X1) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l3_lattices(X1)
            & v10_lattices(X1)
            & ~ v2_struct_0(X1) )
         => ( ( v13_lattices(X1)
              & v13_lattices(X0) )
          <=> v13_lattices(k7_filter_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_filter_1)).

fof(f140,plain,(
    spl2_19 ),
    inference(avatar_split_clause,[],[f40,f138])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v14_lattices(k7_filter_1(X0,X1))
      | ~ v14_lattices(X1)
      | ~ v14_lattices(X0)
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( ( v14_lattices(X1)
                & v14_lattices(X0) )
              | ~ v14_lattices(k7_filter_1(X0,X1)) )
            & ( v14_lattices(k7_filter_1(X0,X1))
              | ~ v14_lattices(X1)
              | ~ v14_lattices(X0) ) )
          | ~ l3_lattices(X1)
          | ~ v10_lattices(X1)
          | v2_struct_0(X1) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( ( v14_lattices(X1)
                & v14_lattices(X0) )
              | ~ v14_lattices(k7_filter_1(X0,X1)) )
            & ( v14_lattices(k7_filter_1(X0,X1))
              | ~ v14_lattices(X1)
              | ~ v14_lattices(X0) ) )
          | ~ l3_lattices(X1)
          | ~ v10_lattices(X1)
          | v2_struct_0(X1) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v14_lattices(X1)
              & v14_lattices(X0) )
          <=> v14_lattices(k7_filter_1(X0,X1)) )
          | ~ l3_lattices(X1)
          | ~ v10_lattices(X1)
          | v2_struct_0(X1) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v14_lattices(X1)
              & v14_lattices(X0) )
          <=> v14_lattices(k7_filter_1(X0,X1)) )
          | ~ l3_lattices(X1)
          | ~ v10_lattices(X1)
          | v2_struct_0(X1) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l3_lattices(X1)
            & v10_lattices(X1)
            & ~ v2_struct_0(X1) )
         => ( ( v14_lattices(X1)
              & v14_lattices(X0) )
          <=> v14_lattices(k7_filter_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_filter_1)).

fof(f134,plain,(
    spl2_18 ),
    inference(avatar_split_clause,[],[f45,f132])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v13_lattices(X1)
      | ~ v13_lattices(k7_filter_1(X0,X1))
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f130,plain,(
    spl2_17 ),
    inference(avatar_split_clause,[],[f44,f128])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v13_lattices(X0)
      | ~ v13_lattices(k7_filter_1(X0,X1))
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f126,plain,(
    spl2_16 ),
    inference(avatar_split_clause,[],[f42,f124])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v14_lattices(X1)
      | ~ v14_lattices(k7_filter_1(X0,X1))
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f122,plain,(
    spl2_15 ),
    inference(avatar_split_clause,[],[f41,f120])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v14_lattices(X0)
      | ~ v14_lattices(k7_filter_1(X0,X1))
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f118,plain,(
    spl2_14 ),
    inference(avatar_split_clause,[],[f52,f116])).

fof(f52,plain,(
    ! [X0,X1] :
      ( l3_lattices(k7_filter_1(X0,X1))
      | ~ l3_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( l3_lattices(k7_filter_1(X0,X1))
        & v3_lattices(k7_filter_1(X0,X1)) )
      | ~ l3_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( l3_lattices(k7_filter_1(X0,X1))
        & v3_lattices(k7_filter_1(X0,X1)) )
      | ~ l3_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X1)
        & ~ v2_struct_0(X1)
        & l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( l3_lattices(k7_filter_1(X0,X1))
        & v3_lattices(k7_filter_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_filter_1)).

fof(f109,plain,(
    spl2_12 ),
    inference(avatar_split_clause,[],[f49,f107])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k7_filter_1(X0,X1))
      | ~ l3_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( v3_lattices(k7_filter_1(X0,X1))
        & ~ v2_struct_0(k7_filter_1(X0,X1)) )
      | ~ l3_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( v3_lattices(k7_filter_1(X0,X1))
        & ~ v2_struct_0(k7_filter_1(X0,X1)) )
      | ~ l3_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X1)
        & ~ v2_struct_0(X1)
        & l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v3_lattices(k7_filter_1(X0,X1))
        & ~ v2_struct_0(k7_filter_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_filter_1)).

fof(f103,plain,(
    spl2_11 ),
    inference(avatar_split_clause,[],[f48,f101])).

fof(f48,plain,(
    ! [X0] :
      ( v15_lattices(X0)
      | ~ v14_lattices(X0)
      | ~ v13_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( ( v15_lattices(X0)
          | ~ v14_lattices(X0)
          | ~ v13_lattices(X0) )
        & ( ( v14_lattices(X0)
            & v13_lattices(X0) )
          | ~ v15_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( ( v15_lattices(X0)
          | ~ v14_lattices(X0)
          | ~ v13_lattices(X0) )
        & ( ( v14_lattices(X0)
            & v13_lattices(X0) )
          | ~ v15_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( v15_lattices(X0)
      <=> ( v14_lattices(X0)
          & v13_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( v15_lattices(X0)
      <=> ( v14_lattices(X0)
          & v13_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v15_lattices(X0)
      <=> ( v14_lattices(X0)
          & v13_lattices(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d15_lattices)).

fof(f99,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f47,f97])).

fof(f47,plain,(
    ! [X0] :
      ( v14_lattices(X0)
      | ~ v15_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f95,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f46,f93])).

fof(f46,plain,(
    ! [X0] :
      ( v13_lattices(X0)
      | ~ v15_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f91,plain,
    ( spl2_7
    | spl2_8 ),
    inference(avatar_split_clause,[],[f37,f88,f84])).

fof(f37,plain,
    ( v15_lattices(k7_filter_1(sK0,sK1))
    | v15_lattices(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f82,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f36,f79])).

fof(f36,plain,(
    l3_lattices(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f77,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f35,f74])).

fof(f35,plain,(
    v10_lattices(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f72,plain,(
    ~ spl2_4 ),
    inference(avatar_split_clause,[],[f34,f69])).

fof(f34,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f67,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f33,f64])).

fof(f33,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f62,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f32,f59])).

fof(f32,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f57,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f31,f54])).

fof(f31,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:54:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.47  % (20949)dis+1_3_add=large:afp=4000:afq=1.0:anc=none:gs=on:gsem=off:inw=on:lcm=reverse:lwlo=on:nm=64:nwc=1:sas=z3:sos=all:sac=on:thi=all:uwa=all:updr=off:uhcvi=on_12 on theBenchmark
% 0.22/0.47  % (20957)dis+11_3_awrs=decay:awrsf=256:av=off:gs=on:gsem=on:lcm=reverse:nm=0:nwc=1:sos=all:sp=frequency:updr=off_4 on theBenchmark
% 0.22/0.48  % (20948)lrs-11_4:1_afp=4000:afq=2.0:anc=none:br=off:gs=on:lwlo=on:nm=64:nwc=3:stl=30:urr=on_3 on theBenchmark
% 0.22/0.48  % (20962)dis+1011_4_awrs=decay:awrsf=32:afp=40000:afq=1.0:amm=off:anc=all:bs=on:cond=on:fsr=off:gsp=input_only:lma=on:nm=16:nwc=1:nicw=on:sac=on:sp=frequency:thi=all:updr=off:uhcvi=on_670 on theBenchmark
% 0.22/0.49  % (20960)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.22/0.49  % (20962)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f487,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(avatar_sat_refutation,[],[f57,f62,f67,f72,f77,f82,f91,f95,f99,f103,f109,f118,f122,f126,f130,f134,f140,f144,f150,f161,f175,f179,f183,f185,f193,f198,f208,f215,f220,f227,f242,f252,f259,f326,f352,f413,f453,f455,f457,f465,f486])).
% 0.22/0.49  fof(f486,plain,(
% 0.22/0.49    spl2_1 | ~spl2_2 | ~spl2_3 | spl2_4 | ~spl2_5 | ~spl2_6 | ~spl2_28 | ~spl2_31 | ~spl2_20 | spl2_46),
% 0.22/0.49    inference(avatar_split_clause,[],[f466,f349,f142,f217,f190,f79,f74,f69,f64,f59,f54])).
% 0.22/0.49  fof(f54,plain,(
% 0.22/0.49    spl2_1 <=> v2_struct_0(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.49  fof(f59,plain,(
% 0.22/0.49    spl2_2 <=> v10_lattices(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.49  fof(f64,plain,(
% 0.22/0.49    spl2_3 <=> l3_lattices(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.49  fof(f69,plain,(
% 0.22/0.49    spl2_4 <=> v2_struct_0(sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.49  fof(f74,plain,(
% 0.22/0.49    spl2_5 <=> v10_lattices(sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.22/0.49  fof(f79,plain,(
% 0.22/0.49    spl2_6 <=> l3_lattices(sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.22/0.49  fof(f190,plain,(
% 0.22/0.49    spl2_28 <=> v13_lattices(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).
% 0.22/0.49  fof(f217,plain,(
% 0.22/0.49    spl2_31 <=> v13_lattices(sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).
% 0.22/0.49  fof(f142,plain,(
% 0.22/0.49    spl2_20 <=> ! [X1,X0] : (v13_lattices(k7_filter_1(X0,X1)) | ~v13_lattices(X1) | ~v13_lattices(X0) | ~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 0.22/0.49  fof(f349,plain,(
% 0.22/0.49    spl2_46 <=> v13_lattices(k7_filter_1(sK0,sK1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_46])])).
% 0.22/0.49  fof(f466,plain,(
% 0.22/0.49    ~v13_lattices(sK1) | ~v13_lattices(sK0) | ~l3_lattices(sK1) | ~v10_lattices(sK1) | v2_struct_0(sK1) | ~l3_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | (~spl2_20 | spl2_46)),
% 0.22/0.49    inference(resolution,[],[f351,f143])).
% 0.22/0.49  fof(f143,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v13_lattices(k7_filter_1(X0,X1)) | ~v13_lattices(X1) | ~v13_lattices(X0) | ~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) ) | ~spl2_20),
% 0.22/0.49    inference(avatar_component_clause,[],[f142])).
% 0.22/0.49  fof(f351,plain,(
% 0.22/0.49    ~v13_lattices(k7_filter_1(sK0,sK1)) | spl2_46),
% 0.22/0.49    inference(avatar_component_clause,[],[f349])).
% 0.22/0.49  fof(f465,plain,(
% 0.22/0.49    spl2_24 | ~spl2_25 | ~spl2_46 | spl2_8 | ~spl2_11 | ~spl2_35),
% 0.22/0.49    inference(avatar_split_clause,[],[f266,f256,f101,f88,f349,f168,f164])).
% 0.22/0.49  fof(f164,plain,(
% 0.22/0.49    spl2_24 <=> v2_struct_0(k7_filter_1(sK0,sK1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).
% 0.22/0.49  fof(f168,plain,(
% 0.22/0.49    spl2_25 <=> l3_lattices(k7_filter_1(sK0,sK1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).
% 0.22/0.49  fof(f88,plain,(
% 0.22/0.49    spl2_8 <=> v15_lattices(k7_filter_1(sK0,sK1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.22/0.49  fof(f101,plain,(
% 0.22/0.49    spl2_11 <=> ! [X0] : (v15_lattices(X0) | ~v14_lattices(X0) | ~v13_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.22/0.49  fof(f256,plain,(
% 0.22/0.49    spl2_35 <=> v14_lattices(k7_filter_1(sK0,sK1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_35])])).
% 0.22/0.49  fof(f266,plain,(
% 0.22/0.49    v15_lattices(k7_filter_1(sK0,sK1)) | ~v13_lattices(k7_filter_1(sK0,sK1)) | ~l3_lattices(k7_filter_1(sK0,sK1)) | v2_struct_0(k7_filter_1(sK0,sK1)) | (~spl2_11 | ~spl2_35)),
% 0.22/0.49    inference(resolution,[],[f258,f102])).
% 0.22/0.49  fof(f102,plain,(
% 0.22/0.49    ( ! [X0] : (~v14_lattices(X0) | v15_lattices(X0) | ~v13_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) ) | ~spl2_11),
% 0.22/0.49    inference(avatar_component_clause,[],[f101])).
% 0.22/0.49  fof(f258,plain,(
% 0.22/0.49    v14_lattices(k7_filter_1(sK0,sK1)) | ~spl2_35),
% 0.22/0.49    inference(avatar_component_clause,[],[f256])).
% 0.22/0.49  fof(f457,plain,(
% 0.22/0.49    ~spl2_7 | ~spl2_30 | ~spl2_8),
% 0.22/0.49    inference(avatar_split_clause,[],[f39,f88,f205,f84])).
% 0.22/0.49  fof(f84,plain,(
% 0.22/0.49    spl2_7 <=> v15_lattices(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.22/0.49  fof(f205,plain,(
% 0.22/0.49    spl2_30 <=> v15_lattices(sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).
% 0.22/0.49  fof(f39,plain,(
% 0.22/0.49    ~v15_lattices(k7_filter_1(sK0,sK1)) | ~v15_lattices(sK1) | ~v15_lattices(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f24])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    ((~v15_lattices(k7_filter_1(sK0,sK1)) | ~v15_lattices(sK1) | ~v15_lattices(sK0)) & (v15_lattices(k7_filter_1(sK0,sK1)) | (v15_lattices(sK1) & v15_lattices(sK0))) & l3_lattices(sK1) & v10_lattices(sK1) & ~v2_struct_0(sK1)) & l3_lattices(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f23,f22])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : ((~v15_lattices(k7_filter_1(X0,X1)) | ~v15_lattices(X1) | ~v15_lattices(X0)) & (v15_lattices(k7_filter_1(X0,X1)) | (v15_lattices(X1) & v15_lattices(X0))) & l3_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) & l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v15_lattices(k7_filter_1(sK0,X1)) | ~v15_lattices(X1) | ~v15_lattices(sK0)) & (v15_lattices(k7_filter_1(sK0,X1)) | (v15_lattices(X1) & v15_lattices(sK0))) & l3_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) & l3_lattices(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    ? [X1] : ((~v15_lattices(k7_filter_1(sK0,X1)) | ~v15_lattices(X1) | ~v15_lattices(sK0)) & (v15_lattices(k7_filter_1(sK0,X1)) | (v15_lattices(X1) & v15_lattices(sK0))) & l3_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => ((~v15_lattices(k7_filter_1(sK0,sK1)) | ~v15_lattices(sK1) | ~v15_lattices(sK0)) & (v15_lattices(k7_filter_1(sK0,sK1)) | (v15_lattices(sK1) & v15_lattices(sK0))) & l3_lattices(sK1) & v10_lattices(sK1) & ~v2_struct_0(sK1))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : ((~v15_lattices(k7_filter_1(X0,X1)) | ~v15_lattices(X1) | ~v15_lattices(X0)) & (v15_lattices(k7_filter_1(X0,X1)) | (v15_lattices(X1) & v15_lattices(X0))) & l3_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) & l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f20])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (((~v15_lattices(k7_filter_1(X0,X1)) | (~v15_lattices(X1) | ~v15_lattices(X0))) & (v15_lattices(k7_filter_1(X0,X1)) | (v15_lattices(X1) & v15_lattices(X0)))) & l3_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) & l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 0.22/0.49    inference(nnf_transformation,[],[f9])).
% 0.22/0.49  fof(f9,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (((v15_lattices(X1) & v15_lattices(X0)) <~> v15_lattices(k7_filter_1(X0,X1))) & l3_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) & l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f8])).
% 0.22/0.49  fof(f8,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (((v15_lattices(X1) & v15_lattices(X0)) <~> v15_lattices(k7_filter_1(X0,X1))) & (l3_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1))) & (l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,negated_conjecture,(
% 0.22/0.49    ~! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l3_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => ((v15_lattices(X1) & v15_lattices(X0)) <=> v15_lattices(k7_filter_1(X0,X1)))))),
% 0.22/0.49    inference(negated_conjecture,[],[f6])).
% 0.22/0.49  fof(f6,conjecture,(
% 0.22/0.49    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l3_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => ((v15_lattices(X1) & v15_lattices(X0)) <=> v15_lattices(k7_filter_1(X0,X1)))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_filter_1)).
% 0.22/0.49  fof(f455,plain,(
% 0.22/0.49    ~spl2_3 | ~spl2_46 | spl2_1 | ~spl2_2 | ~spl2_56),
% 0.22/0.49    inference(avatar_split_clause,[],[f414,f411,f59,f54,f349,f64])).
% 0.22/0.49  fof(f411,plain,(
% 0.22/0.49    spl2_56 <=> ! [X0] : (~v13_lattices(k7_filter_1(X0,sK1)) | v2_struct_0(X0) | ~v10_lattices(X0) | ~l3_lattices(X0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_56])])).
% 0.22/0.49  fof(f414,plain,(
% 0.22/0.49    v2_struct_0(sK0) | ~v13_lattices(k7_filter_1(sK0,sK1)) | ~l3_lattices(sK0) | (~spl2_2 | ~spl2_56)),
% 0.22/0.49    inference(resolution,[],[f412,f61])).
% 0.22/0.49  fof(f61,plain,(
% 0.22/0.49    v10_lattices(sK0) | ~spl2_2),
% 0.22/0.49    inference(avatar_component_clause,[],[f59])).
% 0.22/0.49  fof(f412,plain,(
% 0.22/0.49    ( ! [X0] : (~v10_lattices(X0) | v2_struct_0(X0) | ~v13_lattices(k7_filter_1(X0,sK1)) | ~l3_lattices(X0)) ) | ~spl2_56),
% 0.22/0.49    inference(avatar_component_clause,[],[f411])).
% 0.22/0.49  fof(f453,plain,(
% 0.22/0.49    spl2_24 | ~spl2_25 | ~spl2_8 | ~spl2_9 | spl2_46),
% 0.22/0.49    inference(avatar_split_clause,[],[f356,f349,f93,f88,f168,f164])).
% 0.22/0.49  fof(f93,plain,(
% 0.22/0.49    spl2_9 <=> ! [X0] : (v13_lattices(X0) | ~v15_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.22/0.49  fof(f356,plain,(
% 0.22/0.49    ~v15_lattices(k7_filter_1(sK0,sK1)) | ~l3_lattices(k7_filter_1(sK0,sK1)) | v2_struct_0(k7_filter_1(sK0,sK1)) | (~spl2_9 | spl2_46)),
% 0.22/0.49    inference(resolution,[],[f351,f94])).
% 0.22/0.49  fof(f94,plain,(
% 0.22/0.49    ( ! [X0] : (v13_lattices(X0) | ~v15_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) ) | ~spl2_9),
% 0.22/0.49    inference(avatar_component_clause,[],[f93])).
% 0.22/0.49  fof(f413,plain,(
% 0.22/0.49    spl2_4 | ~spl2_5 | ~spl2_6 | spl2_56 | ~spl2_18 | spl2_31),
% 0.22/0.49    inference(avatar_split_clause,[],[f407,f217,f132,f411,f79,f74,f69])).
% 0.22/0.49  fof(f132,plain,(
% 0.22/0.49    spl2_18 <=> ! [X1,X0] : (v13_lattices(X1) | ~v13_lattices(k7_filter_1(X0,X1)) | ~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.22/0.49  fof(f407,plain,(
% 0.22/0.49    ( ! [X0] : (~v13_lattices(k7_filter_1(X0,sK1)) | ~l3_lattices(sK1) | ~v10_lattices(sK1) | v2_struct_0(sK1) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) ) | (~spl2_18 | spl2_31)),
% 0.22/0.49    inference(resolution,[],[f219,f133])).
% 0.22/0.49  fof(f133,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v13_lattices(X1) | ~v13_lattices(k7_filter_1(X0,X1)) | ~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) ) | ~spl2_18),
% 0.22/0.49    inference(avatar_component_clause,[],[f132])).
% 0.22/0.49  fof(f219,plain,(
% 0.22/0.49    ~v13_lattices(sK1) | spl2_31),
% 0.22/0.49    inference(avatar_component_clause,[],[f217])).
% 0.22/0.49  fof(f352,plain,(
% 0.22/0.49    ~spl2_6 | ~spl2_46 | spl2_4 | ~spl2_5 | ~spl2_43),
% 0.22/0.49    inference(avatar_split_clause,[],[f333,f324,f74,f69,f349,f79])).
% 0.22/0.49  fof(f324,plain,(
% 0.22/0.49    spl2_43 <=> ! [X1] : (~v13_lattices(k7_filter_1(sK0,X1)) | v2_struct_0(X1) | ~v10_lattices(X1) | ~l3_lattices(X1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_43])])).
% 0.22/0.49  fof(f333,plain,(
% 0.22/0.49    v2_struct_0(sK1) | ~v13_lattices(k7_filter_1(sK0,sK1)) | ~l3_lattices(sK1) | (~spl2_5 | ~spl2_43)),
% 0.22/0.49    inference(resolution,[],[f325,f76])).
% 0.22/0.49  fof(f76,plain,(
% 0.22/0.49    v10_lattices(sK1) | ~spl2_5),
% 0.22/0.49    inference(avatar_component_clause,[],[f74])).
% 0.22/0.49  fof(f325,plain,(
% 0.22/0.49    ( ! [X1] : (~v10_lattices(X1) | v2_struct_0(X1) | ~v13_lattices(k7_filter_1(sK0,X1)) | ~l3_lattices(X1)) ) | ~spl2_43),
% 0.22/0.49    inference(avatar_component_clause,[],[f324])).
% 0.22/0.49  fof(f326,plain,(
% 0.22/0.49    spl2_1 | ~spl2_2 | ~spl2_3 | spl2_43 | ~spl2_17 | spl2_28),
% 0.22/0.49    inference(avatar_split_clause,[],[f250,f190,f128,f324,f64,f59,f54])).
% 0.22/0.49  fof(f128,plain,(
% 0.22/0.49    spl2_17 <=> ! [X1,X0] : (v13_lattices(X0) | ~v13_lattices(k7_filter_1(X0,X1)) | ~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.22/0.49  fof(f250,plain,(
% 0.22/0.49    ( ! [X1] : (~v13_lattices(k7_filter_1(sK0,X1)) | ~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | (~spl2_17 | spl2_28)),
% 0.22/0.49    inference(resolution,[],[f192,f129])).
% 0.22/0.49  fof(f129,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v13_lattices(X0) | ~v13_lattices(k7_filter_1(X0,X1)) | ~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) ) | ~spl2_17),
% 0.22/0.49    inference(avatar_component_clause,[],[f128])).
% 0.22/0.49  fof(f192,plain,(
% 0.22/0.49    ~v13_lattices(sK0) | spl2_28),
% 0.22/0.49    inference(avatar_component_clause,[],[f190])).
% 0.22/0.49  fof(f259,plain,(
% 0.22/0.49    ~spl2_6 | spl2_35 | spl2_4 | ~spl2_30 | ~spl2_5 | ~spl2_32),
% 0.22/0.49    inference(avatar_split_clause,[],[f254,f225,f74,f205,f69,f256,f79])).
% 0.22/0.49  fof(f225,plain,(
% 0.22/0.49    spl2_32 <=> ! [X0] : (v14_lattices(k7_filter_1(sK0,X0)) | ~v15_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | ~l3_lattices(X0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).
% 0.22/0.49  fof(f254,plain,(
% 0.22/0.49    ~v15_lattices(sK1) | v2_struct_0(sK1) | v14_lattices(k7_filter_1(sK0,sK1)) | ~l3_lattices(sK1) | (~spl2_5 | ~spl2_32)),
% 0.22/0.49    inference(resolution,[],[f226,f76])).
% 0.22/0.49  % (20952)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.22/0.49  fof(f226,plain,(
% 0.22/0.49    ( ! [X0] : (~v10_lattices(X0) | ~v15_lattices(X0) | v2_struct_0(X0) | v14_lattices(k7_filter_1(sK0,X0)) | ~l3_lattices(X0)) ) | ~spl2_32),
% 0.22/0.49    inference(avatar_component_clause,[],[f225])).
% 0.22/0.49  fof(f252,plain,(
% 0.22/0.49    spl2_4 | ~spl2_6 | ~spl2_30 | ~spl2_9 | spl2_31),
% 0.22/0.49    inference(avatar_split_clause,[],[f223,f217,f93,f205,f79,f69])).
% 0.22/0.49  fof(f223,plain,(
% 0.22/0.49    ~v15_lattices(sK1) | ~l3_lattices(sK1) | v2_struct_0(sK1) | (~spl2_9 | spl2_31)),
% 0.22/0.49    inference(resolution,[],[f219,f94])).
% 0.22/0.49  fof(f242,plain,(
% 0.22/0.49    spl2_1 | ~spl2_3 | ~spl2_7 | ~spl2_10 | spl2_26),
% 0.22/0.49    inference(avatar_split_clause,[],[f240,f172,f97,f84,f64,f54])).
% 0.22/0.49  fof(f97,plain,(
% 0.22/0.49    spl2_10 <=> ! [X0] : (v14_lattices(X0) | ~v15_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.22/0.49  fof(f172,plain,(
% 0.22/0.49    spl2_26 <=> v14_lattices(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).
% 0.22/0.49  fof(f240,plain,(
% 0.22/0.49    ~v15_lattices(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK0) | (~spl2_10 | spl2_26)),
% 0.22/0.49    inference(resolution,[],[f173,f98])).
% 0.22/0.49  fof(f98,plain,(
% 0.22/0.49    ( ! [X0] : (v14_lattices(X0) | ~v15_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) ) | ~spl2_10),
% 0.22/0.49    inference(avatar_component_clause,[],[f97])).
% 0.22/0.49  fof(f173,plain,(
% 0.22/0.49    ~v14_lattices(sK0) | spl2_26),
% 0.22/0.49    inference(avatar_component_clause,[],[f172])).
% 0.22/0.49  fof(f227,plain,(
% 0.22/0.49    spl2_1 | ~spl2_2 | ~spl2_3 | spl2_32 | ~spl2_21 | ~spl2_26),
% 0.22/0.49    inference(avatar_split_clause,[],[f186,f172,f148,f225,f64,f59,f54])).
% 0.22/0.49  fof(f148,plain,(
% 0.22/0.49    spl2_21 <=> ! [X1,X0] : (v14_lattices(k7_filter_1(X0,X1)) | ~v14_lattices(X0) | ~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~v15_lattices(X1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).
% 0.22/0.49  fof(f186,plain,(
% 0.22/0.49    ( ! [X0] : (v14_lattices(k7_filter_1(sK0,X0)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | ~v15_lattices(X0)) ) | (~spl2_21 | ~spl2_26)),
% 0.22/0.49    inference(resolution,[],[f174,f149])).
% 0.22/0.49  fof(f149,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v14_lattices(X0) | v14_lattices(k7_filter_1(X0,X1)) | ~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~v15_lattices(X1)) ) | ~spl2_21),
% 0.22/0.49    inference(avatar_component_clause,[],[f148])).
% 0.22/0.49  fof(f174,plain,(
% 0.22/0.49    v14_lattices(sK0) | ~spl2_26),
% 0.22/0.49    inference(avatar_component_clause,[],[f172])).
% 0.22/0.49  fof(f220,plain,(
% 0.22/0.49    spl2_4 | ~spl2_6 | ~spl2_31 | spl2_30 | ~spl2_11 | ~spl2_29),
% 0.22/0.49    inference(avatar_split_clause,[],[f214,f195,f101,f205,f217,f79,f69])).
% 0.22/0.49  fof(f195,plain,(
% 0.22/0.49    spl2_29 <=> v14_lattices(sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).
% 0.22/0.49  fof(f214,plain,(
% 0.22/0.49    v15_lattices(sK1) | ~v13_lattices(sK1) | ~l3_lattices(sK1) | v2_struct_0(sK1) | (~spl2_11 | ~spl2_29)),
% 0.22/0.49    inference(resolution,[],[f197,f102])).
% 0.22/0.49  fof(f197,plain,(
% 0.22/0.49    v14_lattices(sK1) | ~spl2_29),
% 0.22/0.49    inference(avatar_component_clause,[],[f195])).
% 0.22/0.49  fof(f215,plain,(
% 0.22/0.49    spl2_1 | ~spl2_3 | ~spl2_7 | ~spl2_9 | spl2_28),
% 0.22/0.49    inference(avatar_split_clause,[],[f203,f190,f93,f84,f64,f54])).
% 0.22/0.49  fof(f203,plain,(
% 0.22/0.49    ~v15_lattices(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK0) | (~spl2_9 | spl2_28)),
% 0.22/0.49    inference(resolution,[],[f192,f94])).
% 0.22/0.49  fof(f208,plain,(
% 0.22/0.49    spl2_30 | spl2_8),
% 0.22/0.49    inference(avatar_split_clause,[],[f38,f88,f205])).
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    v15_lattices(k7_filter_1(sK0,sK1)) | v15_lattices(sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f24])).
% 0.22/0.49  fof(f198,plain,(
% 0.22/0.49    spl2_24 | ~spl2_25 | spl2_29 | spl2_1 | ~spl2_2 | ~spl2_3 | spl2_4 | ~spl2_5 | ~spl2_6 | ~spl2_8 | ~spl2_27),
% 0.22/0.49    inference(avatar_split_clause,[],[f181,f177,f88,f79,f74,f69,f64,f59,f54,f195,f168,f164])).
% 0.22/0.49  fof(f177,plain,(
% 0.22/0.49    spl2_27 <=> ! [X1,X0] : (v14_lattices(X0) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~v15_lattices(k7_filter_1(X1,X0)) | ~l3_lattices(k7_filter_1(X1,X0)) | v2_struct_0(k7_filter_1(X1,X0)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).
% 0.22/0.49  fof(f181,plain,(
% 0.22/0.49    ~l3_lattices(sK1) | ~v10_lattices(sK1) | v2_struct_0(sK1) | ~l3_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | v14_lattices(sK1) | ~l3_lattices(k7_filter_1(sK0,sK1)) | v2_struct_0(k7_filter_1(sK0,sK1)) | (~spl2_8 | ~spl2_27)),
% 0.22/0.49    inference(resolution,[],[f178,f90])).
% 0.22/0.49  fof(f90,plain,(
% 0.22/0.49    v15_lattices(k7_filter_1(sK0,sK1)) | ~spl2_8),
% 0.22/0.49    inference(avatar_component_clause,[],[f88])).
% 0.22/0.49  fof(f178,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v15_lattices(k7_filter_1(X1,X0)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | v14_lattices(X0) | ~l3_lattices(k7_filter_1(X1,X0)) | v2_struct_0(k7_filter_1(X1,X0))) ) | ~spl2_27),
% 0.22/0.49    inference(avatar_component_clause,[],[f177])).
% 0.22/0.49  fof(f193,plain,(
% 0.22/0.49    spl2_1 | ~spl2_3 | ~spl2_28 | spl2_7 | ~spl2_11 | ~spl2_26),
% 0.22/0.49    inference(avatar_split_clause,[],[f188,f172,f101,f84,f190,f64,f54])).
% 0.22/0.49  fof(f188,plain,(
% 0.22/0.49    v15_lattices(sK0) | ~v13_lattices(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK0) | (~spl2_11 | ~spl2_26)),
% 0.22/0.49    inference(resolution,[],[f174,f102])).
% 0.22/0.49  fof(f185,plain,(
% 0.22/0.49    spl2_1 | ~spl2_3 | spl2_4 | ~spl2_6 | ~spl2_12 | ~spl2_24),
% 0.22/0.49    inference(avatar_split_clause,[],[f184,f164,f107,f79,f69,f64,f54])).
% 0.22/0.49  fof(f107,plain,(
% 0.22/0.49    spl2_12 <=> ! [X1,X0] : (~v2_struct_0(k7_filter_1(X0,X1)) | ~l3_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.22/0.49  fof(f184,plain,(
% 0.22/0.49    ~l3_lattices(sK1) | v2_struct_0(sK1) | ~l3_lattices(sK0) | v2_struct_0(sK0) | (~spl2_12 | ~spl2_24)),
% 0.22/0.49    inference(resolution,[],[f166,f108])).
% 0.22/0.49  fof(f108,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v2_struct_0(k7_filter_1(X0,X1)) | ~l3_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X0) | v2_struct_0(X0)) ) | ~spl2_12),
% 0.22/0.49    inference(avatar_component_clause,[],[f107])).
% 0.22/0.49  fof(f166,plain,(
% 0.22/0.49    v2_struct_0(k7_filter_1(sK0,sK1)) | ~spl2_24),
% 0.22/0.49    inference(avatar_component_clause,[],[f164])).
% 0.22/0.49  fof(f183,plain,(
% 0.22/0.49    spl2_1 | ~spl2_3 | spl2_4 | ~spl2_6 | ~spl2_14 | spl2_25),
% 0.22/0.49    inference(avatar_split_clause,[],[f182,f168,f116,f79,f69,f64,f54])).
% 0.22/0.49  fof(f116,plain,(
% 0.22/0.49    spl2_14 <=> ! [X1,X0] : (l3_lattices(k7_filter_1(X0,X1)) | ~l3_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.22/0.49  fof(f182,plain,(
% 0.22/0.49    ~l3_lattices(sK1) | v2_struct_0(sK1) | ~l3_lattices(sK0) | v2_struct_0(sK0) | (~spl2_14 | spl2_25)),
% 0.22/0.49    inference(resolution,[],[f170,f117])).
% 0.22/0.49  fof(f117,plain,(
% 0.22/0.49    ( ! [X0,X1] : (l3_lattices(k7_filter_1(X0,X1)) | ~l3_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X0) | v2_struct_0(X0)) ) | ~spl2_14),
% 0.22/0.49    inference(avatar_component_clause,[],[f116])).
% 0.22/0.49  fof(f170,plain,(
% 0.22/0.49    ~l3_lattices(k7_filter_1(sK0,sK1)) | spl2_25),
% 0.22/0.49    inference(avatar_component_clause,[],[f168])).
% 0.22/0.49  fof(f179,plain,(
% 0.22/0.49    spl2_27 | ~spl2_10 | ~spl2_16),
% 0.22/0.49    inference(avatar_split_clause,[],[f136,f124,f97,f177])).
% 0.22/0.49  fof(f124,plain,(
% 0.22/0.49    spl2_16 <=> ! [X1,X0] : (v14_lattices(X1) | ~v14_lattices(k7_filter_1(X0,X1)) | ~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.22/0.49  fof(f136,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v14_lattices(X0) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~v15_lattices(k7_filter_1(X1,X0)) | ~l3_lattices(k7_filter_1(X1,X0)) | v2_struct_0(k7_filter_1(X1,X0))) ) | (~spl2_10 | ~spl2_16)),
% 0.22/0.49    inference(resolution,[],[f125,f98])).
% 0.22/0.49  fof(f125,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v14_lattices(k7_filter_1(X0,X1)) | v14_lattices(X1) | ~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) ) | ~spl2_16),
% 0.22/0.49    inference(avatar_component_clause,[],[f124])).
% 0.22/0.49  fof(f175,plain,(
% 0.22/0.49    spl2_24 | ~spl2_25 | spl2_26 | spl2_1 | ~spl2_2 | ~spl2_3 | spl2_4 | ~spl2_5 | ~spl2_6 | ~spl2_8 | ~spl2_23),
% 0.22/0.49    inference(avatar_split_clause,[],[f162,f159,f88,f79,f74,f69,f64,f59,f54,f172,f168,f164])).
% 0.22/0.49  fof(f159,plain,(
% 0.22/0.49    spl2_23 <=> ! [X1,X0] : (v14_lattices(X0) | ~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~v15_lattices(k7_filter_1(X0,X1)) | ~l3_lattices(k7_filter_1(X0,X1)) | v2_struct_0(k7_filter_1(X0,X1)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 0.22/0.49  fof(f162,plain,(
% 0.22/0.49    ~l3_lattices(sK1) | ~v10_lattices(sK1) | v2_struct_0(sK1) | ~l3_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | v14_lattices(sK0) | ~l3_lattices(k7_filter_1(sK0,sK1)) | v2_struct_0(k7_filter_1(sK0,sK1)) | (~spl2_8 | ~spl2_23)),
% 0.22/0.49    inference(resolution,[],[f160,f90])).
% 0.22/0.49  fof(f160,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v15_lattices(k7_filter_1(X0,X1)) | ~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | v14_lattices(X0) | ~l3_lattices(k7_filter_1(X0,X1)) | v2_struct_0(k7_filter_1(X0,X1))) ) | ~spl2_23),
% 0.22/0.49    inference(avatar_component_clause,[],[f159])).
% 0.22/0.49  fof(f161,plain,(
% 0.22/0.49    spl2_23 | ~spl2_10 | ~spl2_15),
% 0.22/0.49    inference(avatar_split_clause,[],[f135,f120,f97,f159])).
% 0.22/0.49  fof(f120,plain,(
% 0.22/0.49    spl2_15 <=> ! [X1,X0] : (v14_lattices(X0) | ~v14_lattices(k7_filter_1(X0,X1)) | ~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.22/0.49  fof(f135,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v14_lattices(X0) | ~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~v15_lattices(k7_filter_1(X0,X1)) | ~l3_lattices(k7_filter_1(X0,X1)) | v2_struct_0(k7_filter_1(X0,X1))) ) | (~spl2_10 | ~spl2_15)),
% 0.22/0.49    inference(resolution,[],[f121,f98])).
% 0.22/0.49  fof(f121,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v14_lattices(k7_filter_1(X0,X1)) | v14_lattices(X0) | ~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) ) | ~spl2_15),
% 0.22/0.49    inference(avatar_component_clause,[],[f120])).
% 0.22/0.49  fof(f150,plain,(
% 0.22/0.49    spl2_21 | ~spl2_10 | ~spl2_19),
% 0.22/0.49    inference(avatar_split_clause,[],[f146,f138,f97,f148])).
% 0.22/0.49  fof(f138,plain,(
% 0.22/0.49    spl2_19 <=> ! [X1,X0] : (v14_lattices(k7_filter_1(X0,X1)) | ~v14_lattices(X1) | ~v14_lattices(X0) | ~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 0.22/0.49  fof(f146,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v14_lattices(k7_filter_1(X0,X1)) | ~v14_lattices(X0) | ~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~v15_lattices(X1)) ) | (~spl2_10 | ~spl2_19)),
% 0.22/0.49    inference(duplicate_literal_removal,[],[f145])).
% 0.22/0.49  fof(f145,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v14_lattices(k7_filter_1(X0,X1)) | ~v14_lattices(X0) | ~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~v15_lattices(X1) | ~l3_lattices(X1) | v2_struct_0(X1)) ) | (~spl2_10 | ~spl2_19)),
% 0.22/0.49    inference(resolution,[],[f139,f98])).
% 0.22/0.49  fof(f139,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v14_lattices(X1) | v14_lattices(k7_filter_1(X0,X1)) | ~v14_lattices(X0) | ~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) ) | ~spl2_19),
% 0.22/0.49    inference(avatar_component_clause,[],[f138])).
% 0.22/0.49  fof(f144,plain,(
% 0.22/0.49    spl2_20),
% 0.22/0.49    inference(avatar_split_clause,[],[f43,f142])).
% 0.22/0.49  fof(f43,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v13_lattices(k7_filter_1(X0,X1)) | ~v13_lattices(X1) | ~v13_lattices(X0) | ~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f28])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : ((((v13_lattices(X1) & v13_lattices(X0)) | ~v13_lattices(k7_filter_1(X0,X1))) & (v13_lattices(k7_filter_1(X0,X1)) | ~v13_lattices(X1) | ~v13_lattices(X0))) | ~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f27])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : ((((v13_lattices(X1) & v13_lattices(X0)) | ~v13_lattices(k7_filter_1(X0,X1))) & (v13_lattices(k7_filter_1(X0,X1)) | (~v13_lattices(X1) | ~v13_lattices(X0)))) | ~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(nnf_transformation,[],[f13])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (((v13_lattices(X1) & v13_lattices(X0)) <=> v13_lattices(k7_filter_1(X0,X1))) | ~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f12])).
% 0.22/0.49  fof(f12,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (((v13_lattices(X1) & v13_lattices(X0)) <=> v13_lattices(k7_filter_1(X0,X1))) | (~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1))) | (~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l3_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => ((v13_lattices(X1) & v13_lattices(X0)) <=> v13_lattices(k7_filter_1(X0,X1)))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_filter_1)).
% 0.22/0.49  fof(f140,plain,(
% 0.22/0.49    spl2_19),
% 0.22/0.49    inference(avatar_split_clause,[],[f40,f138])).
% 0.22/0.49  fof(f40,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v14_lattices(k7_filter_1(X0,X1)) | ~v14_lattices(X1) | ~v14_lattices(X0) | ~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f26])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : ((((v14_lattices(X1) & v14_lattices(X0)) | ~v14_lattices(k7_filter_1(X0,X1))) & (v14_lattices(k7_filter_1(X0,X1)) | ~v14_lattices(X1) | ~v14_lattices(X0))) | ~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f25])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : ((((v14_lattices(X1) & v14_lattices(X0)) | ~v14_lattices(k7_filter_1(X0,X1))) & (v14_lattices(k7_filter_1(X0,X1)) | (~v14_lattices(X1) | ~v14_lattices(X0)))) | ~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(nnf_transformation,[],[f11])).
% 0.22/0.49  fof(f11,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (((v14_lattices(X1) & v14_lattices(X0)) <=> v14_lattices(k7_filter_1(X0,X1))) | ~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f10])).
% 0.22/0.49  fof(f10,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (((v14_lattices(X1) & v14_lattices(X0)) <=> v14_lattices(k7_filter_1(X0,X1))) | (~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1))) | (~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l3_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => ((v14_lattices(X1) & v14_lattices(X0)) <=> v14_lattices(k7_filter_1(X0,X1)))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_filter_1)).
% 0.22/0.49  fof(f134,plain,(
% 0.22/0.49    spl2_18),
% 0.22/0.49    inference(avatar_split_clause,[],[f45,f132])).
% 0.22/0.49  fof(f45,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v13_lattices(X1) | ~v13_lattices(k7_filter_1(X0,X1)) | ~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f28])).
% 0.22/0.49  fof(f130,plain,(
% 0.22/0.49    spl2_17),
% 0.22/0.49    inference(avatar_split_clause,[],[f44,f128])).
% 0.22/0.49  fof(f44,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v13_lattices(X0) | ~v13_lattices(k7_filter_1(X0,X1)) | ~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f28])).
% 0.22/0.49  fof(f126,plain,(
% 0.22/0.49    spl2_16),
% 0.22/0.49    inference(avatar_split_clause,[],[f42,f124])).
% 0.22/0.49  fof(f42,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v14_lattices(X1) | ~v14_lattices(k7_filter_1(X0,X1)) | ~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f26])).
% 0.22/0.49  fof(f122,plain,(
% 0.22/0.49    spl2_15),
% 0.22/0.49    inference(avatar_split_clause,[],[f41,f120])).
% 0.22/0.49  fof(f41,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v14_lattices(X0) | ~v14_lattices(k7_filter_1(X0,X1)) | ~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f26])).
% 0.22/0.49  fof(f118,plain,(
% 0.22/0.49    spl2_14),
% 0.22/0.49    inference(avatar_split_clause,[],[f52,f116])).
% 0.22/0.49  fof(f52,plain,(
% 0.22/0.49    ( ! [X0,X1] : (l3_lattices(k7_filter_1(X0,X1)) | ~l3_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f19])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ! [X0,X1] : ((l3_lattices(k7_filter_1(X0,X1)) & v3_lattices(k7_filter_1(X0,X1))) | ~l3_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f18])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ! [X0,X1] : ((l3_lattices(k7_filter_1(X0,X1)) & v3_lattices(k7_filter_1(X0,X1))) | (~l3_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0,X1] : ((l3_lattices(X1) & ~v2_struct_0(X1) & l3_lattices(X0) & ~v2_struct_0(X0)) => (l3_lattices(k7_filter_1(X0,X1)) & v3_lattices(k7_filter_1(X0,X1))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_filter_1)).
% 0.22/0.49  fof(f109,plain,(
% 0.22/0.49    spl2_12),
% 0.22/0.49    inference(avatar_split_clause,[],[f49,f107])).
% 0.22/0.49  fof(f49,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v2_struct_0(k7_filter_1(X0,X1)) | ~l3_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f17])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ! [X0,X1] : ((v3_lattices(k7_filter_1(X0,X1)) & ~v2_struct_0(k7_filter_1(X0,X1))) | ~l3_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f16])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ! [X0,X1] : ((v3_lattices(k7_filter_1(X0,X1)) & ~v2_struct_0(k7_filter_1(X0,X1))) | (~l3_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0,X1] : ((l3_lattices(X1) & ~v2_struct_0(X1) & l3_lattices(X0) & ~v2_struct_0(X0)) => (v3_lattices(k7_filter_1(X0,X1)) & ~v2_struct_0(k7_filter_1(X0,X1))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_filter_1)).
% 0.22/0.49  fof(f103,plain,(
% 0.22/0.49    spl2_11),
% 0.22/0.49    inference(avatar_split_clause,[],[f48,f101])).
% 0.22/0.49  fof(f48,plain,(
% 0.22/0.49    ( ! [X0] : (v15_lattices(X0) | ~v14_lattices(X0) | ~v13_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f30])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    ! [X0] : (((v15_lattices(X0) | ~v14_lattices(X0) | ~v13_lattices(X0)) & ((v14_lattices(X0) & v13_lattices(X0)) | ~v15_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f29])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    ! [X0] : (((v15_lattices(X0) | (~v14_lattices(X0) | ~v13_lattices(X0))) & ((v14_lattices(X0) & v13_lattices(X0)) | ~v15_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(nnf_transformation,[],[f15])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    ! [X0] : ((v15_lattices(X0) <=> (v14_lattices(X0) & v13_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f14])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    ! [X0] : ((v15_lattices(X0) <=> (v14_lattices(X0) & v13_lattices(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v15_lattices(X0) <=> (v14_lattices(X0) & v13_lattices(X0))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d15_lattices)).
% 0.22/0.49  fof(f99,plain,(
% 0.22/0.49    spl2_10),
% 0.22/0.49    inference(avatar_split_clause,[],[f47,f97])).
% 0.22/0.49  fof(f47,plain,(
% 0.22/0.49    ( ! [X0] : (v14_lattices(X0) | ~v15_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f30])).
% 0.22/0.49  fof(f95,plain,(
% 0.22/0.49    spl2_9),
% 0.22/0.49    inference(avatar_split_clause,[],[f46,f93])).
% 0.22/0.49  fof(f46,plain,(
% 0.22/0.49    ( ! [X0] : (v13_lattices(X0) | ~v15_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f30])).
% 0.22/0.49  fof(f91,plain,(
% 0.22/0.49    spl2_7 | spl2_8),
% 0.22/0.49    inference(avatar_split_clause,[],[f37,f88,f84])).
% 0.22/0.49  fof(f37,plain,(
% 0.22/0.49    v15_lattices(k7_filter_1(sK0,sK1)) | v15_lattices(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f24])).
% 0.22/0.49  fof(f82,plain,(
% 0.22/0.49    spl2_6),
% 0.22/0.49    inference(avatar_split_clause,[],[f36,f79])).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    l3_lattices(sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f24])).
% 0.22/0.49  fof(f77,plain,(
% 0.22/0.49    spl2_5),
% 0.22/0.49    inference(avatar_split_clause,[],[f35,f74])).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    v10_lattices(sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f24])).
% 0.22/0.49  fof(f72,plain,(
% 0.22/0.49    ~spl2_4),
% 0.22/0.49    inference(avatar_split_clause,[],[f34,f69])).
% 0.22/0.49  fof(f34,plain,(
% 0.22/0.49    ~v2_struct_0(sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f24])).
% 0.22/0.49  fof(f67,plain,(
% 0.22/0.49    spl2_3),
% 0.22/0.49    inference(avatar_split_clause,[],[f33,f64])).
% 0.22/0.49  fof(f33,plain,(
% 0.22/0.49    l3_lattices(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f24])).
% 0.22/0.49  fof(f62,plain,(
% 0.22/0.49    spl2_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f32,f59])).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    v10_lattices(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f24])).
% 0.22/0.49  fof(f57,plain,(
% 0.22/0.49    ~spl2_1),
% 0.22/0.49    inference(avatar_split_clause,[],[f31,f54])).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    ~v2_struct_0(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f24])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (20962)------------------------------
% 0.22/0.49  % (20962)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (20962)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (20962)Memory used [KB]: 5628
% 0.22/0.49  % (20962)Time elapsed: 0.070 s
% 0.22/0.49  % (20962)------------------------------
% 0.22/0.49  % (20962)------------------------------
% 0.22/0.49  % (20958)lrs+1011_2:1_add=large:afr=on:afp=4000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:gs=on:irw=on:nm=64:nwc=1:sas=z3:stl=30:sos=on:sp=reverse_arity:thf=on:urr=on:updr=off_81 on theBenchmark
% 0.22/0.49  % (20943)Success in time 0.13 s
%------------------------------------------------------------------------------
