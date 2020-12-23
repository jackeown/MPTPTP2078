%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1193+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:27 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 158 expanded)
%              Number of leaves         :   21 (  73 expanded)
%              Depth                    :   10
%              Number of atoms          :  279 ( 685 expanded)
%              Number of equality atoms :   44 ( 100 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (26350)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
fof(f110,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f43,f48,f53,f58,f63,f68,f73,f79,f85,f92,f104,f109])).

fof(f109,plain,
    ( sK1 != k2_lattices(sK0,sK1,sK1)
    | k4_lattices(sK0,sK1,sK1) != k2_lattices(sK0,sK1,sK1)
    | sK1 = k4_lattices(sK0,sK1,sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f104,plain,
    ( spl4_12
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | spl4_7
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f99,f82,f70,f55,f50,f45,f101])).

fof(f101,plain,
    ( spl4_12
  <=> sK1 = k2_lattices(sK0,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f45,plain,
    ( spl4_2
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f50,plain,
    ( spl4_3
  <=> l3_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f55,plain,
    ( spl4_4
  <=> v9_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f70,plain,
    ( spl4_7
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f82,plain,
    ( spl4_9
  <=> sK1 = k1_lattices(sK0,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f99,plain,
    ( sK1 = k2_lattices(sK0,sK1,sK1)
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | spl4_7
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f97,f84])).

fof(f84,plain,
    ( sK1 = k1_lattices(sK0,sK1,sK1)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f82])).

fof(f97,plain,
    ( sK1 = k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK1))
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | spl4_7 ),
    inference(unit_resulting_resolution,[],[f72,f52,f57,f47,f47,f33])).

fof(f33,plain,(
    ! [X4,X0,X3] :
      ( ~ v9_lattices(X0)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( ( v9_lattices(X0)
          | ( sK2(X0) != k2_lattices(X0,sK2(X0),k1_lattices(X0,sK2(X0),sK3(X0)))
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f21,f23,f22])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( sK2(X0) != k2_lattices(X0,sK2(X0),k1_lattices(X0,sK2(X0),X2))
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK2(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X2] :
          ( sK2(X0) != k2_lattices(X0,sK2(X0),k1_lattices(X0,sK2(X0),X2))
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( sK2(X0) != k2_lattices(X0,sK2(X0),k1_lattices(X0,sK2(X0),sK3(X0)))
        & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
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
    inference(rectify,[],[f20])).

fof(f20,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v9_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattices)).

fof(f47,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f45])).

fof(f57,plain,
    ( v9_lattices(sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f55])).

fof(f52,plain,
    ( l3_lattices(sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f50])).

fof(f72,plain,
    ( ~ v2_struct_0(sK0)
    | spl4_7 ),
    inference(avatar_component_clause,[],[f70])).

fof(f92,plain,
    ( spl4_10
    | ~ spl4_2
    | ~ spl4_6
    | spl4_7
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f86,f76,f70,f65,f45,f89])).

fof(f89,plain,
    ( spl4_10
  <=> k4_lattices(sK0,sK1,sK1) = k2_lattices(sK0,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f65,plain,
    ( spl4_6
  <=> v6_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f76,plain,
    ( spl4_8
  <=> l1_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f86,plain,
    ( k4_lattices(sK0,sK1,sK1) = k2_lattices(sK0,sK1,sK1)
    | ~ spl4_2
    | ~ spl4_6
    | spl4_7
    | ~ spl4_8 ),
    inference(unit_resulting_resolution,[],[f72,f67,f78,f47,f47,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ v6_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_lattices)).

fof(f78,plain,
    ( l1_lattices(sK0)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f76])).

fof(f67,plain,
    ( v6_lattices(sK0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f65])).

fof(f85,plain,
    ( spl4_9
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | spl4_7 ),
    inference(avatar_split_clause,[],[f80,f70,f65,f60,f55,f50,f45,f82])).

fof(f60,plain,
    ( spl4_5
  <=> v8_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f80,plain,
    ( sK1 = k1_lattices(sK0,sK1,sK1)
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | spl4_7 ),
    inference(unit_resulting_resolution,[],[f72,f67,f62,f57,f52,f47,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_lattices(X0,X1,X1) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_lattices(X0,X1,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_lattices(X0,X1,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k1_lattices(X0,X1,X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_lattices)).

fof(f62,plain,
    ( v8_lattices(sK0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f60])).

fof(f79,plain,
    ( spl4_8
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f74,f50,f76])).

fof(f74,plain,
    ( l1_lattices(sK0)
    | ~ spl4_3 ),
    inference(unit_resulting_resolution,[],[f52,f38])).

fof(f38,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => l1_lattices(X0) ) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f73,plain,(
    ~ spl4_7 ),
    inference(avatar_split_clause,[],[f25,f70])).

fof(f25,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( sK1 != k4_lattices(sK0,sK1,sK1)
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l3_lattices(sK0)
    & v9_lattices(sK0)
    & v8_lattices(sK0)
    & v6_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f18,f17])).

fof(f17,plain,
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

fof(f18,plain,
    ( ? [X1] :
        ( k4_lattices(sK0,X1,X1) != X1
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( sK1 != k4_lattices(sK0,sK1,sK1)
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k4_lattices(X0,X1,X1) != X1
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v9_lattices(X0)
      & v8_lattices(X0)
      & v6_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k4_lattices(X0,X1,X1) != X1
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v9_lattices(X0)
      & v8_lattices(X0)
      & v6_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => k4_lattices(X0,X1,X1) = X1 ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k4_lattices(X0,X1,X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_lattices)).

fof(f68,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f26,f65])).

fof(f26,plain,(
    v6_lattices(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f63,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f27,f60])).

fof(f27,plain,(
    v8_lattices(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f58,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f28,f55])).

fof(f28,plain,(
    v9_lattices(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f53,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f29,f50])).

fof(f29,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f48,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f30,f45])).

fof(f30,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f43,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f31,f40])).

fof(f40,plain,
    ( spl4_1
  <=> sK1 = k4_lattices(sK0,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f31,plain,(
    sK1 != k4_lattices(sK0,sK1,sK1) ),
    inference(cnf_transformation,[],[f19])).

%------------------------------------------------------------------------------
