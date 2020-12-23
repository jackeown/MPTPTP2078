%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:19 EST 2020

% Result     : Theorem 1.10s
% Output     : Refutation 1.10s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 186 expanded)
%              Number of leaves         :   28 (  95 expanded)
%              Depth                    :    7
%              Number of atoms          :  297 (1147 expanded)
%              Number of equality atoms :   57 ( 269 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f193,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f50,f55,f60,f61,f66,f71,f76,f81,f86,f98,f111,f117,f132,f178,f190,f191,f192])).

fof(f192,plain,
    ( sK2 != k1_tops_1(sK0,sK2)
    | v3_pre_topc(sK2,sK0)
    | ~ v3_pre_topc(k1_tops_1(sK0,sK2),sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f191,plain,
    ( k3_subset_1(u1_struct_0(sK1),sK3) != k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK3))
    | k1_tops_1(sK1,sK3) != k3_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK3)))
    | sK3 != k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),sK3))
    | sK3 = k1_tops_1(sK1,sK3) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f190,plain,
    ( ~ spl4_7
    | ~ spl4_11
    | spl4_23
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f182,f175,f184,f95,f73])).

fof(f73,plain,
    ( spl4_7
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f95,plain,
    ( spl4_11
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK3),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f184,plain,
    ( spl4_23
  <=> k3_subset_1(u1_struct_0(sK1),sK3) = k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f175,plain,
    ( spl4_22
  <=> v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f182,plain,
    ( k3_subset_1(u1_struct_0(sK1),sK3) = k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK3))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | ~ spl4_22 ),
    inference(resolution,[],[f177,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f177,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK3),sK1)
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f175])).

fof(f178,plain,
    ( ~ spl4_7
    | ~ spl4_11
    | spl4_22
    | ~ spl4_3
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f172,f108,f52,f175,f95,f73])).

fof(f52,plain,
    ( spl4_3
  <=> v3_pre_topc(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f108,plain,
    ( spl4_13
  <=> sK3 = k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f172,plain,
    ( ~ v3_pre_topc(sK3,sK1)
    | v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK3),sK1)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | ~ spl4_13 ),
    inference(superposition,[],[f40,f110])).

fof(f110,plain,
    ( sK3 = k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),sK3))
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f108])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).

fof(f132,plain,
    ( spl4_16
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f119,f73,f63,f129])).

fof(f129,plain,
    ( spl4_16
  <=> k1_tops_1(sK1,sK3) = k3_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f63,plain,
    ( spl4_5
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f119,plain,
    ( k1_tops_1(sK1,sK3) = k3_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK3)))
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(unit_resulting_resolution,[],[f75,f65,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).

fof(f65,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f63])).

fof(f75,plain,
    ( l1_pre_topc(sK1)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f73])).

fof(f117,plain,
    ( spl4_14
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f112,f83,f78,f68,f114])).

fof(f114,plain,
    ( spl4_14
  <=> v3_pre_topc(k1_tops_1(sK0,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f68,plain,
    ( spl4_6
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f78,plain,
    ( spl4_8
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f83,plain,
    ( spl4_9
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f112,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK2),sK0)
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_9 ),
    inference(unit_resulting_resolution,[],[f85,f80,f70,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f70,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f68])).

fof(f80,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f78])).

fof(f85,plain,
    ( v2_pre_topc(sK0)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f83])).

fof(f111,plain,
    ( spl4_13
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f99,f63,f108])).

fof(f99,plain,
    ( sK3 = k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),sK3))
    | ~ spl4_5 ),
    inference(unit_resulting_resolution,[],[f65,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f98,plain,
    ( spl4_11
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f87,f63,f95])).

fof(f87,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl4_5 ),
    inference(unit_resulting_resolution,[],[f65,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f86,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f25,f83])).

fof(f25,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ( ( ~ v3_pre_topc(sK2,sK0)
        & sK2 = k1_tops_1(sK0,sK2) )
      | ( sK3 != k1_tops_1(sK1,sK3)
        & v3_pre_topc(sK3,sK1) ) )
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f22,f21,f20,f19])).

fof(f19,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ( ~ v3_pre_topc(X2,X0)
                        & k1_tops_1(X0,X2) = X2 )
                      | ( k1_tops_1(X1,X3) != X3
                        & v3_pre_topc(X3,X1) ) )
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & l1_pre_topc(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ~ v3_pre_topc(X2,sK0)
                      & k1_tops_1(sK0,X2) = X2 )
                    | ( k1_tops_1(X1,X3) != X3
                      & v3_pre_topc(X3,X1) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

% (999)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
fof(f20,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ( ~ v3_pre_topc(X2,sK0)
                    & k1_tops_1(sK0,X2) = X2 )
                  | ( k1_tops_1(X1,X3) != X3
                    & v3_pre_topc(X3,X1) ) )
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & l1_pre_topc(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ( ~ v3_pre_topc(X2,sK0)
                  & k1_tops_1(sK0,X2) = X2 )
                | ( k1_tops_1(sK1,X3) != X3
                  & v3_pre_topc(X3,sK1) ) )
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ( ~ v3_pre_topc(X2,sK0)
                & k1_tops_1(sK0,X2) = X2 )
              | ( k1_tops_1(sK1,X3) != X3
                & v3_pre_topc(X3,sK1) ) )
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X3] :
          ( ( ( ~ v3_pre_topc(sK2,sK0)
              & sK2 = k1_tops_1(sK0,sK2) )
            | ( k1_tops_1(sK1,X3) != X3
              & v3_pre_topc(X3,sK1) ) )
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X3] :
        ( ( ( ~ v3_pre_topc(sK2,sK0)
            & sK2 = k1_tops_1(sK0,sK2) )
          | ( k1_tops_1(sK1,X3) != X3
            & v3_pre_topc(X3,sK1) ) )
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
   => ( ( ( ~ v3_pre_topc(sK2,sK0)
          & sK2 = k1_tops_1(sK0,sK2) )
        | ( sK3 != k1_tops_1(sK1,sK3)
          & v3_pre_topc(sK3,sK1) ) )
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ~ v3_pre_topc(X2,X0)
                      & k1_tops_1(X0,X2) = X2 )
                    | ( k1_tops_1(X1,X3) != X3
                      & v3_pre_topc(X3,X1) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ~ v3_pre_topc(X2,X0)
                      & k1_tops_1(X0,X2) = X2 )
                    | ( k1_tops_1(X1,X3) != X3
                      & v3_pre_topc(X3,X1) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( ( k1_tops_1(X0,X2) = X2
                       => v3_pre_topc(X2,X0) )
                      & ( v3_pre_topc(X3,X1)
                       => k1_tops_1(X1,X3) = X3 ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( k1_tops_1(X0,X2) = X2
                     => v3_pre_topc(X2,X0) )
                    & ( v3_pre_topc(X3,X1)
                     => k1_tops_1(X1,X3) = X3 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_1)).

fof(f81,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f26,f78])).

fof(f26,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f76,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f27,f73])).

fof(f27,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f71,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f28,f68])).

fof(f28,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f66,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f29,f63])).

fof(f29,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f23])).

fof(f61,plain,
    ( spl4_3
    | spl4_4 ),
    inference(avatar_split_clause,[],[f30,f57,f52])).

fof(f57,plain,
    ( spl4_4
  <=> sK2 = k1_tops_1(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f30,plain,
    ( sK2 = k1_tops_1(sK0,sK2)
    | v3_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f60,plain,
    ( ~ spl4_1
    | spl4_4 ),
    inference(avatar_split_clause,[],[f31,f57,f43])).

fof(f43,plain,
    ( spl4_1
  <=> sK3 = k1_tops_1(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f31,plain,
    ( sK2 = k1_tops_1(sK0,sK2)
    | sK3 != k1_tops_1(sK1,sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f55,plain,
    ( spl4_3
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f32,f47,f52])).

fof(f47,plain,
    ( spl4_2
  <=> v3_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f32,plain,
    ( ~ v3_pre_topc(sK2,sK0)
    | v3_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f50,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f33,f47,f43])).

fof(f33,plain,
    ( ~ v3_pre_topc(sK2,sK0)
    | sK3 != k1_tops_1(sK1,sK3) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 18:59:06 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.23/0.50  % (980)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.23/0.50  % (982)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.23/0.50  % (978)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.23/0.50  % (989)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.23/0.51  % (981)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 1.10/0.51  % (996)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 1.10/0.51  % (977)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 1.10/0.51  % (992)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 1.10/0.51  % (976)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 1.10/0.51  % (982)Refutation found. Thanks to Tanya!
% 1.10/0.51  % SZS status Theorem for theBenchmark
% 1.10/0.52  % (1000)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 1.10/0.52  % SZS output start Proof for theBenchmark
% 1.10/0.52  fof(f193,plain,(
% 1.10/0.52    $false),
% 1.10/0.52    inference(avatar_sat_refutation,[],[f50,f55,f60,f61,f66,f71,f76,f81,f86,f98,f111,f117,f132,f178,f190,f191,f192])).
% 1.10/0.52  fof(f192,plain,(
% 1.10/0.52    sK2 != k1_tops_1(sK0,sK2) | v3_pre_topc(sK2,sK0) | ~v3_pre_topc(k1_tops_1(sK0,sK2),sK0)),
% 1.10/0.52    introduced(theory_tautology_sat_conflict,[])).
% 1.10/0.52  fof(f191,plain,(
% 1.10/0.52    k3_subset_1(u1_struct_0(sK1),sK3) != k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK3)) | k1_tops_1(sK1,sK3) != k3_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK3))) | sK3 != k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),sK3)) | sK3 = k1_tops_1(sK1,sK3)),
% 1.10/0.52    introduced(theory_tautology_sat_conflict,[])).
% 1.10/0.52  fof(f190,plain,(
% 1.10/0.52    ~spl4_7 | ~spl4_11 | spl4_23 | ~spl4_22),
% 1.10/0.52    inference(avatar_split_clause,[],[f182,f175,f184,f95,f73])).
% 1.10/0.52  fof(f73,plain,(
% 1.10/0.52    spl4_7 <=> l1_pre_topc(sK1)),
% 1.10/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.10/0.52  fof(f95,plain,(
% 1.10/0.52    spl4_11 <=> m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK3),k1_zfmisc_1(u1_struct_0(sK1)))),
% 1.10/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 1.10/0.52  fof(f184,plain,(
% 1.10/0.52    spl4_23 <=> k3_subset_1(u1_struct_0(sK1),sK3) = k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK3))),
% 1.10/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 1.10/0.52  fof(f175,plain,(
% 1.10/0.52    spl4_22 <=> v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK3),sK1)),
% 1.10/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 1.10/0.52  fof(f182,plain,(
% 1.10/0.52    k3_subset_1(u1_struct_0(sK1),sK3) = k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK3)) | ~m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK3),k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1) | ~spl4_22),
% 1.10/0.52    inference(resolution,[],[f177,f35])).
% 1.10/0.52  fof(f35,plain,(
% 1.10/0.52    ( ! [X0,X1] : (~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.10/0.52    inference(cnf_transformation,[],[f13])).
% 1.10/0.52  fof(f13,plain,(
% 1.10/0.52    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.10/0.52    inference(flattening,[],[f12])).
% 1.10/0.52  fof(f12,plain,(
% 1.10/0.52    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.10/0.52    inference(ennf_transformation,[],[f3])).
% 1.10/0.52  fof(f3,axiom,(
% 1.10/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 1.10/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).
% 1.10/0.52  fof(f177,plain,(
% 1.10/0.52    v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK3),sK1) | ~spl4_22),
% 1.10/0.52    inference(avatar_component_clause,[],[f175])).
% 1.10/0.52  fof(f178,plain,(
% 1.10/0.52    ~spl4_7 | ~spl4_11 | spl4_22 | ~spl4_3 | ~spl4_13),
% 1.10/0.52    inference(avatar_split_clause,[],[f172,f108,f52,f175,f95,f73])).
% 1.10/0.52  fof(f52,plain,(
% 1.10/0.52    spl4_3 <=> v3_pre_topc(sK3,sK1)),
% 1.10/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.10/0.52  fof(f108,plain,(
% 1.10/0.52    spl4_13 <=> sK3 = k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),sK3))),
% 1.10/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 1.10/0.52  fof(f172,plain,(
% 1.10/0.52    ~v3_pre_topc(sK3,sK1) | v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK3),sK1) | ~m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK3),k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1) | ~spl4_13),
% 1.10/0.52    inference(superposition,[],[f40,f110])).
% 1.10/0.52  fof(f110,plain,(
% 1.10/0.52    sK3 = k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),sK3)) | ~spl4_13),
% 1.10/0.52    inference(avatar_component_clause,[],[f108])).
% 1.10/0.52  fof(f40,plain,(
% 1.10/0.52    ( ! [X0,X1] : (~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.10/0.52    inference(cnf_transformation,[],[f24])).
% 1.10/0.52  fof(f24,plain,(
% 1.10/0.52    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.10/0.52    inference(nnf_transformation,[],[f17])).
% 1.10/0.52  fof(f17,plain,(
% 1.10/0.52    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.10/0.52    inference(ennf_transformation,[],[f6])).
% 1.10/0.52  fof(f6,axiom,(
% 1.10/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 1.10/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).
% 1.10/0.52  fof(f132,plain,(
% 1.10/0.52    spl4_16 | ~spl4_5 | ~spl4_7),
% 1.10/0.52    inference(avatar_split_clause,[],[f119,f73,f63,f129])).
% 1.10/0.52  fof(f129,plain,(
% 1.10/0.52    spl4_16 <=> k1_tops_1(sK1,sK3) = k3_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK3)))),
% 1.10/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 1.10/0.52  fof(f63,plain,(
% 1.10/0.52    spl4_5 <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))),
% 1.10/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.10/0.52  fof(f119,plain,(
% 1.10/0.52    k1_tops_1(sK1,sK3) = k3_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK3))) | (~spl4_5 | ~spl4_7)),
% 1.10/0.52    inference(unit_resulting_resolution,[],[f75,f65,f37])).
% 1.10/0.52  fof(f37,plain,(
% 1.10/0.52    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))) )),
% 1.10/0.52    inference(cnf_transformation,[],[f14])).
% 1.10/0.52  fof(f14,plain,(
% 1.10/0.52    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.10/0.52    inference(ennf_transformation,[],[f4])).
% 1.10/0.52  fof(f4,axiom,(
% 1.10/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))))),
% 1.10/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).
% 1.10/0.52  fof(f65,plain,(
% 1.10/0.52    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) | ~spl4_5),
% 1.10/0.52    inference(avatar_component_clause,[],[f63])).
% 1.10/0.52  fof(f75,plain,(
% 1.10/0.52    l1_pre_topc(sK1) | ~spl4_7),
% 1.10/0.52    inference(avatar_component_clause,[],[f73])).
% 1.10/0.52  fof(f117,plain,(
% 1.10/0.52    spl4_14 | ~spl4_6 | ~spl4_8 | ~spl4_9),
% 1.10/0.52    inference(avatar_split_clause,[],[f112,f83,f78,f68,f114])).
% 1.10/0.52  fof(f114,plain,(
% 1.10/0.52    spl4_14 <=> v3_pre_topc(k1_tops_1(sK0,sK2),sK0)),
% 1.10/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 1.10/0.52  fof(f68,plain,(
% 1.10/0.52    spl4_6 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.10/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.10/0.52  fof(f78,plain,(
% 1.10/0.52    spl4_8 <=> l1_pre_topc(sK0)),
% 1.10/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.10/0.52  fof(f83,plain,(
% 1.10/0.52    spl4_9 <=> v2_pre_topc(sK0)),
% 1.10/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 1.10/0.52  fof(f112,plain,(
% 1.10/0.52    v3_pre_topc(k1_tops_1(sK0,sK2),sK0) | (~spl4_6 | ~spl4_8 | ~spl4_9)),
% 1.10/0.52    inference(unit_resulting_resolution,[],[f85,f80,f70,f38])).
% 1.10/0.52  fof(f38,plain,(
% 1.10/0.52    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.10/0.52    inference(cnf_transformation,[],[f16])).
% 1.10/0.52  fof(f16,plain,(
% 1.10/0.52    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.10/0.52    inference(flattening,[],[f15])).
% 1.10/0.52  fof(f15,plain,(
% 1.10/0.52    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.10/0.52    inference(ennf_transformation,[],[f5])).
% 1.10/0.52  fof(f5,axiom,(
% 1.10/0.52    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 1.10/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).
% 1.10/0.52  fof(f70,plain,(
% 1.10/0.52    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_6),
% 1.10/0.52    inference(avatar_component_clause,[],[f68])).
% 1.10/0.52  fof(f80,plain,(
% 1.10/0.52    l1_pre_topc(sK0) | ~spl4_8),
% 1.10/0.52    inference(avatar_component_clause,[],[f78])).
% 1.10/0.52  fof(f85,plain,(
% 1.10/0.52    v2_pre_topc(sK0) | ~spl4_9),
% 1.10/0.52    inference(avatar_component_clause,[],[f83])).
% 1.10/0.52  fof(f111,plain,(
% 1.10/0.52    spl4_13 | ~spl4_5),
% 1.10/0.52    inference(avatar_split_clause,[],[f99,f63,f108])).
% 1.10/0.52  fof(f99,plain,(
% 1.10/0.52    sK3 = k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),sK3)) | ~spl4_5),
% 1.10/0.52    inference(unit_resulting_resolution,[],[f65,f34])).
% 1.10/0.52  fof(f34,plain,(
% 1.10/0.52    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.10/0.52    inference(cnf_transformation,[],[f11])).
% 1.10/0.52  fof(f11,plain,(
% 1.10/0.52    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.10/0.52    inference(ennf_transformation,[],[f2])).
% 1.10/0.52  fof(f2,axiom,(
% 1.10/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 1.10/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 1.10/0.52  fof(f98,plain,(
% 1.10/0.52    spl4_11 | ~spl4_5),
% 1.10/0.52    inference(avatar_split_clause,[],[f87,f63,f95])).
% 1.10/0.52  fof(f87,plain,(
% 1.10/0.52    m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK3),k1_zfmisc_1(u1_struct_0(sK1))) | ~spl4_5),
% 1.10/0.52    inference(unit_resulting_resolution,[],[f65,f41])).
% 1.10/0.52  fof(f41,plain,(
% 1.10/0.52    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.10/0.52    inference(cnf_transformation,[],[f18])).
% 1.10/0.52  fof(f18,plain,(
% 1.10/0.52    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.10/0.52    inference(ennf_transformation,[],[f1])).
% 1.10/0.52  fof(f1,axiom,(
% 1.10/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.10/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 1.10/0.52  fof(f86,plain,(
% 1.10/0.52    spl4_9),
% 1.10/0.52    inference(avatar_split_clause,[],[f25,f83])).
% 1.10/0.52  fof(f25,plain,(
% 1.10/0.52    v2_pre_topc(sK0)),
% 1.10/0.52    inference(cnf_transformation,[],[f23])).
% 1.10/0.52  fof(f23,plain,(
% 1.10/0.52    (((((~v3_pre_topc(sK2,sK0) & sK2 = k1_tops_1(sK0,sK2)) | (sK3 != k1_tops_1(sK1,sK3) & v3_pre_topc(sK3,sK1))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 1.10/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f22,f21,f20,f19])).
% 1.10/0.52  fof(f19,plain,(
% 1.10/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~v3_pre_topc(X2,X0) & k1_tops_1(X0,X2) = X2) | (k1_tops_1(X1,X3) != X3 & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : (((~v3_pre_topc(X2,sK0) & k1_tops_1(sK0,X2) = X2) | (k1_tops_1(X1,X3) != X3 & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 1.10/0.52    introduced(choice_axiom,[])).
% 1.10/0.52  % (999)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 1.10/0.52  fof(f20,plain,(
% 1.10/0.52    ? [X1] : (? [X2] : (? [X3] : (((~v3_pre_topc(X2,sK0) & k1_tops_1(sK0,X2) = X2) | (k1_tops_1(X1,X3) != X3 & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(X1)) => (? [X2] : (? [X3] : (((~v3_pre_topc(X2,sK0) & k1_tops_1(sK0,X2) = X2) | (k1_tops_1(sK1,X3) != X3 & v3_pre_topc(X3,sK1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK1))),
% 1.10/0.52    introduced(choice_axiom,[])).
% 1.10/0.52  fof(f21,plain,(
% 1.10/0.52    ? [X2] : (? [X3] : (((~v3_pre_topc(X2,sK0) & k1_tops_1(sK0,X2) = X2) | (k1_tops_1(sK1,X3) != X3 & v3_pre_topc(X3,sK1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X3] : (((~v3_pre_topc(sK2,sK0) & sK2 = k1_tops_1(sK0,sK2)) | (k1_tops_1(sK1,X3) != X3 & v3_pre_topc(X3,sK1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.10/0.52    introduced(choice_axiom,[])).
% 1.10/0.52  fof(f22,plain,(
% 1.10/0.52    ? [X3] : (((~v3_pre_topc(sK2,sK0) & sK2 = k1_tops_1(sK0,sK2)) | (k1_tops_1(sK1,X3) != X3 & v3_pre_topc(X3,sK1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) => (((~v3_pre_topc(sK2,sK0) & sK2 = k1_tops_1(sK0,sK2)) | (sK3 != k1_tops_1(sK1,sK3) & v3_pre_topc(sK3,sK1))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))))),
% 1.10/0.52    introduced(choice_axiom,[])).
% 1.10/0.52  fof(f10,plain,(
% 1.10/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~v3_pre_topc(X2,X0) & k1_tops_1(X0,X2) = X2) | (k1_tops_1(X1,X3) != X3 & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.10/0.52    inference(flattening,[],[f9])).
% 1.10/0.52  fof(f9,plain,(
% 1.10/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~v3_pre_topc(X2,X0) & k1_tops_1(X0,X2) = X2) | (k1_tops_1(X1,X3) != X3 & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.10/0.52    inference(ennf_transformation,[],[f8])).
% 1.10/0.52  fof(f8,negated_conjecture,(
% 1.10/0.52    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 1.10/0.52    inference(negated_conjecture,[],[f7])).
% 1.10/0.52  fof(f7,conjecture,(
% 1.10/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 1.10/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_1)).
% 1.10/0.52  fof(f81,plain,(
% 1.10/0.52    spl4_8),
% 1.10/0.52    inference(avatar_split_clause,[],[f26,f78])).
% 1.10/0.52  fof(f26,plain,(
% 1.10/0.52    l1_pre_topc(sK0)),
% 1.10/0.52    inference(cnf_transformation,[],[f23])).
% 1.10/0.52  fof(f76,plain,(
% 1.10/0.52    spl4_7),
% 1.10/0.52    inference(avatar_split_clause,[],[f27,f73])).
% 1.10/0.52  fof(f27,plain,(
% 1.10/0.52    l1_pre_topc(sK1)),
% 1.10/0.52    inference(cnf_transformation,[],[f23])).
% 1.10/0.52  fof(f71,plain,(
% 1.10/0.52    spl4_6),
% 1.10/0.52    inference(avatar_split_clause,[],[f28,f68])).
% 1.10/0.52  fof(f28,plain,(
% 1.10/0.52    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.10/0.52    inference(cnf_transformation,[],[f23])).
% 1.10/0.52  fof(f66,plain,(
% 1.10/0.52    spl4_5),
% 1.10/0.52    inference(avatar_split_clause,[],[f29,f63])).
% 1.10/0.52  fof(f29,plain,(
% 1.10/0.52    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))),
% 1.10/0.52    inference(cnf_transformation,[],[f23])).
% 1.10/0.52  fof(f61,plain,(
% 1.10/0.52    spl4_3 | spl4_4),
% 1.10/0.52    inference(avatar_split_clause,[],[f30,f57,f52])).
% 1.10/0.52  fof(f57,plain,(
% 1.10/0.52    spl4_4 <=> sK2 = k1_tops_1(sK0,sK2)),
% 1.10/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.10/0.52  fof(f30,plain,(
% 1.10/0.52    sK2 = k1_tops_1(sK0,sK2) | v3_pre_topc(sK3,sK1)),
% 1.10/0.52    inference(cnf_transformation,[],[f23])).
% 1.10/0.52  fof(f60,plain,(
% 1.10/0.52    ~spl4_1 | spl4_4),
% 1.10/0.52    inference(avatar_split_clause,[],[f31,f57,f43])).
% 1.10/0.52  fof(f43,plain,(
% 1.10/0.52    spl4_1 <=> sK3 = k1_tops_1(sK1,sK3)),
% 1.10/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.10/0.52  fof(f31,plain,(
% 1.10/0.52    sK2 = k1_tops_1(sK0,sK2) | sK3 != k1_tops_1(sK1,sK3)),
% 1.10/0.52    inference(cnf_transformation,[],[f23])).
% 1.10/0.52  fof(f55,plain,(
% 1.10/0.52    spl4_3 | ~spl4_2),
% 1.10/0.52    inference(avatar_split_clause,[],[f32,f47,f52])).
% 1.10/0.52  fof(f47,plain,(
% 1.10/0.52    spl4_2 <=> v3_pre_topc(sK2,sK0)),
% 1.10/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.10/0.52  fof(f32,plain,(
% 1.10/0.52    ~v3_pre_topc(sK2,sK0) | v3_pre_topc(sK3,sK1)),
% 1.10/0.52    inference(cnf_transformation,[],[f23])).
% 1.10/0.52  fof(f50,plain,(
% 1.10/0.52    ~spl4_1 | ~spl4_2),
% 1.10/0.52    inference(avatar_split_clause,[],[f33,f47,f43])).
% 1.10/0.52  fof(f33,plain,(
% 1.10/0.52    ~v3_pre_topc(sK2,sK0) | sK3 != k1_tops_1(sK1,sK3)),
% 1.10/0.52    inference(cnf_transformation,[],[f23])).
% 1.10/0.52  % SZS output end Proof for theBenchmark
% 1.10/0.52  % (982)------------------------------
% 1.10/0.52  % (982)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.10/0.52  % (982)Termination reason: Refutation
% 1.10/0.52  
% 1.10/0.52  % (982)Memory used [KB]: 10746
% 1.10/0.52  % (982)Time elapsed: 0.100 s
% 1.10/0.52  % (982)------------------------------
% 1.10/0.52  % (982)------------------------------
% 1.10/0.52  % (994)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 1.10/0.52  % (975)Success in time 0.15 s
%------------------------------------------------------------------------------
