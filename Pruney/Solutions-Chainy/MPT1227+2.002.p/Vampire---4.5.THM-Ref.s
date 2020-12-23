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
% DateTime   : Thu Dec  3 13:10:55 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 148 expanded)
%              Number of leaves         :   19 (  67 expanded)
%              Depth                    :    8
%              Number of atoms          :  278 ( 754 expanded)
%              Number of equality atoms :   12 (  18 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f119,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f28,f33,f38,f43,f48,f53,f58,f62,f66,f76,f95,f106,f112,f118])).

fof(f118,plain,
    ( ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | spl3_16
    | ~ spl3_17 ),
    inference(avatar_contradiction_clause,[],[f117])).

fof(f117,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | spl3_16
    | ~ spl3_17 ),
    inference(subsumption_resolution,[],[f116,f42])).

fof(f42,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl3_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f116,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_5
    | spl3_16
    | ~ spl3_17 ),
    inference(subsumption_resolution,[],[f115,f37])).

fof(f37,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f35])).

fof(f35,plain,
    ( spl3_3
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f115,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2
    | ~ spl3_5
    | spl3_16
    | ~ spl3_17 ),
    inference(subsumption_resolution,[],[f114,f47])).

fof(f47,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl3_5
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f114,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2
    | spl3_16
    | ~ spl3_17 ),
    inference(subsumption_resolution,[],[f113,f32])).

fof(f32,plain,
    ( v4_pre_topc(sK2,sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f30])).

fof(f30,plain,
    ( spl3_2
  <=> v4_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f113,plain,
    ( ~ v4_pre_topc(sK2,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_16
    | ~ spl3_17 ),
    inference(resolution,[],[f111,f105])).

fof(f105,plain,
    ( ~ v4_pre_topc(k2_xboole_0(sK1,sK2),sK0)
    | spl3_16 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl3_16
  <=> v4_pre_topc(k2_xboole_0(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f111,plain,
    ( ! [X0,X1] :
        ( v4_pre_topc(k2_xboole_0(X1,X0),sK0)
        | ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_pre_topc(X1,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl3_17
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_pre_topc(X1,sK0)
        | v4_pre_topc(k2_xboole_0(X1,X0),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f112,plain,
    ( spl3_17
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f108,f60,f55,f50,f110])).

fof(f50,plain,
    ( spl3_6
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f55,plain,
    ( spl3_7
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f60,plain,
    ( spl3_8
  <=> ! [X1,X0,X2] :
        ( v4_pre_topc(k2_xboole_0(X1,X2),X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v4_pre_topc(X2,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v4_pre_topc(X1,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f108,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_pre_topc(X1,sK0)
        | v4_pre_topc(k2_xboole_0(X1,X0),sK0) )
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f107,f57])).

fof(f57,plain,
    ( v2_pre_topc(sK0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f55])).

fof(f107,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_pre_topc(X1,sK0)
        | v4_pre_topc(k2_xboole_0(X1,X0),sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl3_6
    | ~ spl3_8 ),
    inference(resolution,[],[f61,f52])).

fof(f52,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f50])).

fof(f61,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v4_pre_topc(X2,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v4_pre_topc(X1,X0)
        | v4_pre_topc(k2_xboole_0(X1,X2),X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f60])).

fof(f106,plain,
    ( ~ spl3_16
    | spl3_1
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f101,f92,f25,f103])).

fof(f25,plain,
    ( spl3_1
  <=> v4_pre_topc(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f92,plain,
    ( spl3_14
  <=> k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f101,plain,
    ( ~ v4_pre_topc(k2_xboole_0(sK1,sK2),sK0)
    | spl3_1
    | ~ spl3_14 ),
    inference(superposition,[],[f27,f94])).

fof(f94,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f92])).

fof(f27,plain,
    ( ~ v4_pre_topc(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f25])).

fof(f95,plain,
    ( spl3_14
    | ~ spl3_4
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f89,f74,f40,f92])).

fof(f74,plain,
    ( spl3_11
  <=> ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_subset_1(u1_struct_0(sK0),sK1,X1) = k2_xboole_0(sK1,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f89,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2)
    | ~ spl3_4
    | ~ spl3_11 ),
    inference(resolution,[],[f75,f42])).

fof(f75,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_subset_1(u1_struct_0(sK0),sK1,X1) = k2_xboole_0(sK1,X1) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f74])).

fof(f76,plain,
    ( spl3_11
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f68,f64,f45,f74])).

fof(f64,plain,
    ( spl3_9
  <=> ! [X1,X0,X2] :
        ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f68,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_subset_1(u1_struct_0(sK0),sK1,X1) = k2_xboole_0(sK1,X1) )
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(resolution,[],[f65,f47])).

fof(f65,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f64])).

fof(f66,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f23,f64])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f62,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f22,f60])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( v4_pre_topc(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( v4_pre_topc(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( v4_pre_topc(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        & v4_pre_topc(X2,X0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v4_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_xboole_0(X1,X2),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_tops_1)).

fof(f58,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f15,f55])).

fof(f15,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ~ v4_pre_topc(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    & v4_pre_topc(sK2,sK0)
    & v4_pre_topc(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f13,f12,f11])).

fof(f11,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v4_pre_topc(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
                & v4_pre_topc(X2,X0)
                & v4_pre_topc(X1,X0)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v4_pre_topc(k4_subset_1(u1_struct_0(sK0),X1,X2),sK0)
              & v4_pre_topc(X2,sK0)
              & v4_pre_topc(X1,sK0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ v4_pre_topc(k4_subset_1(u1_struct_0(sK0),X1,X2),sK0)
            & v4_pre_topc(X2,sK0)
            & v4_pre_topc(X1,sK0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ~ v4_pre_topc(k4_subset_1(u1_struct_0(sK0),sK1,X2),sK0)
          & v4_pre_topc(X2,sK0)
          & v4_pre_topc(sK1,sK0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( ? [X2] :
        ( ~ v4_pre_topc(k4_subset_1(u1_struct_0(sK0),sK1,X2),sK0)
        & v4_pre_topc(X2,sK0)
        & v4_pre_topc(sK1,sK0)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ v4_pre_topc(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
      & v4_pre_topc(sK2,sK0)
      & v4_pre_topc(sK1,sK0)
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v4_pre_topc(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v4_pre_topc(X2,X0)
              & v4_pre_topc(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v4_pre_topc(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v4_pre_topc(X2,X0)
              & v4_pre_topc(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v4_pre_topc(X2,X0)
                    & v4_pre_topc(X1,X0) )
                 => v4_pre_topc(k4_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v4_pre_topc(X2,X0)
                  & v4_pre_topc(X1,X0) )
               => v4_pre_topc(k4_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tops_1)).

fof(f53,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f16,f50])).

fof(f16,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f48,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f17,f45])).

fof(f17,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f43,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f18,f40])).

fof(f18,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f38,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f19,f35])).

fof(f19,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f33,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f20,f30])).

fof(f20,plain,(
    v4_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f28,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f21,f25])).

fof(f21,plain,(
    ~ v4_pre_topc(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:48:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.41  % (6200)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.13/0.41  % (6205)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.13/0.41  % (6201)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.20/0.41  % (6201)Refutation found. Thanks to Tanya!
% 0.20/0.41  % SZS status Theorem for theBenchmark
% 0.20/0.41  % SZS output start Proof for theBenchmark
% 0.20/0.41  fof(f119,plain,(
% 0.20/0.41    $false),
% 0.20/0.41    inference(avatar_sat_refutation,[],[f28,f33,f38,f43,f48,f53,f58,f62,f66,f76,f95,f106,f112,f118])).
% 0.20/0.41  fof(f118,plain,(
% 0.20/0.41    ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | spl3_16 | ~spl3_17),
% 0.20/0.41    inference(avatar_contradiction_clause,[],[f117])).
% 0.20/0.41  fof(f117,plain,(
% 0.20/0.41    $false | (~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | spl3_16 | ~spl3_17)),
% 0.20/0.41    inference(subsumption_resolution,[],[f116,f42])).
% 0.20/0.41  fof(f42,plain,(
% 0.20/0.41    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_4),
% 0.20/0.41    inference(avatar_component_clause,[],[f40])).
% 0.20/0.41  fof(f40,plain,(
% 0.20/0.41    spl3_4 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.41  fof(f116,plain,(
% 0.20/0.41    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_2 | ~spl3_3 | ~spl3_5 | spl3_16 | ~spl3_17)),
% 0.20/0.41    inference(subsumption_resolution,[],[f115,f37])).
% 0.20/0.41  fof(f37,plain,(
% 0.20/0.41    v4_pre_topc(sK1,sK0) | ~spl3_3),
% 0.20/0.41    inference(avatar_component_clause,[],[f35])).
% 0.20/0.41  fof(f35,plain,(
% 0.20/0.41    spl3_3 <=> v4_pre_topc(sK1,sK0)),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.41  fof(f115,plain,(
% 0.20/0.41    ~v4_pre_topc(sK1,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_2 | ~spl3_5 | spl3_16 | ~spl3_17)),
% 0.20/0.41    inference(subsumption_resolution,[],[f114,f47])).
% 0.20/0.41  fof(f47,plain,(
% 0.20/0.41    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_5),
% 0.20/0.41    inference(avatar_component_clause,[],[f45])).
% 0.20/0.41  fof(f45,plain,(
% 0.20/0.41    spl3_5 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.41  fof(f114,plain,(
% 0.20/0.41    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(sK1,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_2 | spl3_16 | ~spl3_17)),
% 0.20/0.41    inference(subsumption_resolution,[],[f113,f32])).
% 0.20/0.41  fof(f32,plain,(
% 0.20/0.41    v4_pre_topc(sK2,sK0) | ~spl3_2),
% 0.20/0.41    inference(avatar_component_clause,[],[f30])).
% 0.20/0.41  fof(f30,plain,(
% 0.20/0.41    spl3_2 <=> v4_pre_topc(sK2,sK0)),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.41  fof(f113,plain,(
% 0.20/0.41    ~v4_pre_topc(sK2,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(sK1,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | (spl3_16 | ~spl3_17)),
% 0.20/0.41    inference(resolution,[],[f111,f105])).
% 0.20/0.41  fof(f105,plain,(
% 0.20/0.41    ~v4_pre_topc(k2_xboole_0(sK1,sK2),sK0) | spl3_16),
% 0.20/0.41    inference(avatar_component_clause,[],[f103])).
% 0.20/0.41  fof(f103,plain,(
% 0.20/0.41    spl3_16 <=> v4_pre_topc(k2_xboole_0(sK1,sK2),sK0)),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.20/0.41  fof(f111,plain,(
% 0.20/0.41    ( ! [X0,X1] : (v4_pre_topc(k2_xboole_0(X1,X0),sK0) | ~v4_pre_topc(X0,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X1,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_17),
% 0.20/0.41    inference(avatar_component_clause,[],[f110])).
% 0.20/0.41  fof(f110,plain,(
% 0.20/0.41    spl3_17 <=> ! [X1,X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X0,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X1,sK0) | v4_pre_topc(k2_xboole_0(X1,X0),sK0))),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.20/0.41  fof(f112,plain,(
% 0.20/0.41    spl3_17 | ~spl3_6 | ~spl3_7 | ~spl3_8),
% 0.20/0.41    inference(avatar_split_clause,[],[f108,f60,f55,f50,f110])).
% 0.20/0.41  fof(f50,plain,(
% 0.20/0.41    spl3_6 <=> l1_pre_topc(sK0)),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.41  fof(f55,plain,(
% 0.20/0.41    spl3_7 <=> v2_pre_topc(sK0)),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.41  fof(f60,plain,(
% 0.20/0.41    spl3_8 <=> ! [X1,X0,X2] : (v4_pre_topc(k2_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.41  fof(f108,plain,(
% 0.20/0.41    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X0,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X1,sK0) | v4_pre_topc(k2_xboole_0(X1,X0),sK0)) ) | (~spl3_6 | ~spl3_7 | ~spl3_8)),
% 0.20/0.41    inference(subsumption_resolution,[],[f107,f57])).
% 0.20/0.41  fof(f57,plain,(
% 0.20/0.41    v2_pre_topc(sK0) | ~spl3_7),
% 0.20/0.41    inference(avatar_component_clause,[],[f55])).
% 0.20/0.41  fof(f107,plain,(
% 0.20/0.41    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X0,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X1,sK0) | v4_pre_topc(k2_xboole_0(X1,X0),sK0) | ~v2_pre_topc(sK0)) ) | (~spl3_6 | ~spl3_8)),
% 0.20/0.41    inference(resolution,[],[f61,f52])).
% 0.20/0.41  fof(f52,plain,(
% 0.20/0.41    l1_pre_topc(sK0) | ~spl3_6),
% 0.20/0.41    inference(avatar_component_clause,[],[f50])).
% 0.20/0.41  fof(f61,plain,(
% 0.20/0.41    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | v4_pre_topc(k2_xboole_0(X1,X2),X0) | ~v2_pre_topc(X0)) ) | ~spl3_8),
% 0.20/0.41    inference(avatar_component_clause,[],[f60])).
% 0.20/0.41  fof(f106,plain,(
% 0.20/0.41    ~spl3_16 | spl3_1 | ~spl3_14),
% 0.20/0.41    inference(avatar_split_clause,[],[f101,f92,f25,f103])).
% 0.20/0.41  fof(f25,plain,(
% 0.20/0.41    spl3_1 <=> v4_pre_topc(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.41  fof(f92,plain,(
% 0.20/0.41    spl3_14 <=> k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2)),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.20/0.41  fof(f101,plain,(
% 0.20/0.41    ~v4_pre_topc(k2_xboole_0(sK1,sK2),sK0) | (spl3_1 | ~spl3_14)),
% 0.20/0.41    inference(superposition,[],[f27,f94])).
% 0.20/0.41  fof(f94,plain,(
% 0.20/0.41    k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2) | ~spl3_14),
% 0.20/0.41    inference(avatar_component_clause,[],[f92])).
% 0.20/0.41  fof(f27,plain,(
% 0.20/0.41    ~v4_pre_topc(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) | spl3_1),
% 0.20/0.41    inference(avatar_component_clause,[],[f25])).
% 0.20/0.41  fof(f95,plain,(
% 0.20/0.41    spl3_14 | ~spl3_4 | ~spl3_11),
% 0.20/0.41    inference(avatar_split_clause,[],[f89,f74,f40,f92])).
% 0.20/0.41  fof(f74,plain,(
% 0.20/0.41    spl3_11 <=> ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),sK1,X1) = k2_xboole_0(sK1,X1))),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.20/0.41  fof(f89,plain,(
% 0.20/0.41    k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2) | (~spl3_4 | ~spl3_11)),
% 0.20/0.41    inference(resolution,[],[f75,f42])).
% 0.20/0.41  fof(f75,plain,(
% 0.20/0.41    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),sK1,X1) = k2_xboole_0(sK1,X1)) ) | ~spl3_11),
% 0.20/0.41    inference(avatar_component_clause,[],[f74])).
% 0.20/0.41  fof(f76,plain,(
% 0.20/0.41    spl3_11 | ~spl3_5 | ~spl3_9),
% 0.20/0.41    inference(avatar_split_clause,[],[f68,f64,f45,f74])).
% 0.20/0.41  fof(f64,plain,(
% 0.20/0.41    spl3_9 <=> ! [X1,X0,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.41  fof(f68,plain,(
% 0.20/0.41    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),sK1,X1) = k2_xboole_0(sK1,X1)) ) | (~spl3_5 | ~spl3_9)),
% 0.20/0.41    inference(resolution,[],[f65,f47])).
% 0.20/0.41  fof(f65,plain,(
% 0.20/0.41    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)) ) | ~spl3_9),
% 0.20/0.41    inference(avatar_component_clause,[],[f64])).
% 0.20/0.41  fof(f66,plain,(
% 0.20/0.41    spl3_9),
% 0.20/0.41    inference(avatar_split_clause,[],[f23,f64])).
% 0.20/0.41  fof(f23,plain,(
% 0.20/0.41    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.41    inference(cnf_transformation,[],[f10])).
% 0.20/0.41  fof(f10,plain,(
% 0.20/0.41    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.41    inference(flattening,[],[f9])).
% 0.20/0.41  fof(f9,plain,(
% 0.20/0.41    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.20/0.41    inference(ennf_transformation,[],[f1])).
% 0.20/0.41  fof(f1,axiom,(
% 0.20/0.41    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.20/0.41  fof(f62,plain,(
% 0.20/0.41    spl3_8),
% 0.20/0.41    inference(avatar_split_clause,[],[f22,f60])).
% 0.20/0.41  fof(f22,plain,(
% 0.20/0.41    ( ! [X2,X0,X1] : (v4_pre_topc(k2_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f8])).
% 0.20/0.41  fof(f8,plain,(
% 0.20/0.41    ! [X0,X1,X2] : (v4_pre_topc(k2_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.41    inference(flattening,[],[f7])).
% 0.20/0.41  fof(f7,plain,(
% 0.20/0.41    ! [X0,X1,X2] : (v4_pre_topc(k2_xboole_0(X1,X2),X0) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.41    inference(ennf_transformation,[],[f2])).
% 0.20/0.41  fof(f2,axiom,(
% 0.20/0.41    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X2,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_xboole_0(X1,X2),X0))),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_tops_1)).
% 0.20/0.42  fof(f58,plain,(
% 0.20/0.42    spl3_7),
% 0.20/0.42    inference(avatar_split_clause,[],[f15,f55])).
% 0.20/0.42  fof(f15,plain,(
% 0.20/0.42    v2_pre_topc(sK0)),
% 0.20/0.42    inference(cnf_transformation,[],[f14])).
% 0.20/0.42  fof(f14,plain,(
% 0.20/0.42    ((~v4_pre_topc(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & v4_pre_topc(sK2,sK0) & v4_pre_topc(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.20/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f13,f12,f11])).
% 0.20/0.42  fof(f11,plain,(
% 0.20/0.42    ? [X0] : (? [X1] : (? [X2] : (~v4_pre_topc(k4_subset_1(u1_struct_0(X0),X1,X2),X0) & v4_pre_topc(X2,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (~v4_pre_topc(k4_subset_1(u1_struct_0(sK0),X1,X2),sK0) & v4_pre_topc(X2,sK0) & v4_pre_topc(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.20/0.42    introduced(choice_axiom,[])).
% 0.20/0.42  fof(f12,plain,(
% 0.20/0.42    ? [X1] : (? [X2] : (~v4_pre_topc(k4_subset_1(u1_struct_0(sK0),X1,X2),sK0) & v4_pre_topc(X2,sK0) & v4_pre_topc(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (~v4_pre_topc(k4_subset_1(u1_struct_0(sK0),sK1,X2),sK0) & v4_pre_topc(X2,sK0) & v4_pre_topc(sK1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.42    introduced(choice_axiom,[])).
% 0.20/0.42  fof(f13,plain,(
% 0.20/0.42    ? [X2] : (~v4_pre_topc(k4_subset_1(u1_struct_0(sK0),sK1,X2),sK0) & v4_pre_topc(X2,sK0) & v4_pre_topc(sK1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (~v4_pre_topc(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & v4_pre_topc(sK2,sK0) & v4_pre_topc(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.42    introduced(choice_axiom,[])).
% 0.20/0.42  fof(f6,plain,(
% 0.20/0.42    ? [X0] : (? [X1] : (? [X2] : (~v4_pre_topc(k4_subset_1(u1_struct_0(X0),X1,X2),X0) & v4_pre_topc(X2,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.20/0.42    inference(flattening,[],[f5])).
% 0.20/0.42  fof(f5,plain,(
% 0.20/0.42    ? [X0] : (? [X1] : (? [X2] : ((~v4_pre_topc(k4_subset_1(u1_struct_0(X0),X1,X2),X0) & (v4_pre_topc(X2,X0) & v4_pre_topc(X1,X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.20/0.42    inference(ennf_transformation,[],[f4])).
% 0.20/0.42  fof(f4,negated_conjecture,(
% 0.20/0.42    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X2,X0) & v4_pre_topc(X1,X0)) => v4_pre_topc(k4_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 0.20/0.42    inference(negated_conjecture,[],[f3])).
% 0.20/0.42  fof(f3,conjecture,(
% 0.20/0.42    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X2,X0) & v4_pre_topc(X1,X0)) => v4_pre_topc(k4_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tops_1)).
% 0.20/0.42  fof(f53,plain,(
% 0.20/0.42    spl3_6),
% 0.20/0.42    inference(avatar_split_clause,[],[f16,f50])).
% 0.20/0.42  fof(f16,plain,(
% 0.20/0.42    l1_pre_topc(sK0)),
% 0.20/0.42    inference(cnf_transformation,[],[f14])).
% 0.20/0.42  fof(f48,plain,(
% 0.20/0.42    spl3_5),
% 0.20/0.42    inference(avatar_split_clause,[],[f17,f45])).
% 0.20/0.42  fof(f17,plain,(
% 0.20/0.42    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.42    inference(cnf_transformation,[],[f14])).
% 0.20/0.42  fof(f43,plain,(
% 0.20/0.42    spl3_4),
% 0.20/0.42    inference(avatar_split_clause,[],[f18,f40])).
% 0.20/0.42  fof(f18,plain,(
% 0.20/0.42    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.42    inference(cnf_transformation,[],[f14])).
% 0.20/0.42  fof(f38,plain,(
% 0.20/0.42    spl3_3),
% 0.20/0.42    inference(avatar_split_clause,[],[f19,f35])).
% 0.20/0.42  fof(f19,plain,(
% 0.20/0.42    v4_pre_topc(sK1,sK0)),
% 0.20/0.42    inference(cnf_transformation,[],[f14])).
% 0.20/0.42  fof(f33,plain,(
% 0.20/0.42    spl3_2),
% 0.20/0.42    inference(avatar_split_clause,[],[f20,f30])).
% 0.20/0.42  fof(f20,plain,(
% 0.20/0.42    v4_pre_topc(sK2,sK0)),
% 0.20/0.42    inference(cnf_transformation,[],[f14])).
% 0.20/0.42  fof(f28,plain,(
% 0.20/0.42    ~spl3_1),
% 0.20/0.42    inference(avatar_split_clause,[],[f21,f25])).
% 0.20/0.42  fof(f21,plain,(
% 0.20/0.42    ~v4_pre_topc(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 0.20/0.42    inference(cnf_transformation,[],[f14])).
% 0.20/0.42  % SZS output end Proof for theBenchmark
% 0.20/0.42  % (6201)------------------------------
% 0.20/0.42  % (6201)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.42  % (6201)Termination reason: Refutation
% 0.20/0.42  
% 0.20/0.42  % (6201)Memory used [KB]: 10618
% 0.20/0.42  % (6201)Time elapsed: 0.007 s
% 0.20/0.42  % (6201)------------------------------
% 0.20/0.42  % (6201)------------------------------
% 0.20/0.42  % (6195)Success in time 0.065 s
%------------------------------------------------------------------------------
