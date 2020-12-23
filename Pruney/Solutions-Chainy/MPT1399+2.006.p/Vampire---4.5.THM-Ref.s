%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:12 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  202 ( 429 expanded)
%              Number of leaves         :   52 ( 178 expanded)
%              Depth                    :   13
%              Number of atoms          :  737 (2847 expanded)
%              Number of equality atoms :   47 ( 229 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f464,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f85,f90,f95,f100,f104,f109,f113,f117,f121,f127,f131,f140,f144,f155,f160,f164,f168,f172,f177,f183,f211,f220,f224,f228,f237,f350,f354,f358,f367,f382,f449,f457,f463])).

fof(f463,plain,
    ( spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_21
    | ~ spl4_56 ),
    inference(avatar_contradiction_clause,[],[f462])).

fof(f462,plain,
    ( $false
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_21
    | ~ spl4_56 ),
    inference(subsumption_resolution,[],[f461,f84])).

fof(f84,plain,
    ( ~ v2_struct_0(sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl4_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f461,plain,
    ( v2_struct_0(sK0)
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_21
    | ~ spl4_56 ),
    inference(subsumption_resolution,[],[f460,f89])).

fof(f89,plain,
    ( v2_pre_topc(sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl4_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f460,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_3
    | ~ spl4_21
    | ~ spl4_56 ),
    inference(subsumption_resolution,[],[f458,f94])).

fof(f94,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl4_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f458,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_21
    | ~ spl4_56 ),
    inference(resolution,[],[f456,f182])).

fof(f182,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(sK3(X0))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f181])).

fof(f181,plain,
    ( spl4_21
  <=> ! [X0] :
        ( ~ v1_xboole_0(sK3(X0))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f456,plain,
    ( v1_xboole_0(sK3(sK0))
    | ~ spl4_56 ),
    inference(avatar_component_clause,[],[f454])).

fof(f454,plain,
    ( spl4_56
  <=> v1_xboole_0(sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).

fof(f457,plain,
    ( spl4_56
    | ~ spl4_20
    | ~ spl4_55 ),
    inference(avatar_split_clause,[],[f450,f446,f175,f454])).

fof(f175,plain,
    ( spl4_20
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK2))
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f446,plain,
    ( spl4_55
  <=> m1_subset_1(sK3(sK0),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_55])])).

fof(f450,plain,
    ( v1_xboole_0(sK3(sK0))
    | ~ spl4_20
    | ~ spl4_55 ),
    inference(resolution,[],[f448,f176])).

fof(f176,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK2))
        | v1_xboole_0(X0) )
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f175])).

fof(f448,plain,
    ( m1_subset_1(sK3(sK0),k1_zfmisc_1(sK2))
    | ~ spl4_55 ),
    inference(avatar_component_clause,[],[f446])).

fof(f449,plain,
    ( spl4_55
    | ~ spl4_15
    | ~ spl4_29
    | ~ spl4_32
    | spl4_36
    | spl4_37 ),
    inference(avatar_split_clause,[],[f390,f260,f256,f235,f217,f152,f446])).

fof(f152,plain,
    ( spl4_15
  <=> m1_subset_1(sK1,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f217,plain,
    ( spl4_29
  <=> m1_subset_1(sK3(sK0),k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f235,plain,
    ( spl4_32
  <=> ! [X3,X2] :
        ( r2_hidden(X2,X3)
        | r2_hidden(X2,sK2)
        | ~ m1_subset_1(X2,X3)
        | sK2 = X3 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f256,plain,
    ( spl4_36
  <=> r2_hidden(sK1,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f260,plain,
    ( spl4_37
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f390,plain,
    ( m1_subset_1(sK3(sK0),k1_zfmisc_1(sK2))
    | ~ spl4_15
    | ~ spl4_29
    | ~ spl4_32
    | spl4_36
    | spl4_37 ),
    inference(backward_demodulation,[],[f219,f383])).

fof(f383,plain,
    ( sK2 = k2_struct_0(sK0)
    | ~ spl4_15
    | ~ spl4_32
    | spl4_36
    | spl4_37 ),
    inference(subsumption_resolution,[],[f368,f261])).

fof(f261,plain,
    ( ~ r2_hidden(sK1,sK2)
    | spl4_37 ),
    inference(avatar_component_clause,[],[f260])).

fof(f368,plain,
    ( r2_hidden(sK1,sK2)
    | sK2 = k2_struct_0(sK0)
    | ~ spl4_15
    | ~ spl4_32
    | spl4_36 ),
    inference(subsumption_resolution,[],[f291,f257])).

fof(f257,plain,
    ( ~ r2_hidden(sK1,k2_struct_0(sK0))
    | spl4_36 ),
    inference(avatar_component_clause,[],[f256])).

fof(f291,plain,
    ( r2_hidden(sK1,sK2)
    | r2_hidden(sK1,k2_struct_0(sK0))
    | sK2 = k2_struct_0(sK0)
    | ~ spl4_15
    | ~ spl4_32 ),
    inference(resolution,[],[f154,f236])).

fof(f236,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,X3)
        | r2_hidden(X2,sK2)
        | r2_hidden(X2,X3)
        | sK2 = X3 )
    | ~ spl4_32 ),
    inference(avatar_component_clause,[],[f235])).

fof(f154,plain,
    ( m1_subset_1(sK1,k2_struct_0(sK0))
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f152])).

fof(f219,plain,
    ( m1_subset_1(sK3(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl4_29 ),
    inference(avatar_component_clause,[],[f217])).

fof(f382,plain,
    ( ~ spl4_5
    | ~ spl4_13
    | ~ spl4_37 ),
    inference(avatar_contradiction_clause,[],[f381])).

fof(f381,plain,
    ( $false
    | ~ spl4_5
    | ~ spl4_13
    | ~ spl4_37 ),
    inference(subsumption_resolution,[],[f374,f103])).

fof(f103,plain,
    ( ! [X0] : r1_tarski(sK2,X0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl4_5
  <=> ! [X0] : r1_tarski(sK2,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f374,plain,
    ( ~ r1_tarski(sK2,sK1)
    | ~ spl4_13
    | ~ spl4_37 ),
    inference(resolution,[],[f262,f139])).

fof(f139,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ r1_tarski(X1,X0) )
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl4_13
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X1,X0)
        | ~ r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f262,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl4_37 ),
    inference(avatar_component_clause,[],[f260])).

fof(f367,plain,
    ( ~ spl4_5
    | ~ spl4_13
    | ~ spl4_47 ),
    inference(avatar_contradiction_clause,[],[f366])).

fof(f366,plain,
    ( $false
    | ~ spl4_5
    | ~ spl4_13
    | ~ spl4_47 ),
    inference(subsumption_resolution,[],[f363,f103])).

fof(f363,plain,
    ( ~ r1_tarski(sK2,k2_struct_0(sK0))
    | ~ spl4_13
    | ~ spl4_47 ),
    inference(resolution,[],[f349,f139])).

fof(f349,plain,
    ( r2_hidden(k2_struct_0(sK0),sK2)
    | ~ spl4_47 ),
    inference(avatar_component_clause,[],[f347])).

fof(f347,plain,
    ( spl4_47
  <=> r2_hidden(k2_struct_0(sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).

fof(f358,plain,
    ( ~ spl4_2
    | ~ spl4_3
    | ~ spl4_18
    | spl4_46 ),
    inference(avatar_contradiction_clause,[],[f357])).

fof(f357,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_18
    | spl4_46 ),
    inference(subsumption_resolution,[],[f356,f89])).

fof(f356,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ spl4_3
    | ~ spl4_18
    | spl4_46 ),
    inference(subsumption_resolution,[],[f355,f94])).

fof(f355,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl4_18
    | spl4_46 ),
    inference(resolution,[],[f345,f167])).

fof(f167,plain,
    ( ! [X0] :
        ( v4_pre_topc(k2_struct_0(X0),X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f166])).

fof(f166,plain,
    ( spl4_18
  <=> ! [X0] :
        ( v4_pre_topc(k2_struct_0(X0),X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f345,plain,
    ( ~ v4_pre_topc(k2_struct_0(sK0),sK0)
    | spl4_46 ),
    inference(avatar_component_clause,[],[f343])).

fof(f343,plain,
    ( spl4_46
  <=> v4_pre_topc(k2_struct_0(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).

fof(f354,plain,
    ( ~ spl4_2
    | ~ spl4_3
    | ~ spl4_19
    | spl4_45 ),
    inference(avatar_contradiction_clause,[],[f353])).

fof(f353,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_19
    | spl4_45 ),
    inference(subsumption_resolution,[],[f352,f89])).

fof(f352,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ spl4_3
    | ~ spl4_19
    | spl4_45 ),
    inference(subsumption_resolution,[],[f351,f94])).

fof(f351,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl4_19
    | spl4_45 ),
    inference(resolution,[],[f341,f171])).

fof(f171,plain,
    ( ! [X0] :
        ( v3_pre_topc(k2_struct_0(X0),X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f170])).

fof(f170,plain,
    ( spl4_19
  <=> ! [X0] :
        ( v3_pre_topc(k2_struct_0(X0),X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f341,plain,
    ( ~ v3_pre_topc(k2_struct_0(sK0),sK0)
    | spl4_45 ),
    inference(avatar_component_clause,[],[f339])).

fof(f339,plain,
    ( spl4_45
  <=> v3_pre_topc(k2_struct_0(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).

fof(f350,plain,
    ( ~ spl4_45
    | ~ spl4_46
    | spl4_47
    | ~ spl4_8
    | ~ spl4_30
    | ~ spl4_36 ),
    inference(avatar_split_clause,[],[f326,f256,f222,f115,f347,f343,f339])).

fof(f115,plain,
    ( spl4_8
  <=> ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f222,plain,
    ( spl4_30
  <=> ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0)))
        | r2_hidden(X3,sK2)
        | ~ r2_hidden(sK1,X3)
        | ~ v4_pre_topc(X3,sK0)
        | ~ v3_pre_topc(X3,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f326,plain,
    ( r2_hidden(k2_struct_0(sK0),sK2)
    | ~ v4_pre_topc(k2_struct_0(sK0),sK0)
    | ~ v3_pre_topc(k2_struct_0(sK0),sK0)
    | ~ spl4_8
    | ~ spl4_30
    | ~ spl4_36 ),
    inference(subsumption_resolution,[],[f325,f116])).

fof(f116,plain,
    ( ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f115])).

fof(f325,plain,
    ( r2_hidden(k2_struct_0(sK0),sK2)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ v4_pre_topc(k2_struct_0(sK0),sK0)
    | ~ v3_pre_topc(k2_struct_0(sK0),sK0)
    | ~ spl4_30
    | ~ spl4_36 ),
    inference(resolution,[],[f223,f258])).

fof(f258,plain,
    ( r2_hidden(sK1,k2_struct_0(sK0))
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f256])).

fof(f223,plain,
    ( ! [X3] :
        ( ~ r2_hidden(sK1,X3)
        | r2_hidden(X3,sK2)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v4_pre_topc(X3,sK0)
        | ~ v3_pre_topc(X3,sK0) )
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f222])).

fof(f237,plain,
    ( spl4_32
    | ~ spl4_7
    | ~ spl4_11
    | ~ spl4_31 ),
    inference(avatar_split_clause,[],[f233,f226,f129,f111,f235])).

fof(f111,plain,
    ( spl4_7
  <=> ! [X0] : m1_subset_1(sK2,k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f129,plain,
    ( spl4_11
  <=> ! [X0] : k3_subset_1(X0,sK2) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f226,plain,
    ( spl4_31
  <=> ! [X1,X0,X2] :
        ( r2_hidden(X2,k3_subset_1(X0,X1))
        | r2_hidden(X2,X1)
        | ~ m1_subset_1(X2,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | sK2 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f233,plain,
    ( ! [X2,X3] :
        ( r2_hidden(X2,X3)
        | r2_hidden(X2,sK2)
        | ~ m1_subset_1(X2,X3)
        | sK2 = X3 )
    | ~ spl4_7
    | ~ spl4_11
    | ~ spl4_31 ),
    inference(forward_demodulation,[],[f230,f130])).

fof(f130,plain,
    ( ! [X0] : k3_subset_1(X0,sK2) = X0
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f129])).

fof(f230,plain,
    ( ! [X2,X3] :
        ( r2_hidden(X2,sK2)
        | ~ m1_subset_1(X2,X3)
        | r2_hidden(X2,k3_subset_1(X3,sK2))
        | sK2 = X3 )
    | ~ spl4_7
    | ~ spl4_31 ),
    inference(resolution,[],[f227,f112])).

fof(f112,plain,
    ( ! [X0] : m1_subset_1(sK2,k1_zfmisc_1(X0))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f111])).

fof(f227,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | r2_hidden(X2,X1)
        | ~ m1_subset_1(X2,X0)
        | r2_hidden(X2,k3_subset_1(X0,X1))
        | sK2 = X0 )
    | ~ spl4_31 ),
    inference(avatar_component_clause,[],[f226])).

fof(f228,plain,(
    spl4_31 ),
    inference(avatar_split_clause,[],[f79,f226])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k3_subset_1(X0,X1))
      | r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | sK2 = X0 ) ),
    inference(definition_unfolding,[],[f63,f52])).

fof(f52,plain,(
    k1_xboole_0 = sK2 ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( k1_xboole_0 = sK2
    & ! [X3] :
        ( ( ( r2_hidden(X3,sK2)
            | ~ r2_hidden(sK1,X3)
            | ~ v4_pre_topc(X3,sK0)
            | ~ v3_pre_topc(X3,sK0) )
          & ( ( r2_hidden(sK1,X3)
              & v4_pre_topc(X3,sK0)
              & v3_pre_topc(X3,sK0) )
            | ~ r2_hidden(X3,sK2) ) )
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f36,f39,f38,f37])).

fof(f37,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k1_xboole_0 = X2
                & ! [X3] :
                    ( ( ( r2_hidden(X3,X2)
                        | ~ r2_hidden(X1,X3)
                        | ~ v4_pre_topc(X3,X0)
                        | ~ v3_pre_topc(X3,X0) )
                      & ( ( r2_hidden(X1,X3)
                          & v4_pre_topc(X3,X0)
                          & v3_pre_topc(X3,X0) )
                        | ~ r2_hidden(X3,X2) ) )
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ v4_pre_topc(X3,sK0)
                      | ~ v3_pre_topc(X3,sK0) )
                    & ( ( r2_hidden(X1,X3)
                        & v4_pre_topc(X3,sK0)
                        & v3_pre_topc(X3,sK0) )
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k1_xboole_0 = X2
            & ! [X3] :
                ( ( ( r2_hidden(X3,X2)
                    | ~ r2_hidden(X1,X3)
                    | ~ v4_pre_topc(X3,sK0)
                    | ~ v3_pre_topc(X3,sK0) )
                  & ( ( r2_hidden(X1,X3)
                      & v4_pre_topc(X3,sK0)
                      & v3_pre_topc(X3,sK0) )
                    | ~ r2_hidden(X3,X2) ) )
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( k1_xboole_0 = X2
          & ! [X3] :
              ( ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(sK1,X3)
                  | ~ v4_pre_topc(X3,sK0)
                  | ~ v3_pre_topc(X3,sK0) )
                & ( ( r2_hidden(sK1,X3)
                    & v4_pre_topc(X3,sK0)
                    & v3_pre_topc(X3,sK0) )
                  | ~ r2_hidden(X3,X2) ) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X2] :
        ( k1_xboole_0 = X2
        & ! [X3] :
            ( ( ( r2_hidden(X3,X2)
                | ~ r2_hidden(sK1,X3)
                | ~ v4_pre_topc(X3,sK0)
                | ~ v3_pre_topc(X3,sK0) )
              & ( ( r2_hidden(sK1,X3)
                  & v4_pre_topc(X3,sK0)
                  & v3_pre_topc(X3,sK0) )
                | ~ r2_hidden(X3,X2) ) )
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( k1_xboole_0 = sK2
      & ! [X3] :
          ( ( ( r2_hidden(X3,sK2)
              | ~ r2_hidden(sK1,X3)
              | ~ v4_pre_topc(X3,sK0)
              | ~ v3_pre_topc(X3,sK0) )
            & ( ( r2_hidden(sK1,X3)
                & v4_pre_topc(X3,sK0)
                & v3_pre_topc(X3,sK0) )
              | ~ r2_hidden(X3,sK2) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ v4_pre_topc(X3,X0)
                      | ~ v3_pre_topc(X3,X0) )
                    & ( ( r2_hidden(X1,X3)
                        & v4_pre_topc(X3,X0)
                        & v3_pre_topc(X3,X0) )
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ v4_pre_topc(X3,X0)
                      | ~ v3_pre_topc(X3,X0) )
                    & ( ( r2_hidden(X1,X3)
                        & v4_pre_topc(X3,X0)
                        & v3_pre_topc(X3,X0) )
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( r2_hidden(X3,X2)
                  <=> ( r2_hidden(X1,X3)
                      & v4_pre_topc(X3,X0)
                      & v3_pre_topc(X3,X0) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( r2_hidden(X3,X2)
                  <=> ( r2_hidden(X1,X3)
                      & v4_pre_topc(X3,X0)
                      & v3_pre_topc(X3,X0) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ~ ( k1_xboole_0 = X2
                    & ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ( r2_hidden(X3,X2)
                        <=> ( r2_hidden(X1,X3)
                            & v4_pre_topc(X3,X0)
                            & v3_pre_topc(X3,X0) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ~ ( k1_xboole_0 = X2
                  & ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                     => ( r2_hidden(X3,X2)
                      <=> ( r2_hidden(X1,X3)
                          & v4_pre_topc(X3,X0)
                          & v3_pre_topc(X3,X0) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_connsp_2)).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k3_subset_1(X0,X1))
      | r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k3_subset_1(X0,X1))
              | r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | k1_xboole_0 = X0 ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k3_subset_1(X0,X1))
              | r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ! [X2] :
              ( m1_subset_1(X2,X0)
             => ( ~ r2_hidden(X2,X1)
               => r2_hidden(X2,k3_subset_1(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_subset_1)).

fof(f224,plain,
    ( spl4_30
    | ~ spl4_10
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f150,f142,f124,f222])).

fof(f124,plain,
    ( spl4_10
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f142,plain,
    ( spl4_14
  <=> ! [X0] :
        ( k2_struct_0(X0) = u1_struct_0(X0)
        | ~ l1_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f150,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0)))
        | r2_hidden(X3,sK2)
        | ~ r2_hidden(sK1,X3)
        | ~ v4_pre_topc(X3,sK0)
        | ~ v3_pre_topc(X3,sK0) )
    | ~ spl4_10
    | ~ spl4_14 ),
    inference(backward_demodulation,[],[f51,f145])).

fof(f145,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl4_10
    | ~ spl4_14 ),
    inference(resolution,[],[f143,f126])).

fof(f126,plain,
    ( l1_struct_0(sK0)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f124])).

fof(f143,plain,
    ( ! [X0] :
        ( ~ l1_struct_0(X0)
        | k2_struct_0(X0) = u1_struct_0(X0) )
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f142])).

fof(f51,plain,(
    ! [X3] :
      ( r2_hidden(X3,sK2)
      | ~ r2_hidden(sK1,X3)
      | ~ v4_pre_topc(X3,sK0)
      | ~ v3_pre_topc(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f220,plain,
    ( spl4_29
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_16
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f215,f209,f157,f92,f87,f82,f217])).

fof(f157,plain,
    ( spl4_16
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f209,plain,
    ( spl4_28
  <=> ! [X0] :
        ( m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f215,plain,
    ( m1_subset_1(sK3(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_16
    | ~ spl4_28 ),
    inference(subsumption_resolution,[],[f214,f84])).

fof(f214,plain,
    ( m1_subset_1(sK3(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_16
    | ~ spl4_28 ),
    inference(subsumption_resolution,[],[f213,f89])).

fof(f213,plain,
    ( m1_subset_1(sK3(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_3
    | ~ spl4_16
    | ~ spl4_28 ),
    inference(subsumption_resolution,[],[f212,f94])).

fof(f212,plain,
    ( m1_subset_1(sK3(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_16
    | ~ spl4_28 ),
    inference(superposition,[],[f210,f159])).

fof(f159,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f157])).

fof(f210,plain,
    ( ! [X0] :
        ( m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f209])).

fof(f211,plain,(
    spl4_28 ),
    inference(avatar_split_clause,[],[f64,f209])).

fof(f64,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ( v4_pre_topc(sK3(X0),X0)
        & v3_pre_topc(sK3(X0),X0)
        & ~ v1_xboole_0(sK3(X0))
        & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( v4_pre_topc(sK3(X0),X0)
        & v3_pre_topc(sK3(X0),X0)
        & ~ v1_xboole_0(sK3(X0))
        & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_tops_1)).

fof(f183,plain,(
    spl4_21 ),
    inference(avatar_split_clause,[],[f65,f181])).

fof(f65,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK3(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f177,plain,
    ( spl4_20
    | ~ spl4_4
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f173,f162,f97,f175])).

fof(f97,plain,
    ( spl4_4
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f162,plain,
    ( spl4_17
  <=> ! [X1,X0] :
        ( v1_xboole_0(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f173,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK2))
        | v1_xboole_0(X0) )
    | ~ spl4_4
    | ~ spl4_17 ),
    inference(resolution,[],[f163,f99])).

fof(f99,plain,
    ( v1_xboole_0(sK2)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f97])).

fof(f163,plain,
    ( ! [X0,X1] :
        ( ~ v1_xboole_0(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | v1_xboole_0(X1) )
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f162])).

fof(f172,plain,(
    spl4_19 ),
    inference(avatar_split_clause,[],[f69,f170])).

fof(f69,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).

fof(f168,plain,(
    spl4_18 ),
    inference(avatar_split_clause,[],[f68,f166])).

fof(f68,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_pre_topc)).

fof(f164,plain,(
    spl4_17 ),
    inference(avatar_split_clause,[],[f62,f162])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f160,plain,
    ( spl4_16
    | ~ spl4_10
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f145,f142,f124,f157])).

fof(f155,plain,
    ( spl4_15
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f146,f142,f124,f106,f152])).

fof(f106,plain,
    ( spl4_6
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f146,plain,
    ( m1_subset_1(sK1,k2_struct_0(sK0))
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_14 ),
    inference(backward_demodulation,[],[f108,f145])).

fof(f108,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f106])).

fof(f144,plain,(
    spl4_14 ),
    inference(avatar_split_clause,[],[f60,f142])).

fof(f60,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f140,plain,(
    spl4_13 ),
    inference(avatar_split_clause,[],[f70,f138])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f131,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f76,f129])).

fof(f76,plain,(
    ! [X0] : k3_subset_1(X0,sK2) = X0 ),
    inference(definition_unfolding,[],[f56,f73])).

fof(f73,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,sK2) ),
    inference(definition_unfolding,[],[f59,f72])).

fof(f72,plain,(
    ! [X0] : k1_subset_1(X0) = sK2 ),
    inference(definition_unfolding,[],[f55,f52])).

fof(f55,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

fof(f59,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

fof(f56,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f127,plain,
    ( spl4_10
    | ~ spl4_3
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f122,f119,f92,f124])).

fof(f119,plain,
    ( spl4_9
  <=> ! [X0] :
        ( l1_struct_0(X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f122,plain,
    ( l1_struct_0(sK0)
    | ~ spl4_3
    | ~ spl4_9 ),
    inference(resolution,[],[f120,f94])).

fof(f120,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | l1_struct_0(X0) )
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f119])).

fof(f121,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f61,f119])).

fof(f61,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f117,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f80,f115])).

fof(f80,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f78,f76])).

fof(f78,plain,(
    ! [X0] : m1_subset_1(k3_subset_1(X0,sK2),k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f58,f73])).

fof(f58,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f113,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f77,f111])).

fof(f77,plain,(
    ! [X0] : m1_subset_1(sK2,k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f57,f52])).

fof(f57,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f109,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f46,f106])).

fof(f46,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f40])).

fof(f104,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f75,f102])).

fof(f75,plain,(
    ! [X0] : r1_tarski(sK2,X0) ),
    inference(definition_unfolding,[],[f54,f52])).

fof(f54,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f100,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f74,f97])).

fof(f74,plain,(
    v1_xboole_0(sK2) ),
    inference(definition_unfolding,[],[f53,f52])).

fof(f53,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f95,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f45,f92])).

fof(f45,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f90,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f44,f87])).

fof(f44,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f85,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f43,f82])).

fof(f43,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:28:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.43  % (29902)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.43  % (29902)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f464,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(avatar_sat_refutation,[],[f85,f90,f95,f100,f104,f109,f113,f117,f121,f127,f131,f140,f144,f155,f160,f164,f168,f172,f177,f183,f211,f220,f224,f228,f237,f350,f354,f358,f367,f382,f449,f457,f463])).
% 0.21/0.43  fof(f463,plain,(
% 0.21/0.43    spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_21 | ~spl4_56),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f462])).
% 0.21/0.43  fof(f462,plain,(
% 0.21/0.43    $false | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_21 | ~spl4_56)),
% 0.21/0.43    inference(subsumption_resolution,[],[f461,f84])).
% 0.21/0.43  fof(f84,plain,(
% 0.21/0.43    ~v2_struct_0(sK0) | spl4_1),
% 0.21/0.43    inference(avatar_component_clause,[],[f82])).
% 0.21/0.43  fof(f82,plain,(
% 0.21/0.43    spl4_1 <=> v2_struct_0(sK0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.43  fof(f461,plain,(
% 0.21/0.43    v2_struct_0(sK0) | (~spl4_2 | ~spl4_3 | ~spl4_21 | ~spl4_56)),
% 0.21/0.43    inference(subsumption_resolution,[],[f460,f89])).
% 0.21/0.43  fof(f89,plain,(
% 0.21/0.43    v2_pre_topc(sK0) | ~spl4_2),
% 0.21/0.43    inference(avatar_component_clause,[],[f87])).
% 0.21/0.43  fof(f87,plain,(
% 0.21/0.43    spl4_2 <=> v2_pre_topc(sK0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.43  fof(f460,plain,(
% 0.21/0.43    ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl4_3 | ~spl4_21 | ~spl4_56)),
% 0.21/0.43    inference(subsumption_resolution,[],[f458,f94])).
% 0.21/0.43  fof(f94,plain,(
% 0.21/0.43    l1_pre_topc(sK0) | ~spl4_3),
% 0.21/0.43    inference(avatar_component_clause,[],[f92])).
% 0.21/0.43  fof(f92,plain,(
% 0.21/0.43    spl4_3 <=> l1_pre_topc(sK0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.43  fof(f458,plain,(
% 0.21/0.43    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl4_21 | ~spl4_56)),
% 0.21/0.43    inference(resolution,[],[f456,f182])).
% 0.21/0.43  fof(f182,plain,(
% 0.21/0.43    ( ! [X0] : (~v1_xboole_0(sK3(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) ) | ~spl4_21),
% 0.21/0.43    inference(avatar_component_clause,[],[f181])).
% 0.21/0.43  fof(f181,plain,(
% 0.21/0.43    spl4_21 <=> ! [X0] : (~v1_xboole_0(sK3(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.21/0.43  fof(f456,plain,(
% 0.21/0.43    v1_xboole_0(sK3(sK0)) | ~spl4_56),
% 0.21/0.43    inference(avatar_component_clause,[],[f454])).
% 0.21/0.43  fof(f454,plain,(
% 0.21/0.43    spl4_56 <=> v1_xboole_0(sK3(sK0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).
% 0.21/0.43  fof(f457,plain,(
% 0.21/0.43    spl4_56 | ~spl4_20 | ~spl4_55),
% 0.21/0.43    inference(avatar_split_clause,[],[f450,f446,f175,f454])).
% 0.21/0.43  fof(f175,plain,(
% 0.21/0.43    spl4_20 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK2)) | v1_xboole_0(X0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.21/0.43  fof(f446,plain,(
% 0.21/0.43    spl4_55 <=> m1_subset_1(sK3(sK0),k1_zfmisc_1(sK2))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_55])])).
% 0.21/0.43  fof(f450,plain,(
% 0.21/0.43    v1_xboole_0(sK3(sK0)) | (~spl4_20 | ~spl4_55)),
% 0.21/0.43    inference(resolution,[],[f448,f176])).
% 0.21/0.43  fof(f176,plain,(
% 0.21/0.43    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK2)) | v1_xboole_0(X0)) ) | ~spl4_20),
% 0.21/0.43    inference(avatar_component_clause,[],[f175])).
% 0.21/0.43  fof(f448,plain,(
% 0.21/0.43    m1_subset_1(sK3(sK0),k1_zfmisc_1(sK2)) | ~spl4_55),
% 0.21/0.43    inference(avatar_component_clause,[],[f446])).
% 0.21/0.43  fof(f449,plain,(
% 0.21/0.43    spl4_55 | ~spl4_15 | ~spl4_29 | ~spl4_32 | spl4_36 | spl4_37),
% 0.21/0.43    inference(avatar_split_clause,[],[f390,f260,f256,f235,f217,f152,f446])).
% 0.21/0.43  fof(f152,plain,(
% 0.21/0.43    spl4_15 <=> m1_subset_1(sK1,k2_struct_0(sK0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.21/0.43  fof(f217,plain,(
% 0.21/0.43    spl4_29 <=> m1_subset_1(sK3(sK0),k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 0.21/0.43  fof(f235,plain,(
% 0.21/0.43    spl4_32 <=> ! [X3,X2] : (r2_hidden(X2,X3) | r2_hidden(X2,sK2) | ~m1_subset_1(X2,X3) | sK2 = X3)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 0.21/0.43  fof(f256,plain,(
% 0.21/0.43    spl4_36 <=> r2_hidden(sK1,k2_struct_0(sK0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 0.21/0.43  fof(f260,plain,(
% 0.21/0.43    spl4_37 <=> r2_hidden(sK1,sK2)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).
% 0.21/0.43  fof(f390,plain,(
% 0.21/0.43    m1_subset_1(sK3(sK0),k1_zfmisc_1(sK2)) | (~spl4_15 | ~spl4_29 | ~spl4_32 | spl4_36 | spl4_37)),
% 0.21/0.43    inference(backward_demodulation,[],[f219,f383])).
% 0.21/0.43  fof(f383,plain,(
% 0.21/0.43    sK2 = k2_struct_0(sK0) | (~spl4_15 | ~spl4_32 | spl4_36 | spl4_37)),
% 0.21/0.43    inference(subsumption_resolution,[],[f368,f261])).
% 0.21/0.43  fof(f261,plain,(
% 0.21/0.43    ~r2_hidden(sK1,sK2) | spl4_37),
% 0.21/0.43    inference(avatar_component_clause,[],[f260])).
% 0.21/0.43  fof(f368,plain,(
% 0.21/0.43    r2_hidden(sK1,sK2) | sK2 = k2_struct_0(sK0) | (~spl4_15 | ~spl4_32 | spl4_36)),
% 0.21/0.43    inference(subsumption_resolution,[],[f291,f257])).
% 0.21/0.43  fof(f257,plain,(
% 0.21/0.43    ~r2_hidden(sK1,k2_struct_0(sK0)) | spl4_36),
% 0.21/0.43    inference(avatar_component_clause,[],[f256])).
% 0.21/0.43  fof(f291,plain,(
% 0.21/0.43    r2_hidden(sK1,sK2) | r2_hidden(sK1,k2_struct_0(sK0)) | sK2 = k2_struct_0(sK0) | (~spl4_15 | ~spl4_32)),
% 0.21/0.43    inference(resolution,[],[f154,f236])).
% 0.21/0.43  fof(f236,plain,(
% 0.21/0.43    ( ! [X2,X3] : (~m1_subset_1(X2,X3) | r2_hidden(X2,sK2) | r2_hidden(X2,X3) | sK2 = X3) ) | ~spl4_32),
% 0.21/0.43    inference(avatar_component_clause,[],[f235])).
% 0.21/0.43  fof(f154,plain,(
% 0.21/0.43    m1_subset_1(sK1,k2_struct_0(sK0)) | ~spl4_15),
% 0.21/0.43    inference(avatar_component_clause,[],[f152])).
% 0.21/0.43  fof(f219,plain,(
% 0.21/0.43    m1_subset_1(sK3(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~spl4_29),
% 0.21/0.43    inference(avatar_component_clause,[],[f217])).
% 0.21/0.43  fof(f382,plain,(
% 0.21/0.43    ~spl4_5 | ~spl4_13 | ~spl4_37),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f381])).
% 0.21/0.43  fof(f381,plain,(
% 0.21/0.43    $false | (~spl4_5 | ~spl4_13 | ~spl4_37)),
% 0.21/0.43    inference(subsumption_resolution,[],[f374,f103])).
% 0.21/0.43  fof(f103,plain,(
% 0.21/0.43    ( ! [X0] : (r1_tarski(sK2,X0)) ) | ~spl4_5),
% 0.21/0.43    inference(avatar_component_clause,[],[f102])).
% 0.21/0.43  fof(f102,plain,(
% 0.21/0.43    spl4_5 <=> ! [X0] : r1_tarski(sK2,X0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.44  fof(f374,plain,(
% 0.21/0.44    ~r1_tarski(sK2,sK1) | (~spl4_13 | ~spl4_37)),
% 0.21/0.44    inference(resolution,[],[f262,f139])).
% 0.21/0.44  fof(f139,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) ) | ~spl4_13),
% 0.21/0.44    inference(avatar_component_clause,[],[f138])).
% 0.21/0.44  fof(f138,plain,(
% 0.21/0.44    spl4_13 <=> ! [X1,X0] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.21/0.44  fof(f262,plain,(
% 0.21/0.44    r2_hidden(sK1,sK2) | ~spl4_37),
% 0.21/0.44    inference(avatar_component_clause,[],[f260])).
% 0.21/0.44  fof(f367,plain,(
% 0.21/0.44    ~spl4_5 | ~spl4_13 | ~spl4_47),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f366])).
% 0.21/0.44  fof(f366,plain,(
% 0.21/0.44    $false | (~spl4_5 | ~spl4_13 | ~spl4_47)),
% 0.21/0.44    inference(subsumption_resolution,[],[f363,f103])).
% 0.21/0.44  fof(f363,plain,(
% 0.21/0.44    ~r1_tarski(sK2,k2_struct_0(sK0)) | (~spl4_13 | ~spl4_47)),
% 0.21/0.44    inference(resolution,[],[f349,f139])).
% 0.21/0.44  fof(f349,plain,(
% 0.21/0.44    r2_hidden(k2_struct_0(sK0),sK2) | ~spl4_47),
% 0.21/0.44    inference(avatar_component_clause,[],[f347])).
% 0.21/0.44  fof(f347,plain,(
% 0.21/0.44    spl4_47 <=> r2_hidden(k2_struct_0(sK0),sK2)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).
% 0.21/0.44  fof(f358,plain,(
% 0.21/0.44    ~spl4_2 | ~spl4_3 | ~spl4_18 | spl4_46),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f357])).
% 0.21/0.44  fof(f357,plain,(
% 0.21/0.44    $false | (~spl4_2 | ~spl4_3 | ~spl4_18 | spl4_46)),
% 0.21/0.44    inference(subsumption_resolution,[],[f356,f89])).
% 0.21/0.44  fof(f356,plain,(
% 0.21/0.44    ~v2_pre_topc(sK0) | (~spl4_3 | ~spl4_18 | spl4_46)),
% 0.21/0.44    inference(subsumption_resolution,[],[f355,f94])).
% 0.21/0.44  fof(f355,plain,(
% 0.21/0.44    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl4_18 | spl4_46)),
% 0.21/0.44    inference(resolution,[],[f345,f167])).
% 0.21/0.44  fof(f167,plain,(
% 0.21/0.44    ( ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl4_18),
% 0.21/0.44    inference(avatar_component_clause,[],[f166])).
% 0.21/0.44  fof(f166,plain,(
% 0.21/0.44    spl4_18 <=> ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.21/0.44  fof(f345,plain,(
% 0.21/0.44    ~v4_pre_topc(k2_struct_0(sK0),sK0) | spl4_46),
% 0.21/0.44    inference(avatar_component_clause,[],[f343])).
% 0.21/0.44  fof(f343,plain,(
% 0.21/0.44    spl4_46 <=> v4_pre_topc(k2_struct_0(sK0),sK0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).
% 0.21/0.44  fof(f354,plain,(
% 0.21/0.44    ~spl4_2 | ~spl4_3 | ~spl4_19 | spl4_45),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f353])).
% 0.21/0.44  fof(f353,plain,(
% 0.21/0.44    $false | (~spl4_2 | ~spl4_3 | ~spl4_19 | spl4_45)),
% 0.21/0.44    inference(subsumption_resolution,[],[f352,f89])).
% 0.21/0.44  fof(f352,plain,(
% 0.21/0.44    ~v2_pre_topc(sK0) | (~spl4_3 | ~spl4_19 | spl4_45)),
% 0.21/0.44    inference(subsumption_resolution,[],[f351,f94])).
% 0.21/0.44  fof(f351,plain,(
% 0.21/0.44    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl4_19 | spl4_45)),
% 0.21/0.44    inference(resolution,[],[f341,f171])).
% 0.21/0.44  fof(f171,plain,(
% 0.21/0.44    ( ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl4_19),
% 0.21/0.44    inference(avatar_component_clause,[],[f170])).
% 0.21/0.44  fof(f170,plain,(
% 0.21/0.44    spl4_19 <=> ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.21/0.44  fof(f341,plain,(
% 0.21/0.44    ~v3_pre_topc(k2_struct_0(sK0),sK0) | spl4_45),
% 0.21/0.44    inference(avatar_component_clause,[],[f339])).
% 0.21/0.44  fof(f339,plain,(
% 0.21/0.44    spl4_45 <=> v3_pre_topc(k2_struct_0(sK0),sK0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).
% 0.21/0.44  fof(f350,plain,(
% 0.21/0.44    ~spl4_45 | ~spl4_46 | spl4_47 | ~spl4_8 | ~spl4_30 | ~spl4_36),
% 0.21/0.44    inference(avatar_split_clause,[],[f326,f256,f222,f115,f347,f343,f339])).
% 0.21/0.44  fof(f115,plain,(
% 0.21/0.44    spl4_8 <=> ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.44  fof(f222,plain,(
% 0.21/0.44    spl4_30 <=> ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0))) | r2_hidden(X3,sK2) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 0.21/0.44  fof(f326,plain,(
% 0.21/0.44    r2_hidden(k2_struct_0(sK0),sK2) | ~v4_pre_topc(k2_struct_0(sK0),sK0) | ~v3_pre_topc(k2_struct_0(sK0),sK0) | (~spl4_8 | ~spl4_30 | ~spl4_36)),
% 0.21/0.44    inference(subsumption_resolution,[],[f325,f116])).
% 0.21/0.44  fof(f116,plain,(
% 0.21/0.44    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) ) | ~spl4_8),
% 0.21/0.44    inference(avatar_component_clause,[],[f115])).
% 0.21/0.44  fof(f325,plain,(
% 0.21/0.44    r2_hidden(k2_struct_0(sK0),sK2) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~v4_pre_topc(k2_struct_0(sK0),sK0) | ~v3_pre_topc(k2_struct_0(sK0),sK0) | (~spl4_30 | ~spl4_36)),
% 0.21/0.44    inference(resolution,[],[f223,f258])).
% 0.21/0.44  fof(f258,plain,(
% 0.21/0.44    r2_hidden(sK1,k2_struct_0(sK0)) | ~spl4_36),
% 0.21/0.44    inference(avatar_component_clause,[],[f256])).
% 0.21/0.44  fof(f223,plain,(
% 0.21/0.44    ( ! [X3] : (~r2_hidden(sK1,X3) | r2_hidden(X3,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0))) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) ) | ~spl4_30),
% 0.21/0.44    inference(avatar_component_clause,[],[f222])).
% 0.21/0.44  fof(f237,plain,(
% 0.21/0.44    spl4_32 | ~spl4_7 | ~spl4_11 | ~spl4_31),
% 0.21/0.44    inference(avatar_split_clause,[],[f233,f226,f129,f111,f235])).
% 0.21/0.44  fof(f111,plain,(
% 0.21/0.44    spl4_7 <=> ! [X0] : m1_subset_1(sK2,k1_zfmisc_1(X0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.44  fof(f129,plain,(
% 0.21/0.44    spl4_11 <=> ! [X0] : k3_subset_1(X0,sK2) = X0),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.44  fof(f226,plain,(
% 0.21/0.44    spl4_31 <=> ! [X1,X0,X2] : (r2_hidden(X2,k3_subset_1(X0,X1)) | r2_hidden(X2,X1) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | sK2 = X0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).
% 0.21/0.44  fof(f233,plain,(
% 0.21/0.44    ( ! [X2,X3] : (r2_hidden(X2,X3) | r2_hidden(X2,sK2) | ~m1_subset_1(X2,X3) | sK2 = X3) ) | (~spl4_7 | ~spl4_11 | ~spl4_31)),
% 0.21/0.44    inference(forward_demodulation,[],[f230,f130])).
% 0.21/0.44  fof(f130,plain,(
% 0.21/0.44    ( ! [X0] : (k3_subset_1(X0,sK2) = X0) ) | ~spl4_11),
% 0.21/0.44    inference(avatar_component_clause,[],[f129])).
% 0.21/0.44  fof(f230,plain,(
% 0.21/0.44    ( ! [X2,X3] : (r2_hidden(X2,sK2) | ~m1_subset_1(X2,X3) | r2_hidden(X2,k3_subset_1(X3,sK2)) | sK2 = X3) ) | (~spl4_7 | ~spl4_31)),
% 0.21/0.44    inference(resolution,[],[f227,f112])).
% 0.21/0.44  fof(f112,plain,(
% 0.21/0.44    ( ! [X0] : (m1_subset_1(sK2,k1_zfmisc_1(X0))) ) | ~spl4_7),
% 0.21/0.44    inference(avatar_component_clause,[],[f111])).
% 0.21/0.44  fof(f227,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | r2_hidden(X2,X1) | ~m1_subset_1(X2,X0) | r2_hidden(X2,k3_subset_1(X0,X1)) | sK2 = X0) ) | ~spl4_31),
% 0.21/0.44    inference(avatar_component_clause,[],[f226])).
% 0.21/0.44  fof(f228,plain,(
% 0.21/0.44    spl4_31),
% 0.21/0.44    inference(avatar_split_clause,[],[f79,f226])).
% 0.21/0.44  fof(f79,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (r2_hidden(X2,k3_subset_1(X0,X1)) | r2_hidden(X2,X1) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | sK2 = X0) )),
% 0.21/0.44    inference(definition_unfolding,[],[f63,f52])).
% 0.21/0.44  fof(f52,plain,(
% 0.21/0.44    k1_xboole_0 = sK2),
% 0.21/0.44    inference(cnf_transformation,[],[f40])).
% 0.21/0.44  fof(f40,plain,(
% 0.21/0.44    ((k1_xboole_0 = sK2 & ! [X3] : (((r2_hidden(X3,sK2) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(sK1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,sK2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f36,f39,f38,f37])).
% 0.21/0.44  fof(f37,plain,(
% 0.21/0.44    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f38,plain,(
% 0.21/0.44    ? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(sK1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f39,plain,(
% 0.21/0.44    ? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(sK1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => (k1_xboole_0 = sK2 & ! [X3] : (((r2_hidden(X3,sK2) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(sK1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,sK2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f36,plain,(
% 0.21/0.44    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.44    inference(flattening,[],[f35])).
% 0.21/0.44  fof(f35,plain,(
% 0.21/0.44    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | (~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0))) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.44    inference(nnf_transformation,[],[f20])).
% 0.21/0.44  fof(f20,plain,(
% 0.21/0.44    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : ((r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.44    inference(flattening,[],[f19])).
% 0.21/0.44  fof(f19,plain,(
% 0.21/0.44    ? [X0] : (? [X1] : (? [X2] : ((k1_xboole_0 = X2 & ! [X3] : ((r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.44    inference(ennf_transformation,[],[f18])).
% 0.21/0.44  fof(f18,negated_conjecture,(
% 0.21/0.44    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X2 & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))))))))),
% 0.21/0.44    inference(negated_conjecture,[],[f17])).
% 0.21/0.44  fof(f17,conjecture,(
% 0.21/0.44    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X2 & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))))))))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_connsp_2)).
% 0.21/0.44  fof(f63,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (r2_hidden(X2,k3_subset_1(X0,X1)) | r2_hidden(X2,X1) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k1_xboole_0 = X0) )),
% 0.21/0.44    inference(cnf_transformation,[],[f25])).
% 0.21/0.44  fof(f25,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,k3_subset_1(X0,X1)) | r2_hidden(X2,X1) | ~m1_subset_1(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | k1_xboole_0 = X0)),
% 0.21/0.44    inference(flattening,[],[f24])).
% 0.21/0.44  fof(f24,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k3_subset_1(X0,X1)) | r2_hidden(X2,X1)) | ~m1_subset_1(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | k1_xboole_0 = X0)),
% 0.21/0.44    inference(ennf_transformation,[],[f8])).
% 0.21/0.44  fof(f8,axiom,(
% 0.21/0.44    ! [X0] : (k1_xboole_0 != X0 => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,X0) => (~r2_hidden(X2,X1) => r2_hidden(X2,k3_subset_1(X0,X1))))))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_subset_1)).
% 0.21/0.44  fof(f224,plain,(
% 0.21/0.44    spl4_30 | ~spl4_10 | ~spl4_14),
% 0.21/0.44    inference(avatar_split_clause,[],[f150,f142,f124,f222])).
% 0.21/0.44  fof(f124,plain,(
% 0.21/0.44    spl4_10 <=> l1_struct_0(sK0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.44  fof(f142,plain,(
% 0.21/0.44    spl4_14 <=> ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.21/0.44  fof(f150,plain,(
% 0.21/0.44    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0))) | r2_hidden(X3,sK2) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) ) | (~spl4_10 | ~spl4_14)),
% 0.21/0.44    inference(backward_demodulation,[],[f51,f145])).
% 0.21/0.44  fof(f145,plain,(
% 0.21/0.44    u1_struct_0(sK0) = k2_struct_0(sK0) | (~spl4_10 | ~spl4_14)),
% 0.21/0.44    inference(resolution,[],[f143,f126])).
% 0.21/0.44  fof(f126,plain,(
% 0.21/0.44    l1_struct_0(sK0) | ~spl4_10),
% 0.21/0.44    inference(avatar_component_clause,[],[f124])).
% 0.21/0.44  fof(f143,plain,(
% 0.21/0.44    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) ) | ~spl4_14),
% 0.21/0.44    inference(avatar_component_clause,[],[f142])).
% 0.21/0.44  fof(f51,plain,(
% 0.21/0.44    ( ! [X3] : (r2_hidden(X3,sK2) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f40])).
% 0.21/0.44  fof(f220,plain,(
% 0.21/0.44    spl4_29 | spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_16 | ~spl4_28),
% 0.21/0.44    inference(avatar_split_clause,[],[f215,f209,f157,f92,f87,f82,f217])).
% 0.21/0.44  fof(f157,plain,(
% 0.21/0.44    spl4_16 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.21/0.44  fof(f209,plain,(
% 0.21/0.44    spl4_28 <=> ! [X0] : (m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 0.21/0.44  fof(f215,plain,(
% 0.21/0.44    m1_subset_1(sK3(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_16 | ~spl4_28)),
% 0.21/0.44    inference(subsumption_resolution,[],[f214,f84])).
% 0.21/0.44  fof(f214,plain,(
% 0.21/0.44    m1_subset_1(sK3(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | v2_struct_0(sK0) | (~spl4_2 | ~spl4_3 | ~spl4_16 | ~spl4_28)),
% 0.21/0.44    inference(subsumption_resolution,[],[f213,f89])).
% 0.21/0.44  fof(f213,plain,(
% 0.21/0.44    m1_subset_1(sK3(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl4_3 | ~spl4_16 | ~spl4_28)),
% 0.21/0.44    inference(subsumption_resolution,[],[f212,f94])).
% 0.21/0.44  fof(f212,plain,(
% 0.21/0.44    m1_subset_1(sK3(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl4_16 | ~spl4_28)),
% 0.21/0.44    inference(superposition,[],[f210,f159])).
% 0.21/0.44  fof(f159,plain,(
% 0.21/0.44    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl4_16),
% 0.21/0.44    inference(avatar_component_clause,[],[f157])).
% 0.21/0.44  fof(f210,plain,(
% 0.21/0.44    ( ! [X0] : (m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) ) | ~spl4_28),
% 0.21/0.44    inference(avatar_component_clause,[],[f209])).
% 0.21/0.44  fof(f211,plain,(
% 0.21/0.44    spl4_28),
% 0.21/0.44    inference(avatar_split_clause,[],[f64,f209])).
% 0.21/0.44  fof(f64,plain,(
% 0.21/0.44    ( ! [X0] : (m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f42])).
% 0.21/0.44  fof(f42,plain,(
% 0.21/0.44    ! [X0] : ((v4_pre_topc(sK3(X0),X0) & v3_pre_topc(sK3(X0),X0) & ~v1_xboole_0(sK3(X0)) & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f41])).
% 0.21/0.44  fof(f41,plain,(
% 0.21/0.44    ! [X0] : (? [X1] : (v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (v4_pre_topc(sK3(X0),X0) & v3_pre_topc(sK3(X0),X0) & ~v1_xboole_0(sK3(X0)) & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f27,plain,(
% 0.21/0.44    ! [X0] : (? [X1] : (v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.44    inference(flattening,[],[f26])).
% 0.21/0.44  fof(f26,plain,(
% 0.21/0.44    ! [X0] : (? [X1] : (v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.44    inference(ennf_transformation,[],[f16])).
% 0.21/0.44  fof(f16,axiom,(
% 0.21/0.44    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_tops_1)).
% 0.21/0.44  fof(f183,plain,(
% 0.21/0.44    spl4_21),
% 0.21/0.44    inference(avatar_split_clause,[],[f65,f181])).
% 0.21/0.44  fof(f65,plain,(
% 0.21/0.44    ( ! [X0] : (~v1_xboole_0(sK3(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f42])).
% 0.21/0.44  fof(f177,plain,(
% 0.21/0.44    spl4_20 | ~spl4_4 | ~spl4_17),
% 0.21/0.44    inference(avatar_split_clause,[],[f173,f162,f97,f175])).
% 0.21/0.44  fof(f97,plain,(
% 0.21/0.44    spl4_4 <=> v1_xboole_0(sK2)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.44  fof(f162,plain,(
% 0.21/0.44    spl4_17 <=> ! [X1,X0] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.21/0.44  fof(f173,plain,(
% 0.21/0.44    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK2)) | v1_xboole_0(X0)) ) | (~spl4_4 | ~spl4_17)),
% 0.21/0.44    inference(resolution,[],[f163,f99])).
% 0.21/0.44  fof(f99,plain,(
% 0.21/0.44    v1_xboole_0(sK2) | ~spl4_4),
% 0.21/0.44    inference(avatar_component_clause,[],[f97])).
% 0.21/0.44  fof(f163,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1)) ) | ~spl4_17),
% 0.21/0.44    inference(avatar_component_clause,[],[f162])).
% 0.21/0.44  fof(f172,plain,(
% 0.21/0.44    spl4_19),
% 0.21/0.44    inference(avatar_split_clause,[],[f69,f170])).
% 0.21/0.44  fof(f69,plain,(
% 0.21/0.44    ( ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f31])).
% 0.21/0.44  fof(f31,plain,(
% 0.21/0.44    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.44    inference(flattening,[],[f30])).
% 0.21/0.44  fof(f30,plain,(
% 0.21/0.44    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.44    inference(ennf_transformation,[],[f15])).
% 0.21/0.44  fof(f15,axiom,(
% 0.21/0.44    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).
% 0.21/0.44  fof(f168,plain,(
% 0.21/0.44    spl4_18),
% 0.21/0.44    inference(avatar_split_clause,[],[f68,f166])).
% 0.21/0.44  fof(f68,plain,(
% 0.21/0.44    ( ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f29])).
% 0.21/0.44  fof(f29,plain,(
% 0.21/0.44    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.44    inference(flattening,[],[f28])).
% 0.21/0.44  fof(f28,plain,(
% 0.21/0.44    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.44    inference(ennf_transformation,[],[f14])).
% 0.21/0.44  fof(f14,axiom,(
% 0.21/0.44    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_struct_0(X0),X0))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_pre_topc)).
% 0.21/0.44  fof(f164,plain,(
% 0.21/0.44    spl4_17),
% 0.21/0.44    inference(avatar_split_clause,[],[f62,f162])).
% 0.21/0.44  fof(f62,plain,(
% 0.21/0.44    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f23])).
% 0.21/0.44  fof(f23,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f9])).
% 0.21/0.44  fof(f9,axiom,(
% 0.21/0.44    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.21/0.44  fof(f160,plain,(
% 0.21/0.44    spl4_16 | ~spl4_10 | ~spl4_14),
% 0.21/0.44    inference(avatar_split_clause,[],[f145,f142,f124,f157])).
% 0.21/0.44  fof(f155,plain,(
% 0.21/0.44    spl4_15 | ~spl4_6 | ~spl4_10 | ~spl4_14),
% 0.21/0.44    inference(avatar_split_clause,[],[f146,f142,f124,f106,f152])).
% 0.21/0.44  fof(f106,plain,(
% 0.21/0.44    spl4_6 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.44  fof(f146,plain,(
% 0.21/0.44    m1_subset_1(sK1,k2_struct_0(sK0)) | (~spl4_6 | ~spl4_10 | ~spl4_14)),
% 0.21/0.44    inference(backward_demodulation,[],[f108,f145])).
% 0.21/0.44  fof(f108,plain,(
% 0.21/0.44    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl4_6),
% 0.21/0.44    inference(avatar_component_clause,[],[f106])).
% 0.21/0.44  fof(f144,plain,(
% 0.21/0.44    spl4_14),
% 0.21/0.44    inference(avatar_split_clause,[],[f60,f142])).
% 0.21/0.44  fof(f60,plain,(
% 0.21/0.44    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f21])).
% 0.21/0.44  fof(f21,plain,(
% 0.21/0.44    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f12])).
% 0.21/0.44  fof(f12,axiom,(
% 0.21/0.44    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.44  fof(f140,plain,(
% 0.21/0.44    spl4_13),
% 0.21/0.44    inference(avatar_split_clause,[],[f70,f138])).
% 0.21/0.44  fof(f70,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f32])).
% 0.21/0.44  fof(f32,plain,(
% 0.21/0.44    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f11])).
% 0.21/0.44  fof(f11,axiom,(
% 0.21/0.44    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.21/0.44  fof(f131,plain,(
% 0.21/0.44    spl4_11),
% 0.21/0.44    inference(avatar_split_clause,[],[f76,f129])).
% 0.21/0.44  fof(f76,plain,(
% 0.21/0.44    ( ! [X0] : (k3_subset_1(X0,sK2) = X0) )),
% 0.21/0.44    inference(definition_unfolding,[],[f56,f73])).
% 0.21/0.44  fof(f73,plain,(
% 0.21/0.44    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,sK2)) )),
% 0.21/0.44    inference(definition_unfolding,[],[f59,f72])).
% 0.21/0.44  fof(f72,plain,(
% 0.21/0.44    ( ! [X0] : (k1_subset_1(X0) = sK2) )),
% 0.21/0.44    inference(definition_unfolding,[],[f55,f52])).
% 0.21/0.44  fof(f55,plain,(
% 0.21/0.44    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f3])).
% 0.21/0.44  fof(f3,axiom,(
% 0.21/0.44    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).
% 0.21/0.44  fof(f59,plain,(
% 0.21/0.44    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f6])).
% 0.21/0.44  fof(f6,axiom,(
% 0.21/0.44    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).
% 0.21/0.44  fof(f56,plain,(
% 0.21/0.44    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.21/0.44    inference(cnf_transformation,[],[f4])).
% 0.21/0.44  fof(f4,axiom,(
% 0.21/0.44    ! [X0] : k2_subset_1(X0) = X0),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.21/0.44  fof(f127,plain,(
% 0.21/0.44    spl4_10 | ~spl4_3 | ~spl4_9),
% 0.21/0.44    inference(avatar_split_clause,[],[f122,f119,f92,f124])).
% 0.21/0.44  fof(f119,plain,(
% 0.21/0.44    spl4_9 <=> ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.44  fof(f122,plain,(
% 0.21/0.44    l1_struct_0(sK0) | (~spl4_3 | ~spl4_9)),
% 0.21/0.44    inference(resolution,[],[f120,f94])).
% 0.21/0.44  fof(f120,plain,(
% 0.21/0.44    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) ) | ~spl4_9),
% 0.21/0.44    inference(avatar_component_clause,[],[f119])).
% 0.21/0.44  fof(f121,plain,(
% 0.21/0.44    spl4_9),
% 0.21/0.44    inference(avatar_split_clause,[],[f61,f119])).
% 0.21/0.44  fof(f61,plain,(
% 0.21/0.44    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f22])).
% 0.21/0.44  fof(f22,plain,(
% 0.21/0.44    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f13])).
% 0.21/0.44  fof(f13,axiom,(
% 0.21/0.44    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.44  fof(f117,plain,(
% 0.21/0.44    spl4_8),
% 0.21/0.44    inference(avatar_split_clause,[],[f80,f115])).
% 0.21/0.44  fof(f80,plain,(
% 0.21/0.44    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.21/0.44    inference(forward_demodulation,[],[f78,f76])).
% 0.21/0.44  fof(f78,plain,(
% 0.21/0.44    ( ! [X0] : (m1_subset_1(k3_subset_1(X0,sK2),k1_zfmisc_1(X0))) )),
% 0.21/0.44    inference(definition_unfolding,[],[f58,f73])).
% 0.21/0.44  fof(f58,plain,(
% 0.21/0.44    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f5])).
% 0.21/0.44  fof(f5,axiom,(
% 0.21/0.44    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.21/0.44  fof(f113,plain,(
% 0.21/0.44    spl4_7),
% 0.21/0.44    inference(avatar_split_clause,[],[f77,f111])).
% 0.21/0.44  fof(f77,plain,(
% 0.21/0.44    ( ! [X0] : (m1_subset_1(sK2,k1_zfmisc_1(X0))) )),
% 0.21/0.44    inference(definition_unfolding,[],[f57,f52])).
% 0.21/0.44  fof(f57,plain,(
% 0.21/0.44    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f7])).
% 0.21/0.44  fof(f7,axiom,(
% 0.21/0.44    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.44  fof(f109,plain,(
% 0.21/0.44    spl4_6),
% 0.21/0.44    inference(avatar_split_clause,[],[f46,f106])).
% 0.21/0.44  fof(f46,plain,(
% 0.21/0.44    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.44    inference(cnf_transformation,[],[f40])).
% 0.21/0.44  fof(f104,plain,(
% 0.21/0.44    spl4_5),
% 0.21/0.44    inference(avatar_split_clause,[],[f75,f102])).
% 0.21/0.44  fof(f75,plain,(
% 0.21/0.44    ( ! [X0] : (r1_tarski(sK2,X0)) )),
% 0.21/0.44    inference(definition_unfolding,[],[f54,f52])).
% 0.21/0.44  fof(f54,plain,(
% 0.21/0.44    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f2])).
% 0.21/0.44  fof(f2,axiom,(
% 0.21/0.44    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.44  fof(f100,plain,(
% 0.21/0.44    spl4_4),
% 0.21/0.44    inference(avatar_split_clause,[],[f74,f97])).
% 0.21/0.44  fof(f74,plain,(
% 0.21/0.44    v1_xboole_0(sK2)),
% 0.21/0.44    inference(definition_unfolding,[],[f53,f52])).
% 0.21/0.44  fof(f53,plain,(
% 0.21/0.44    v1_xboole_0(k1_xboole_0)),
% 0.21/0.44    inference(cnf_transformation,[],[f1])).
% 0.21/0.44  fof(f1,axiom,(
% 0.21/0.44    v1_xboole_0(k1_xboole_0)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.44  fof(f95,plain,(
% 0.21/0.44    spl4_3),
% 0.21/0.44    inference(avatar_split_clause,[],[f45,f92])).
% 0.21/0.44  fof(f45,plain,(
% 0.21/0.44    l1_pre_topc(sK0)),
% 0.21/0.44    inference(cnf_transformation,[],[f40])).
% 0.21/0.44  fof(f90,plain,(
% 0.21/0.44    spl4_2),
% 0.21/0.44    inference(avatar_split_clause,[],[f44,f87])).
% 0.21/0.44  fof(f44,plain,(
% 0.21/0.44    v2_pre_topc(sK0)),
% 0.21/0.44    inference(cnf_transformation,[],[f40])).
% 0.21/0.44  fof(f85,plain,(
% 0.21/0.44    ~spl4_1),
% 0.21/0.44    inference(avatar_split_clause,[],[f43,f82])).
% 0.21/0.44  fof(f43,plain,(
% 0.21/0.44    ~v2_struct_0(sK0)),
% 0.21/0.44    inference(cnf_transformation,[],[f40])).
% 0.21/0.44  % SZS output end Proof for theBenchmark
% 0.21/0.44  % (29902)------------------------------
% 0.21/0.44  % (29902)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (29902)Termination reason: Refutation
% 0.21/0.44  
% 0.21/0.44  % (29902)Memory used [KB]: 6396
% 0.21/0.44  % (29902)Time elapsed: 0.015 s
% 0.21/0.44  % (29902)------------------------------
% 0.21/0.44  % (29902)------------------------------
% 0.21/0.44  % (29894)Success in time 0.082 s
%------------------------------------------------------------------------------
