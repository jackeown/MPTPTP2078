%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1227+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:13 EST 2020

% Result     : Theorem 1.12s
% Output     : Refutation 1.12s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 121 expanded)
%              Number of leaves         :   15 (  54 expanded)
%              Depth                    :    7
%              Number of atoms          :  188 ( 624 expanded)
%              Number of equality atoms :    8 (  10 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2368,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f2187,f2191,f2195,f2199,f2203,f2207,f2211,f2263,f2287,f2366])).

fof(f2366,plain,
    ( ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | spl9_17 ),
    inference(avatar_contradiction_clause,[],[f2364])).

fof(f2364,plain,
    ( $false
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | spl9_17 ),
    inference(unit_resulting_resolution,[],[f2210,f2206,f2190,f2194,f2286,f2202,f2198,f2167])).

fof(f2167,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v4_pre_topc(k2_xboole_0(X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f2120])).

fof(f2120,plain,(
    ! [X0,X1,X2] :
      ( v4_pre_topc(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f2119])).

fof(f2119,plain,(
    ! [X0,X1,X2] :
      ( v4_pre_topc(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2088])).

fof(f2088,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        & v4_pre_topc(X2,X0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v4_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_xboole_0(X1,X2),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_tops_1)).

fof(f2198,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f2197])).

fof(f2197,plain,
    ( spl9_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f2202,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f2201])).

fof(f2201,plain,
    ( spl9_5
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f2286,plain,
    ( ~ v4_pre_topc(k2_xboole_0(sK1,sK2),sK0)
    | spl9_17 ),
    inference(avatar_component_clause,[],[f2285])).

fof(f2285,plain,
    ( spl9_17
  <=> v4_pre_topc(k2_xboole_0(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).

fof(f2194,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f2193])).

fof(f2193,plain,
    ( spl9_3
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f2190,plain,
    ( v4_pre_topc(sK2,sK0)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f2189])).

fof(f2189,plain,
    ( spl9_2
  <=> v4_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f2206,plain,
    ( l1_pre_topc(sK0)
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f2205])).

fof(f2205,plain,
    ( spl9_6
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f2210,plain,
    ( v2_pre_topc(sK0)
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f2209])).

fof(f2209,plain,
    ( spl9_7
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f2287,plain,
    ( ~ spl9_17
    | spl9_1
    | ~ spl9_14 ),
    inference(avatar_split_clause,[],[f2282,f2261,f2185,f2285])).

fof(f2185,plain,
    ( spl9_1
  <=> v4_pre_topc(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f2261,plain,
    ( spl9_14
  <=> k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f2282,plain,
    ( ~ v4_pre_topc(k2_xboole_0(sK1,sK2),sK0)
    | spl9_1
    | ~ spl9_14 ),
    inference(backward_demodulation,[],[f2186,f2262])).

fof(f2262,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2)
    | ~ spl9_14 ),
    inference(avatar_component_clause,[],[f2261])).

fof(f2186,plain,
    ( ~ v4_pre_topc(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | spl9_1 ),
    inference(avatar_component_clause,[],[f2185])).

fof(f2263,plain,
    ( spl9_14
    | ~ spl9_4
    | ~ spl9_5 ),
    inference(avatar_split_clause,[],[f2251,f2201,f2197,f2261])).

fof(f2251,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2)
    | ~ spl9_4
    | ~ spl9_5 ),
    inference(resolution,[],[f2245,f2202])).

fof(f2245,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_xboole_0(X0,sK2) = k4_subset_1(u1_struct_0(sK0),X0,sK2) )
    | ~ spl9_4 ),
    inference(resolution,[],[f2157,f2198])).

fof(f2157,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f2108])).

fof(f2108,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f2107])).

fof(f2107,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f491])).

fof(f491,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f2211,plain,(
    spl9_7 ),
    inference(avatar_split_clause,[],[f2149,f2209])).

fof(f2149,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f2133])).

fof(f2133,plain,
    ( ~ v4_pre_topc(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    & v4_pre_topc(sK2,sK0)
    & v4_pre_topc(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f2104,f2132,f2131,f2130])).

fof(f2130,plain,
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

fof(f2131,plain,
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

fof(f2132,plain,
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

fof(f2104,plain,(
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
    inference(flattening,[],[f2103])).

fof(f2103,plain,(
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
    inference(ennf_transformation,[],[f2098])).

fof(f2098,negated_conjecture,(
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
    inference(negated_conjecture,[],[f2097])).

fof(f2097,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tops_1)).

fof(f2207,plain,(
    spl9_6 ),
    inference(avatar_split_clause,[],[f2150,f2205])).

fof(f2150,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f2133])).

fof(f2203,plain,(
    spl9_5 ),
    inference(avatar_split_clause,[],[f2151,f2201])).

fof(f2151,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f2133])).

fof(f2199,plain,(
    spl9_4 ),
    inference(avatar_split_clause,[],[f2152,f2197])).

fof(f2152,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f2133])).

fof(f2195,plain,(
    spl9_3 ),
    inference(avatar_split_clause,[],[f2153,f2193])).

fof(f2153,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f2133])).

fof(f2191,plain,(
    spl9_2 ),
    inference(avatar_split_clause,[],[f2154,f2189])).

fof(f2154,plain,(
    v4_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f2133])).

fof(f2187,plain,(
    ~ spl9_1 ),
    inference(avatar_split_clause,[],[f2155,f2185])).

fof(f2155,plain,(
    ~ v4_pre_topc(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f2133])).
%------------------------------------------------------------------------------
