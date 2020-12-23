%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1226+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:13 EST 2020

% Result     : Theorem 0.96s
% Output     : Refutation 0.96s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 111 expanded)
%              Number of leaves         :   14 (  49 expanded)
%              Depth                    :    7
%              Number of atoms          :  171 ( 597 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2297,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f2171,f2175,f2179,f2183,f2187,f2191,f2195,f2230,f2295])).

fof(f2295,plain,
    ( ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | spl9_11 ),
    inference(avatar_contradiction_clause,[],[f2293])).

fof(f2293,plain,
    ( $false
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | spl9_11 ),
    inference(unit_resulting_resolution,[],[f2194,f2190,f2174,f2178,f2229,f2186,f2182,f2153])).

fof(f2153,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v4_pre_topc(k3_xboole_0(X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f2110])).

fof(f2110,plain,(
    ! [X0,X1,X2] :
      ( v4_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f2109])).

fof(f2109,plain,(
    ! [X0,X1,X2] :
      ( v4_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2087])).

fof(f2087,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        & v4_pre_topc(X2,X0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v4_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k3_xboole_0(X1,X2),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_tops_1)).

fof(f2182,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f2181])).

fof(f2181,plain,
    ( spl9_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f2186,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f2185])).

fof(f2185,plain,
    ( spl9_5
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f2229,plain,
    ( ~ v4_pre_topc(k3_xboole_0(sK1,sK2),sK0)
    | spl9_11 ),
    inference(avatar_component_clause,[],[f2228])).

fof(f2228,plain,
    ( spl9_11
  <=> v4_pre_topc(k3_xboole_0(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f2178,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f2177])).

fof(f2177,plain,
    ( spl9_3
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f2174,plain,
    ( v4_pre_topc(sK2,sK0)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f2173])).

fof(f2173,plain,
    ( spl9_2
  <=> v4_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f2190,plain,
    ( l1_pre_topc(sK0)
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f2189])).

fof(f2189,plain,
    ( spl9_6
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f2194,plain,
    ( v2_pre_topc(sK0)
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f2193])).

fof(f2193,plain,
    ( spl9_7
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f2230,plain,
    ( ~ spl9_11
    | spl9_1
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f2223,f2181,f2169,f2228])).

fof(f2169,plain,
    ( spl9_1
  <=> v4_pre_topc(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f2223,plain,
    ( ~ v4_pre_topc(k3_xboole_0(sK1,sK2),sK0)
    | spl9_1
    | ~ spl9_4 ),
    inference(backward_demodulation,[],[f2170,f2218])).

fof(f2218,plain,
    ( ! [X0] : k3_xboole_0(X0,sK2) = k9_subset_1(u1_struct_0(sK0),X0,sK2)
    | ~ spl9_4 ),
    inference(resolution,[],[f2145,f2182])).

% (6415)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_88 on theBenchmark
fof(f2145,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f2103])).

fof(f2103,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f496])).

fof(f496,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f2170,plain,
    ( ~ v4_pre_topc(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | spl9_1 ),
    inference(avatar_component_clause,[],[f2169])).

fof(f2195,plain,(
    spl9_7 ),
    inference(avatar_split_clause,[],[f2137,f2193])).

fof(f2137,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f2121])).

fof(f2121,plain,
    ( ~ v4_pre_topc(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    & v4_pre_topc(sK2,sK0)
    & v4_pre_topc(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f2101,f2120,f2119,f2118])).

fof(f2118,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
                & v4_pre_topc(X2,X0)
                & v4_pre_topc(X1,X0)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v4_pre_topc(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0)
              & v4_pre_topc(X2,sK0)
              & v4_pre_topc(X1,sK0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f2119,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ v4_pre_topc(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0)
            & v4_pre_topc(X2,sK0)
            & v4_pre_topc(X1,sK0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ~ v4_pre_topc(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0)
          & v4_pre_topc(X2,sK0)
          & v4_pre_topc(sK1,sK0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f2120,plain,
    ( ? [X2] :
        ( ~ v4_pre_topc(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0)
        & v4_pre_topc(X2,sK0)
        & v4_pre_topc(sK1,sK0)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ v4_pre_topc(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
      & v4_pre_topc(sK2,sK0)
      & v4_pre_topc(sK1,sK0)
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f2101,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v4_pre_topc(X2,X0)
              & v4_pre_topc(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f2100])).

fof(f2100,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v4_pre_topc(X2,X0)
              & v4_pre_topc(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2096])).

fof(f2096,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v4_pre_topc(X2,X0)
                    & v4_pre_topc(X1,X0) )
                 => v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f2095])).

fof(f2095,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v4_pre_topc(X2,X0)
                  & v4_pre_topc(X1,X0) )
               => v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tops_1)).

fof(f2191,plain,(
    spl9_6 ),
    inference(avatar_split_clause,[],[f2138,f2189])).

fof(f2138,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f2121])).

fof(f2187,plain,(
    spl9_5 ),
    inference(avatar_split_clause,[],[f2139,f2185])).

fof(f2139,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f2121])).

fof(f2183,plain,(
    spl9_4 ),
    inference(avatar_split_clause,[],[f2140,f2181])).

fof(f2140,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f2121])).

fof(f2179,plain,(
    spl9_3 ),
    inference(avatar_split_clause,[],[f2141,f2177])).

fof(f2141,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f2121])).

fof(f2175,plain,(
    spl9_2 ),
    inference(avatar_split_clause,[],[f2142,f2173])).

fof(f2142,plain,(
    v4_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f2121])).

fof(f2171,plain,(
    ~ spl9_1 ),
    inference(avatar_split_clause,[],[f2143,f2169])).

fof(f2143,plain,(
    ~ v4_pre_topc(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f2121])).
%------------------------------------------------------------------------------
