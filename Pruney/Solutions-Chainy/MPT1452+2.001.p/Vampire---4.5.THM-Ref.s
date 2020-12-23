%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:32 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  277 (1112 expanded)
%              Number of leaves         :   18 ( 282 expanded)
%              Depth                    :   25
%              Number of atoms          : 1666 (10707 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2254,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f88,f93,f98,f103,f118,f175,f307,f515,f551,f561,f769,f770,f779,f780,f964,f970,f1059,f1147,f1824,f1886,f1945,f1991,f2011,f2240])).

fof(f2240,plain,
    ( spl2_3
    | ~ spl2_4
    | ~ spl2_23 ),
    inference(avatar_contradiction_clause,[],[f2239])).

fof(f2239,plain,
    ( $false
    | spl2_3
    | ~ spl2_4
    | ~ spl2_23 ),
    inference(subsumption_resolution,[],[f2238,f55])).

fof(f55,plain,(
    l3_lattices(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( l3_lattices(X1)
              & v17_lattices(X1)
              & v10_lattices(X1)
              & ~ v2_struct_0(X1)
              & l3_lattices(X0)
              & v17_lattices(X0)
              & v10_lattices(X0)
              & ~ v2_struct_0(X0) )
          <~> ( l3_lattices(k7_filter_1(X0,X1))
              & v17_lattices(k7_filter_1(X0,X1))
              & v10_lattices(k7_filter_1(X0,X1))
              & ~ v2_struct_0(k7_filter_1(X0,X1)) ) )
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
          ( ( ( l3_lattices(X1)
              & v17_lattices(X1)
              & v10_lattices(X1)
              & ~ v2_struct_0(X1)
              & l3_lattices(X0)
              & v17_lattices(X0)
              & v10_lattices(X0)
              & ~ v2_struct_0(X0) )
          <~> ( l3_lattices(k7_filter_1(X0,X1))
              & v17_lattices(k7_filter_1(X0,X1))
              & v10_lattices(k7_filter_1(X0,X1))
              & ~ v2_struct_0(k7_filter_1(X0,X1)) ) )
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
           => ( ( l3_lattices(X1)
                & v17_lattices(X1)
                & v10_lattices(X1)
                & ~ v2_struct_0(X1)
                & l3_lattices(X0)
                & v17_lattices(X0)
                & v10_lattices(X0)
                & ~ v2_struct_0(X0) )
            <=> ( l3_lattices(k7_filter_1(X0,X1))
                & v17_lattices(k7_filter_1(X0,X1))
                & v10_lattices(k7_filter_1(X0,X1))
                & ~ v2_struct_0(k7_filter_1(X0,X1)) ) ) ) ) ),
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
         => ( ( l3_lattices(X1)
              & v17_lattices(X1)
              & v10_lattices(X1)
              & ~ v2_struct_0(X1)
              & l3_lattices(X0)
              & v17_lattices(X0)
              & v10_lattices(X0)
              & ~ v2_struct_0(X0) )
          <=> ( l3_lattices(k7_filter_1(X0,X1))
              & v17_lattices(k7_filter_1(X0,X1))
              & v10_lattices(k7_filter_1(X0,X1))
              & ~ v2_struct_0(k7_filter_1(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_filter_1)).

fof(f2238,plain,
    ( ~ l3_lattices(sK1)
    | spl2_3
    | ~ spl2_4
    | ~ spl2_23 ),
    inference(subsumption_resolution,[],[f2237,f513])).

fof(f513,plain,
    ( v11_lattices(sK1)
    | ~ spl2_23 ),
    inference(avatar_component_clause,[],[f512])).

fof(f512,plain,
    ( spl2_23
  <=> v11_lattices(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f2237,plain,
    ( ~ v11_lattices(sK1)
    | ~ l3_lattices(sK1)
    | spl2_3
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f2236,f91])).

fof(f91,plain,
    ( ~ v10_lattices(k7_filter_1(sK0,sK1))
    | spl2_3 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl2_3
  <=> v10_lattices(k7_filter_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f2236,plain,
    ( v10_lattices(k7_filter_1(sK0,sK1))
    | ~ v11_lattices(sK1)
    | ~ l3_lattices(sK1)
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f2228,f53])).

fof(f53,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f2228,plain,
    ( v2_struct_0(sK1)
    | v10_lattices(k7_filter_1(sK0,sK1))
    | ~ v11_lattices(sK1)
    | ~ l3_lattices(sK1)
    | ~ spl2_4 ),
    inference(resolution,[],[f2227,f54])).

fof(f54,plain,(
    v10_lattices(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f2227,plain,
    ( ! [X1] :
        ( ~ v10_lattices(X1)
        | v2_struct_0(X1)
        | v10_lattices(k7_filter_1(sK0,X1))
        | ~ v11_lattices(X1)
        | ~ l3_lattices(X1) )
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f438,f2010])).

fof(f2010,plain,
    ( v11_lattices(sK0)
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f2009,f58])).

fof(f58,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f2009,plain,
    ( ~ l3_lattices(sK0)
    | v11_lattices(sK0)
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f2006,f56])).

fof(f56,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f2006,plain,
    ( v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | v11_lattices(sK0)
    | ~ spl2_4 ),
    inference(resolution,[],[f97,f60])).

fof(f60,plain,(
    ! [X0] :
      ( ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v11_lattices(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( v16_lattices(X0)
        & v15_lattices(X0)
        & v11_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ( v16_lattices(X0)
        & v15_lattices(X0)
        & v11_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v17_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v16_lattices(X0)
          & v15_lattices(X0)
          & v11_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_lattices)).

fof(f97,plain,
    ( v17_lattices(sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl2_4
  <=> v17_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f438,plain,(
    ! [X1] :
      ( v10_lattices(k7_filter_1(sK0,X1))
      | ~ v11_lattices(sK0)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ v11_lattices(X1)
      | ~ l3_lattices(X1) ) ),
    inference(subsumption_resolution,[],[f212,f58])).

fof(f212,plain,(
    ! [X1] :
      ( v10_lattices(k7_filter_1(sK0,X1))
      | ~ v11_lattices(sK0)
      | ~ l3_lattices(sK0)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ v11_lattices(X1)
      | ~ l3_lattices(X1) ) ),
    inference(subsumption_resolution,[],[f207,f56])).

fof(f207,plain,(
    ! [X1] :
      ( v2_struct_0(sK0)
      | v10_lattices(k7_filter_1(sK0,X1))
      | ~ v11_lattices(sK0)
      | ~ l3_lattices(sK0)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ v11_lattices(X1)
      | ~ l3_lattices(X1) ) ),
    inference(resolution,[],[f75,f57])).

fof(f57,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | v10_lattices(k7_filter_1(X0,X1))
      | ~ v11_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ v11_lattices(X1)
      | ~ l3_lattices(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( l3_lattices(X1)
              & v11_lattices(X1)
              & v10_lattices(X1)
              & ~ v2_struct_0(X1)
              & l3_lattices(X0)
              & v11_lattices(X0)
              & v10_lattices(X0)
              & ~ v2_struct_0(X0) )
          <=> ( l3_lattices(k7_filter_1(X0,X1))
              & v11_lattices(k7_filter_1(X0,X1))
              & v10_lattices(k7_filter_1(X0,X1))
              & ~ v2_struct_0(k7_filter_1(X0,X1)) ) )
          | ~ l3_lattices(X1)
          | ~ v10_lattices(X1)
          | v2_struct_0(X1) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( l3_lattices(X1)
              & v11_lattices(X1)
              & v10_lattices(X1)
              & ~ v2_struct_0(X1)
              & l3_lattices(X0)
              & v11_lattices(X0)
              & v10_lattices(X0)
              & ~ v2_struct_0(X0) )
          <=> ( l3_lattices(k7_filter_1(X0,X1))
              & v11_lattices(k7_filter_1(X0,X1))
              & v10_lattices(k7_filter_1(X0,X1))
              & ~ v2_struct_0(k7_filter_1(X0,X1)) ) )
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
         => ( ( l3_lattices(X1)
              & v11_lattices(X1)
              & v10_lattices(X1)
              & ~ v2_struct_0(X1)
              & l3_lattices(X0)
              & v11_lattices(X0)
              & v10_lattices(X0)
              & ~ v2_struct_0(X0) )
          <=> ( l3_lattices(k7_filter_1(X0,X1))
              & v11_lattices(k7_filter_1(X0,X1))
              & v10_lattices(k7_filter_1(X0,X1))
              & ~ v2_struct_0(k7_filter_1(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_filter_1)).

fof(f2011,plain,
    ( spl2_20
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f2008,f95,f444])).

fof(f444,plain,
    ( spl2_20
  <=> v15_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f2008,plain,
    ( v15_lattices(sK0)
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f2007,f58])).

fof(f2007,plain,
    ( ~ l3_lattices(sK0)
    | v15_lattices(sK0)
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f2005,f56])).

fof(f2005,plain,
    ( v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | v15_lattices(sK0)
    | ~ spl2_4 ),
    inference(resolution,[],[f97,f61])).

fof(f61,plain,(
    ! [X0] :
      ( ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v15_lattices(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f1991,plain,
    ( ~ spl2_2
    | spl2_4 ),
    inference(avatar_contradiction_clause,[],[f1990])).

fof(f1990,plain,
    ( $false
    | ~ spl2_2
    | spl2_4 ),
    inference(subsumption_resolution,[],[f1955,f96])).

fof(f96,plain,
    ( ~ v17_lattices(sK0)
    | spl2_4 ),
    inference(avatar_component_clause,[],[f95])).

fof(f1955,plain,
    ( v17_lattices(sK0)
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f40,f86])).

fof(f86,plain,
    ( v2_struct_0(k7_filter_1(sK0,sK1))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl2_2
  <=> v2_struct_0(k7_filter_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f40,plain,
    ( ~ v2_struct_0(k7_filter_1(sK0,sK1))
    | v17_lattices(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f1945,plain,
    ( ~ spl2_2
    | ~ spl2_4
    | ~ spl2_23 ),
    inference(avatar_contradiction_clause,[],[f1944])).

fof(f1944,plain,
    ( $false
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_23 ),
    inference(subsumption_resolution,[],[f1943,f55])).

fof(f1943,plain,
    ( ~ l3_lattices(sK1)
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_23 ),
    inference(subsumption_resolution,[],[f1942,f513])).

fof(f1942,plain,
    ( ~ v11_lattices(sK1)
    | ~ l3_lattices(sK1)
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f1941,f54])).

fof(f1941,plain,
    ( ~ v10_lattices(sK1)
    | ~ v11_lattices(sK1)
    | ~ l3_lattices(sK1)
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f1940,f53])).

fof(f1940,plain,
    ( v2_struct_0(sK1)
    | ~ v10_lattices(sK1)
    | ~ v11_lattices(sK1)
    | ~ l3_lattices(sK1)
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f1939,f58])).

fof(f1939,plain,
    ( ~ l3_lattices(sK0)
    | v2_struct_0(sK1)
    | ~ v10_lattices(sK1)
    | ~ v11_lattices(sK1)
    | ~ l3_lattices(sK1)
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f1938,f1089])).

fof(f1089,plain,
    ( v11_lattices(sK0)
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f1088,f58])).

fof(f1088,plain,
    ( ~ l3_lattices(sK0)
    | v11_lattices(sK0)
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f1085,f56])).

fof(f1085,plain,
    ( v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | v11_lattices(sK0)
    | ~ spl2_4 ),
    inference(resolution,[],[f97,f60])).

fof(f1938,plain,
    ( ~ v11_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK1)
    | ~ v10_lattices(sK1)
    | ~ v11_lattices(sK1)
    | ~ l3_lattices(sK1)
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f1937,f57])).

fof(f1937,plain,
    ( ~ v10_lattices(sK0)
    | ~ v11_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK1)
    | ~ v10_lattices(sK1)
    | ~ v11_lattices(sK1)
    | ~ l3_lattices(sK1)
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f1925,f56])).

fof(f1925,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ v11_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK1)
    | ~ v10_lattices(sK1)
    | ~ v11_lattices(sK1)
    | ~ l3_lattices(sK1)
    | ~ spl2_2 ),
    inference(resolution,[],[f86,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k7_filter_1(X0,X1))
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ v11_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ v11_lattices(X1)
      | ~ l3_lattices(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f1886,plain,
    ( spl2_19
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f1885,f95,f440])).

fof(f440,plain,
    ( spl2_19
  <=> v16_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f1885,plain,
    ( v16_lattices(sK0)
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f1884,f58])).

fof(f1884,plain,
    ( ~ l3_lattices(sK0)
    | v16_lattices(sK0)
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f1083,f56])).

fof(f1083,plain,
    ( v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | v16_lattices(sK0)
    | ~ spl2_4 ),
    inference(resolution,[],[f97,f62])).

fof(f62,plain,(
    ! [X0] :
      ( ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v16_lattices(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f1824,plain,
    ( spl2_2
    | spl2_5
    | ~ spl2_6
    | ~ spl2_14
    | ~ spl2_15
    | ~ spl2_19
    | ~ spl2_20
    | ~ spl2_35 ),
    inference(avatar_contradiction_clause,[],[f1823])).

fof(f1823,plain,
    ( $false
    | spl2_2
    | spl2_5
    | ~ spl2_6
    | ~ spl2_14
    | ~ spl2_15
    | ~ spl2_19
    | ~ spl2_20
    | ~ spl2_35 ),
    inference(subsumption_resolution,[],[f1822,f55])).

fof(f1822,plain,
    ( ~ l3_lattices(sK1)
    | spl2_2
    | spl2_5
    | ~ spl2_6
    | ~ spl2_14
    | ~ spl2_15
    | ~ spl2_19
    | ~ spl2_20
    | ~ spl2_35 ),
    inference(subsumption_resolution,[],[f1821,f379])).

fof(f379,plain,
    ( v16_lattices(sK1)
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f378])).

fof(f378,plain,
    ( spl2_14
  <=> v16_lattices(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f1821,plain,
    ( ~ v16_lattices(sK1)
    | ~ l3_lattices(sK1)
    | spl2_2
    | spl2_5
    | ~ spl2_6
    | ~ spl2_14
    | ~ spl2_15
    | ~ spl2_19
    | ~ spl2_20
    | ~ spl2_35 ),
    inference(subsumption_resolution,[],[f1820,f383])).

fof(f383,plain,
    ( v15_lattices(sK1)
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f382])).

fof(f382,plain,
    ( spl2_15
  <=> v15_lattices(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f1820,plain,
    ( ~ v15_lattices(sK1)
    | ~ v16_lattices(sK1)
    | ~ l3_lattices(sK1)
    | spl2_2
    | spl2_5
    | ~ spl2_6
    | ~ spl2_14
    | ~ spl2_15
    | ~ spl2_19
    | ~ spl2_20
    | ~ spl2_35 ),
    inference(subsumption_resolution,[],[f1819,f1778])).

fof(f1778,plain,
    ( ~ v15_lattices(k7_filter_1(sK0,sK1))
    | spl2_2
    | spl2_5
    | ~ spl2_6
    | ~ spl2_14
    | ~ spl2_15
    | ~ spl2_19
    | ~ spl2_20
    | ~ spl2_35 ),
    inference(subsumption_resolution,[],[f1777,f101])).

fof(f101,plain,
    ( ~ v17_lattices(k7_filter_1(sK0,sK1))
    | spl2_5 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl2_5
  <=> v17_lattices(k7_filter_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f1777,plain,
    ( ~ v15_lattices(k7_filter_1(sK0,sK1))
    | v17_lattices(k7_filter_1(sK0,sK1))
    | spl2_2
    | ~ spl2_6
    | ~ spl2_14
    | ~ spl2_15
    | ~ spl2_19
    | ~ spl2_20
    | ~ spl2_35 ),
    inference(subsumption_resolution,[],[f1776,f116])).

fof(f116,plain,
    ( l3_lattices(k7_filter_1(sK0,sK1))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl2_6
  <=> l3_lattices(k7_filter_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f1776,plain,
    ( ~ v15_lattices(k7_filter_1(sK0,sK1))
    | ~ l3_lattices(k7_filter_1(sK0,sK1))
    | v17_lattices(k7_filter_1(sK0,sK1))
    | spl2_2
    | ~ spl2_14
    | ~ spl2_15
    | ~ spl2_19
    | ~ spl2_20
    | ~ spl2_35 ),
    inference(subsumption_resolution,[],[f1775,f1113])).

fof(f1113,plain,
    ( v11_lattices(k7_filter_1(sK0,sK1))
    | ~ spl2_35 ),
    inference(avatar_component_clause,[],[f1112])).

fof(f1112,plain,
    ( spl2_35
  <=> v11_lattices(k7_filter_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_35])])).

fof(f1775,plain,
    ( ~ v11_lattices(k7_filter_1(sK0,sK1))
    | ~ v15_lattices(k7_filter_1(sK0,sK1))
    | ~ l3_lattices(k7_filter_1(sK0,sK1))
    | v17_lattices(k7_filter_1(sK0,sK1))
    | spl2_2
    | ~ spl2_14
    | ~ spl2_15
    | ~ spl2_19
    | ~ spl2_20 ),
    inference(subsumption_resolution,[],[f1774,f87])).

fof(f87,plain,
    ( ~ v2_struct_0(k7_filter_1(sK0,sK1))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f85])).

fof(f1774,plain,
    ( v2_struct_0(k7_filter_1(sK0,sK1))
    | ~ v11_lattices(k7_filter_1(sK0,sK1))
    | ~ v15_lattices(k7_filter_1(sK0,sK1))
    | ~ l3_lattices(k7_filter_1(sK0,sK1))
    | v17_lattices(k7_filter_1(sK0,sK1))
    | ~ spl2_14
    | ~ spl2_15
    | ~ spl2_19
    | ~ spl2_20 ),
    inference(resolution,[],[f1749,f59])).

fof(f59,plain,(
    ! [X0] :
      ( ~ v16_lattices(X0)
      | v2_struct_0(X0)
      | ~ v11_lattices(X0)
      | ~ v15_lattices(X0)
      | ~ l3_lattices(X0)
      | v17_lattices(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ( v17_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v16_lattices(X0)
      | ~ v15_lattices(X0)
      | ~ v11_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ( v17_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v16_lattices(X0)
      | ~ v15_lattices(X0)
      | ~ v11_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v16_lattices(X0)
          & v15_lattices(X0)
          & v11_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v17_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc6_lattices)).

fof(f1749,plain,
    ( v16_lattices(k7_filter_1(sK0,sK1))
    | ~ spl2_14
    | ~ spl2_15
    | ~ spl2_19
    | ~ spl2_20 ),
    inference(subsumption_resolution,[],[f1748,f55])).

fof(f1748,plain,
    ( v16_lattices(k7_filter_1(sK0,sK1))
    | ~ l3_lattices(sK1)
    | ~ spl2_14
    | ~ spl2_15
    | ~ spl2_19
    | ~ spl2_20 ),
    inference(subsumption_resolution,[],[f1747,f379])).

fof(f1747,plain,
    ( v16_lattices(k7_filter_1(sK0,sK1))
    | ~ v16_lattices(sK1)
    | ~ l3_lattices(sK1)
    | ~ spl2_15
    | ~ spl2_19
    | ~ spl2_20 ),
    inference(subsumption_resolution,[],[f1746,f383])).

fof(f1746,plain,
    ( v16_lattices(k7_filter_1(sK0,sK1))
    | ~ v15_lattices(sK1)
    | ~ v16_lattices(sK1)
    | ~ l3_lattices(sK1)
    | ~ spl2_19
    | ~ spl2_20 ),
    inference(subsumption_resolution,[],[f1732,f53])).

fof(f1732,plain,
    ( v2_struct_0(sK1)
    | v16_lattices(k7_filter_1(sK0,sK1))
    | ~ v15_lattices(sK1)
    | ~ v16_lattices(sK1)
    | ~ l3_lattices(sK1)
    | ~ spl2_19
    | ~ spl2_20 ),
    inference(resolution,[],[f1731,f54])).

fof(f1731,plain,
    ( ! [X1] :
        ( ~ v10_lattices(X1)
        | v2_struct_0(X1)
        | v16_lattices(k7_filter_1(sK0,X1))
        | ~ v15_lattices(X1)
        | ~ v16_lattices(X1)
        | ~ l3_lattices(X1) )
    | ~ spl2_19
    | ~ spl2_20 ),
    inference(subsumption_resolution,[],[f1730,f441])).

fof(f441,plain,
    ( v16_lattices(sK0)
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f440])).

fof(f1730,plain,
    ( ! [X1] :
        ( v16_lattices(k7_filter_1(sK0,X1))
        | ~ v16_lattices(sK0)
        | v2_struct_0(X1)
        | ~ v10_lattices(X1)
        | ~ v15_lattices(X1)
        | ~ v16_lattices(X1)
        | ~ l3_lattices(X1) )
    | ~ spl2_20 ),
    inference(subsumption_resolution,[],[f961,f445])).

fof(f445,plain,
    ( v15_lattices(sK0)
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f444])).

fof(f961,plain,(
    ! [X1] :
      ( v16_lattices(k7_filter_1(sK0,X1))
      | ~ v15_lattices(sK0)
      | ~ v16_lattices(sK0)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ v15_lattices(X1)
      | ~ v16_lattices(X1)
      | ~ l3_lattices(X1) ) ),
    inference(subsumption_resolution,[],[f960,f58])).

fof(f960,plain,(
    ! [X1] :
      ( v16_lattices(k7_filter_1(sK0,X1))
      | ~ v15_lattices(sK0)
      | ~ v16_lattices(sK0)
      | ~ l3_lattices(sK0)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ v15_lattices(X1)
      | ~ v16_lattices(X1)
      | ~ l3_lattices(X1) ) ),
    inference(subsumption_resolution,[],[f456,f56])).

fof(f456,plain,(
    ! [X1] :
      ( v2_struct_0(sK0)
      | v16_lattices(k7_filter_1(sK0,X1))
      | ~ v15_lattices(sK0)
      | ~ v16_lattices(sK0)
      | ~ l3_lattices(sK0)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ v15_lattices(X1)
      | ~ v16_lattices(X1)
      | ~ l3_lattices(X1) ) ),
    inference(resolution,[],[f70,f57])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | v16_lattices(k7_filter_1(X0,X1))
      | ~ v15_lattices(X0)
      | ~ v16_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ v15_lattices(X1)
      | ~ v16_lattices(X1)
      | ~ l3_lattices(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( l3_lattices(X1)
              & v16_lattices(X1)
              & v15_lattices(X1)
              & v10_lattices(X1)
              & ~ v2_struct_0(X1)
              & l3_lattices(X0)
              & v16_lattices(X0)
              & v15_lattices(X0)
              & v10_lattices(X0)
              & ~ v2_struct_0(X0) )
          <=> ( l3_lattices(k7_filter_1(X0,X1))
              & v16_lattices(k7_filter_1(X0,X1))
              & v15_lattices(k7_filter_1(X0,X1))
              & v10_lattices(k7_filter_1(X0,X1))
              & ~ v2_struct_0(k7_filter_1(X0,X1)) ) )
          | ~ l3_lattices(X1)
          | ~ v10_lattices(X1)
          | v2_struct_0(X1) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( l3_lattices(X1)
              & v16_lattices(X1)
              & v15_lattices(X1)
              & v10_lattices(X1)
              & ~ v2_struct_0(X1)
              & l3_lattices(X0)
              & v16_lattices(X0)
              & v15_lattices(X0)
              & v10_lattices(X0)
              & ~ v2_struct_0(X0) )
          <=> ( l3_lattices(k7_filter_1(X0,X1))
              & v16_lattices(k7_filter_1(X0,X1))
              & v15_lattices(k7_filter_1(X0,X1))
              & v10_lattices(k7_filter_1(X0,X1))
              & ~ v2_struct_0(k7_filter_1(X0,X1)) ) )
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
         => ( ( l3_lattices(X1)
              & v16_lattices(X1)
              & v15_lattices(X1)
              & v10_lattices(X1)
              & ~ v2_struct_0(X1)
              & l3_lattices(X0)
              & v16_lattices(X0)
              & v15_lattices(X0)
              & v10_lattices(X0)
              & ~ v2_struct_0(X0) )
          <=> ( l3_lattices(k7_filter_1(X0,X1))
              & v16_lattices(k7_filter_1(X0,X1))
              & v15_lattices(k7_filter_1(X0,X1))
              & v10_lattices(k7_filter_1(X0,X1))
              & ~ v2_struct_0(k7_filter_1(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_filter_1)).

fof(f1819,plain,
    ( v15_lattices(k7_filter_1(sK0,sK1))
    | ~ v15_lattices(sK1)
    | ~ v16_lattices(sK1)
    | ~ l3_lattices(sK1)
    | ~ spl2_19
    | ~ spl2_20 ),
    inference(subsumption_resolution,[],[f1805,f53])).

fof(f1805,plain,
    ( v2_struct_0(sK1)
    | v15_lattices(k7_filter_1(sK0,sK1))
    | ~ v15_lattices(sK1)
    | ~ v16_lattices(sK1)
    | ~ l3_lattices(sK1)
    | ~ spl2_19
    | ~ spl2_20 ),
    inference(resolution,[],[f1801,f54])).

fof(f1801,plain,
    ( ! [X1] :
        ( ~ v10_lattices(X1)
        | v2_struct_0(X1)
        | v15_lattices(k7_filter_1(sK0,X1))
        | ~ v15_lattices(X1)
        | ~ v16_lattices(X1)
        | ~ l3_lattices(X1) )
    | ~ spl2_19
    | ~ spl2_20 ),
    inference(subsumption_resolution,[],[f1800,f441])).

fof(f1800,plain,
    ( ! [X1] :
        ( v15_lattices(k7_filter_1(sK0,X1))
        | ~ v16_lattices(sK0)
        | v2_struct_0(X1)
        | ~ v10_lattices(X1)
        | ~ v15_lattices(X1)
        | ~ v16_lattices(X1)
        | ~ l3_lattices(X1) )
    | ~ spl2_20 ),
    inference(subsumption_resolution,[],[f963,f445])).

fof(f963,plain,(
    ! [X1] :
      ( v15_lattices(k7_filter_1(sK0,X1))
      | ~ v15_lattices(sK0)
      | ~ v16_lattices(sK0)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ v15_lattices(X1)
      | ~ v16_lattices(X1)
      | ~ l3_lattices(X1) ) ),
    inference(subsumption_resolution,[],[f962,f58])).

fof(f962,plain,(
    ! [X1] :
      ( v15_lattices(k7_filter_1(sK0,X1))
      | ~ v15_lattices(sK0)
      | ~ v16_lattices(sK0)
      | ~ l3_lattices(sK0)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ v15_lattices(X1)
      | ~ v16_lattices(X1)
      | ~ l3_lattices(X1) ) ),
    inference(subsumption_resolution,[],[f449,f56])).

fof(f449,plain,(
    ! [X1] :
      ( v2_struct_0(sK0)
      | v15_lattices(k7_filter_1(sK0,X1))
      | ~ v15_lattices(sK0)
      | ~ v16_lattices(sK0)
      | ~ l3_lattices(sK0)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ v15_lattices(X1)
      | ~ v16_lattices(X1)
      | ~ l3_lattices(X1) ) ),
    inference(resolution,[],[f69,f57])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | v15_lattices(k7_filter_1(X0,X1))
      | ~ v15_lattices(X0)
      | ~ v16_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ v15_lattices(X1)
      | ~ v16_lattices(X1)
      | ~ l3_lattices(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f1147,plain,
    ( spl2_35
    | ~ spl2_4
    | ~ spl2_23 ),
    inference(avatar_split_clause,[],[f1146,f512,f95,f1112])).

fof(f1146,plain,
    ( v11_lattices(k7_filter_1(sK0,sK1))
    | ~ spl2_4
    | ~ spl2_23 ),
    inference(subsumption_resolution,[],[f1145,f55])).

fof(f1145,plain,
    ( v11_lattices(k7_filter_1(sK0,sK1))
    | ~ l3_lattices(sK1)
    | ~ spl2_4
    | ~ spl2_23 ),
    inference(subsumption_resolution,[],[f1128,f513])).

fof(f1128,plain,
    ( v11_lattices(k7_filter_1(sK0,sK1))
    | ~ v11_lattices(sK1)
    | ~ l3_lattices(sK1)
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f1121,f53])).

fof(f1121,plain,
    ( v2_struct_0(sK1)
    | v11_lattices(k7_filter_1(sK0,sK1))
    | ~ v11_lattices(sK1)
    | ~ l3_lattices(sK1)
    | ~ spl2_4 ),
    inference(resolution,[],[f1120,f54])).

fof(f1120,plain,
    ( ! [X1] :
        ( ~ v10_lattices(X1)
        | v2_struct_0(X1)
        | v11_lattices(k7_filter_1(sK0,X1))
        | ~ v11_lattices(X1)
        | ~ l3_lattices(X1) )
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f437,f1089])).

fof(f437,plain,(
    ! [X1] :
      ( v11_lattices(k7_filter_1(sK0,X1))
      | ~ v11_lattices(sK0)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ v11_lattices(X1)
      | ~ l3_lattices(X1) ) ),
    inference(subsumption_resolution,[],[f269,f58])).

fof(f269,plain,(
    ! [X1] :
      ( v11_lattices(k7_filter_1(sK0,X1))
      | ~ v11_lattices(sK0)
      | ~ l3_lattices(sK0)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ v11_lattices(X1)
      | ~ l3_lattices(X1) ) ),
    inference(subsumption_resolution,[],[f264,f56])).

fof(f264,plain,(
    ! [X1] :
      ( v2_struct_0(sK0)
      | v11_lattices(k7_filter_1(sK0,X1))
      | ~ v11_lattices(sK0)
      | ~ l3_lattices(sK0)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ v11_lattices(X1)
      | ~ l3_lattices(X1) ) ),
    inference(resolution,[],[f76,f57])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | v11_lattices(k7_filter_1(X0,X1))
      | ~ v11_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ v11_lattices(X1)
      | ~ l3_lattices(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f1059,plain,
    ( spl2_2
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_6
    | spl2_20 ),
    inference(avatar_contradiction_clause,[],[f1058])).

fof(f1058,plain,
    ( $false
    | spl2_2
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_6
    | spl2_20 ),
    inference(subsumption_resolution,[],[f1057,f446])).

fof(f446,plain,
    ( ~ v15_lattices(sK0)
    | spl2_20 ),
    inference(avatar_component_clause,[],[f444])).

fof(f1057,plain,
    ( v15_lattices(sK0)
    | spl2_2
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(subsumption_resolution,[],[f1056,f564])).

fof(f564,plain,
    ( v16_lattices(k7_filter_1(sK0,sK1))
    | spl2_2
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(subsumption_resolution,[],[f476,f87])).

fof(f476,plain,
    ( v2_struct_0(k7_filter_1(sK0,sK1))
    | v16_lattices(k7_filter_1(sK0,sK1))
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(subsumption_resolution,[],[f325,f116])).

fof(f325,plain,
    ( v2_struct_0(k7_filter_1(sK0,sK1))
    | ~ l3_lattices(k7_filter_1(sK0,sK1))
    | v16_lattices(k7_filter_1(sK0,sK1))
    | ~ spl2_5 ),
    inference(resolution,[],[f102,f62])).

fof(f102,plain,
    ( v17_lattices(k7_filter_1(sK0,sK1))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f100])).

fof(f1056,plain,
    ( ~ v16_lattices(k7_filter_1(sK0,sK1))
    | v15_lattices(sK0)
    | spl2_2
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(subsumption_resolution,[],[f1055,f563])).

fof(f563,plain,
    ( v15_lattices(k7_filter_1(sK0,sK1))
    | spl2_2
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(subsumption_resolution,[],[f475,f87])).

fof(f475,plain,
    ( v2_struct_0(k7_filter_1(sK0,sK1))
    | v15_lattices(k7_filter_1(sK0,sK1))
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(subsumption_resolution,[],[f326,f116])).

fof(f326,plain,
    ( v2_struct_0(k7_filter_1(sK0,sK1))
    | ~ l3_lattices(k7_filter_1(sK0,sK1))
    | v15_lattices(k7_filter_1(sK0,sK1))
    | ~ spl2_5 ),
    inference(resolution,[],[f102,f61])).

fof(f1055,plain,
    ( ~ v15_lattices(k7_filter_1(sK0,sK1))
    | ~ v16_lattices(k7_filter_1(sK0,sK1))
    | v15_lattices(sK0)
    | spl2_2
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f1054,f56])).

fof(f1054,plain,
    ( v2_struct_0(sK0)
    | ~ v15_lattices(k7_filter_1(sK0,sK1))
    | ~ v16_lattices(k7_filter_1(sK0,sK1))
    | v15_lattices(sK0)
    | spl2_2
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f1053,f87])).

fof(f1053,plain,
    ( v2_struct_0(k7_filter_1(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ v15_lattices(k7_filter_1(sK0,sK1))
    | ~ v16_lattices(k7_filter_1(sK0,sK1))
    | v15_lattices(sK0)
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f1052,f55])).

fof(f1052,plain,
    ( ~ l3_lattices(sK1)
    | v2_struct_0(k7_filter_1(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ v15_lattices(k7_filter_1(sK0,sK1))
    | ~ v16_lattices(k7_filter_1(sK0,sK1))
    | v15_lattices(sK0)
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f1051,f54])).

fof(f1051,plain,
    ( ~ v10_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(k7_filter_1(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ v15_lattices(k7_filter_1(sK0,sK1))
    | ~ v16_lattices(k7_filter_1(sK0,sK1))
    | v15_lattices(sK0)
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f1050,f53])).

fof(f1050,plain,
    ( v2_struct_0(sK1)
    | ~ v10_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(k7_filter_1(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ v15_lattices(k7_filter_1(sK0,sK1))
    | ~ v16_lattices(k7_filter_1(sK0,sK1))
    | v15_lattices(sK0)
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f1049,f58])).

fof(f1049,plain,
    ( ~ l3_lattices(sK0)
    | v2_struct_0(sK1)
    | ~ v10_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(k7_filter_1(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ v15_lattices(k7_filter_1(sK0,sK1))
    | ~ v16_lattices(k7_filter_1(sK0,sK1))
    | v15_lattices(sK0)
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f1042,f57])).

fof(f1042,plain,
    ( ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK1)
    | ~ v10_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(k7_filter_1(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ v15_lattices(k7_filter_1(sK0,sK1))
    | ~ v16_lattices(k7_filter_1(sK0,sK1))
    | v15_lattices(sK0)
    | ~ spl2_3 ),
    inference(resolution,[],[f1009,f92])).

fof(f92,plain,
    ( v10_lattices(k7_filter_1(sK0,sK1))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f90])).

fof(f1009,plain,(
    ! [X0,X1] :
      ( ~ v10_lattices(k7_filter_1(X0,X1))
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ l3_lattices(X1)
      | v2_struct_0(k7_filter_1(X0,X1))
      | v2_struct_0(X0)
      | ~ v15_lattices(k7_filter_1(X0,X1))
      | ~ v16_lattices(k7_filter_1(X0,X1))
      | v15_lattices(X0) ) ),
    inference(subsumption_resolution,[],[f66,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l3_lattices(X1)
      | l3_lattices(k7_filter_1(X0,X1)) ) ),
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X1)
        & ~ v2_struct_0(X1)
        & l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( l3_lattices(k7_filter_1(X0,X1))
        & v3_lattices(k7_filter_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_filter_1)).

fof(f66,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ l3_lattices(X1)
      | v2_struct_0(k7_filter_1(X0,X1))
      | ~ v10_lattices(k7_filter_1(X0,X1))
      | ~ v15_lattices(k7_filter_1(X0,X1))
      | ~ v16_lattices(k7_filter_1(X0,X1))
      | ~ l3_lattices(k7_filter_1(X0,X1))
      | v15_lattices(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f970,plain,
    ( ~ spl2_20
    | spl2_2
    | ~ spl2_3
    | spl2_4
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_19 ),
    inference(avatar_split_clause,[],[f969,f440,f115,f100,f95,f90,f85,f444])).

fof(f969,plain,
    ( ~ v15_lattices(sK0)
    | spl2_2
    | ~ spl2_3
    | spl2_4
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_19 ),
    inference(subsumption_resolution,[],[f968,f96])).

fof(f968,plain,
    ( ~ v15_lattices(sK0)
    | v17_lattices(sK0)
    | spl2_2
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_19 ),
    inference(subsumption_resolution,[],[f967,f58])).

fof(f967,plain,
    ( ~ v15_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v17_lattices(sK0)
    | spl2_2
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_19 ),
    inference(subsumption_resolution,[],[f966,f591])).

fof(f591,plain,
    ( v11_lattices(sK0)
    | spl2_2
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(subsumption_resolution,[],[f590,f562])).

fof(f562,plain,
    ( v11_lattices(k7_filter_1(sK0,sK1))
    | spl2_2
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(subsumption_resolution,[],[f474,f87])).

fof(f474,plain,
    ( v2_struct_0(k7_filter_1(sK0,sK1))
    | v11_lattices(k7_filter_1(sK0,sK1))
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(subsumption_resolution,[],[f327,f116])).

fof(f327,plain,
    ( v2_struct_0(k7_filter_1(sK0,sK1))
    | ~ l3_lattices(k7_filter_1(sK0,sK1))
    | v11_lattices(k7_filter_1(sK0,sK1))
    | ~ spl2_5 ),
    inference(resolution,[],[f102,f60])).

fof(f590,plain,
    ( ~ v11_lattices(k7_filter_1(sK0,sK1))
    | v11_lattices(sK0)
    | spl2_2
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f589,f56])).

fof(f589,plain,
    ( v2_struct_0(sK0)
    | ~ v11_lattices(k7_filter_1(sK0,sK1))
    | v11_lattices(sK0)
    | spl2_2
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f588,f87])).

fof(f588,plain,
    ( v2_struct_0(k7_filter_1(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ v11_lattices(k7_filter_1(sK0,sK1))
    | v11_lattices(sK0)
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f587,f55])).

fof(f587,plain,
    ( ~ l3_lattices(sK1)
    | v2_struct_0(k7_filter_1(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ v11_lattices(k7_filter_1(sK0,sK1))
    | v11_lattices(sK0)
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f586,f54])).

fof(f586,plain,
    ( ~ v10_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(k7_filter_1(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ v11_lattices(k7_filter_1(sK0,sK1))
    | v11_lattices(sK0)
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f585,f53])).

fof(f585,plain,
    ( v2_struct_0(sK1)
    | ~ v10_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(k7_filter_1(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ v11_lattices(k7_filter_1(sK0,sK1))
    | v11_lattices(sK0)
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f584,f58])).

fof(f584,plain,
    ( ~ l3_lattices(sK0)
    | v2_struct_0(sK1)
    | ~ v10_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(k7_filter_1(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ v11_lattices(k7_filter_1(sK0,sK1))
    | v11_lattices(sK0)
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f583,f57])).

fof(f583,plain,
    ( ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK1)
    | ~ v10_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(k7_filter_1(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ v11_lattices(k7_filter_1(sK0,sK1))
    | v11_lattices(sK0)
    | ~ spl2_3 ),
    inference(resolution,[],[f566,f92])).

fof(f566,plain,(
    ! [X0,X1] :
      ( ~ v10_lattices(k7_filter_1(X0,X1))
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ l3_lattices(X1)
      | v2_struct_0(k7_filter_1(X0,X1))
      | v2_struct_0(X0)
      | ~ v11_lattices(k7_filter_1(X0,X1))
      | v11_lattices(X0) ) ),
    inference(subsumption_resolution,[],[f73,f79])).

fof(f73,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ l3_lattices(X1)
      | v2_struct_0(k7_filter_1(X0,X1))
      | ~ v10_lattices(k7_filter_1(X0,X1))
      | ~ v11_lattices(k7_filter_1(X0,X1))
      | ~ l3_lattices(k7_filter_1(X0,X1))
      | v11_lattices(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f966,plain,
    ( ~ v11_lattices(sK0)
    | ~ v15_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v17_lattices(sK0)
    | ~ spl2_19 ),
    inference(subsumption_resolution,[],[f965,f56])).

fof(f965,plain,
    ( v2_struct_0(sK0)
    | ~ v11_lattices(sK0)
    | ~ v15_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v17_lattices(sK0)
    | ~ spl2_19 ),
    inference(resolution,[],[f441,f59])).

fof(f964,plain,
    ( spl2_19
    | spl2_2
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f957,f115,f100,f90,f85,f440])).

fof(f957,plain,
    ( v16_lattices(sK0)
    | spl2_2
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(subsumption_resolution,[],[f956,f564])).

fof(f956,plain,
    ( ~ v16_lattices(k7_filter_1(sK0,sK1))
    | v16_lattices(sK0)
    | spl2_2
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(subsumption_resolution,[],[f955,f563])).

fof(f955,plain,
    ( ~ v15_lattices(k7_filter_1(sK0,sK1))
    | ~ v16_lattices(k7_filter_1(sK0,sK1))
    | v16_lattices(sK0)
    | spl2_2
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f954,f56])).

fof(f954,plain,
    ( v2_struct_0(sK0)
    | ~ v15_lattices(k7_filter_1(sK0,sK1))
    | ~ v16_lattices(k7_filter_1(sK0,sK1))
    | v16_lattices(sK0)
    | spl2_2
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f953,f87])).

fof(f953,plain,
    ( v2_struct_0(k7_filter_1(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ v15_lattices(k7_filter_1(sK0,sK1))
    | ~ v16_lattices(k7_filter_1(sK0,sK1))
    | v16_lattices(sK0)
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f952,f55])).

fof(f952,plain,
    ( ~ l3_lattices(sK1)
    | v2_struct_0(k7_filter_1(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ v15_lattices(k7_filter_1(sK0,sK1))
    | ~ v16_lattices(k7_filter_1(sK0,sK1))
    | v16_lattices(sK0)
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f951,f54])).

fof(f951,plain,
    ( ~ v10_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(k7_filter_1(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ v15_lattices(k7_filter_1(sK0,sK1))
    | ~ v16_lattices(k7_filter_1(sK0,sK1))
    | v16_lattices(sK0)
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f950,f53])).

fof(f950,plain,
    ( v2_struct_0(sK1)
    | ~ v10_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(k7_filter_1(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ v15_lattices(k7_filter_1(sK0,sK1))
    | ~ v16_lattices(k7_filter_1(sK0,sK1))
    | v16_lattices(sK0)
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f949,f58])).

fof(f949,plain,
    ( ~ l3_lattices(sK0)
    | v2_struct_0(sK1)
    | ~ v10_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(k7_filter_1(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ v15_lattices(k7_filter_1(sK0,sK1))
    | ~ v16_lattices(k7_filter_1(sK0,sK1))
    | v16_lattices(sK0)
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f943,f57])).

fof(f943,plain,
    ( ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK1)
    | ~ v10_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(k7_filter_1(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ v15_lattices(k7_filter_1(sK0,sK1))
    | ~ v16_lattices(k7_filter_1(sK0,sK1))
    | v16_lattices(sK0)
    | ~ spl2_3 ),
    inference(resolution,[],[f800,f92])).

fof(f800,plain,(
    ! [X0,X1] :
      ( ~ v10_lattices(k7_filter_1(X0,X1))
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ l3_lattices(X1)
      | v2_struct_0(k7_filter_1(X0,X1))
      | v2_struct_0(X0)
      | ~ v15_lattices(k7_filter_1(X0,X1))
      | ~ v16_lattices(k7_filter_1(X0,X1))
      | v16_lattices(X0) ) ),
    inference(subsumption_resolution,[],[f65,f79])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ l3_lattices(X1)
      | v2_struct_0(k7_filter_1(X0,X1))
      | ~ v10_lattices(k7_filter_1(X0,X1))
      | ~ v15_lattices(k7_filter_1(X0,X1))
      | ~ v16_lattices(k7_filter_1(X0,X1))
      | ~ l3_lattices(k7_filter_1(X0,X1))
      | v16_lattices(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f780,plain,
    ( spl2_15
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f778,f81,f382])).

fof(f81,plain,
    ( spl2_1
  <=> v17_lattices(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f778,plain,
    ( v15_lattices(sK1)
    | ~ spl2_1 ),
    inference(subsumption_resolution,[],[f777,f55])).

fof(f777,plain,
    ( ~ l3_lattices(sK1)
    | v15_lattices(sK1)
    | ~ spl2_1 ),
    inference(subsumption_resolution,[],[f773,f53])).

fof(f773,plain,
    ( v2_struct_0(sK1)
    | ~ l3_lattices(sK1)
    | v15_lattices(sK1)
    | ~ spl2_1 ),
    inference(resolution,[],[f83,f61])).

fof(f83,plain,
    ( v17_lattices(sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f81])).

fof(f779,plain,
    ( spl2_14
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f776,f81,f378])).

fof(f776,plain,
    ( v16_lattices(sK1)
    | ~ spl2_1 ),
    inference(subsumption_resolution,[],[f775,f55])).

fof(f775,plain,
    ( ~ l3_lattices(sK1)
    | v16_lattices(sK1)
    | ~ spl2_1 ),
    inference(subsumption_resolution,[],[f772,f53])).

fof(f772,plain,
    ( v2_struct_0(sK1)
    | ~ l3_lattices(sK1)
    | v16_lattices(sK1)
    | ~ spl2_1 ),
    inference(resolution,[],[f83,f62])).

fof(f770,plain,
    ( spl2_14
    | spl2_2
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f768,f115,f100,f90,f85,f378])).

fof(f768,plain,
    ( v16_lattices(sK1)
    | spl2_2
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(subsumption_resolution,[],[f767,f564])).

fof(f767,plain,
    ( ~ v16_lattices(k7_filter_1(sK0,sK1))
    | v16_lattices(sK1)
    | spl2_2
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(subsumption_resolution,[],[f766,f563])).

fof(f766,plain,
    ( ~ v15_lattices(k7_filter_1(sK0,sK1))
    | ~ v16_lattices(k7_filter_1(sK0,sK1))
    | v16_lattices(sK1)
    | spl2_2
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f765,f56])).

fof(f765,plain,
    ( v2_struct_0(sK0)
    | ~ v15_lattices(k7_filter_1(sK0,sK1))
    | ~ v16_lattices(k7_filter_1(sK0,sK1))
    | v16_lattices(sK1)
    | spl2_2
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f764,f87])).

fof(f764,plain,
    ( v2_struct_0(k7_filter_1(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ v15_lattices(k7_filter_1(sK0,sK1))
    | ~ v16_lattices(k7_filter_1(sK0,sK1))
    | v16_lattices(sK1)
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f763,f55])).

fof(f763,plain,
    ( ~ l3_lattices(sK1)
    | v2_struct_0(k7_filter_1(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ v15_lattices(k7_filter_1(sK0,sK1))
    | ~ v16_lattices(k7_filter_1(sK0,sK1))
    | v16_lattices(sK1)
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f762,f54])).

fof(f762,plain,
    ( ~ v10_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(k7_filter_1(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ v15_lattices(k7_filter_1(sK0,sK1))
    | ~ v16_lattices(k7_filter_1(sK0,sK1))
    | v16_lattices(sK1)
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f761,f53])).

fof(f761,plain,
    ( v2_struct_0(sK1)
    | ~ v10_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(k7_filter_1(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ v15_lattices(k7_filter_1(sK0,sK1))
    | ~ v16_lattices(k7_filter_1(sK0,sK1))
    | v16_lattices(sK1)
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f760,f58])).

fof(f760,plain,
    ( ~ l3_lattices(sK0)
    | v2_struct_0(sK1)
    | ~ v10_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(k7_filter_1(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ v15_lattices(k7_filter_1(sK0,sK1))
    | ~ v16_lattices(k7_filter_1(sK0,sK1))
    | v16_lattices(sK1)
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f644,f57])).

fof(f644,plain,
    ( ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK1)
    | ~ v10_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(k7_filter_1(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ v15_lattices(k7_filter_1(sK0,sK1))
    | ~ v16_lattices(k7_filter_1(sK0,sK1))
    | v16_lattices(sK1)
    | ~ spl2_3 ),
    inference(resolution,[],[f615,f92])).

fof(f615,plain,(
    ! [X0,X1] :
      ( ~ v10_lattices(k7_filter_1(X0,X1))
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ l3_lattices(X1)
      | v2_struct_0(k7_filter_1(X0,X1))
      | v2_struct_0(X0)
      | ~ v15_lattices(k7_filter_1(X0,X1))
      | ~ v16_lattices(k7_filter_1(X0,X1))
      | v16_lattices(X1) ) ),
    inference(subsumption_resolution,[],[f63,f79])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ l3_lattices(X1)
      | v2_struct_0(k7_filter_1(X0,X1))
      | ~ v10_lattices(k7_filter_1(X0,X1))
      | ~ v15_lattices(k7_filter_1(X0,X1))
      | ~ v16_lattices(k7_filter_1(X0,X1))
      | ~ l3_lattices(k7_filter_1(X0,X1))
      | v16_lattices(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f769,plain,
    ( spl2_15
    | spl2_2
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f757,f115,f100,f90,f85,f382])).

fof(f757,plain,
    ( v15_lattices(sK1)
    | spl2_2
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(subsumption_resolution,[],[f756,f564])).

fof(f756,plain,
    ( ~ v16_lattices(k7_filter_1(sK0,sK1))
    | v15_lattices(sK1)
    | spl2_2
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(subsumption_resolution,[],[f755,f563])).

fof(f755,plain,
    ( ~ v15_lattices(k7_filter_1(sK0,sK1))
    | ~ v16_lattices(k7_filter_1(sK0,sK1))
    | v15_lattices(sK1)
    | spl2_2
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f754,f56])).

fof(f754,plain,
    ( v2_struct_0(sK0)
    | ~ v15_lattices(k7_filter_1(sK0,sK1))
    | ~ v16_lattices(k7_filter_1(sK0,sK1))
    | v15_lattices(sK1)
    | spl2_2
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f753,f87])).

fof(f753,plain,
    ( v2_struct_0(k7_filter_1(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ v15_lattices(k7_filter_1(sK0,sK1))
    | ~ v16_lattices(k7_filter_1(sK0,sK1))
    | v15_lattices(sK1)
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f752,f55])).

fof(f752,plain,
    ( ~ l3_lattices(sK1)
    | v2_struct_0(k7_filter_1(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ v15_lattices(k7_filter_1(sK0,sK1))
    | ~ v16_lattices(k7_filter_1(sK0,sK1))
    | v15_lattices(sK1)
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f751,f54])).

fof(f751,plain,
    ( ~ v10_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(k7_filter_1(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ v15_lattices(k7_filter_1(sK0,sK1))
    | ~ v16_lattices(k7_filter_1(sK0,sK1))
    | v15_lattices(sK1)
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f750,f53])).

fof(f750,plain,
    ( v2_struct_0(sK1)
    | ~ v10_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(k7_filter_1(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ v15_lattices(k7_filter_1(sK0,sK1))
    | ~ v16_lattices(k7_filter_1(sK0,sK1))
    | v15_lattices(sK1)
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f749,f58])).

fof(f749,plain,
    ( ~ l3_lattices(sK0)
    | v2_struct_0(sK1)
    | ~ v10_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(k7_filter_1(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ v15_lattices(k7_filter_1(sK0,sK1))
    | ~ v16_lattices(k7_filter_1(sK0,sK1))
    | v15_lattices(sK1)
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f748,f57])).

fof(f748,plain,
    ( ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK1)
    | ~ v10_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(k7_filter_1(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ v15_lattices(k7_filter_1(sK0,sK1))
    | ~ v16_lattices(k7_filter_1(sK0,sK1))
    | v15_lattices(sK1)
    | ~ spl2_3 ),
    inference(resolution,[],[f709,f92])).

fof(f709,plain,(
    ! [X0,X1] :
      ( ~ v10_lattices(k7_filter_1(X0,X1))
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ l3_lattices(X1)
      | v2_struct_0(k7_filter_1(X0,X1))
      | v2_struct_0(X0)
      | ~ v15_lattices(k7_filter_1(X0,X1))
      | ~ v16_lattices(k7_filter_1(X0,X1))
      | v15_lattices(X1) ) ),
    inference(subsumption_resolution,[],[f64,f79])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ l3_lattices(X1)
      | v2_struct_0(k7_filter_1(X0,X1))
      | ~ v10_lattices(k7_filter_1(X0,X1))
      | ~ v15_lattices(k7_filter_1(X0,X1))
      | ~ v16_lattices(k7_filter_1(X0,X1))
      | ~ l3_lattices(k7_filter_1(X0,X1))
      | v15_lattices(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f561,plain,
    ( spl2_23
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f559,f81,f512])).

fof(f559,plain,
    ( v11_lattices(sK1)
    | ~ spl2_1 ),
    inference(subsumption_resolution,[],[f558,f55])).

fof(f558,plain,
    ( ~ l3_lattices(sK1)
    | v11_lattices(sK1)
    | ~ spl2_1 ),
    inference(subsumption_resolution,[],[f555,f53])).

fof(f555,plain,
    ( v2_struct_0(sK1)
    | ~ l3_lattices(sK1)
    | v11_lattices(sK1)
    | ~ spl2_1 ),
    inference(resolution,[],[f83,f60])).

fof(f551,plain,
    ( spl2_23
    | spl2_2
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f550,f115,f100,f90,f85,f512])).

fof(f550,plain,
    ( v11_lattices(sK1)
    | spl2_2
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(subsumption_resolution,[],[f549,f516])).

fof(f516,plain,
    ( v11_lattices(k7_filter_1(sK0,sK1))
    | spl2_2
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(subsumption_resolution,[],[f474,f87])).

fof(f549,plain,
    ( ~ v11_lattices(k7_filter_1(sK0,sK1))
    | v11_lattices(sK1)
    | spl2_2
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f548,f56])).

fof(f548,plain,
    ( v2_struct_0(sK0)
    | ~ v11_lattices(k7_filter_1(sK0,sK1))
    | v11_lattices(sK1)
    | spl2_2
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f547,f87])).

fof(f547,plain,
    ( v2_struct_0(k7_filter_1(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ v11_lattices(k7_filter_1(sK0,sK1))
    | v11_lattices(sK1)
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f546,f55])).

fof(f546,plain,
    ( ~ l3_lattices(sK1)
    | v2_struct_0(k7_filter_1(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ v11_lattices(k7_filter_1(sK0,sK1))
    | v11_lattices(sK1)
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f545,f54])).

fof(f545,plain,
    ( ~ v10_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(k7_filter_1(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ v11_lattices(k7_filter_1(sK0,sK1))
    | v11_lattices(sK1)
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f544,f53])).

fof(f544,plain,
    ( v2_struct_0(sK1)
    | ~ v10_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(k7_filter_1(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ v11_lattices(k7_filter_1(sK0,sK1))
    | v11_lattices(sK1)
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f543,f58])).

fof(f543,plain,
    ( ~ l3_lattices(sK0)
    | v2_struct_0(sK1)
    | ~ v10_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(k7_filter_1(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ v11_lattices(k7_filter_1(sK0,sK1))
    | v11_lattices(sK1)
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f542,f57])).

fof(f542,plain,
    ( ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK1)
    | ~ v10_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(k7_filter_1(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ v11_lattices(k7_filter_1(sK0,sK1))
    | v11_lattices(sK1)
    | ~ spl2_3 ),
    inference(resolution,[],[f518,f92])).

fof(f518,plain,(
    ! [X0,X1] :
      ( ~ v10_lattices(k7_filter_1(X0,X1))
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ l3_lattices(X1)
      | v2_struct_0(k7_filter_1(X0,X1))
      | v2_struct_0(X0)
      | ~ v11_lattices(k7_filter_1(X0,X1))
      | v11_lattices(X1) ) ),
    inference(subsumption_resolution,[],[f72,f79])).

fof(f72,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ l3_lattices(X1)
      | v2_struct_0(k7_filter_1(X0,X1))
      | ~ v10_lattices(k7_filter_1(X0,X1))
      | ~ v11_lattices(k7_filter_1(X0,X1))
      | ~ l3_lattices(k7_filter_1(X0,X1))
      | v11_lattices(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f515,plain,
    ( ~ spl2_15
    | ~ spl2_23
    | spl2_1
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f510,f378,f81,f512,f382])).

fof(f510,plain,
    ( ~ v11_lattices(sK1)
    | ~ v15_lattices(sK1)
    | spl2_1
    | ~ spl2_14 ),
    inference(subsumption_resolution,[],[f509,f82])).

fof(f82,plain,
    ( ~ v17_lattices(sK1)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f81])).

fof(f509,plain,
    ( ~ v11_lattices(sK1)
    | ~ v15_lattices(sK1)
    | v17_lattices(sK1)
    | ~ spl2_14 ),
    inference(subsumption_resolution,[],[f508,f55])).

fof(f508,plain,
    ( ~ v11_lattices(sK1)
    | ~ v15_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v17_lattices(sK1)
    | ~ spl2_14 ),
    inference(subsumption_resolution,[],[f507,f53])).

fof(f507,plain,
    ( v2_struct_0(sK1)
    | ~ v11_lattices(sK1)
    | ~ v15_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v17_lattices(sK1)
    | ~ spl2_14 ),
    inference(resolution,[],[f379,f59])).

fof(f307,plain,
    ( spl2_1
    | spl2_5 ),
    inference(avatar_split_clause,[],[f306,f100,f81])).

fof(f306,plain,
    ( v17_lattices(sK1)
    | spl2_5 ),
    inference(subsumption_resolution,[],[f26,f101])).

fof(f26,plain,
    ( v17_lattices(k7_filter_1(sK0,sK1))
    | v17_lattices(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f175,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f173,f115])).

fof(f173,plain,(
    l3_lattices(k7_filter_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f169,f53])).

fof(f169,plain,
    ( v2_struct_0(sK1)
    | l3_lattices(k7_filter_1(sK0,sK1)) ),
    inference(resolution,[],[f154,f55])).

fof(f154,plain,(
    ! [X1] :
      ( ~ l3_lattices(X1)
      | v2_struct_0(X1)
      | l3_lattices(k7_filter_1(sK0,X1)) ) ),
    inference(subsumption_resolution,[],[f152,f56])).

fof(f152,plain,(
    ! [X1] :
      ( v2_struct_0(sK0)
      | v2_struct_0(X1)
      | ~ l3_lattices(X1)
      | l3_lattices(k7_filter_1(sK0,X1)) ) ),
    inference(resolution,[],[f79,f58])).

fof(f118,plain,
    ( ~ spl2_6
    | ~ spl2_5
    | ~ spl2_1
    | spl2_2
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f113,f95,f90,f85,f81,f100,f115])).

fof(f113,plain,
    ( ~ v17_lattices(k7_filter_1(sK0,sK1))
    | ~ l3_lattices(k7_filter_1(sK0,sK1))
    | ~ spl2_1
    | spl2_2
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f112,f55])).

fof(f112,plain,
    ( ~ v17_lattices(k7_filter_1(sK0,sK1))
    | ~ l3_lattices(k7_filter_1(sK0,sK1))
    | ~ l3_lattices(sK1)
    | ~ spl2_1
    | spl2_2
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f111,f83])).

fof(f111,plain,
    ( ~ v17_lattices(k7_filter_1(sK0,sK1))
    | ~ l3_lattices(k7_filter_1(sK0,sK1))
    | ~ v17_lattices(sK1)
    | ~ l3_lattices(sK1)
    | spl2_2
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f110,f54])).

fof(f110,plain,
    ( ~ v17_lattices(k7_filter_1(sK0,sK1))
    | ~ l3_lattices(k7_filter_1(sK0,sK1))
    | ~ v10_lattices(sK1)
    | ~ v17_lattices(sK1)
    | ~ l3_lattices(sK1)
    | spl2_2
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f109,f53])).

fof(f109,plain,
    ( ~ v17_lattices(k7_filter_1(sK0,sK1))
    | ~ l3_lattices(k7_filter_1(sK0,sK1))
    | v2_struct_0(sK1)
    | ~ v10_lattices(sK1)
    | ~ v17_lattices(sK1)
    | ~ l3_lattices(sK1)
    | spl2_2
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f108,f58])).

fof(f108,plain,
    ( ~ v17_lattices(k7_filter_1(sK0,sK1))
    | ~ l3_lattices(k7_filter_1(sK0,sK1))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK1)
    | ~ v10_lattices(sK1)
    | ~ v17_lattices(sK1)
    | ~ l3_lattices(sK1)
    | spl2_2
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f107,f97])).

fof(f107,plain,
    ( ~ v17_lattices(k7_filter_1(sK0,sK1))
    | ~ l3_lattices(k7_filter_1(sK0,sK1))
    | ~ v17_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK1)
    | ~ v10_lattices(sK1)
    | ~ v17_lattices(sK1)
    | ~ l3_lattices(sK1)
    | spl2_2
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f106,f57])).

fof(f106,plain,
    ( ~ v17_lattices(k7_filter_1(sK0,sK1))
    | ~ l3_lattices(k7_filter_1(sK0,sK1))
    | ~ v10_lattices(sK0)
    | ~ v17_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK1)
    | ~ v10_lattices(sK1)
    | ~ v17_lattices(sK1)
    | ~ l3_lattices(sK1)
    | spl2_2
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f105,f56])).

fof(f105,plain,
    ( ~ v17_lattices(k7_filter_1(sK0,sK1))
    | ~ l3_lattices(k7_filter_1(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ v17_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK1)
    | ~ v10_lattices(sK1)
    | ~ v17_lattices(sK1)
    | ~ l3_lattices(sK1)
    | spl2_2
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f104,f92])).

fof(f104,plain,
    ( ~ v10_lattices(k7_filter_1(sK0,sK1))
    | ~ v17_lattices(k7_filter_1(sK0,sK1))
    | ~ l3_lattices(k7_filter_1(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ v17_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK1)
    | ~ v10_lattices(sK1)
    | ~ v17_lattices(sK1)
    | ~ l3_lattices(sK1)
    | spl2_2 ),
    inference(subsumption_resolution,[],[f52,f87])).

fof(f52,plain,
    ( v2_struct_0(k7_filter_1(sK0,sK1))
    | ~ v10_lattices(k7_filter_1(sK0,sK1))
    | ~ v17_lattices(k7_filter_1(sK0,sK1))
    | ~ l3_lattices(k7_filter_1(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ v17_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK1)
    | ~ v10_lattices(sK1)
    | ~ v17_lattices(sK1)
    | ~ l3_lattices(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f103,plain,
    ( spl2_4
    | spl2_5 ),
    inference(avatar_split_clause,[],[f42,f100,f95])).

fof(f42,plain,
    ( v17_lattices(k7_filter_1(sK0,sK1))
    | v17_lattices(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f98,plain,
    ( spl2_4
    | spl2_3 ),
    inference(avatar_split_clause,[],[f41,f90,f95])).

fof(f41,plain,
    ( v10_lattices(k7_filter_1(sK0,sK1))
    | v17_lattices(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f93,plain,
    ( spl2_1
    | spl2_3 ),
    inference(avatar_split_clause,[],[f25,f90,f81])).

fof(f25,plain,
    ( v10_lattices(k7_filter_1(sK0,sK1))
    | v17_lattices(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f88,plain,
    ( spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f24,f85,f81])).

fof(f24,plain,
    ( ~ v2_struct_0(k7_filter_1(sK0,sK1))
    | v17_lattices(sK1) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:52:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.42  % (3439)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.21/0.43  % (3431)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.21/0.43  % (3439)Refutation not found, incomplete strategy% (3439)------------------------------
% 0.21/0.43  % (3439)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (3439)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.44  
% 0.21/0.44  % (3439)Memory used [KB]: 5500
% 0.21/0.44  % (3439)Time elapsed: 0.027 s
% 0.21/0.44  % (3439)------------------------------
% 0.21/0.44  % (3439)------------------------------
% 0.21/0.45  % (3431)Refutation found. Thanks to Tanya!
% 0.21/0.45  % SZS status Theorem for theBenchmark
% 0.21/0.45  % SZS output start Proof for theBenchmark
% 0.21/0.45  fof(f2254,plain,(
% 0.21/0.45    $false),
% 0.21/0.45    inference(avatar_sat_refutation,[],[f88,f93,f98,f103,f118,f175,f307,f515,f551,f561,f769,f770,f779,f780,f964,f970,f1059,f1147,f1824,f1886,f1945,f1991,f2011,f2240])).
% 0.21/0.45  fof(f2240,plain,(
% 0.21/0.45    spl2_3 | ~spl2_4 | ~spl2_23),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f2239])).
% 0.21/0.45  fof(f2239,plain,(
% 0.21/0.45    $false | (spl2_3 | ~spl2_4 | ~spl2_23)),
% 0.21/0.45    inference(subsumption_resolution,[],[f2238,f55])).
% 0.21/0.45  fof(f55,plain,(
% 0.21/0.45    l3_lattices(sK1)),
% 0.21/0.45    inference(cnf_transformation,[],[f9])).
% 0.21/0.45  fof(f9,plain,(
% 0.21/0.45    ? [X0] : (? [X1] : (((l3_lattices(X1) & v17_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1) & l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) <~> (l3_lattices(k7_filter_1(X0,X1)) & v17_lattices(k7_filter_1(X0,X1)) & v10_lattices(k7_filter_1(X0,X1)) & ~v2_struct_0(k7_filter_1(X0,X1)))) & l3_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) & l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 0.21/0.45    inference(flattening,[],[f8])).
% 0.21/0.45  fof(f8,plain,(
% 0.21/0.45    ? [X0] : (? [X1] : (((l3_lattices(X1) & v17_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1) & l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) <~> (l3_lattices(k7_filter_1(X0,X1)) & v17_lattices(k7_filter_1(X0,X1)) & v10_lattices(k7_filter_1(X0,X1)) & ~v2_struct_0(k7_filter_1(X0,X1)))) & (l3_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1))) & (l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 0.21/0.45    inference(ennf_transformation,[],[f7])).
% 0.21/0.45  fof(f7,negated_conjecture,(
% 0.21/0.45    ~! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l3_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => ((l3_lattices(X1) & v17_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1) & l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) <=> (l3_lattices(k7_filter_1(X0,X1)) & v17_lattices(k7_filter_1(X0,X1)) & v10_lattices(k7_filter_1(X0,X1)) & ~v2_struct_0(k7_filter_1(X0,X1))))))),
% 0.21/0.45    inference(negated_conjecture,[],[f6])).
% 0.21/0.45  fof(f6,conjecture,(
% 0.21/0.45    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l3_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => ((l3_lattices(X1) & v17_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1) & l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) <=> (l3_lattices(k7_filter_1(X0,X1)) & v17_lattices(k7_filter_1(X0,X1)) & v10_lattices(k7_filter_1(X0,X1)) & ~v2_struct_0(k7_filter_1(X0,X1))))))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_filter_1)).
% 0.21/0.45  fof(f2238,plain,(
% 0.21/0.45    ~l3_lattices(sK1) | (spl2_3 | ~spl2_4 | ~spl2_23)),
% 0.21/0.45    inference(subsumption_resolution,[],[f2237,f513])).
% 0.21/0.45  fof(f513,plain,(
% 0.21/0.45    v11_lattices(sK1) | ~spl2_23),
% 0.21/0.45    inference(avatar_component_clause,[],[f512])).
% 0.21/0.45  fof(f512,plain,(
% 0.21/0.45    spl2_23 <=> v11_lattices(sK1)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 0.21/0.45  fof(f2237,plain,(
% 0.21/0.45    ~v11_lattices(sK1) | ~l3_lattices(sK1) | (spl2_3 | ~spl2_4)),
% 0.21/0.45    inference(subsumption_resolution,[],[f2236,f91])).
% 0.21/0.45  fof(f91,plain,(
% 0.21/0.45    ~v10_lattices(k7_filter_1(sK0,sK1)) | spl2_3),
% 0.21/0.45    inference(avatar_component_clause,[],[f90])).
% 0.21/0.45  fof(f90,plain,(
% 0.21/0.45    spl2_3 <=> v10_lattices(k7_filter_1(sK0,sK1))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.45  fof(f2236,plain,(
% 0.21/0.45    v10_lattices(k7_filter_1(sK0,sK1)) | ~v11_lattices(sK1) | ~l3_lattices(sK1) | ~spl2_4),
% 0.21/0.45    inference(subsumption_resolution,[],[f2228,f53])).
% 0.21/0.45  fof(f53,plain,(
% 0.21/0.45    ~v2_struct_0(sK1)),
% 0.21/0.45    inference(cnf_transformation,[],[f9])).
% 0.21/0.45  fof(f2228,plain,(
% 0.21/0.45    v2_struct_0(sK1) | v10_lattices(k7_filter_1(sK0,sK1)) | ~v11_lattices(sK1) | ~l3_lattices(sK1) | ~spl2_4),
% 0.21/0.45    inference(resolution,[],[f2227,f54])).
% 0.21/0.45  fof(f54,plain,(
% 0.21/0.45    v10_lattices(sK1)),
% 0.21/0.45    inference(cnf_transformation,[],[f9])).
% 0.21/0.45  fof(f2227,plain,(
% 0.21/0.45    ( ! [X1] : (~v10_lattices(X1) | v2_struct_0(X1) | v10_lattices(k7_filter_1(sK0,X1)) | ~v11_lattices(X1) | ~l3_lattices(X1)) ) | ~spl2_4),
% 0.21/0.45    inference(subsumption_resolution,[],[f438,f2010])).
% 0.21/0.45  fof(f2010,plain,(
% 0.21/0.45    v11_lattices(sK0) | ~spl2_4),
% 0.21/0.45    inference(subsumption_resolution,[],[f2009,f58])).
% 0.21/0.45  fof(f58,plain,(
% 0.21/0.45    l3_lattices(sK0)),
% 0.21/0.45    inference(cnf_transformation,[],[f9])).
% 0.21/0.45  fof(f2009,plain,(
% 0.21/0.45    ~l3_lattices(sK0) | v11_lattices(sK0) | ~spl2_4),
% 0.21/0.45    inference(subsumption_resolution,[],[f2006,f56])).
% 0.21/0.45  fof(f56,plain,(
% 0.21/0.45    ~v2_struct_0(sK0)),
% 0.21/0.45    inference(cnf_transformation,[],[f9])).
% 0.21/0.45  fof(f2006,plain,(
% 0.21/0.45    v2_struct_0(sK0) | ~l3_lattices(sK0) | v11_lattices(sK0) | ~spl2_4),
% 0.21/0.45    inference(resolution,[],[f97,f60])).
% 0.21/0.45  fof(f60,plain,(
% 0.21/0.45    ( ! [X0] : (~v17_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v11_lattices(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f13])).
% 0.21/0.45  fof(f13,plain,(
% 0.21/0.45    ! [X0] : ((v16_lattices(X0) & v15_lattices(X0) & v11_lattices(X0) & ~v2_struct_0(X0)) | ~v17_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 0.21/0.45    inference(flattening,[],[f12])).
% 0.21/0.45  fof(f12,plain,(
% 0.21/0.45    ! [X0] : (((v16_lattices(X0) & v15_lattices(X0) & v11_lattices(X0) & ~v2_struct_0(X0)) | (~v17_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 0.21/0.45    inference(ennf_transformation,[],[f1])).
% 0.21/0.45  fof(f1,axiom,(
% 0.21/0.45    ! [X0] : (l3_lattices(X0) => ((v17_lattices(X0) & ~v2_struct_0(X0)) => (v16_lattices(X0) & v15_lattices(X0) & v11_lattices(X0) & ~v2_struct_0(X0))))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_lattices)).
% 0.21/0.45  fof(f97,plain,(
% 0.21/0.45    v17_lattices(sK0) | ~spl2_4),
% 0.21/0.45    inference(avatar_component_clause,[],[f95])).
% 0.21/0.45  fof(f95,plain,(
% 0.21/0.45    spl2_4 <=> v17_lattices(sK0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.45  fof(f438,plain,(
% 0.21/0.45    ( ! [X1] : (v10_lattices(k7_filter_1(sK0,X1)) | ~v11_lattices(sK0) | v2_struct_0(X1) | ~v10_lattices(X1) | ~v11_lattices(X1) | ~l3_lattices(X1)) )),
% 0.21/0.45    inference(subsumption_resolution,[],[f212,f58])).
% 0.21/0.45  fof(f212,plain,(
% 0.21/0.45    ( ! [X1] : (v10_lattices(k7_filter_1(sK0,X1)) | ~v11_lattices(sK0) | ~l3_lattices(sK0) | v2_struct_0(X1) | ~v10_lattices(X1) | ~v11_lattices(X1) | ~l3_lattices(X1)) )),
% 0.21/0.45    inference(subsumption_resolution,[],[f207,f56])).
% 0.21/0.45  fof(f207,plain,(
% 0.21/0.45    ( ! [X1] : (v2_struct_0(sK0) | v10_lattices(k7_filter_1(sK0,X1)) | ~v11_lattices(sK0) | ~l3_lattices(sK0) | v2_struct_0(X1) | ~v10_lattices(X1) | ~v11_lattices(X1) | ~l3_lattices(X1)) )),
% 0.21/0.45    inference(resolution,[],[f75,f57])).
% 0.21/0.45  fof(f57,plain,(
% 0.21/0.45    v10_lattices(sK0)),
% 0.21/0.45    inference(cnf_transformation,[],[f9])).
% 0.21/0.45  fof(f75,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~v10_lattices(X0) | v2_struct_0(X0) | v10_lattices(k7_filter_1(X0,X1)) | ~v11_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X1) | ~v10_lattices(X1) | ~v11_lattices(X1) | ~l3_lattices(X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f17])).
% 0.21/0.45  fof(f17,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (((l3_lattices(X1) & v11_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1) & l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) <=> (l3_lattices(k7_filter_1(X0,X1)) & v11_lattices(k7_filter_1(X0,X1)) & v10_lattices(k7_filter_1(X0,X1)) & ~v2_struct_0(k7_filter_1(X0,X1)))) | ~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.45    inference(flattening,[],[f16])).
% 0.21/0.45  fof(f16,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (((l3_lattices(X1) & v11_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1) & l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) <=> (l3_lattices(k7_filter_1(X0,X1)) & v11_lattices(k7_filter_1(X0,X1)) & v10_lattices(k7_filter_1(X0,X1)) & ~v2_struct_0(k7_filter_1(X0,X1)))) | (~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1))) | (~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.45    inference(ennf_transformation,[],[f4])).
% 0.21/0.45  fof(f4,axiom,(
% 0.21/0.45    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l3_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => ((l3_lattices(X1) & v11_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1) & l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) <=> (l3_lattices(k7_filter_1(X0,X1)) & v11_lattices(k7_filter_1(X0,X1)) & v10_lattices(k7_filter_1(X0,X1)) & ~v2_struct_0(k7_filter_1(X0,X1))))))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_filter_1)).
% 0.21/0.45  fof(f2011,plain,(
% 0.21/0.45    spl2_20 | ~spl2_4),
% 0.21/0.45    inference(avatar_split_clause,[],[f2008,f95,f444])).
% 0.21/0.45  fof(f444,plain,(
% 0.21/0.45    spl2_20 <=> v15_lattices(sK0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 0.21/0.45  fof(f2008,plain,(
% 0.21/0.45    v15_lattices(sK0) | ~spl2_4),
% 0.21/0.45    inference(subsumption_resolution,[],[f2007,f58])).
% 0.21/0.45  fof(f2007,plain,(
% 0.21/0.45    ~l3_lattices(sK0) | v15_lattices(sK0) | ~spl2_4),
% 0.21/0.45    inference(subsumption_resolution,[],[f2005,f56])).
% 0.21/0.45  fof(f2005,plain,(
% 0.21/0.45    v2_struct_0(sK0) | ~l3_lattices(sK0) | v15_lattices(sK0) | ~spl2_4),
% 0.21/0.45    inference(resolution,[],[f97,f61])).
% 0.21/0.45  fof(f61,plain,(
% 0.21/0.45    ( ! [X0] : (~v17_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v15_lattices(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f13])).
% 0.21/0.45  fof(f1991,plain,(
% 0.21/0.45    ~spl2_2 | spl2_4),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f1990])).
% 0.21/0.45  fof(f1990,plain,(
% 0.21/0.45    $false | (~spl2_2 | spl2_4)),
% 0.21/0.45    inference(subsumption_resolution,[],[f1955,f96])).
% 0.21/0.45  fof(f96,plain,(
% 0.21/0.45    ~v17_lattices(sK0) | spl2_4),
% 0.21/0.45    inference(avatar_component_clause,[],[f95])).
% 0.21/0.45  fof(f1955,plain,(
% 0.21/0.45    v17_lattices(sK0) | ~spl2_2),
% 0.21/0.45    inference(subsumption_resolution,[],[f40,f86])).
% 0.21/0.45  fof(f86,plain,(
% 0.21/0.45    v2_struct_0(k7_filter_1(sK0,sK1)) | ~spl2_2),
% 0.21/0.45    inference(avatar_component_clause,[],[f85])).
% 0.21/0.45  fof(f85,plain,(
% 0.21/0.45    spl2_2 <=> v2_struct_0(k7_filter_1(sK0,sK1))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.45  fof(f40,plain,(
% 0.21/0.45    ~v2_struct_0(k7_filter_1(sK0,sK1)) | v17_lattices(sK0)),
% 0.21/0.45    inference(cnf_transformation,[],[f9])).
% 0.21/0.45  fof(f1945,plain,(
% 0.21/0.45    ~spl2_2 | ~spl2_4 | ~spl2_23),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f1944])).
% 0.21/0.45  fof(f1944,plain,(
% 0.21/0.45    $false | (~spl2_2 | ~spl2_4 | ~spl2_23)),
% 0.21/0.45    inference(subsumption_resolution,[],[f1943,f55])).
% 0.21/0.45  fof(f1943,plain,(
% 0.21/0.45    ~l3_lattices(sK1) | (~spl2_2 | ~spl2_4 | ~spl2_23)),
% 0.21/0.45    inference(subsumption_resolution,[],[f1942,f513])).
% 0.21/0.45  fof(f1942,plain,(
% 0.21/0.45    ~v11_lattices(sK1) | ~l3_lattices(sK1) | (~spl2_2 | ~spl2_4)),
% 0.21/0.45    inference(subsumption_resolution,[],[f1941,f54])).
% 0.21/0.45  fof(f1941,plain,(
% 0.21/0.45    ~v10_lattices(sK1) | ~v11_lattices(sK1) | ~l3_lattices(sK1) | (~spl2_2 | ~spl2_4)),
% 0.21/0.45    inference(subsumption_resolution,[],[f1940,f53])).
% 0.21/0.45  fof(f1940,plain,(
% 0.21/0.45    v2_struct_0(sK1) | ~v10_lattices(sK1) | ~v11_lattices(sK1) | ~l3_lattices(sK1) | (~spl2_2 | ~spl2_4)),
% 0.21/0.45    inference(subsumption_resolution,[],[f1939,f58])).
% 0.21/0.45  fof(f1939,plain,(
% 0.21/0.45    ~l3_lattices(sK0) | v2_struct_0(sK1) | ~v10_lattices(sK1) | ~v11_lattices(sK1) | ~l3_lattices(sK1) | (~spl2_2 | ~spl2_4)),
% 0.21/0.45    inference(subsumption_resolution,[],[f1938,f1089])).
% 0.21/0.45  fof(f1089,plain,(
% 0.21/0.45    v11_lattices(sK0) | ~spl2_4),
% 0.21/0.45    inference(subsumption_resolution,[],[f1088,f58])).
% 0.21/0.45  fof(f1088,plain,(
% 0.21/0.45    ~l3_lattices(sK0) | v11_lattices(sK0) | ~spl2_4),
% 0.21/0.45    inference(subsumption_resolution,[],[f1085,f56])).
% 0.21/0.45  fof(f1085,plain,(
% 0.21/0.45    v2_struct_0(sK0) | ~l3_lattices(sK0) | v11_lattices(sK0) | ~spl2_4),
% 0.21/0.45    inference(resolution,[],[f97,f60])).
% 0.21/0.45  fof(f1938,plain,(
% 0.21/0.45    ~v11_lattices(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK1) | ~v10_lattices(sK1) | ~v11_lattices(sK1) | ~l3_lattices(sK1) | ~spl2_2),
% 0.21/0.45    inference(subsumption_resolution,[],[f1937,f57])).
% 0.21/0.45  fof(f1937,plain,(
% 0.21/0.45    ~v10_lattices(sK0) | ~v11_lattices(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK1) | ~v10_lattices(sK1) | ~v11_lattices(sK1) | ~l3_lattices(sK1) | ~spl2_2),
% 0.21/0.45    inference(subsumption_resolution,[],[f1925,f56])).
% 0.21/0.45  fof(f1925,plain,(
% 0.21/0.45    v2_struct_0(sK0) | ~v10_lattices(sK0) | ~v11_lattices(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK1) | ~v10_lattices(sK1) | ~v11_lattices(sK1) | ~l3_lattices(sK1) | ~spl2_2),
% 0.21/0.45    inference(resolution,[],[f86,f74])).
% 0.21/0.45  fof(f74,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~v2_struct_0(k7_filter_1(X0,X1)) | v2_struct_0(X0) | ~v10_lattices(X0) | ~v11_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X1) | ~v10_lattices(X1) | ~v11_lattices(X1) | ~l3_lattices(X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f17])).
% 0.21/0.45  fof(f1886,plain,(
% 0.21/0.45    spl2_19 | ~spl2_4),
% 0.21/0.45    inference(avatar_split_clause,[],[f1885,f95,f440])).
% 0.21/0.45  fof(f440,plain,(
% 0.21/0.45    spl2_19 <=> v16_lattices(sK0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 0.21/0.45  fof(f1885,plain,(
% 0.21/0.45    v16_lattices(sK0) | ~spl2_4),
% 0.21/0.45    inference(subsumption_resolution,[],[f1884,f58])).
% 0.21/0.45  fof(f1884,plain,(
% 0.21/0.45    ~l3_lattices(sK0) | v16_lattices(sK0) | ~spl2_4),
% 0.21/0.45    inference(subsumption_resolution,[],[f1083,f56])).
% 0.21/0.45  fof(f1083,plain,(
% 0.21/0.45    v2_struct_0(sK0) | ~l3_lattices(sK0) | v16_lattices(sK0) | ~spl2_4),
% 0.21/0.45    inference(resolution,[],[f97,f62])).
% 0.21/0.45  fof(f62,plain,(
% 0.21/0.45    ( ! [X0] : (~v17_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v16_lattices(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f13])).
% 0.21/0.45  fof(f1824,plain,(
% 0.21/0.45    spl2_2 | spl2_5 | ~spl2_6 | ~spl2_14 | ~spl2_15 | ~spl2_19 | ~spl2_20 | ~spl2_35),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f1823])).
% 0.21/0.45  fof(f1823,plain,(
% 0.21/0.45    $false | (spl2_2 | spl2_5 | ~spl2_6 | ~spl2_14 | ~spl2_15 | ~spl2_19 | ~spl2_20 | ~spl2_35)),
% 0.21/0.45    inference(subsumption_resolution,[],[f1822,f55])).
% 0.21/0.45  fof(f1822,plain,(
% 0.21/0.45    ~l3_lattices(sK1) | (spl2_2 | spl2_5 | ~spl2_6 | ~spl2_14 | ~spl2_15 | ~spl2_19 | ~spl2_20 | ~spl2_35)),
% 0.21/0.45    inference(subsumption_resolution,[],[f1821,f379])).
% 0.21/0.45  fof(f379,plain,(
% 0.21/0.45    v16_lattices(sK1) | ~spl2_14),
% 0.21/0.45    inference(avatar_component_clause,[],[f378])).
% 0.21/0.45  fof(f378,plain,(
% 0.21/0.45    spl2_14 <=> v16_lattices(sK1)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.21/0.45  fof(f1821,plain,(
% 0.21/0.45    ~v16_lattices(sK1) | ~l3_lattices(sK1) | (spl2_2 | spl2_5 | ~spl2_6 | ~spl2_14 | ~spl2_15 | ~spl2_19 | ~spl2_20 | ~spl2_35)),
% 0.21/0.45    inference(subsumption_resolution,[],[f1820,f383])).
% 0.21/0.45  fof(f383,plain,(
% 0.21/0.45    v15_lattices(sK1) | ~spl2_15),
% 0.21/0.45    inference(avatar_component_clause,[],[f382])).
% 0.21/0.45  fof(f382,plain,(
% 0.21/0.45    spl2_15 <=> v15_lattices(sK1)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.21/0.45  fof(f1820,plain,(
% 0.21/0.45    ~v15_lattices(sK1) | ~v16_lattices(sK1) | ~l3_lattices(sK1) | (spl2_2 | spl2_5 | ~spl2_6 | ~spl2_14 | ~spl2_15 | ~spl2_19 | ~spl2_20 | ~spl2_35)),
% 0.21/0.45    inference(subsumption_resolution,[],[f1819,f1778])).
% 0.21/0.45  fof(f1778,plain,(
% 0.21/0.45    ~v15_lattices(k7_filter_1(sK0,sK1)) | (spl2_2 | spl2_5 | ~spl2_6 | ~spl2_14 | ~spl2_15 | ~spl2_19 | ~spl2_20 | ~spl2_35)),
% 0.21/0.45    inference(subsumption_resolution,[],[f1777,f101])).
% 0.21/0.45  fof(f101,plain,(
% 0.21/0.45    ~v17_lattices(k7_filter_1(sK0,sK1)) | spl2_5),
% 0.21/0.45    inference(avatar_component_clause,[],[f100])).
% 0.21/0.45  fof(f100,plain,(
% 0.21/0.45    spl2_5 <=> v17_lattices(k7_filter_1(sK0,sK1))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.45  fof(f1777,plain,(
% 0.21/0.45    ~v15_lattices(k7_filter_1(sK0,sK1)) | v17_lattices(k7_filter_1(sK0,sK1)) | (spl2_2 | ~spl2_6 | ~spl2_14 | ~spl2_15 | ~spl2_19 | ~spl2_20 | ~spl2_35)),
% 0.21/0.45    inference(subsumption_resolution,[],[f1776,f116])).
% 0.21/0.45  fof(f116,plain,(
% 0.21/0.45    l3_lattices(k7_filter_1(sK0,sK1)) | ~spl2_6),
% 0.21/0.45    inference(avatar_component_clause,[],[f115])).
% 0.21/0.45  fof(f115,plain,(
% 0.21/0.45    spl2_6 <=> l3_lattices(k7_filter_1(sK0,sK1))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.45  fof(f1776,plain,(
% 0.21/0.45    ~v15_lattices(k7_filter_1(sK0,sK1)) | ~l3_lattices(k7_filter_1(sK0,sK1)) | v17_lattices(k7_filter_1(sK0,sK1)) | (spl2_2 | ~spl2_14 | ~spl2_15 | ~spl2_19 | ~spl2_20 | ~spl2_35)),
% 0.21/0.45    inference(subsumption_resolution,[],[f1775,f1113])).
% 0.21/0.45  fof(f1113,plain,(
% 0.21/0.45    v11_lattices(k7_filter_1(sK0,sK1)) | ~spl2_35),
% 0.21/0.45    inference(avatar_component_clause,[],[f1112])).
% 0.21/0.45  fof(f1112,plain,(
% 0.21/0.45    spl2_35 <=> v11_lattices(k7_filter_1(sK0,sK1))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_35])])).
% 0.21/0.45  fof(f1775,plain,(
% 0.21/0.45    ~v11_lattices(k7_filter_1(sK0,sK1)) | ~v15_lattices(k7_filter_1(sK0,sK1)) | ~l3_lattices(k7_filter_1(sK0,sK1)) | v17_lattices(k7_filter_1(sK0,sK1)) | (spl2_2 | ~spl2_14 | ~spl2_15 | ~spl2_19 | ~spl2_20)),
% 0.21/0.45    inference(subsumption_resolution,[],[f1774,f87])).
% 0.21/0.45  fof(f87,plain,(
% 0.21/0.45    ~v2_struct_0(k7_filter_1(sK0,sK1)) | spl2_2),
% 0.21/0.45    inference(avatar_component_clause,[],[f85])).
% 0.21/0.45  fof(f1774,plain,(
% 0.21/0.45    v2_struct_0(k7_filter_1(sK0,sK1)) | ~v11_lattices(k7_filter_1(sK0,sK1)) | ~v15_lattices(k7_filter_1(sK0,sK1)) | ~l3_lattices(k7_filter_1(sK0,sK1)) | v17_lattices(k7_filter_1(sK0,sK1)) | (~spl2_14 | ~spl2_15 | ~spl2_19 | ~spl2_20)),
% 0.21/0.45    inference(resolution,[],[f1749,f59])).
% 0.21/0.45  fof(f59,plain,(
% 0.21/0.45    ( ! [X0] : (~v16_lattices(X0) | v2_struct_0(X0) | ~v11_lattices(X0) | ~v15_lattices(X0) | ~l3_lattices(X0) | v17_lattices(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f11])).
% 0.21/0.45  fof(f11,plain,(
% 0.21/0.45    ! [X0] : ((v17_lattices(X0) & ~v2_struct_0(X0)) | ~v16_lattices(X0) | ~v15_lattices(X0) | ~v11_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 0.21/0.45    inference(flattening,[],[f10])).
% 0.21/0.45  fof(f10,plain,(
% 0.21/0.45    ! [X0] : (((v17_lattices(X0) & ~v2_struct_0(X0)) | (~v16_lattices(X0) | ~v15_lattices(X0) | ~v11_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 0.21/0.45    inference(ennf_transformation,[],[f2])).
% 0.21/0.45  fof(f2,axiom,(
% 0.21/0.45    ! [X0] : (l3_lattices(X0) => ((v16_lattices(X0) & v15_lattices(X0) & v11_lattices(X0) & ~v2_struct_0(X0)) => (v17_lattices(X0) & ~v2_struct_0(X0))))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc6_lattices)).
% 0.21/0.45  fof(f1749,plain,(
% 0.21/0.45    v16_lattices(k7_filter_1(sK0,sK1)) | (~spl2_14 | ~spl2_15 | ~spl2_19 | ~spl2_20)),
% 0.21/0.45    inference(subsumption_resolution,[],[f1748,f55])).
% 0.21/0.45  fof(f1748,plain,(
% 0.21/0.45    v16_lattices(k7_filter_1(sK0,sK1)) | ~l3_lattices(sK1) | (~spl2_14 | ~spl2_15 | ~spl2_19 | ~spl2_20)),
% 0.21/0.45    inference(subsumption_resolution,[],[f1747,f379])).
% 0.21/0.45  fof(f1747,plain,(
% 0.21/0.45    v16_lattices(k7_filter_1(sK0,sK1)) | ~v16_lattices(sK1) | ~l3_lattices(sK1) | (~spl2_15 | ~spl2_19 | ~spl2_20)),
% 0.21/0.45    inference(subsumption_resolution,[],[f1746,f383])).
% 0.21/0.45  fof(f1746,plain,(
% 0.21/0.45    v16_lattices(k7_filter_1(sK0,sK1)) | ~v15_lattices(sK1) | ~v16_lattices(sK1) | ~l3_lattices(sK1) | (~spl2_19 | ~spl2_20)),
% 0.21/0.45    inference(subsumption_resolution,[],[f1732,f53])).
% 0.21/0.45  fof(f1732,plain,(
% 0.21/0.45    v2_struct_0(sK1) | v16_lattices(k7_filter_1(sK0,sK1)) | ~v15_lattices(sK1) | ~v16_lattices(sK1) | ~l3_lattices(sK1) | (~spl2_19 | ~spl2_20)),
% 0.21/0.45    inference(resolution,[],[f1731,f54])).
% 0.21/0.45  fof(f1731,plain,(
% 0.21/0.45    ( ! [X1] : (~v10_lattices(X1) | v2_struct_0(X1) | v16_lattices(k7_filter_1(sK0,X1)) | ~v15_lattices(X1) | ~v16_lattices(X1) | ~l3_lattices(X1)) ) | (~spl2_19 | ~spl2_20)),
% 0.21/0.45    inference(subsumption_resolution,[],[f1730,f441])).
% 0.21/0.45  fof(f441,plain,(
% 0.21/0.45    v16_lattices(sK0) | ~spl2_19),
% 0.21/0.45    inference(avatar_component_clause,[],[f440])).
% 0.21/0.45  fof(f1730,plain,(
% 0.21/0.45    ( ! [X1] : (v16_lattices(k7_filter_1(sK0,X1)) | ~v16_lattices(sK0) | v2_struct_0(X1) | ~v10_lattices(X1) | ~v15_lattices(X1) | ~v16_lattices(X1) | ~l3_lattices(X1)) ) | ~spl2_20),
% 0.21/0.45    inference(subsumption_resolution,[],[f961,f445])).
% 0.21/0.45  fof(f445,plain,(
% 0.21/0.45    v15_lattices(sK0) | ~spl2_20),
% 0.21/0.45    inference(avatar_component_clause,[],[f444])).
% 0.21/0.45  fof(f961,plain,(
% 0.21/0.45    ( ! [X1] : (v16_lattices(k7_filter_1(sK0,X1)) | ~v15_lattices(sK0) | ~v16_lattices(sK0) | v2_struct_0(X1) | ~v10_lattices(X1) | ~v15_lattices(X1) | ~v16_lattices(X1) | ~l3_lattices(X1)) )),
% 0.21/0.45    inference(subsumption_resolution,[],[f960,f58])).
% 0.21/0.45  fof(f960,plain,(
% 0.21/0.45    ( ! [X1] : (v16_lattices(k7_filter_1(sK0,X1)) | ~v15_lattices(sK0) | ~v16_lattices(sK0) | ~l3_lattices(sK0) | v2_struct_0(X1) | ~v10_lattices(X1) | ~v15_lattices(X1) | ~v16_lattices(X1) | ~l3_lattices(X1)) )),
% 0.21/0.45    inference(subsumption_resolution,[],[f456,f56])).
% 0.21/0.45  fof(f456,plain,(
% 0.21/0.45    ( ! [X1] : (v2_struct_0(sK0) | v16_lattices(k7_filter_1(sK0,X1)) | ~v15_lattices(sK0) | ~v16_lattices(sK0) | ~l3_lattices(sK0) | v2_struct_0(X1) | ~v10_lattices(X1) | ~v15_lattices(X1) | ~v16_lattices(X1) | ~l3_lattices(X1)) )),
% 0.21/0.45    inference(resolution,[],[f70,f57])).
% 0.21/0.45  fof(f70,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~v10_lattices(X0) | v2_struct_0(X0) | v16_lattices(k7_filter_1(X0,X1)) | ~v15_lattices(X0) | ~v16_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X1) | ~v10_lattices(X1) | ~v15_lattices(X1) | ~v16_lattices(X1) | ~l3_lattices(X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f15])).
% 0.21/0.45  fof(f15,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (((l3_lattices(X1) & v16_lattices(X1) & v15_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1) & l3_lattices(X0) & v16_lattices(X0) & v15_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) <=> (l3_lattices(k7_filter_1(X0,X1)) & v16_lattices(k7_filter_1(X0,X1)) & v15_lattices(k7_filter_1(X0,X1)) & v10_lattices(k7_filter_1(X0,X1)) & ~v2_struct_0(k7_filter_1(X0,X1)))) | ~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.45    inference(flattening,[],[f14])).
% 0.21/0.45  fof(f14,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (((l3_lattices(X1) & v16_lattices(X1) & v15_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1) & l3_lattices(X0) & v16_lattices(X0) & v15_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) <=> (l3_lattices(k7_filter_1(X0,X1)) & v16_lattices(k7_filter_1(X0,X1)) & v15_lattices(k7_filter_1(X0,X1)) & v10_lattices(k7_filter_1(X0,X1)) & ~v2_struct_0(k7_filter_1(X0,X1)))) | (~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1))) | (~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.45    inference(ennf_transformation,[],[f5])).
% 0.21/0.45  fof(f5,axiom,(
% 0.21/0.45    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l3_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => ((l3_lattices(X1) & v16_lattices(X1) & v15_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1) & l3_lattices(X0) & v16_lattices(X0) & v15_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) <=> (l3_lattices(k7_filter_1(X0,X1)) & v16_lattices(k7_filter_1(X0,X1)) & v15_lattices(k7_filter_1(X0,X1)) & v10_lattices(k7_filter_1(X0,X1)) & ~v2_struct_0(k7_filter_1(X0,X1))))))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_filter_1)).
% 0.21/0.45  fof(f1819,plain,(
% 0.21/0.45    v15_lattices(k7_filter_1(sK0,sK1)) | ~v15_lattices(sK1) | ~v16_lattices(sK1) | ~l3_lattices(sK1) | (~spl2_19 | ~spl2_20)),
% 0.21/0.45    inference(subsumption_resolution,[],[f1805,f53])).
% 0.21/0.45  fof(f1805,plain,(
% 0.21/0.45    v2_struct_0(sK1) | v15_lattices(k7_filter_1(sK0,sK1)) | ~v15_lattices(sK1) | ~v16_lattices(sK1) | ~l3_lattices(sK1) | (~spl2_19 | ~spl2_20)),
% 0.21/0.45    inference(resolution,[],[f1801,f54])).
% 0.21/0.45  fof(f1801,plain,(
% 0.21/0.45    ( ! [X1] : (~v10_lattices(X1) | v2_struct_0(X1) | v15_lattices(k7_filter_1(sK0,X1)) | ~v15_lattices(X1) | ~v16_lattices(X1) | ~l3_lattices(X1)) ) | (~spl2_19 | ~spl2_20)),
% 0.21/0.45    inference(subsumption_resolution,[],[f1800,f441])).
% 0.21/0.45  fof(f1800,plain,(
% 0.21/0.45    ( ! [X1] : (v15_lattices(k7_filter_1(sK0,X1)) | ~v16_lattices(sK0) | v2_struct_0(X1) | ~v10_lattices(X1) | ~v15_lattices(X1) | ~v16_lattices(X1) | ~l3_lattices(X1)) ) | ~spl2_20),
% 0.21/0.45    inference(subsumption_resolution,[],[f963,f445])).
% 0.21/0.45  fof(f963,plain,(
% 0.21/0.45    ( ! [X1] : (v15_lattices(k7_filter_1(sK0,X1)) | ~v15_lattices(sK0) | ~v16_lattices(sK0) | v2_struct_0(X1) | ~v10_lattices(X1) | ~v15_lattices(X1) | ~v16_lattices(X1) | ~l3_lattices(X1)) )),
% 0.21/0.45    inference(subsumption_resolution,[],[f962,f58])).
% 0.21/0.45  fof(f962,plain,(
% 0.21/0.45    ( ! [X1] : (v15_lattices(k7_filter_1(sK0,X1)) | ~v15_lattices(sK0) | ~v16_lattices(sK0) | ~l3_lattices(sK0) | v2_struct_0(X1) | ~v10_lattices(X1) | ~v15_lattices(X1) | ~v16_lattices(X1) | ~l3_lattices(X1)) )),
% 0.21/0.45    inference(subsumption_resolution,[],[f449,f56])).
% 0.21/0.45  fof(f449,plain,(
% 0.21/0.45    ( ! [X1] : (v2_struct_0(sK0) | v15_lattices(k7_filter_1(sK0,X1)) | ~v15_lattices(sK0) | ~v16_lattices(sK0) | ~l3_lattices(sK0) | v2_struct_0(X1) | ~v10_lattices(X1) | ~v15_lattices(X1) | ~v16_lattices(X1) | ~l3_lattices(X1)) )),
% 0.21/0.45    inference(resolution,[],[f69,f57])).
% 0.21/0.45  fof(f69,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~v10_lattices(X0) | v2_struct_0(X0) | v15_lattices(k7_filter_1(X0,X1)) | ~v15_lattices(X0) | ~v16_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X1) | ~v10_lattices(X1) | ~v15_lattices(X1) | ~v16_lattices(X1) | ~l3_lattices(X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f15])).
% 0.21/0.45  fof(f1147,plain,(
% 0.21/0.45    spl2_35 | ~spl2_4 | ~spl2_23),
% 0.21/0.45    inference(avatar_split_clause,[],[f1146,f512,f95,f1112])).
% 0.21/0.45  fof(f1146,plain,(
% 0.21/0.45    v11_lattices(k7_filter_1(sK0,sK1)) | (~spl2_4 | ~spl2_23)),
% 0.21/0.45    inference(subsumption_resolution,[],[f1145,f55])).
% 0.21/0.45  fof(f1145,plain,(
% 0.21/0.45    v11_lattices(k7_filter_1(sK0,sK1)) | ~l3_lattices(sK1) | (~spl2_4 | ~spl2_23)),
% 0.21/0.45    inference(subsumption_resolution,[],[f1128,f513])).
% 0.21/0.45  fof(f1128,plain,(
% 0.21/0.45    v11_lattices(k7_filter_1(sK0,sK1)) | ~v11_lattices(sK1) | ~l3_lattices(sK1) | ~spl2_4),
% 0.21/0.45    inference(subsumption_resolution,[],[f1121,f53])).
% 0.21/0.45  fof(f1121,plain,(
% 0.21/0.45    v2_struct_0(sK1) | v11_lattices(k7_filter_1(sK0,sK1)) | ~v11_lattices(sK1) | ~l3_lattices(sK1) | ~spl2_4),
% 0.21/0.45    inference(resolution,[],[f1120,f54])).
% 0.21/0.45  fof(f1120,plain,(
% 0.21/0.45    ( ! [X1] : (~v10_lattices(X1) | v2_struct_0(X1) | v11_lattices(k7_filter_1(sK0,X1)) | ~v11_lattices(X1) | ~l3_lattices(X1)) ) | ~spl2_4),
% 0.21/0.45    inference(subsumption_resolution,[],[f437,f1089])).
% 0.21/0.45  fof(f437,plain,(
% 0.21/0.45    ( ! [X1] : (v11_lattices(k7_filter_1(sK0,X1)) | ~v11_lattices(sK0) | v2_struct_0(X1) | ~v10_lattices(X1) | ~v11_lattices(X1) | ~l3_lattices(X1)) )),
% 0.21/0.45    inference(subsumption_resolution,[],[f269,f58])).
% 0.21/0.45  fof(f269,plain,(
% 0.21/0.45    ( ! [X1] : (v11_lattices(k7_filter_1(sK0,X1)) | ~v11_lattices(sK0) | ~l3_lattices(sK0) | v2_struct_0(X1) | ~v10_lattices(X1) | ~v11_lattices(X1) | ~l3_lattices(X1)) )),
% 0.21/0.45    inference(subsumption_resolution,[],[f264,f56])).
% 0.21/0.45  fof(f264,plain,(
% 0.21/0.45    ( ! [X1] : (v2_struct_0(sK0) | v11_lattices(k7_filter_1(sK0,X1)) | ~v11_lattices(sK0) | ~l3_lattices(sK0) | v2_struct_0(X1) | ~v10_lattices(X1) | ~v11_lattices(X1) | ~l3_lattices(X1)) )),
% 0.21/0.45    inference(resolution,[],[f76,f57])).
% 0.21/0.45  fof(f76,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~v10_lattices(X0) | v2_struct_0(X0) | v11_lattices(k7_filter_1(X0,X1)) | ~v11_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X1) | ~v10_lattices(X1) | ~v11_lattices(X1) | ~l3_lattices(X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f17])).
% 0.21/0.45  fof(f1059,plain,(
% 0.21/0.45    spl2_2 | ~spl2_3 | ~spl2_5 | ~spl2_6 | spl2_20),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f1058])).
% 0.21/0.45  fof(f1058,plain,(
% 0.21/0.45    $false | (spl2_2 | ~spl2_3 | ~spl2_5 | ~spl2_6 | spl2_20)),
% 0.21/0.45    inference(subsumption_resolution,[],[f1057,f446])).
% 0.21/0.45  fof(f446,plain,(
% 0.21/0.45    ~v15_lattices(sK0) | spl2_20),
% 0.21/0.45    inference(avatar_component_clause,[],[f444])).
% 0.21/0.45  fof(f1057,plain,(
% 0.21/0.45    v15_lattices(sK0) | (spl2_2 | ~spl2_3 | ~spl2_5 | ~spl2_6)),
% 0.21/0.45    inference(subsumption_resolution,[],[f1056,f564])).
% 0.21/0.45  fof(f564,plain,(
% 0.21/0.45    v16_lattices(k7_filter_1(sK0,sK1)) | (spl2_2 | ~spl2_5 | ~spl2_6)),
% 0.21/0.45    inference(subsumption_resolution,[],[f476,f87])).
% 0.21/0.45  fof(f476,plain,(
% 0.21/0.45    v2_struct_0(k7_filter_1(sK0,sK1)) | v16_lattices(k7_filter_1(sK0,sK1)) | (~spl2_5 | ~spl2_6)),
% 0.21/0.45    inference(subsumption_resolution,[],[f325,f116])).
% 0.21/0.45  fof(f325,plain,(
% 0.21/0.45    v2_struct_0(k7_filter_1(sK0,sK1)) | ~l3_lattices(k7_filter_1(sK0,sK1)) | v16_lattices(k7_filter_1(sK0,sK1)) | ~spl2_5),
% 0.21/0.45    inference(resolution,[],[f102,f62])).
% 0.21/0.45  fof(f102,plain,(
% 0.21/0.45    v17_lattices(k7_filter_1(sK0,sK1)) | ~spl2_5),
% 0.21/0.45    inference(avatar_component_clause,[],[f100])).
% 0.21/0.45  fof(f1056,plain,(
% 0.21/0.45    ~v16_lattices(k7_filter_1(sK0,sK1)) | v15_lattices(sK0) | (spl2_2 | ~spl2_3 | ~spl2_5 | ~spl2_6)),
% 0.21/0.45    inference(subsumption_resolution,[],[f1055,f563])).
% 0.21/0.45  fof(f563,plain,(
% 0.21/0.45    v15_lattices(k7_filter_1(sK0,sK1)) | (spl2_2 | ~spl2_5 | ~spl2_6)),
% 0.21/0.45    inference(subsumption_resolution,[],[f475,f87])).
% 0.21/0.45  fof(f475,plain,(
% 0.21/0.45    v2_struct_0(k7_filter_1(sK0,sK1)) | v15_lattices(k7_filter_1(sK0,sK1)) | (~spl2_5 | ~spl2_6)),
% 0.21/0.45    inference(subsumption_resolution,[],[f326,f116])).
% 0.21/0.45  fof(f326,plain,(
% 0.21/0.45    v2_struct_0(k7_filter_1(sK0,sK1)) | ~l3_lattices(k7_filter_1(sK0,sK1)) | v15_lattices(k7_filter_1(sK0,sK1)) | ~spl2_5),
% 0.21/0.45    inference(resolution,[],[f102,f61])).
% 0.21/0.45  fof(f1055,plain,(
% 0.21/0.45    ~v15_lattices(k7_filter_1(sK0,sK1)) | ~v16_lattices(k7_filter_1(sK0,sK1)) | v15_lattices(sK0) | (spl2_2 | ~spl2_3)),
% 0.21/0.45    inference(subsumption_resolution,[],[f1054,f56])).
% 0.21/0.45  fof(f1054,plain,(
% 0.21/0.45    v2_struct_0(sK0) | ~v15_lattices(k7_filter_1(sK0,sK1)) | ~v16_lattices(k7_filter_1(sK0,sK1)) | v15_lattices(sK0) | (spl2_2 | ~spl2_3)),
% 0.21/0.45    inference(subsumption_resolution,[],[f1053,f87])).
% 0.21/0.45  fof(f1053,plain,(
% 0.21/0.45    v2_struct_0(k7_filter_1(sK0,sK1)) | v2_struct_0(sK0) | ~v15_lattices(k7_filter_1(sK0,sK1)) | ~v16_lattices(k7_filter_1(sK0,sK1)) | v15_lattices(sK0) | ~spl2_3),
% 0.21/0.45    inference(subsumption_resolution,[],[f1052,f55])).
% 0.21/0.45  fof(f1052,plain,(
% 0.21/0.45    ~l3_lattices(sK1) | v2_struct_0(k7_filter_1(sK0,sK1)) | v2_struct_0(sK0) | ~v15_lattices(k7_filter_1(sK0,sK1)) | ~v16_lattices(k7_filter_1(sK0,sK1)) | v15_lattices(sK0) | ~spl2_3),
% 0.21/0.45    inference(subsumption_resolution,[],[f1051,f54])).
% 0.21/0.45  fof(f1051,plain,(
% 0.21/0.45    ~v10_lattices(sK1) | ~l3_lattices(sK1) | v2_struct_0(k7_filter_1(sK0,sK1)) | v2_struct_0(sK0) | ~v15_lattices(k7_filter_1(sK0,sK1)) | ~v16_lattices(k7_filter_1(sK0,sK1)) | v15_lattices(sK0) | ~spl2_3),
% 0.21/0.45    inference(subsumption_resolution,[],[f1050,f53])).
% 0.21/0.45  fof(f1050,plain,(
% 0.21/0.45    v2_struct_0(sK1) | ~v10_lattices(sK1) | ~l3_lattices(sK1) | v2_struct_0(k7_filter_1(sK0,sK1)) | v2_struct_0(sK0) | ~v15_lattices(k7_filter_1(sK0,sK1)) | ~v16_lattices(k7_filter_1(sK0,sK1)) | v15_lattices(sK0) | ~spl2_3),
% 0.21/0.45    inference(subsumption_resolution,[],[f1049,f58])).
% 0.21/0.45  fof(f1049,plain,(
% 0.21/0.45    ~l3_lattices(sK0) | v2_struct_0(sK1) | ~v10_lattices(sK1) | ~l3_lattices(sK1) | v2_struct_0(k7_filter_1(sK0,sK1)) | v2_struct_0(sK0) | ~v15_lattices(k7_filter_1(sK0,sK1)) | ~v16_lattices(k7_filter_1(sK0,sK1)) | v15_lattices(sK0) | ~spl2_3),
% 0.21/0.45    inference(subsumption_resolution,[],[f1042,f57])).
% 0.21/0.45  fof(f1042,plain,(
% 0.21/0.45    ~v10_lattices(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK1) | ~v10_lattices(sK1) | ~l3_lattices(sK1) | v2_struct_0(k7_filter_1(sK0,sK1)) | v2_struct_0(sK0) | ~v15_lattices(k7_filter_1(sK0,sK1)) | ~v16_lattices(k7_filter_1(sK0,sK1)) | v15_lattices(sK0) | ~spl2_3),
% 0.21/0.45    inference(resolution,[],[f1009,f92])).
% 0.21/0.45  fof(f92,plain,(
% 0.21/0.45    v10_lattices(k7_filter_1(sK0,sK1)) | ~spl2_3),
% 0.21/0.45    inference(avatar_component_clause,[],[f90])).
% 0.21/0.45  fof(f1009,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~v10_lattices(k7_filter_1(X0,X1)) | ~v10_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X1) | ~v10_lattices(X1) | ~l3_lattices(X1) | v2_struct_0(k7_filter_1(X0,X1)) | v2_struct_0(X0) | ~v15_lattices(k7_filter_1(X0,X1)) | ~v16_lattices(k7_filter_1(X0,X1)) | v15_lattices(X0)) )),
% 0.21/0.45    inference(subsumption_resolution,[],[f66,f79])).
% 0.21/0.45  fof(f79,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~l3_lattices(X0) | v2_struct_0(X0) | v2_struct_0(X1) | ~l3_lattices(X1) | l3_lattices(k7_filter_1(X0,X1))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f19])).
% 0.21/0.45  fof(f19,plain,(
% 0.21/0.45    ! [X0,X1] : ((l3_lattices(k7_filter_1(X0,X1)) & v3_lattices(k7_filter_1(X0,X1))) | ~l3_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.45    inference(flattening,[],[f18])).
% 0.21/0.45  fof(f18,plain,(
% 0.21/0.45    ! [X0,X1] : ((l3_lattices(k7_filter_1(X0,X1)) & v3_lattices(k7_filter_1(X0,X1))) | (~l3_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.45    inference(ennf_transformation,[],[f3])).
% 0.21/0.45  fof(f3,axiom,(
% 0.21/0.45    ! [X0,X1] : ((l3_lattices(X1) & ~v2_struct_0(X1) & l3_lattices(X0) & ~v2_struct_0(X0)) => (l3_lattices(k7_filter_1(X0,X1)) & v3_lattices(k7_filter_1(X0,X1))))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_filter_1)).
% 0.21/0.45  fof(f66,plain,(
% 0.21/0.45    ( ! [X0,X1] : (v2_struct_0(X0) | ~v10_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X1) | ~v10_lattices(X1) | ~l3_lattices(X1) | v2_struct_0(k7_filter_1(X0,X1)) | ~v10_lattices(k7_filter_1(X0,X1)) | ~v15_lattices(k7_filter_1(X0,X1)) | ~v16_lattices(k7_filter_1(X0,X1)) | ~l3_lattices(k7_filter_1(X0,X1)) | v15_lattices(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f15])).
% 0.21/0.45  fof(f970,plain,(
% 0.21/0.45    ~spl2_20 | spl2_2 | ~spl2_3 | spl2_4 | ~spl2_5 | ~spl2_6 | ~spl2_19),
% 0.21/0.45    inference(avatar_split_clause,[],[f969,f440,f115,f100,f95,f90,f85,f444])).
% 0.21/0.45  fof(f969,plain,(
% 0.21/0.45    ~v15_lattices(sK0) | (spl2_2 | ~spl2_3 | spl2_4 | ~spl2_5 | ~spl2_6 | ~spl2_19)),
% 0.21/0.45    inference(subsumption_resolution,[],[f968,f96])).
% 0.21/0.45  fof(f968,plain,(
% 0.21/0.45    ~v15_lattices(sK0) | v17_lattices(sK0) | (spl2_2 | ~spl2_3 | ~spl2_5 | ~spl2_6 | ~spl2_19)),
% 0.21/0.45    inference(subsumption_resolution,[],[f967,f58])).
% 0.21/0.45  fof(f967,plain,(
% 0.21/0.45    ~v15_lattices(sK0) | ~l3_lattices(sK0) | v17_lattices(sK0) | (spl2_2 | ~spl2_3 | ~spl2_5 | ~spl2_6 | ~spl2_19)),
% 0.21/0.45    inference(subsumption_resolution,[],[f966,f591])).
% 0.21/0.45  fof(f591,plain,(
% 0.21/0.45    v11_lattices(sK0) | (spl2_2 | ~spl2_3 | ~spl2_5 | ~spl2_6)),
% 0.21/0.45    inference(subsumption_resolution,[],[f590,f562])).
% 0.21/0.45  fof(f562,plain,(
% 0.21/0.45    v11_lattices(k7_filter_1(sK0,sK1)) | (spl2_2 | ~spl2_5 | ~spl2_6)),
% 0.21/0.45    inference(subsumption_resolution,[],[f474,f87])).
% 0.21/0.45  fof(f474,plain,(
% 0.21/0.45    v2_struct_0(k7_filter_1(sK0,sK1)) | v11_lattices(k7_filter_1(sK0,sK1)) | (~spl2_5 | ~spl2_6)),
% 0.21/0.45    inference(subsumption_resolution,[],[f327,f116])).
% 0.21/0.45  fof(f327,plain,(
% 0.21/0.45    v2_struct_0(k7_filter_1(sK0,sK1)) | ~l3_lattices(k7_filter_1(sK0,sK1)) | v11_lattices(k7_filter_1(sK0,sK1)) | ~spl2_5),
% 0.21/0.45    inference(resolution,[],[f102,f60])).
% 0.21/0.45  fof(f590,plain,(
% 0.21/0.45    ~v11_lattices(k7_filter_1(sK0,sK1)) | v11_lattices(sK0) | (spl2_2 | ~spl2_3)),
% 0.21/0.45    inference(subsumption_resolution,[],[f589,f56])).
% 0.21/0.45  fof(f589,plain,(
% 0.21/0.45    v2_struct_0(sK0) | ~v11_lattices(k7_filter_1(sK0,sK1)) | v11_lattices(sK0) | (spl2_2 | ~spl2_3)),
% 0.21/0.45    inference(subsumption_resolution,[],[f588,f87])).
% 0.21/0.45  fof(f588,plain,(
% 0.21/0.45    v2_struct_0(k7_filter_1(sK0,sK1)) | v2_struct_0(sK0) | ~v11_lattices(k7_filter_1(sK0,sK1)) | v11_lattices(sK0) | ~spl2_3),
% 0.21/0.45    inference(subsumption_resolution,[],[f587,f55])).
% 0.21/0.45  fof(f587,plain,(
% 0.21/0.45    ~l3_lattices(sK1) | v2_struct_0(k7_filter_1(sK0,sK1)) | v2_struct_0(sK0) | ~v11_lattices(k7_filter_1(sK0,sK1)) | v11_lattices(sK0) | ~spl2_3),
% 0.21/0.45    inference(subsumption_resolution,[],[f586,f54])).
% 0.21/0.45  fof(f586,plain,(
% 0.21/0.45    ~v10_lattices(sK1) | ~l3_lattices(sK1) | v2_struct_0(k7_filter_1(sK0,sK1)) | v2_struct_0(sK0) | ~v11_lattices(k7_filter_1(sK0,sK1)) | v11_lattices(sK0) | ~spl2_3),
% 0.21/0.45    inference(subsumption_resolution,[],[f585,f53])).
% 0.21/0.45  fof(f585,plain,(
% 0.21/0.45    v2_struct_0(sK1) | ~v10_lattices(sK1) | ~l3_lattices(sK1) | v2_struct_0(k7_filter_1(sK0,sK1)) | v2_struct_0(sK0) | ~v11_lattices(k7_filter_1(sK0,sK1)) | v11_lattices(sK0) | ~spl2_3),
% 0.21/0.45    inference(subsumption_resolution,[],[f584,f58])).
% 0.21/0.45  fof(f584,plain,(
% 0.21/0.45    ~l3_lattices(sK0) | v2_struct_0(sK1) | ~v10_lattices(sK1) | ~l3_lattices(sK1) | v2_struct_0(k7_filter_1(sK0,sK1)) | v2_struct_0(sK0) | ~v11_lattices(k7_filter_1(sK0,sK1)) | v11_lattices(sK0) | ~spl2_3),
% 0.21/0.45    inference(subsumption_resolution,[],[f583,f57])).
% 0.21/0.45  fof(f583,plain,(
% 0.21/0.45    ~v10_lattices(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK1) | ~v10_lattices(sK1) | ~l3_lattices(sK1) | v2_struct_0(k7_filter_1(sK0,sK1)) | v2_struct_0(sK0) | ~v11_lattices(k7_filter_1(sK0,sK1)) | v11_lattices(sK0) | ~spl2_3),
% 0.21/0.45    inference(resolution,[],[f566,f92])).
% 0.21/0.45  fof(f566,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~v10_lattices(k7_filter_1(X0,X1)) | ~v10_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X1) | ~v10_lattices(X1) | ~l3_lattices(X1) | v2_struct_0(k7_filter_1(X0,X1)) | v2_struct_0(X0) | ~v11_lattices(k7_filter_1(X0,X1)) | v11_lattices(X0)) )),
% 0.21/0.45    inference(subsumption_resolution,[],[f73,f79])).
% 0.21/0.45  fof(f73,plain,(
% 0.21/0.45    ( ! [X0,X1] : (v2_struct_0(X0) | ~v10_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X1) | ~v10_lattices(X1) | ~l3_lattices(X1) | v2_struct_0(k7_filter_1(X0,X1)) | ~v10_lattices(k7_filter_1(X0,X1)) | ~v11_lattices(k7_filter_1(X0,X1)) | ~l3_lattices(k7_filter_1(X0,X1)) | v11_lattices(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f17])).
% 0.21/0.45  fof(f966,plain,(
% 0.21/0.45    ~v11_lattices(sK0) | ~v15_lattices(sK0) | ~l3_lattices(sK0) | v17_lattices(sK0) | ~spl2_19),
% 0.21/0.45    inference(subsumption_resolution,[],[f965,f56])).
% 0.21/0.45  fof(f965,plain,(
% 0.21/0.45    v2_struct_0(sK0) | ~v11_lattices(sK0) | ~v15_lattices(sK0) | ~l3_lattices(sK0) | v17_lattices(sK0) | ~spl2_19),
% 0.21/0.45    inference(resolution,[],[f441,f59])).
% 0.21/0.45  fof(f964,plain,(
% 0.21/0.45    spl2_19 | spl2_2 | ~spl2_3 | ~spl2_5 | ~spl2_6),
% 0.21/0.45    inference(avatar_split_clause,[],[f957,f115,f100,f90,f85,f440])).
% 0.21/0.45  fof(f957,plain,(
% 0.21/0.45    v16_lattices(sK0) | (spl2_2 | ~spl2_3 | ~spl2_5 | ~spl2_6)),
% 0.21/0.45    inference(subsumption_resolution,[],[f956,f564])).
% 0.21/0.45  fof(f956,plain,(
% 0.21/0.45    ~v16_lattices(k7_filter_1(sK0,sK1)) | v16_lattices(sK0) | (spl2_2 | ~spl2_3 | ~spl2_5 | ~spl2_6)),
% 0.21/0.45    inference(subsumption_resolution,[],[f955,f563])).
% 0.21/0.45  fof(f955,plain,(
% 0.21/0.45    ~v15_lattices(k7_filter_1(sK0,sK1)) | ~v16_lattices(k7_filter_1(sK0,sK1)) | v16_lattices(sK0) | (spl2_2 | ~spl2_3)),
% 0.21/0.45    inference(subsumption_resolution,[],[f954,f56])).
% 0.21/0.45  fof(f954,plain,(
% 0.21/0.45    v2_struct_0(sK0) | ~v15_lattices(k7_filter_1(sK0,sK1)) | ~v16_lattices(k7_filter_1(sK0,sK1)) | v16_lattices(sK0) | (spl2_2 | ~spl2_3)),
% 0.21/0.45    inference(subsumption_resolution,[],[f953,f87])).
% 0.21/0.45  fof(f953,plain,(
% 0.21/0.45    v2_struct_0(k7_filter_1(sK0,sK1)) | v2_struct_0(sK0) | ~v15_lattices(k7_filter_1(sK0,sK1)) | ~v16_lattices(k7_filter_1(sK0,sK1)) | v16_lattices(sK0) | ~spl2_3),
% 0.21/0.45    inference(subsumption_resolution,[],[f952,f55])).
% 0.21/0.45  fof(f952,plain,(
% 0.21/0.45    ~l3_lattices(sK1) | v2_struct_0(k7_filter_1(sK0,sK1)) | v2_struct_0(sK0) | ~v15_lattices(k7_filter_1(sK0,sK1)) | ~v16_lattices(k7_filter_1(sK0,sK1)) | v16_lattices(sK0) | ~spl2_3),
% 0.21/0.45    inference(subsumption_resolution,[],[f951,f54])).
% 0.21/0.45  fof(f951,plain,(
% 0.21/0.45    ~v10_lattices(sK1) | ~l3_lattices(sK1) | v2_struct_0(k7_filter_1(sK0,sK1)) | v2_struct_0(sK0) | ~v15_lattices(k7_filter_1(sK0,sK1)) | ~v16_lattices(k7_filter_1(sK0,sK1)) | v16_lattices(sK0) | ~spl2_3),
% 0.21/0.45    inference(subsumption_resolution,[],[f950,f53])).
% 0.21/0.45  fof(f950,plain,(
% 0.21/0.45    v2_struct_0(sK1) | ~v10_lattices(sK1) | ~l3_lattices(sK1) | v2_struct_0(k7_filter_1(sK0,sK1)) | v2_struct_0(sK0) | ~v15_lattices(k7_filter_1(sK0,sK1)) | ~v16_lattices(k7_filter_1(sK0,sK1)) | v16_lattices(sK0) | ~spl2_3),
% 0.21/0.45    inference(subsumption_resolution,[],[f949,f58])).
% 0.21/0.45  fof(f949,plain,(
% 0.21/0.45    ~l3_lattices(sK0) | v2_struct_0(sK1) | ~v10_lattices(sK1) | ~l3_lattices(sK1) | v2_struct_0(k7_filter_1(sK0,sK1)) | v2_struct_0(sK0) | ~v15_lattices(k7_filter_1(sK0,sK1)) | ~v16_lattices(k7_filter_1(sK0,sK1)) | v16_lattices(sK0) | ~spl2_3),
% 0.21/0.45    inference(subsumption_resolution,[],[f943,f57])).
% 0.21/0.45  fof(f943,plain,(
% 0.21/0.45    ~v10_lattices(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK1) | ~v10_lattices(sK1) | ~l3_lattices(sK1) | v2_struct_0(k7_filter_1(sK0,sK1)) | v2_struct_0(sK0) | ~v15_lattices(k7_filter_1(sK0,sK1)) | ~v16_lattices(k7_filter_1(sK0,sK1)) | v16_lattices(sK0) | ~spl2_3),
% 0.21/0.45    inference(resolution,[],[f800,f92])).
% 0.21/0.45  fof(f800,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~v10_lattices(k7_filter_1(X0,X1)) | ~v10_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X1) | ~v10_lattices(X1) | ~l3_lattices(X1) | v2_struct_0(k7_filter_1(X0,X1)) | v2_struct_0(X0) | ~v15_lattices(k7_filter_1(X0,X1)) | ~v16_lattices(k7_filter_1(X0,X1)) | v16_lattices(X0)) )),
% 0.21/0.45    inference(subsumption_resolution,[],[f65,f79])).
% 0.21/0.45  fof(f65,plain,(
% 0.21/0.45    ( ! [X0,X1] : (v2_struct_0(X0) | ~v10_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X1) | ~v10_lattices(X1) | ~l3_lattices(X1) | v2_struct_0(k7_filter_1(X0,X1)) | ~v10_lattices(k7_filter_1(X0,X1)) | ~v15_lattices(k7_filter_1(X0,X1)) | ~v16_lattices(k7_filter_1(X0,X1)) | ~l3_lattices(k7_filter_1(X0,X1)) | v16_lattices(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f15])).
% 0.21/0.45  fof(f780,plain,(
% 0.21/0.45    spl2_15 | ~spl2_1),
% 0.21/0.45    inference(avatar_split_clause,[],[f778,f81,f382])).
% 0.21/0.45  fof(f81,plain,(
% 0.21/0.45    spl2_1 <=> v17_lattices(sK1)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.45  fof(f778,plain,(
% 0.21/0.45    v15_lattices(sK1) | ~spl2_1),
% 0.21/0.45    inference(subsumption_resolution,[],[f777,f55])).
% 0.21/0.45  fof(f777,plain,(
% 0.21/0.45    ~l3_lattices(sK1) | v15_lattices(sK1) | ~spl2_1),
% 0.21/0.45    inference(subsumption_resolution,[],[f773,f53])).
% 0.21/0.45  fof(f773,plain,(
% 0.21/0.45    v2_struct_0(sK1) | ~l3_lattices(sK1) | v15_lattices(sK1) | ~spl2_1),
% 0.21/0.45    inference(resolution,[],[f83,f61])).
% 0.21/0.45  fof(f83,plain,(
% 0.21/0.45    v17_lattices(sK1) | ~spl2_1),
% 0.21/0.45    inference(avatar_component_clause,[],[f81])).
% 0.21/0.45  fof(f779,plain,(
% 0.21/0.45    spl2_14 | ~spl2_1),
% 0.21/0.45    inference(avatar_split_clause,[],[f776,f81,f378])).
% 0.21/0.45  fof(f776,plain,(
% 0.21/0.45    v16_lattices(sK1) | ~spl2_1),
% 0.21/0.45    inference(subsumption_resolution,[],[f775,f55])).
% 0.21/0.45  fof(f775,plain,(
% 0.21/0.45    ~l3_lattices(sK1) | v16_lattices(sK1) | ~spl2_1),
% 0.21/0.45    inference(subsumption_resolution,[],[f772,f53])).
% 0.21/0.45  fof(f772,plain,(
% 0.21/0.45    v2_struct_0(sK1) | ~l3_lattices(sK1) | v16_lattices(sK1) | ~spl2_1),
% 0.21/0.45    inference(resolution,[],[f83,f62])).
% 0.21/0.45  fof(f770,plain,(
% 0.21/0.45    spl2_14 | spl2_2 | ~spl2_3 | ~spl2_5 | ~spl2_6),
% 0.21/0.45    inference(avatar_split_clause,[],[f768,f115,f100,f90,f85,f378])).
% 0.21/0.45  fof(f768,plain,(
% 0.21/0.45    v16_lattices(sK1) | (spl2_2 | ~spl2_3 | ~spl2_5 | ~spl2_6)),
% 0.21/0.45    inference(subsumption_resolution,[],[f767,f564])).
% 0.21/0.45  fof(f767,plain,(
% 0.21/0.45    ~v16_lattices(k7_filter_1(sK0,sK1)) | v16_lattices(sK1) | (spl2_2 | ~spl2_3 | ~spl2_5 | ~spl2_6)),
% 0.21/0.45    inference(subsumption_resolution,[],[f766,f563])).
% 0.21/0.45  fof(f766,plain,(
% 0.21/0.45    ~v15_lattices(k7_filter_1(sK0,sK1)) | ~v16_lattices(k7_filter_1(sK0,sK1)) | v16_lattices(sK1) | (spl2_2 | ~spl2_3)),
% 0.21/0.45    inference(subsumption_resolution,[],[f765,f56])).
% 0.21/0.45  fof(f765,plain,(
% 0.21/0.45    v2_struct_0(sK0) | ~v15_lattices(k7_filter_1(sK0,sK1)) | ~v16_lattices(k7_filter_1(sK0,sK1)) | v16_lattices(sK1) | (spl2_2 | ~spl2_3)),
% 0.21/0.45    inference(subsumption_resolution,[],[f764,f87])).
% 0.21/0.45  fof(f764,plain,(
% 0.21/0.45    v2_struct_0(k7_filter_1(sK0,sK1)) | v2_struct_0(sK0) | ~v15_lattices(k7_filter_1(sK0,sK1)) | ~v16_lattices(k7_filter_1(sK0,sK1)) | v16_lattices(sK1) | ~spl2_3),
% 0.21/0.45    inference(subsumption_resolution,[],[f763,f55])).
% 0.21/0.45  fof(f763,plain,(
% 0.21/0.45    ~l3_lattices(sK1) | v2_struct_0(k7_filter_1(sK0,sK1)) | v2_struct_0(sK0) | ~v15_lattices(k7_filter_1(sK0,sK1)) | ~v16_lattices(k7_filter_1(sK0,sK1)) | v16_lattices(sK1) | ~spl2_3),
% 0.21/0.45    inference(subsumption_resolution,[],[f762,f54])).
% 0.21/0.45  fof(f762,plain,(
% 0.21/0.45    ~v10_lattices(sK1) | ~l3_lattices(sK1) | v2_struct_0(k7_filter_1(sK0,sK1)) | v2_struct_0(sK0) | ~v15_lattices(k7_filter_1(sK0,sK1)) | ~v16_lattices(k7_filter_1(sK0,sK1)) | v16_lattices(sK1) | ~spl2_3),
% 0.21/0.45    inference(subsumption_resolution,[],[f761,f53])).
% 0.21/0.45  fof(f761,plain,(
% 0.21/0.45    v2_struct_0(sK1) | ~v10_lattices(sK1) | ~l3_lattices(sK1) | v2_struct_0(k7_filter_1(sK0,sK1)) | v2_struct_0(sK0) | ~v15_lattices(k7_filter_1(sK0,sK1)) | ~v16_lattices(k7_filter_1(sK0,sK1)) | v16_lattices(sK1) | ~spl2_3),
% 0.21/0.45    inference(subsumption_resolution,[],[f760,f58])).
% 0.21/0.45  fof(f760,plain,(
% 0.21/0.45    ~l3_lattices(sK0) | v2_struct_0(sK1) | ~v10_lattices(sK1) | ~l3_lattices(sK1) | v2_struct_0(k7_filter_1(sK0,sK1)) | v2_struct_0(sK0) | ~v15_lattices(k7_filter_1(sK0,sK1)) | ~v16_lattices(k7_filter_1(sK0,sK1)) | v16_lattices(sK1) | ~spl2_3),
% 0.21/0.45    inference(subsumption_resolution,[],[f644,f57])).
% 0.21/0.45  fof(f644,plain,(
% 0.21/0.45    ~v10_lattices(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK1) | ~v10_lattices(sK1) | ~l3_lattices(sK1) | v2_struct_0(k7_filter_1(sK0,sK1)) | v2_struct_0(sK0) | ~v15_lattices(k7_filter_1(sK0,sK1)) | ~v16_lattices(k7_filter_1(sK0,sK1)) | v16_lattices(sK1) | ~spl2_3),
% 0.21/0.45    inference(resolution,[],[f615,f92])).
% 0.21/0.45  fof(f615,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~v10_lattices(k7_filter_1(X0,X1)) | ~v10_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X1) | ~v10_lattices(X1) | ~l3_lattices(X1) | v2_struct_0(k7_filter_1(X0,X1)) | v2_struct_0(X0) | ~v15_lattices(k7_filter_1(X0,X1)) | ~v16_lattices(k7_filter_1(X0,X1)) | v16_lattices(X1)) )),
% 0.21/0.45    inference(subsumption_resolution,[],[f63,f79])).
% 0.21/0.45  fof(f63,plain,(
% 0.21/0.45    ( ! [X0,X1] : (v2_struct_0(X0) | ~v10_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X1) | ~v10_lattices(X1) | ~l3_lattices(X1) | v2_struct_0(k7_filter_1(X0,X1)) | ~v10_lattices(k7_filter_1(X0,X1)) | ~v15_lattices(k7_filter_1(X0,X1)) | ~v16_lattices(k7_filter_1(X0,X1)) | ~l3_lattices(k7_filter_1(X0,X1)) | v16_lattices(X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f15])).
% 0.21/0.45  fof(f769,plain,(
% 0.21/0.45    spl2_15 | spl2_2 | ~spl2_3 | ~spl2_5 | ~spl2_6),
% 0.21/0.45    inference(avatar_split_clause,[],[f757,f115,f100,f90,f85,f382])).
% 0.21/0.45  fof(f757,plain,(
% 0.21/0.45    v15_lattices(sK1) | (spl2_2 | ~spl2_3 | ~spl2_5 | ~spl2_6)),
% 0.21/0.45    inference(subsumption_resolution,[],[f756,f564])).
% 0.21/0.45  fof(f756,plain,(
% 0.21/0.45    ~v16_lattices(k7_filter_1(sK0,sK1)) | v15_lattices(sK1) | (spl2_2 | ~spl2_3 | ~spl2_5 | ~spl2_6)),
% 0.21/0.45    inference(subsumption_resolution,[],[f755,f563])).
% 0.21/0.45  fof(f755,plain,(
% 0.21/0.45    ~v15_lattices(k7_filter_1(sK0,sK1)) | ~v16_lattices(k7_filter_1(sK0,sK1)) | v15_lattices(sK1) | (spl2_2 | ~spl2_3)),
% 0.21/0.45    inference(subsumption_resolution,[],[f754,f56])).
% 0.21/0.45  fof(f754,plain,(
% 0.21/0.45    v2_struct_0(sK0) | ~v15_lattices(k7_filter_1(sK0,sK1)) | ~v16_lattices(k7_filter_1(sK0,sK1)) | v15_lattices(sK1) | (spl2_2 | ~spl2_3)),
% 0.21/0.45    inference(subsumption_resolution,[],[f753,f87])).
% 0.21/0.45  fof(f753,plain,(
% 0.21/0.45    v2_struct_0(k7_filter_1(sK0,sK1)) | v2_struct_0(sK0) | ~v15_lattices(k7_filter_1(sK0,sK1)) | ~v16_lattices(k7_filter_1(sK0,sK1)) | v15_lattices(sK1) | ~spl2_3),
% 0.21/0.45    inference(subsumption_resolution,[],[f752,f55])).
% 0.21/0.45  fof(f752,plain,(
% 0.21/0.45    ~l3_lattices(sK1) | v2_struct_0(k7_filter_1(sK0,sK1)) | v2_struct_0(sK0) | ~v15_lattices(k7_filter_1(sK0,sK1)) | ~v16_lattices(k7_filter_1(sK0,sK1)) | v15_lattices(sK1) | ~spl2_3),
% 0.21/0.45    inference(subsumption_resolution,[],[f751,f54])).
% 0.21/0.45  fof(f751,plain,(
% 0.21/0.45    ~v10_lattices(sK1) | ~l3_lattices(sK1) | v2_struct_0(k7_filter_1(sK0,sK1)) | v2_struct_0(sK0) | ~v15_lattices(k7_filter_1(sK0,sK1)) | ~v16_lattices(k7_filter_1(sK0,sK1)) | v15_lattices(sK1) | ~spl2_3),
% 0.21/0.45    inference(subsumption_resolution,[],[f750,f53])).
% 0.21/0.45  fof(f750,plain,(
% 0.21/0.45    v2_struct_0(sK1) | ~v10_lattices(sK1) | ~l3_lattices(sK1) | v2_struct_0(k7_filter_1(sK0,sK1)) | v2_struct_0(sK0) | ~v15_lattices(k7_filter_1(sK0,sK1)) | ~v16_lattices(k7_filter_1(sK0,sK1)) | v15_lattices(sK1) | ~spl2_3),
% 0.21/0.45    inference(subsumption_resolution,[],[f749,f58])).
% 0.21/0.45  fof(f749,plain,(
% 0.21/0.45    ~l3_lattices(sK0) | v2_struct_0(sK1) | ~v10_lattices(sK1) | ~l3_lattices(sK1) | v2_struct_0(k7_filter_1(sK0,sK1)) | v2_struct_0(sK0) | ~v15_lattices(k7_filter_1(sK0,sK1)) | ~v16_lattices(k7_filter_1(sK0,sK1)) | v15_lattices(sK1) | ~spl2_3),
% 0.21/0.45    inference(subsumption_resolution,[],[f748,f57])).
% 0.21/0.45  fof(f748,plain,(
% 0.21/0.45    ~v10_lattices(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK1) | ~v10_lattices(sK1) | ~l3_lattices(sK1) | v2_struct_0(k7_filter_1(sK0,sK1)) | v2_struct_0(sK0) | ~v15_lattices(k7_filter_1(sK0,sK1)) | ~v16_lattices(k7_filter_1(sK0,sK1)) | v15_lattices(sK1) | ~spl2_3),
% 0.21/0.45    inference(resolution,[],[f709,f92])).
% 0.21/0.45  fof(f709,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~v10_lattices(k7_filter_1(X0,X1)) | ~v10_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X1) | ~v10_lattices(X1) | ~l3_lattices(X1) | v2_struct_0(k7_filter_1(X0,X1)) | v2_struct_0(X0) | ~v15_lattices(k7_filter_1(X0,X1)) | ~v16_lattices(k7_filter_1(X0,X1)) | v15_lattices(X1)) )),
% 0.21/0.45    inference(subsumption_resolution,[],[f64,f79])).
% 0.21/0.45  fof(f64,plain,(
% 0.21/0.45    ( ! [X0,X1] : (v2_struct_0(X0) | ~v10_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X1) | ~v10_lattices(X1) | ~l3_lattices(X1) | v2_struct_0(k7_filter_1(X0,X1)) | ~v10_lattices(k7_filter_1(X0,X1)) | ~v15_lattices(k7_filter_1(X0,X1)) | ~v16_lattices(k7_filter_1(X0,X1)) | ~l3_lattices(k7_filter_1(X0,X1)) | v15_lattices(X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f15])).
% 0.21/0.45  fof(f561,plain,(
% 0.21/0.45    spl2_23 | ~spl2_1),
% 0.21/0.45    inference(avatar_split_clause,[],[f559,f81,f512])).
% 0.21/0.45  fof(f559,plain,(
% 0.21/0.45    v11_lattices(sK1) | ~spl2_1),
% 0.21/0.45    inference(subsumption_resolution,[],[f558,f55])).
% 0.21/0.45  fof(f558,plain,(
% 0.21/0.45    ~l3_lattices(sK1) | v11_lattices(sK1) | ~spl2_1),
% 0.21/0.45    inference(subsumption_resolution,[],[f555,f53])).
% 0.21/0.45  fof(f555,plain,(
% 0.21/0.45    v2_struct_0(sK1) | ~l3_lattices(sK1) | v11_lattices(sK1) | ~spl2_1),
% 0.21/0.45    inference(resolution,[],[f83,f60])).
% 0.21/0.45  fof(f551,plain,(
% 0.21/0.45    spl2_23 | spl2_2 | ~spl2_3 | ~spl2_5 | ~spl2_6),
% 0.21/0.45    inference(avatar_split_clause,[],[f550,f115,f100,f90,f85,f512])).
% 0.21/0.45  fof(f550,plain,(
% 0.21/0.45    v11_lattices(sK1) | (spl2_2 | ~spl2_3 | ~spl2_5 | ~spl2_6)),
% 0.21/0.45    inference(subsumption_resolution,[],[f549,f516])).
% 0.21/0.45  fof(f516,plain,(
% 0.21/0.45    v11_lattices(k7_filter_1(sK0,sK1)) | (spl2_2 | ~spl2_5 | ~spl2_6)),
% 0.21/0.45    inference(subsumption_resolution,[],[f474,f87])).
% 0.21/0.45  fof(f549,plain,(
% 0.21/0.45    ~v11_lattices(k7_filter_1(sK0,sK1)) | v11_lattices(sK1) | (spl2_2 | ~spl2_3)),
% 0.21/0.45    inference(subsumption_resolution,[],[f548,f56])).
% 0.21/0.45  fof(f548,plain,(
% 0.21/0.45    v2_struct_0(sK0) | ~v11_lattices(k7_filter_1(sK0,sK1)) | v11_lattices(sK1) | (spl2_2 | ~spl2_3)),
% 0.21/0.45    inference(subsumption_resolution,[],[f547,f87])).
% 0.21/0.45  fof(f547,plain,(
% 0.21/0.45    v2_struct_0(k7_filter_1(sK0,sK1)) | v2_struct_0(sK0) | ~v11_lattices(k7_filter_1(sK0,sK1)) | v11_lattices(sK1) | ~spl2_3),
% 0.21/0.45    inference(subsumption_resolution,[],[f546,f55])).
% 0.21/0.45  fof(f546,plain,(
% 0.21/0.45    ~l3_lattices(sK1) | v2_struct_0(k7_filter_1(sK0,sK1)) | v2_struct_0(sK0) | ~v11_lattices(k7_filter_1(sK0,sK1)) | v11_lattices(sK1) | ~spl2_3),
% 0.21/0.45    inference(subsumption_resolution,[],[f545,f54])).
% 0.21/0.45  fof(f545,plain,(
% 0.21/0.45    ~v10_lattices(sK1) | ~l3_lattices(sK1) | v2_struct_0(k7_filter_1(sK0,sK1)) | v2_struct_0(sK0) | ~v11_lattices(k7_filter_1(sK0,sK1)) | v11_lattices(sK1) | ~spl2_3),
% 0.21/0.45    inference(subsumption_resolution,[],[f544,f53])).
% 0.21/0.45  fof(f544,plain,(
% 0.21/0.45    v2_struct_0(sK1) | ~v10_lattices(sK1) | ~l3_lattices(sK1) | v2_struct_0(k7_filter_1(sK0,sK1)) | v2_struct_0(sK0) | ~v11_lattices(k7_filter_1(sK0,sK1)) | v11_lattices(sK1) | ~spl2_3),
% 0.21/0.45    inference(subsumption_resolution,[],[f543,f58])).
% 0.21/0.45  fof(f543,plain,(
% 0.21/0.45    ~l3_lattices(sK0) | v2_struct_0(sK1) | ~v10_lattices(sK1) | ~l3_lattices(sK1) | v2_struct_0(k7_filter_1(sK0,sK1)) | v2_struct_0(sK0) | ~v11_lattices(k7_filter_1(sK0,sK1)) | v11_lattices(sK1) | ~spl2_3),
% 0.21/0.45    inference(subsumption_resolution,[],[f542,f57])).
% 0.21/0.45  fof(f542,plain,(
% 0.21/0.45    ~v10_lattices(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK1) | ~v10_lattices(sK1) | ~l3_lattices(sK1) | v2_struct_0(k7_filter_1(sK0,sK1)) | v2_struct_0(sK0) | ~v11_lattices(k7_filter_1(sK0,sK1)) | v11_lattices(sK1) | ~spl2_3),
% 0.21/0.45    inference(resolution,[],[f518,f92])).
% 0.21/0.45  fof(f518,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~v10_lattices(k7_filter_1(X0,X1)) | ~v10_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X1) | ~v10_lattices(X1) | ~l3_lattices(X1) | v2_struct_0(k7_filter_1(X0,X1)) | v2_struct_0(X0) | ~v11_lattices(k7_filter_1(X0,X1)) | v11_lattices(X1)) )),
% 0.21/0.45    inference(subsumption_resolution,[],[f72,f79])).
% 0.21/0.45  fof(f72,plain,(
% 0.21/0.45    ( ! [X0,X1] : (v2_struct_0(X0) | ~v10_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X1) | ~v10_lattices(X1) | ~l3_lattices(X1) | v2_struct_0(k7_filter_1(X0,X1)) | ~v10_lattices(k7_filter_1(X0,X1)) | ~v11_lattices(k7_filter_1(X0,X1)) | ~l3_lattices(k7_filter_1(X0,X1)) | v11_lattices(X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f17])).
% 0.21/0.45  fof(f515,plain,(
% 0.21/0.45    ~spl2_15 | ~spl2_23 | spl2_1 | ~spl2_14),
% 0.21/0.45    inference(avatar_split_clause,[],[f510,f378,f81,f512,f382])).
% 0.21/0.45  fof(f510,plain,(
% 0.21/0.45    ~v11_lattices(sK1) | ~v15_lattices(sK1) | (spl2_1 | ~spl2_14)),
% 0.21/0.45    inference(subsumption_resolution,[],[f509,f82])).
% 0.21/0.45  fof(f82,plain,(
% 0.21/0.45    ~v17_lattices(sK1) | spl2_1),
% 0.21/0.45    inference(avatar_component_clause,[],[f81])).
% 0.21/0.45  fof(f509,plain,(
% 0.21/0.45    ~v11_lattices(sK1) | ~v15_lattices(sK1) | v17_lattices(sK1) | ~spl2_14),
% 0.21/0.45    inference(subsumption_resolution,[],[f508,f55])).
% 0.21/0.45  fof(f508,plain,(
% 0.21/0.45    ~v11_lattices(sK1) | ~v15_lattices(sK1) | ~l3_lattices(sK1) | v17_lattices(sK1) | ~spl2_14),
% 0.21/0.45    inference(subsumption_resolution,[],[f507,f53])).
% 0.21/0.45  fof(f507,plain,(
% 0.21/0.45    v2_struct_0(sK1) | ~v11_lattices(sK1) | ~v15_lattices(sK1) | ~l3_lattices(sK1) | v17_lattices(sK1) | ~spl2_14),
% 0.21/0.45    inference(resolution,[],[f379,f59])).
% 0.21/0.45  fof(f307,plain,(
% 0.21/0.45    spl2_1 | spl2_5),
% 0.21/0.45    inference(avatar_split_clause,[],[f306,f100,f81])).
% 0.21/0.45  fof(f306,plain,(
% 0.21/0.45    v17_lattices(sK1) | spl2_5),
% 0.21/0.45    inference(subsumption_resolution,[],[f26,f101])).
% 0.21/0.45  fof(f26,plain,(
% 0.21/0.45    v17_lattices(k7_filter_1(sK0,sK1)) | v17_lattices(sK1)),
% 0.21/0.45    inference(cnf_transformation,[],[f9])).
% 0.21/0.45  fof(f175,plain,(
% 0.21/0.45    spl2_6),
% 0.21/0.45    inference(avatar_split_clause,[],[f173,f115])).
% 0.21/0.45  fof(f173,plain,(
% 0.21/0.45    l3_lattices(k7_filter_1(sK0,sK1))),
% 0.21/0.45    inference(subsumption_resolution,[],[f169,f53])).
% 0.21/0.45  fof(f169,plain,(
% 0.21/0.45    v2_struct_0(sK1) | l3_lattices(k7_filter_1(sK0,sK1))),
% 0.21/0.45    inference(resolution,[],[f154,f55])).
% 0.21/0.45  fof(f154,plain,(
% 0.21/0.45    ( ! [X1] : (~l3_lattices(X1) | v2_struct_0(X1) | l3_lattices(k7_filter_1(sK0,X1))) )),
% 0.21/0.45    inference(subsumption_resolution,[],[f152,f56])).
% 0.21/0.45  fof(f152,plain,(
% 0.21/0.45    ( ! [X1] : (v2_struct_0(sK0) | v2_struct_0(X1) | ~l3_lattices(X1) | l3_lattices(k7_filter_1(sK0,X1))) )),
% 0.21/0.45    inference(resolution,[],[f79,f58])).
% 0.21/0.45  fof(f118,plain,(
% 0.21/0.45    ~spl2_6 | ~spl2_5 | ~spl2_1 | spl2_2 | ~spl2_3 | ~spl2_4),
% 0.21/0.45    inference(avatar_split_clause,[],[f113,f95,f90,f85,f81,f100,f115])).
% 0.21/0.45  fof(f113,plain,(
% 0.21/0.45    ~v17_lattices(k7_filter_1(sK0,sK1)) | ~l3_lattices(k7_filter_1(sK0,sK1)) | (~spl2_1 | spl2_2 | ~spl2_3 | ~spl2_4)),
% 0.21/0.45    inference(subsumption_resolution,[],[f112,f55])).
% 0.21/0.45  fof(f112,plain,(
% 0.21/0.45    ~v17_lattices(k7_filter_1(sK0,sK1)) | ~l3_lattices(k7_filter_1(sK0,sK1)) | ~l3_lattices(sK1) | (~spl2_1 | spl2_2 | ~spl2_3 | ~spl2_4)),
% 0.21/0.45    inference(subsumption_resolution,[],[f111,f83])).
% 0.21/0.45  fof(f111,plain,(
% 0.21/0.45    ~v17_lattices(k7_filter_1(sK0,sK1)) | ~l3_lattices(k7_filter_1(sK0,sK1)) | ~v17_lattices(sK1) | ~l3_lattices(sK1) | (spl2_2 | ~spl2_3 | ~spl2_4)),
% 0.21/0.45    inference(subsumption_resolution,[],[f110,f54])).
% 0.21/0.45  fof(f110,plain,(
% 0.21/0.45    ~v17_lattices(k7_filter_1(sK0,sK1)) | ~l3_lattices(k7_filter_1(sK0,sK1)) | ~v10_lattices(sK1) | ~v17_lattices(sK1) | ~l3_lattices(sK1) | (spl2_2 | ~spl2_3 | ~spl2_4)),
% 0.21/0.45    inference(subsumption_resolution,[],[f109,f53])).
% 0.21/0.45  fof(f109,plain,(
% 0.21/0.45    ~v17_lattices(k7_filter_1(sK0,sK1)) | ~l3_lattices(k7_filter_1(sK0,sK1)) | v2_struct_0(sK1) | ~v10_lattices(sK1) | ~v17_lattices(sK1) | ~l3_lattices(sK1) | (spl2_2 | ~spl2_3 | ~spl2_4)),
% 0.21/0.45    inference(subsumption_resolution,[],[f108,f58])).
% 0.21/0.45  fof(f108,plain,(
% 0.21/0.45    ~v17_lattices(k7_filter_1(sK0,sK1)) | ~l3_lattices(k7_filter_1(sK0,sK1)) | ~l3_lattices(sK0) | v2_struct_0(sK1) | ~v10_lattices(sK1) | ~v17_lattices(sK1) | ~l3_lattices(sK1) | (spl2_2 | ~spl2_3 | ~spl2_4)),
% 0.21/0.45    inference(subsumption_resolution,[],[f107,f97])).
% 0.21/0.45  fof(f107,plain,(
% 0.21/0.45    ~v17_lattices(k7_filter_1(sK0,sK1)) | ~l3_lattices(k7_filter_1(sK0,sK1)) | ~v17_lattices(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK1) | ~v10_lattices(sK1) | ~v17_lattices(sK1) | ~l3_lattices(sK1) | (spl2_2 | ~spl2_3)),
% 0.21/0.45    inference(subsumption_resolution,[],[f106,f57])).
% 0.21/0.45  fof(f106,plain,(
% 0.21/0.45    ~v17_lattices(k7_filter_1(sK0,sK1)) | ~l3_lattices(k7_filter_1(sK0,sK1)) | ~v10_lattices(sK0) | ~v17_lattices(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK1) | ~v10_lattices(sK1) | ~v17_lattices(sK1) | ~l3_lattices(sK1) | (spl2_2 | ~spl2_3)),
% 0.21/0.45    inference(subsumption_resolution,[],[f105,f56])).
% 0.21/0.45  fof(f105,plain,(
% 0.21/0.45    ~v17_lattices(k7_filter_1(sK0,sK1)) | ~l3_lattices(k7_filter_1(sK0,sK1)) | v2_struct_0(sK0) | ~v10_lattices(sK0) | ~v17_lattices(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK1) | ~v10_lattices(sK1) | ~v17_lattices(sK1) | ~l3_lattices(sK1) | (spl2_2 | ~spl2_3)),
% 0.21/0.45    inference(subsumption_resolution,[],[f104,f92])).
% 0.21/0.46  fof(f104,plain,(
% 0.21/0.46    ~v10_lattices(k7_filter_1(sK0,sK1)) | ~v17_lattices(k7_filter_1(sK0,sK1)) | ~l3_lattices(k7_filter_1(sK0,sK1)) | v2_struct_0(sK0) | ~v10_lattices(sK0) | ~v17_lattices(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK1) | ~v10_lattices(sK1) | ~v17_lattices(sK1) | ~l3_lattices(sK1) | spl2_2),
% 0.21/0.46    inference(subsumption_resolution,[],[f52,f87])).
% 0.21/0.46  fof(f52,plain,(
% 0.21/0.46    v2_struct_0(k7_filter_1(sK0,sK1)) | ~v10_lattices(k7_filter_1(sK0,sK1)) | ~v17_lattices(k7_filter_1(sK0,sK1)) | ~l3_lattices(k7_filter_1(sK0,sK1)) | v2_struct_0(sK0) | ~v10_lattices(sK0) | ~v17_lattices(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK1) | ~v10_lattices(sK1) | ~v17_lattices(sK1) | ~l3_lattices(sK1)),
% 0.21/0.46    inference(cnf_transformation,[],[f9])).
% 0.21/0.46  fof(f103,plain,(
% 0.21/0.46    spl2_4 | spl2_5),
% 0.21/0.46    inference(avatar_split_clause,[],[f42,f100,f95])).
% 0.21/0.46  fof(f42,plain,(
% 0.21/0.46    v17_lattices(k7_filter_1(sK0,sK1)) | v17_lattices(sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f9])).
% 0.21/0.46  fof(f98,plain,(
% 0.21/0.46    spl2_4 | spl2_3),
% 0.21/0.46    inference(avatar_split_clause,[],[f41,f90,f95])).
% 0.21/0.46  fof(f41,plain,(
% 0.21/0.46    v10_lattices(k7_filter_1(sK0,sK1)) | v17_lattices(sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f9])).
% 0.21/0.46  fof(f93,plain,(
% 0.21/0.46    spl2_1 | spl2_3),
% 0.21/0.46    inference(avatar_split_clause,[],[f25,f90,f81])).
% 0.21/0.46  fof(f25,plain,(
% 0.21/0.46    v10_lattices(k7_filter_1(sK0,sK1)) | v17_lattices(sK1)),
% 0.21/0.46    inference(cnf_transformation,[],[f9])).
% 0.21/0.46  fof(f88,plain,(
% 0.21/0.46    spl2_1 | ~spl2_2),
% 0.21/0.46    inference(avatar_split_clause,[],[f24,f85,f81])).
% 0.21/0.46  fof(f24,plain,(
% 0.21/0.46    ~v2_struct_0(k7_filter_1(sK0,sK1)) | v17_lattices(sK1)),
% 0.21/0.46    inference(cnf_transformation,[],[f9])).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (3431)------------------------------
% 0.21/0.46  % (3431)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (3431)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (3431)Memory used [KB]: 6140
% 0.21/0.46  % (3431)Time elapsed: 0.059 s
% 0.21/0.46  % (3431)------------------------------
% 0.21/0.46  % (3431)------------------------------
% 0.21/0.46  % (3424)Success in time 0.093 s
%------------------------------------------------------------------------------
