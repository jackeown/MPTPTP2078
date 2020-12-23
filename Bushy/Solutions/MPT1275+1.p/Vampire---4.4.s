%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tops_1__t94_tops_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:34 EDT 2019

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :  554 (1954 expanded)
%              Number of leaves         :  139 ( 775 expanded)
%              Depth                    :   12
%              Number of atoms          : 1496 (4713 expanded)
%              Number of equality atoms :  183 ( 826 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2556,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f176,f183,f190,f197,f204,f213,f220,f227,f243,f256,f263,f278,f287,f304,f307,f325,f338,f348,f355,f366,f376,f387,f400,f411,f423,f444,f461,f469,f484,f562,f577,f715,f725,f739,f823,f877,f887,f943,f959,f988,f1041,f1064,f1112,f1136,f1146,f1171,f1213,f1220,f1244,f1254,f1281,f1399,f1408,f1425,f1434,f1443,f1462,f1473,f1482,f1553,f1570,f1607,f1625,f1689,f1701,f1708,f1794,f1872,f1882,f1894,f2011,f2101,f2115,f2161,f2175,f2182,f2189,f2196,f2219,f2250,f2262,f2267,f2272,f2274,f2276,f2282,f2285,f2288,f2296,f2299,f2432,f2449,f2458,f2477,f2478,f2487,f2494,f2506,f2513,f2536,f2552,f2555])).

fof(f2555,plain,
    ( ~ spl5_2
    | ~ spl5_14
    | spl5_173 ),
    inference(avatar_contradiction_clause,[],[f2554])).

fof(f2554,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_14
    | ~ spl5_173 ),
    inference(subsumption_resolution,[],[f2553,f226])).

fof(f226,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f225])).

fof(f225,plain,
    ( spl5_14
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f2553,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_2
    | ~ spl5_173 ),
    inference(subsumption_resolution,[],[f2550,f230])).

fof(f230,plain,
    ( ! [X0] : k4_xboole_0(X0,o_0_0_xboole_0) = X0
    | ~ spl5_2 ),
    inference(backward_demodulation,[],[f228,f122])).

fof(f122,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f43])).

fof(f43,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t94_tops_1.p',t3_boole)).

fof(f228,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f182,f127])).

fof(f127,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f50])).

fof(f50,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t94_tops_1.p',t6_boole)).

fof(f182,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f181])).

fof(f181,plain,
    ( spl5_2
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f2550,plain,
    ( k4_xboole_0(sK1,o_0_0_xboole_0) != sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_173 ),
    inference(superposition,[],[f2505,f163])).

fof(f163,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f94])).

fof(f94,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t94_tops_1.p',redefinition_k7_subset_1)).

fof(f2505,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,o_0_0_xboole_0) != sK1
    | ~ spl5_173 ),
    inference(avatar_component_clause,[],[f2504])).

fof(f2504,plain,
    ( spl5_173
  <=> k7_subset_1(u1_struct_0(sK0),sK1,o_0_0_xboole_0) != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_173])])).

fof(f2552,plain,
    ( ~ spl5_2
    | ~ spl5_14
    | spl5_173 ),
    inference(avatar_contradiction_clause,[],[f2551])).

fof(f2551,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_14
    | ~ spl5_173 ),
    inference(subsumption_resolution,[],[f2549,f230])).

fof(f2549,plain,
    ( k4_xboole_0(sK1,o_0_0_xboole_0) != sK1
    | ~ spl5_14
    | ~ spl5_173 ),
    inference(superposition,[],[f2505,f750])).

fof(f750,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)
    | ~ spl5_14 ),
    inference(unit_resulting_resolution,[],[f226,f163])).

fof(f2536,plain,
    ( spl5_176
    | ~ spl5_2
    | spl5_175 ),
    inference(avatar_split_clause,[],[f2520,f2508,f181,f2534])).

fof(f2534,plain,
    ( spl5_176
  <=> k1_zfmisc_1(o_0_0_xboole_0) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_176])])).

fof(f2508,plain,
    ( spl5_175
  <=> ~ r2_hidden(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_175])])).

fof(f2520,plain,
    ( k1_zfmisc_1(o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl5_2
    | ~ spl5_175 ),
    inference(unit_resulting_resolution,[],[f1342,f2509,f359])).

fof(f359,plain,
    ( ! [X4,X3] :
        ( r2_hidden(X3,X4)
        | ~ m1_subset_1(X3,X4)
        | o_0_0_xboole_0 = X4 )
    | ~ spl5_2 ),
    inference(resolution,[],[f147,f233])).

fof(f233,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | o_0_0_xboole_0 = X0 )
    | ~ spl5_2 ),
    inference(backward_demodulation,[],[f228,f127])).

fof(f147,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f41])).

fof(f41,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t94_tops_1.p',t2_subset)).

fof(f2509,plain,
    ( ~ r2_hidden(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_175 ),
    inference(avatar_component_clause,[],[f2508])).

fof(f1342,plain,
    ( ! [X5] : m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(X5))
    | ~ spl5_2 ),
    inference(superposition,[],[f843,f264])).

fof(f264,plain,
    ( ! [X1] : k3_xboole_0(o_0_0_xboole_0,X1) = o_0_0_xboole_0
    | ~ spl5_2 ),
    inference(superposition,[],[f143,f231])).

fof(f231,plain,
    ( ! [X0] : k3_xboole_0(X0,o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl5_2 ),
    inference(backward_demodulation,[],[f228,f123])).

fof(f123,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f40])).

fof(f40,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t94_tops_1.p',t2_boole)).

fof(f143,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t94_tops_1.p',commutativity_k3_xboole_0)).

fof(f843,plain,(
    ! [X0,X1] : m1_subset_1(k3_xboole_0(X1,sK2(k1_zfmisc_1(X0))),k1_zfmisc_1(X0)) ),
    inference(backward_demodulation,[],[f834,f644])).

fof(f644,plain,(
    ! [X0,X1] : m1_subset_1(k9_subset_1(X0,X1,sK2(k1_zfmisc_1(X0))),k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f141,f162])).

fof(f162,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f93])).

fof(f93,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t94_tops_1.p',dt_k9_subset_1)).

fof(f141,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(cnf_transformation,[],[f110])).

fof(f110,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f109])).

fof(f109,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f29,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t94_tops_1.p',existence_m1_subset_1)).

fof(f834,plain,(
    ! [X0,X1] : k3_xboole_0(X0,sK2(k1_zfmisc_1(X1))) = k9_subset_1(X1,X0,sK2(k1_zfmisc_1(X1))) ),
    inference(unit_resulting_resolution,[],[f141,f164])).

fof(f164,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f95])).

fof(f95,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t94_tops_1.p',redefinition_k9_subset_1)).

fof(f2513,plain,
    ( spl5_174
    | ~ spl5_104
    | ~ spl5_120 ),
    inference(avatar_split_clause,[],[f2462,f1565,f1403,f2511])).

fof(f2511,plain,
    ( spl5_174
  <=> r2_hidden(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_174])])).

fof(f1403,plain,
    ( spl5_104
  <=> k1_tops_1(sK0,sK1) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_104])])).

fof(f1565,plain,
    ( spl5_120
  <=> r2_hidden(k1_tops_1(sK0,sK1),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_120])])).

fof(f2462,plain,
    ( r2_hidden(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_104
    | ~ spl5_120 ),
    inference(forward_demodulation,[],[f1566,f1404])).

fof(f1404,plain,
    ( k1_tops_1(sK0,sK1) = o_0_0_xboole_0
    | ~ spl5_104 ),
    inference(avatar_component_clause,[],[f1403])).

fof(f1566,plain,
    ( r2_hidden(k1_tops_1(sK0,sK1),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_120 ),
    inference(avatar_component_clause,[],[f1565])).

fof(f2506,plain,
    ( ~ spl5_173
    | ~ spl5_104
    | spl5_147 ),
    inference(avatar_split_clause,[],[f2361,f2156,f1403,f2504])).

fof(f2156,plain,
    ( spl5_147
  <=> k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_147])])).

fof(f2361,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,o_0_0_xboole_0) != sK1
    | ~ spl5_104
    | ~ spl5_147 ),
    inference(backward_demodulation,[],[f1404,f2157])).

fof(f2157,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != sK1
    | ~ spl5_147 ),
    inference(avatar_component_clause,[],[f2156])).

fof(f2494,plain,
    ( ~ spl5_171
    | ~ spl5_2
    | spl5_165 ),
    inference(avatar_split_clause,[],[f2467,f2453,f181,f2492])).

fof(f2492,plain,
    ( spl5_171
  <=> ~ r1_tarski(sK2(o_0_0_xboole_0),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_171])])).

fof(f2453,plain,
    ( spl5_165
  <=> o_0_0_xboole_0 != sK2(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_165])])).

fof(f2467,plain,
    ( ~ r1_tarski(sK2(o_0_0_xboole_0),o_0_0_xboole_0)
    | ~ spl5_2
    | ~ spl5_165 ),
    inference(unit_resulting_resolution,[],[f2454,f380])).

fof(f380,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,o_0_0_xboole_0)
        | o_0_0_xboole_0 = X1 )
    | ~ spl5_2 ),
    inference(superposition,[],[f236,f232])).

fof(f232,plain,
    ( ! [X0] : o_0_0_xboole_0 = k4_xboole_0(o_0_0_xboole_0,X0)
    | ~ spl5_2 ),
    inference(backward_demodulation,[],[f228,f124])).

fof(f124,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f46])).

fof(f46,axiom,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t94_tops_1.p',t4_boole)).

fof(f236,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,k4_xboole_0(X1,X0))
        | o_0_0_xboole_0 = X0 )
    | ~ spl5_2 ),
    inference(backward_demodulation,[],[f228,f150])).

fof(f150,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(ennf_transformation,[],[f42])).

fof(f42,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X0))
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t94_tops_1.p',t38_xboole_1)).

fof(f2454,plain,
    ( o_0_0_xboole_0 != sK2(o_0_0_xboole_0)
    | ~ spl5_165 ),
    inference(avatar_component_clause,[],[f2453])).

fof(f2487,plain,
    ( ~ spl5_169
    | ~ spl5_104
    | spl5_153 ),
    inference(avatar_split_clause,[],[f2363,f2187,f1403,f2485])).

fof(f2485,plain,
    ( spl5_169
  <=> ~ r2_hidden(o_0_0_xboole_0,sK2(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_169])])).

fof(f2187,plain,
    ( spl5_153
  <=> ~ r2_hidden(k1_tops_1(sK0,sK1),sK2(k1_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_153])])).

fof(f2363,plain,
    ( ~ r2_hidden(o_0_0_xboole_0,sK2(o_0_0_xboole_0))
    | ~ spl5_104
    | ~ spl5_153 ),
    inference(backward_demodulation,[],[f1404,f2188])).

fof(f2188,plain,
    ( ~ r2_hidden(k1_tops_1(sK0,sK1),sK2(k1_tops_1(sK0,sK1)))
    | ~ spl5_153 ),
    inference(avatar_component_clause,[],[f2187])).

fof(f2478,plain,
    ( ~ spl5_27
    | ~ spl5_29 ),
    inference(avatar_split_clause,[],[f120,f299,f293])).

fof(f293,plain,
    ( spl5_27
  <=> ~ v3_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f299,plain,
    ( spl5_29
  <=> k2_tops_1(sK0,sK1) != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f120,plain,
    ( k2_tops_1(sK0,sK1) != sK1
    | ~ v3_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f104])).

fof(f104,plain,
    ( ( k2_tops_1(sK0,sK1) != sK1
      | ~ v3_tops_1(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = sK1
      | v3_tops_1(sK1,sK0) )
    & v4_pre_topc(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f101,f103,f102])).

fof(f102,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k2_tops_1(X0,X1) != X1
              | ~ v3_tops_1(X1,X0) )
            & ( k2_tops_1(X0,X1) = X1
              | v3_tops_1(X1,X0) )
            & v4_pre_topc(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k2_tops_1(sK0,X1) != X1
            | ~ v3_tops_1(X1,sK0) )
          & ( k2_tops_1(sK0,X1) = X1
            | v3_tops_1(X1,sK0) )
          & v4_pre_topc(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f103,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != X1
            | ~ v3_tops_1(X1,X0) )
          & ( k2_tops_1(X0,X1) = X1
            | v3_tops_1(X1,X0) )
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( k2_tops_1(X0,sK1) != sK1
          | ~ v3_tops_1(sK1,X0) )
        & ( k2_tops_1(X0,sK1) = sK1
          | v3_tops_1(sK1,X0) )
        & v4_pre_topc(sK1,X0)
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f101,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != X1
            | ~ v3_tops_1(X1,X0) )
          & ( k2_tops_1(X0,X1) = X1
            | v3_tops_1(X1,X0) )
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f100])).

fof(f100,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != X1
            | ~ v3_tops_1(X1,X0) )
          & ( k2_tops_1(X0,X1) = X1
            | v3_tops_1(X1,X0) )
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f57])).

fof(f57,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tops_1(X1,X0)
          <~> k2_tops_1(X0,X1) = X1 )
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tops_1(X1,X0)
          <~> k2_tops_1(X0,X1) = X1 )
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
             => ( v3_tops_1(X1,X0)
              <=> k2_tops_1(X0,X1) = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => ( v3_tops_1(X1,X0)
            <=> k2_tops_1(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t94_tops_1.p',t94_tops_1)).

fof(f2477,plain,
    ( ~ spl5_167
    | ~ spl5_2
    | spl5_165 ),
    inference(avatar_split_clause,[],[f2470,f2453,f181,f2475])).

fof(f2475,plain,
    ( spl5_167
  <=> ~ v1_xboole_0(sK2(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_167])])).

fof(f2470,plain,
    ( ~ v1_xboole_0(sK2(o_0_0_xboole_0))
    | ~ spl5_2
    | ~ spl5_165 ),
    inference(unit_resulting_resolution,[],[f182,f2454,f158])).

fof(f158,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f53])).

fof(f53,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t94_tops_1.p',t8_boole)).

fof(f2458,plain,
    ( spl5_164
    | ~ spl5_2
    | ~ spl5_44
    | ~ spl5_48
    | ~ spl5_104
    | spl5_121 ),
    inference(avatar_split_clause,[],[f2386,f1568,f1403,f421,f398,f181,f2456])).

fof(f2456,plain,
    ( spl5_164
  <=> o_0_0_xboole_0 = sK2(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_164])])).

fof(f398,plain,
    ( spl5_44
  <=> o_0_0_xboole_0 = sK2(k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).

fof(f421,plain,
    ( spl5_48
  <=> m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_48])])).

fof(f1568,plain,
    ( spl5_121
  <=> ~ r2_hidden(k1_tops_1(sK0,sK1),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_121])])).

fof(f2386,plain,
    ( o_0_0_xboole_0 = sK2(o_0_0_xboole_0)
    | ~ spl5_2
    | ~ spl5_44
    | ~ spl5_48
    | ~ spl5_104
    | ~ spl5_121 ),
    inference(backward_demodulation,[],[f2384,f399])).

fof(f399,plain,
    ( o_0_0_xboole_0 = sK2(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_44 ),
    inference(avatar_component_clause,[],[f398])).

fof(f2384,plain,
    ( k1_zfmisc_1(o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl5_2
    | ~ spl5_48
    | ~ spl5_104
    | ~ spl5_121 ),
    inference(subsumption_resolution,[],[f2329,f422])).

fof(f422,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_48 ),
    inference(avatar_component_clause,[],[f421])).

fof(f2329,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | k1_zfmisc_1(o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl5_2
    | ~ spl5_104
    | ~ spl5_121 ),
    inference(backward_demodulation,[],[f1404,f1571])).

fof(f1571,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(o_0_0_xboole_0))
    | k1_zfmisc_1(o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl5_2
    | ~ spl5_121 ),
    inference(resolution,[],[f1569,f359])).

fof(f1569,plain,
    ( ~ r2_hidden(k1_tops_1(sK0,sK1),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_121 ),
    inference(avatar_component_clause,[],[f1568])).

fof(f2449,plain,
    ( spl5_162
    | ~ spl5_2
    | ~ spl5_48
    | ~ spl5_104
    | spl5_121 ),
    inference(avatar_split_clause,[],[f2387,f1568,f1403,f421,f181,f2447])).

fof(f2447,plain,
    ( spl5_162
  <=> m1_subset_1(o_0_0_xboole_0,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_162])])).

fof(f2387,plain,
    ( m1_subset_1(o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ spl5_2
    | ~ spl5_48
    | ~ spl5_104
    | ~ spl5_121 ),
    inference(backward_demodulation,[],[f2384,f422])).

fof(f2432,plain,
    ( ~ spl5_2
    | ~ spl5_104
    | spl5_161 ),
    inference(avatar_contradiction_clause,[],[f2431])).

fof(f2431,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_104
    | ~ spl5_161 ),
    inference(subsumption_resolution,[],[f2372,f230])).

fof(f2372,plain,
    ( k4_xboole_0(sK1,o_0_0_xboole_0) != sK1
    | ~ spl5_104
    | ~ spl5_161 ),
    inference(backward_demodulation,[],[f1404,f2258])).

fof(f2258,plain,
    ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) != sK1
    | ~ spl5_161 ),
    inference(avatar_component_clause,[],[f2257])).

fof(f2257,plain,
    ( spl5_161
  <=> k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_161])])).

fof(f2299,plain,
    ( ~ spl5_2
    | ~ spl5_62
    | spl5_105
    | ~ spl5_160 ),
    inference(avatar_contradiction_clause,[],[f2298])).

fof(f2298,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_62
    | ~ spl5_105
    | ~ spl5_160 ),
    inference(subsumption_resolution,[],[f2297,f1407])).

fof(f1407,plain,
    ( k1_tops_1(sK0,sK1) != o_0_0_xboole_0
    | ~ spl5_105 ),
    inference(avatar_component_clause,[],[f1406])).

fof(f1406,plain,
    ( spl5_105
  <=> k1_tops_1(sK0,sK1) != o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_105])])).

fof(f2297,plain,
    ( k1_tops_1(sK0,sK1) = o_0_0_xboole_0
    | ~ spl5_2
    | ~ spl5_62
    | ~ spl5_160 ),
    inference(subsumption_resolution,[],[f2293,f714])).

fof(f714,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl5_62 ),
    inference(avatar_component_clause,[],[f713])).

fof(f713,plain,
    ( spl5_62
  <=> r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_62])])).

fof(f2293,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | k1_tops_1(sK0,sK1) = o_0_0_xboole_0
    | ~ spl5_2
    | ~ spl5_160 ),
    inference(superposition,[],[f236,f2261])).

fof(f2261,plain,
    ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = sK1
    | ~ spl5_160 ),
    inference(avatar_component_clause,[],[f2260])).

fof(f2260,plain,
    ( spl5_160
  <=> k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_160])])).

fof(f2296,plain,
    ( ~ spl5_2
    | ~ spl5_64
    | spl5_105
    | ~ spl5_160 ),
    inference(avatar_contradiction_clause,[],[f2295])).

fof(f2295,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_64
    | ~ spl5_105
    | ~ spl5_160 ),
    inference(subsumption_resolution,[],[f2294,f1407])).

fof(f2294,plain,
    ( k1_tops_1(sK0,sK1) = o_0_0_xboole_0
    | ~ spl5_2
    | ~ spl5_64
    | ~ spl5_160 ),
    inference(subsumption_resolution,[],[f2292,f724])).

fof(f724,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl5_64 ),
    inference(avatar_component_clause,[],[f723])).

fof(f723,plain,
    ( spl5_64
  <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_64])])).

fof(f2292,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | k1_tops_1(sK0,sK1) = o_0_0_xboole_0
    | ~ spl5_2
    | ~ spl5_160 ),
    inference(superposition,[],[f378,f2261])).

fof(f378,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k4_xboole_0(X1,X0)))
        | o_0_0_xboole_0 = X0 )
    | ~ spl5_2 ),
    inference(resolution,[],[f236,f156])).

fof(f156,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f44,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t94_tops_1.p',t3_subset)).

fof(f2288,plain,
    ( spl5_28
    | ~ spl5_0
    | ~ spl5_14
    | ~ spl5_90
    | ~ spl5_146 ),
    inference(avatar_split_clause,[],[f2277,f2159,f1169,f225,f174,f302])).

fof(f302,plain,
    ( spl5_28
  <=> k2_tops_1(sK0,sK1) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f174,plain,
    ( spl5_0
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_0])])).

fof(f1169,plain,
    ( spl5_90
  <=> k2_pre_topc(sK0,sK1) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_90])])).

fof(f2159,plain,
    ( spl5_146
  <=> k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_146])])).

fof(f2277,plain,
    ( k2_tops_1(sK0,sK1) = sK1
    | ~ spl5_0
    | ~ spl5_14
    | ~ spl5_90
    | ~ spl5_146 ),
    inference(backward_demodulation,[],[f2160,f1735])).

fof(f1735,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl5_0
    | ~ spl5_14
    | ~ spl5_90 ),
    inference(forward_demodulation,[],[f1729,f1170])).

fof(f1170,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | ~ spl5_90 ),
    inference(avatar_component_clause,[],[f1169])).

fof(f1729,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl5_0
    | ~ spl5_14 ),
    inference(unit_resulting_resolution,[],[f175,f226,f130])).

fof(f130,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t94_tops_1.p',l78_tops_1)).

fof(f175,plain,
    ( l1_pre_topc(sK0)
    | ~ spl5_0 ),
    inference(avatar_component_clause,[],[f174])).

fof(f2160,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = sK1
    | ~ spl5_146 ),
    inference(avatar_component_clause,[],[f2159])).

fof(f2285,plain,
    ( ~ spl5_99
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_14
    | spl5_105 ),
    inference(avatar_split_clause,[],[f1409,f1406,f225,f181,f174,f1252])).

fof(f1252,plain,
    ( spl5_99
  <=> ~ v2_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_99])])).

fof(f1409,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_14
    | ~ spl5_105 ),
    inference(unit_resulting_resolution,[],[f175,f226,f1407,f234])).

fof(f234,plain,
    ( ! [X0,X1] :
        ( ~ v2_tops_1(X1,X0)
        | k1_tops_1(X0,X1) = o_0_0_xboole_0
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl5_2 ),
    inference(backward_demodulation,[],[f228,f137])).

fof(f137,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_xboole_0
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f107])).

fof(f107,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | k1_tops_1(X0,X1) != k1_xboole_0 )
            & ( k1_tops_1(X0,X1) = k1_xboole_0
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_tops_1(X0,X1) = k1_xboole_0 )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f52])).

fof(f52,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_tops_1(X0,X1) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t94_tops_1.p',t84_tops_1)).

fof(f2282,plain,
    ( ~ spl5_27
    | ~ spl5_0
    | ~ spl5_14
    | ~ spl5_90
    | ~ spl5_146 ),
    inference(avatar_split_clause,[],[f2281,f2159,f1169,f225,f174,f293])).

fof(f2281,plain,
    ( ~ v3_tops_1(sK1,sK0)
    | ~ spl5_0
    | ~ spl5_14
    | ~ spl5_90
    | ~ spl5_146 ),
    inference(trivial_inequality_removal,[],[f2278])).

fof(f2278,plain,
    ( sK1 != sK1
    | ~ v3_tops_1(sK1,sK0)
    | ~ spl5_0
    | ~ spl5_14
    | ~ spl5_90
    | ~ spl5_146 ),
    inference(backward_demodulation,[],[f2277,f120])).

fof(f2276,plain,
    ( ~ spl5_0
    | ~ spl5_2
    | ~ spl5_14
    | ~ spl5_26
    | ~ spl5_90
    | spl5_105 ),
    inference(avatar_contradiction_clause,[],[f2275])).

fof(f2275,plain,
    ( $false
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_14
    | ~ spl5_26
    | ~ spl5_90
    | ~ spl5_105 ),
    inference(subsumption_resolution,[],[f1409,f2270])).

fof(f2270,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ spl5_0
    | ~ spl5_14
    | ~ spl5_26
    | ~ spl5_90 ),
    inference(forward_demodulation,[],[f2269,f1170])).

fof(f2269,plain,
    ( v2_tops_1(k2_pre_topc(sK0,sK1),sK0)
    | ~ spl5_0
    | ~ spl5_14
    | ~ spl5_26 ),
    inference(subsumption_resolution,[],[f2268,f175])).

fof(f2268,plain,
    ( v2_tops_1(k2_pre_topc(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl5_14
    | ~ spl5_26 ),
    inference(subsumption_resolution,[],[f2264,f226])).

fof(f2264,plain,
    ( v2_tops_1(k2_pre_topc(sK0,sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl5_26 ),
    inference(resolution,[],[f297,f133])).

fof(f133,plain,(
    ! [X0,X1] :
      ( ~ v3_tops_1(X1,X0)
      | v2_tops_1(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f105])).

fof(f105,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tops_1(X1,X0)
              | ~ v2_tops_1(k2_pre_topc(X0,X1),X0) )
            & ( v2_tops_1(k2_pre_topc(X0,X1),X0)
              | ~ v3_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tops_1(X1,X0)
          <=> v2_tops_1(k2_pre_topc(X0,X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tops_1(X1,X0)
          <=> v2_tops_1(k2_pre_topc(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t94_tops_1.p',d5_tops_1)).

fof(f297,plain,
    ( v3_tops_1(sK1,sK0)
    | ~ spl5_26 ),
    inference(avatar_component_clause,[],[f296])).

fof(f296,plain,
    ( spl5_26
  <=> v3_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f2274,plain,
    ( ~ spl5_0
    | ~ spl5_14
    | ~ spl5_26
    | ~ spl5_90
    | spl5_119 ),
    inference(avatar_contradiction_clause,[],[f2273])).

fof(f2273,plain,
    ( $false
    | ~ spl5_0
    | ~ spl5_14
    | ~ spl5_26
    | ~ spl5_90
    | ~ spl5_119 ),
    inference(subsumption_resolution,[],[f1554,f2270])).

fof(f1554,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | ~ spl5_0
    | ~ spl5_14
    | ~ spl5_119 ),
    inference(unit_resulting_resolution,[],[f175,f226,f1552,f139])).

fof(f139,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ),
    inference(cnf_transformation,[],[f108])).

fof(f108,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t94_tops_1.p',d4_tops_1)).

fof(f1552,plain,
    ( ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl5_119 ),
    inference(avatar_component_clause,[],[f1551])).

fof(f1551,plain,
    ( spl5_119
  <=> ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_119])])).

fof(f2272,plain,
    ( ~ spl5_0
    | ~ spl5_14
    | ~ spl5_26
    | ~ spl5_90
    | spl5_99 ),
    inference(avatar_contradiction_clause,[],[f2271])).

fof(f2271,plain,
    ( $false
    | ~ spl5_0
    | ~ spl5_14
    | ~ spl5_26
    | ~ spl5_90
    | ~ spl5_99 ),
    inference(subsumption_resolution,[],[f2270,f1253])).

fof(f1253,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | ~ spl5_99 ),
    inference(avatar_component_clause,[],[f1252])).

fof(f2267,plain,
    ( ~ spl5_0
    | ~ spl5_14
    | ~ spl5_26
    | ~ spl5_90
    | spl5_99 ),
    inference(avatar_contradiction_clause,[],[f2266])).

fof(f2266,plain,
    ( $false
    | ~ spl5_0
    | ~ spl5_14
    | ~ spl5_26
    | ~ spl5_90
    | ~ spl5_99 ),
    inference(subsumption_resolution,[],[f2265,f1253])).

fof(f2265,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ spl5_0
    | ~ spl5_14
    | ~ spl5_26
    | ~ spl5_90 ),
    inference(forward_demodulation,[],[f2263,f1170])).

fof(f2263,plain,
    ( v2_tops_1(k2_pre_topc(sK0,sK1),sK0)
    | ~ spl5_0
    | ~ spl5_14
    | ~ spl5_26 ),
    inference(unit_resulting_resolution,[],[f175,f226,f297,f133])).

fof(f2262,plain,
    ( spl5_160
    | ~ spl5_14
    | ~ spl5_146 ),
    inference(avatar_split_clause,[],[f2251,f2159,f225,f2260])).

fof(f2251,plain,
    ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = sK1
    | ~ spl5_14
    | ~ spl5_146 ),
    inference(superposition,[],[f2160,f750])).

fof(f2250,plain,
    ( spl5_158
    | ~ spl5_148 ),
    inference(avatar_split_clause,[],[f2233,f2173,f2248])).

fof(f2248,plain,
    ( spl5_158
  <=> r1_tarski(k2_tops_1(sK0,u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_158])])).

fof(f2173,plain,
    ( spl5_148
  <=> m1_subset_1(k2_tops_1(sK0,u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_148])])).

fof(f2233,plain,
    ( r1_tarski(k2_tops_1(sK0,u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl5_148 ),
    inference(unit_resulting_resolution,[],[f2174,f156])).

fof(f2174,plain,
    ( m1_subset_1(k2_tops_1(sK0,u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_148 ),
    inference(avatar_component_clause,[],[f2173])).

fof(f2219,plain,
    ( spl5_156
    | ~ spl5_140 ),
    inference(avatar_split_clause,[],[f2201,f2009,f2217])).

fof(f2217,plain,
    ( spl5_156
  <=> r1_tarski(k3_subset_1(sK1,k1_tops_1(sK0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_156])])).

fof(f2009,plain,
    ( spl5_140
  <=> m1_subset_1(k3_subset_1(sK1,k1_tops_1(sK0,sK1)),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_140])])).

fof(f2201,plain,
    ( r1_tarski(k3_subset_1(sK1,k1_tops_1(sK0,sK1)),sK1)
    | ~ spl5_140 ),
    inference(unit_resulting_resolution,[],[f2010,f156])).

fof(f2010,plain,
    ( m1_subset_1(k3_subset_1(sK1,k1_tops_1(sK0,sK1)),k1_zfmisc_1(sK1))
    | ~ spl5_140 ),
    inference(avatar_component_clause,[],[f2009])).

fof(f2196,plain,
    ( spl5_154
    | ~ spl5_126 ),
    inference(avatar_split_clause,[],[f1691,f1687,f2194])).

fof(f2194,plain,
    ( spl5_154
  <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k1_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_154])])).

fof(f1687,plain,
    ( spl5_126
  <=> r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_126])])).

fof(f1691,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k1_tops_1(sK0,sK1)))
    | ~ spl5_126 ),
    inference(unit_resulting_resolution,[],[f1688,f157])).

fof(f157,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f111])).

fof(f1688,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl5_126 ),
    inference(avatar_component_clause,[],[f1687])).

fof(f2189,plain,
    ( ~ spl5_153
    | ~ spl5_2
    | spl5_105 ),
    inference(avatar_split_clause,[],[f1417,f1406,f181,f2187])).

fof(f1417,plain,
    ( ~ r2_hidden(k1_tops_1(sK0,sK1),sK2(k1_tops_1(sK0,sK1)))
    | ~ spl5_2
    | ~ spl5_105 ),
    inference(unit_resulting_resolution,[],[f141,f1407,f537])).

fof(f537,plain,
    ( ! [X8,X9] :
        ( ~ r2_hidden(X9,X8)
        | o_0_0_xboole_0 = X9
        | ~ m1_subset_1(X8,X9) )
    | ~ spl5_2 ),
    inference(resolution,[],[f359,f145])).

fof(f145,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t94_tops_1.p',antisymmetry_r2_hidden)).

fof(f2182,plain,
    ( spl5_150
    | ~ spl5_2
    | spl5_105 ),
    inference(avatar_split_clause,[],[f1413,f1406,f181,f2180])).

fof(f2180,plain,
    ( spl5_150
  <=> r2_hidden(sK2(k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_150])])).

fof(f1413,plain,
    ( r2_hidden(sK2(k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1))
    | ~ spl5_2
    | ~ spl5_105 ),
    inference(unit_resulting_resolution,[],[f141,f1407,f359])).

fof(f2175,plain,
    ( spl5_148
    | ~ spl5_0
    | ~ spl5_34 ),
    inference(avatar_split_clause,[],[f968,f346,f174,f2173])).

fof(f346,plain,
    ( spl5_34
  <=> m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).

fof(f968,plain,
    ( m1_subset_1(k2_tops_1(sK0,u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_0
    | ~ spl5_34 ),
    inference(unit_resulting_resolution,[],[f175,f347,f151])).

fof(f151,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t94_tops_1.p',dt_k2_tops_1)).

fof(f347,plain,
    ( m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_34 ),
    inference(avatar_component_clause,[],[f346])).

fof(f2161,plain,
    ( spl5_146
    | ~ spl5_0
    | ~ spl5_14
    | ~ spl5_28
    | ~ spl5_90 ),
    inference(avatar_split_clause,[],[f1736,f1169,f302,f225,f174,f2159])).

fof(f1736,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = sK1
    | ~ spl5_0
    | ~ spl5_14
    | ~ spl5_28
    | ~ spl5_90 ),
    inference(forward_demodulation,[],[f1735,f303])).

fof(f303,plain,
    ( k2_tops_1(sK0,sK1) = sK1
    | ~ spl5_28 ),
    inference(avatar_component_clause,[],[f302])).

fof(f2115,plain,
    ( spl5_144
    | ~ spl5_64 ),
    inference(avatar_split_clause,[],[f2094,f723,f2113])).

fof(f2113,plain,
    ( spl5_144
  <=> r1_tarski(sK2(k1_zfmisc_1(k1_tops_1(sK0,sK1))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_144])])).

fof(f2094,plain,
    ( r1_tarski(sK2(k1_zfmisc_1(k1_tops_1(sK0,sK1))),sK1)
    | ~ spl5_64 ),
    inference(superposition,[],[f2071,f328])).

fof(f328,plain,(
    ! [X0] : k3_xboole_0(sK2(k1_zfmisc_1(X0)),X0) = sK2(k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f279,f144])).

fof(f144,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f39])).

fof(f39,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t94_tops_1.p',t28_xboole_1)).

fof(f279,plain,(
    ! [X0] : r1_tarski(sK2(k1_zfmisc_1(X0)),X0) ),
    inference(unit_resulting_resolution,[],[f141,f156])).

fof(f2071,plain,
    ( ! [X0] : r1_tarski(k3_xboole_0(X0,k1_tops_1(sK0,sK1)),sK1)
    | ~ spl5_64 ),
    inference(unit_resulting_resolution,[],[f855,f156])).

fof(f855,plain,
    ( ! [X0] : m1_subset_1(k3_xboole_0(X0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(sK1))
    | ~ spl5_64 ),
    inference(backward_demodulation,[],[f830,f730])).

fof(f730,plain,
    ( ! [X0] : m1_subset_1(k9_subset_1(sK1,X0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(sK1))
    | ~ spl5_64 ),
    inference(unit_resulting_resolution,[],[f724,f162])).

fof(f830,plain,
    ( ! [X0] : k3_xboole_0(X0,k1_tops_1(sK0,sK1)) = k9_subset_1(sK1,X0,k1_tops_1(sK0,sK1))
    | ~ spl5_64 ),
    inference(unit_resulting_resolution,[],[f724,f164])).

fof(f2101,plain,
    ( spl5_142
    | ~ spl5_0
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f1671,f225,f174,f2099])).

fof(f2099,plain,
    ( spl5_142
  <=> k1_tops_1(sK0,sK1) = k1_tops_1(sK0,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_142])])).

fof(f1671,plain,
    ( k1_tops_1(sK0,sK1) = k1_tops_1(sK0,k1_tops_1(sK0,sK1))
    | ~ spl5_0
    | ~ spl5_14 ),
    inference(unit_resulting_resolution,[],[f175,f226,f155])).

fof(f155,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t94_tops_1.p',projectivity_k1_tops_1)).

fof(f2011,plain,
    ( spl5_140
    | ~ spl5_64 ),
    inference(avatar_split_clause,[],[f726,f723,f2009])).

fof(f726,plain,
    ( m1_subset_1(k3_subset_1(sK1,k1_tops_1(sK0,sK1)),k1_zfmisc_1(sK1))
    | ~ spl5_64 ),
    inference(unit_resulting_resolution,[],[f724,f148])).

fof(f148,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t94_tops_1.p',dt_k3_subset_1)).

fof(f1894,plain,
    ( spl5_138
    | ~ spl5_2
    | ~ spl5_6
    | ~ spl5_22
    | ~ spl5_122 ),
    inference(avatar_split_clause,[],[f1612,f1605,f276,f195,f181,f1892])).

fof(f1892,plain,
    ( spl5_138
  <=> u1_struct_0(sK4) = k2_pre_topc(sK4,u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_138])])).

fof(f195,plain,
    ( spl5_6
  <=> l1_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f276,plain,
    ( spl5_22
  <=> u1_struct_0(sK4) = k2_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f1605,plain,
    ( spl5_122
  <=> v1_tops_1(k3_subset_1(u1_struct_0(sK4),o_0_0_xboole_0),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_122])])).

fof(f1612,plain,
    ( u1_struct_0(sK4) = k2_pre_topc(sK4,u1_struct_0(sK4))
    | ~ spl5_2
    | ~ spl5_6
    | ~ spl5_22
    | ~ spl5_122 ),
    inference(backward_demodulation,[],[f1611,f1584])).

fof(f1584,plain,
    ( k2_pre_topc(sK4,k3_subset_1(u1_struct_0(sK4),o_0_0_xboole_0)) = k2_pre_topc(sK4,k2_pre_topc(sK4,k3_subset_1(u1_struct_0(sK4),o_0_0_xboole_0)))
    | ~ spl5_2
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f196,f1352,f154])).

fof(f154,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t94_tops_1.p',projectivity_k2_pre_topc)).

fof(f1352,plain,
    ( ! [X0] : m1_subset_1(k3_subset_1(X0,o_0_0_xboole_0),k1_zfmisc_1(X0))
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f1342,f148])).

fof(f196,plain,
    ( l1_pre_topc(sK4)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f195])).

fof(f1611,plain,
    ( u1_struct_0(sK4) = k2_pre_topc(sK4,k3_subset_1(u1_struct_0(sK4),o_0_0_xboole_0))
    | ~ spl5_2
    | ~ spl5_6
    | ~ spl5_22
    | ~ spl5_122 ),
    inference(forward_demodulation,[],[f1609,f277])).

fof(f277,plain,
    ( u1_struct_0(sK4) = k2_struct_0(sK4)
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f276])).

fof(f1609,plain,
    ( k2_pre_topc(sK4,k3_subset_1(u1_struct_0(sK4),o_0_0_xboole_0)) = k2_struct_0(sK4)
    | ~ spl5_2
    | ~ spl5_6
    | ~ spl5_122 ),
    inference(unit_resulting_resolution,[],[f196,f1352,f1606,f135])).

fof(f135,plain,(
    ! [X0,X1] :
      ( ~ v1_tops_1(X1,X0)
      | k2_pre_topc(X0,X1) = k2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f106])).

fof(f106,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_pre_topc(X0,X1) != k2_struct_0(X0) )
            & ( k2_pre_topc(X0,X1) = k2_struct_0(X0)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_pre_topc(X0,X1) = k2_struct_0(X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_pre_topc(X0,X1) = k2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t94_tops_1.p',d3_tops_1)).

fof(f1606,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(sK4),o_0_0_xboole_0),sK4)
    | ~ spl5_122 ),
    inference(avatar_component_clause,[],[f1605])).

fof(f1882,plain,
    ( spl5_136
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_20
    | ~ spl5_124 ),
    inference(avatar_split_clause,[],[f1630,f1623,f261,f181,f174,f1880])).

fof(f1880,plain,
    ( spl5_136
  <=> u1_struct_0(sK0) = k2_pre_topc(sK0,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_136])])).

fof(f261,plain,
    ( spl5_20
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f1623,plain,
    ( spl5_124
  <=> v1_tops_1(k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_124])])).

fof(f1630,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,u1_struct_0(sK0))
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_20
    | ~ spl5_124 ),
    inference(backward_demodulation,[],[f1629,f1583])).

fof(f1583,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0)) = k2_pre_topc(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0)))
    | ~ spl5_0
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f175,f1352,f154])).

fof(f1629,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0))
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_20
    | ~ spl5_124 ),
    inference(forward_demodulation,[],[f1627,f262])).

fof(f262,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f261])).

fof(f1627,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0)) = k2_struct_0(sK0)
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_124 ),
    inference(unit_resulting_resolution,[],[f175,f1352,f1624,f135])).

fof(f1624,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0),sK0)
    | ~ spl5_124 ),
    inference(avatar_component_clause,[],[f1623])).

fof(f1872,plain,
    ( spl5_134
    | ~ spl5_130 ),
    inference(avatar_split_clause,[],[f1851,f1706,f1870])).

fof(f1870,plain,
    ( spl5_134
  <=> r1_tarski(k2_pre_topc(sK4,o_0_0_xboole_0),u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_134])])).

fof(f1706,plain,
    ( spl5_130
  <=> m1_subset_1(k2_pre_topc(sK4,o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_130])])).

fof(f1851,plain,
    ( r1_tarski(k2_pre_topc(sK4,o_0_0_xboole_0),u1_struct_0(sK4))
    | ~ spl5_130 ),
    inference(unit_resulting_resolution,[],[f1707,f156])).

fof(f1707,plain,
    ( m1_subset_1(k2_pre_topc(sK4,o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ spl5_130 ),
    inference(avatar_component_clause,[],[f1706])).

fof(f1794,plain,
    ( spl5_132
    | ~ spl5_128 ),
    inference(avatar_split_clause,[],[f1777,f1699,f1792])).

fof(f1792,plain,
    ( spl5_132
  <=> r1_tarski(k2_tops_1(sK4,o_0_0_xboole_0),u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_132])])).

fof(f1699,plain,
    ( spl5_128
  <=> m1_subset_1(k2_tops_1(sK4,o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_128])])).

fof(f1777,plain,
    ( r1_tarski(k2_tops_1(sK4,o_0_0_xboole_0),u1_struct_0(sK4))
    | ~ spl5_128 ),
    inference(unit_resulting_resolution,[],[f1700,f156])).

fof(f1700,plain,
    ( m1_subset_1(k2_tops_1(sK4,o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ spl5_128 ),
    inference(avatar_component_clause,[],[f1699])).

fof(f1708,plain,
    ( spl5_130
    | ~ spl5_2
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f1367,f195,f181,f1706])).

fof(f1367,plain,
    ( m1_subset_1(k2_pre_topc(sK4,o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ spl5_2
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f196,f1342,f152])).

fof(f152,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t94_tops_1.p',dt_k2_pre_topc)).

fof(f1701,plain,
    ( spl5_128
    | ~ spl5_2
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f1365,f195,f181,f1699])).

fof(f1365,plain,
    ( m1_subset_1(k2_tops_1(sK4,o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ spl5_2
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f196,f1342,f151])).

fof(f1689,plain,
    ( spl5_126
    | ~ spl5_0
    | ~ spl5_14
    | ~ spl5_84 ),
    inference(avatar_split_clause,[],[f1678,f1110,f225,f174,f1687])).

fof(f1110,plain,
    ( spl5_84
  <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_84])])).

fof(f1678,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl5_0
    | ~ spl5_14
    | ~ spl5_84 ),
    inference(backward_demodulation,[],[f1671,f1116])).

fof(f1116,plain,
    ( r1_tarski(k1_tops_1(sK0,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1))
    | ~ spl5_0
    | ~ spl5_84 ),
    inference(unit_resulting_resolution,[],[f175,f1111,f129])).

fof(f129,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f45])).

fof(f45,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t94_tops_1.p',t44_tops_1)).

fof(f1111,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_84 ),
    inference(avatar_component_clause,[],[f1110])).

fof(f1625,plain,
    ( spl5_124
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_102 ),
    inference(avatar_split_clause,[],[f1484,f1397,f181,f174,f1623])).

fof(f1397,plain,
    ( spl5_102
  <=> v2_tops_1(o_0_0_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_102])])).

fof(f1484,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0),sK0)
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_102 ),
    inference(unit_resulting_resolution,[],[f175,f1398,f1342,f139])).

fof(f1398,plain,
    ( v2_tops_1(o_0_0_xboole_0,sK0)
    | ~ spl5_102 ),
    inference(avatar_component_clause,[],[f1397])).

fof(f1607,plain,
    ( spl5_122
    | ~ spl5_2
    | ~ spl5_6
    | ~ spl5_114 ),
    inference(avatar_split_clause,[],[f1485,f1471,f195,f181,f1605])).

fof(f1471,plain,
    ( spl5_114
  <=> v2_tops_1(o_0_0_xboole_0,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_114])])).

fof(f1485,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(sK4),o_0_0_xboole_0),sK4)
    | ~ spl5_2
    | ~ spl5_6
    | ~ spl5_114 ),
    inference(unit_resulting_resolution,[],[f196,f1472,f1342,f139])).

fof(f1472,plain,
    ( v2_tops_1(o_0_0_xboole_0,sK4)
    | ~ spl5_114 ),
    inference(avatar_component_clause,[],[f1471])).

fof(f1570,plain,
    ( ~ spl5_121
    | spl5_117 ),
    inference(avatar_split_clause,[],[f1494,f1480,f1568])).

fof(f1480,plain,
    ( spl5_117
  <=> ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_117])])).

fof(f1494,plain,
    ( ~ r2_hidden(k1_tops_1(sK0,sK1),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_117 ),
    inference(unit_resulting_resolution,[],[f1481,f146])).

fof(f146,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f38])).

fof(f38,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t94_tops_1.p',t1_subset)).

fof(f1481,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_117 ),
    inference(avatar_component_clause,[],[f1480])).

fof(f1553,plain,
    ( ~ spl5_119
    | ~ spl5_0
    | ~ spl5_14
    | spl5_99 ),
    inference(avatar_split_clause,[],[f1544,f1252,f225,f174,f1551])).

fof(f1544,plain,
    ( ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl5_0
    | ~ spl5_14
    | ~ spl5_99 ),
    inference(unit_resulting_resolution,[],[f175,f1253,f226,f140])).

fof(f140,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f108])).

fof(f1482,plain,
    ( ~ spl5_117
    | ~ spl5_2
    | spl5_105 ),
    inference(avatar_split_clause,[],[f1416,f1406,f181,f1480])).

fof(f1416,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_2
    | ~ spl5_105 ),
    inference(unit_resulting_resolution,[],[f1407,f392])).

fof(f392,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(o_0_0_xboole_0))
        | o_0_0_xboole_0 = X0 )
    | ~ spl5_2 ),
    inference(resolution,[],[f380,f156])).

fof(f1473,plain,
    ( spl5_114
    | ~ spl5_2
    | ~ spl5_6
    | ~ spl5_112 ),
    inference(avatar_split_clause,[],[f1463,f1460,f195,f181,f1471])).

fof(f1460,plain,
    ( spl5_112
  <=> k1_tops_1(sK4,o_0_0_xboole_0) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_112])])).

fof(f1463,plain,
    ( v2_tops_1(o_0_0_xboole_0,sK4)
    | ~ spl5_2
    | ~ spl5_6
    | ~ spl5_112 ),
    inference(unit_resulting_resolution,[],[f196,f1342,f1461,f235])).

fof(f235,plain,
    ( ! [X0,X1] :
        ( k1_tops_1(X0,X1) != o_0_0_xboole_0
        | v2_tops_1(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl5_2 ),
    inference(backward_demodulation,[],[f228,f138])).

fof(f138,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | k1_tops_1(X0,X1) != k1_xboole_0
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f107])).

fof(f1461,plain,
    ( k1_tops_1(sK4,o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl5_112 ),
    inference(avatar_component_clause,[],[f1460])).

fof(f1462,plain,
    ( spl5_112
    | ~ spl5_2
    | ~ spl5_110 ),
    inference(avatar_split_clause,[],[f1449,f1441,f181,f1460])).

fof(f1441,plain,
    ( spl5_110
  <=> r1_tarski(k1_tops_1(sK4,o_0_0_xboole_0),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_110])])).

fof(f1449,plain,
    ( k1_tops_1(sK4,o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl5_2
    | ~ spl5_110 ),
    inference(forward_demodulation,[],[f1445,f231])).

fof(f1445,plain,
    ( k3_xboole_0(k1_tops_1(sK4,o_0_0_xboole_0),o_0_0_xboole_0) = k1_tops_1(sK4,o_0_0_xboole_0)
    | ~ spl5_110 ),
    inference(unit_resulting_resolution,[],[f1442,f144])).

fof(f1442,plain,
    ( r1_tarski(k1_tops_1(sK4,o_0_0_xboole_0),o_0_0_xboole_0)
    | ~ spl5_110 ),
    inference(avatar_component_clause,[],[f1441])).

fof(f1443,plain,
    ( spl5_110
    | ~ spl5_2
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f1363,f195,f181,f1441])).

fof(f1363,plain,
    ( r1_tarski(k1_tops_1(sK4,o_0_0_xboole_0),o_0_0_xboole_0)
    | ~ spl5_2
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f196,f1342,f129])).

fof(f1434,plain,
    ( ~ spl5_109
    | ~ spl5_2
    | spl5_105 ),
    inference(avatar_split_clause,[],[f1415,f1406,f181,f1432])).

fof(f1432,plain,
    ( spl5_109
  <=> ~ r1_tarski(k1_tops_1(sK0,sK1),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_109])])).

fof(f1415,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),o_0_0_xboole_0)
    | ~ spl5_2
    | ~ spl5_105 ),
    inference(unit_resulting_resolution,[],[f1407,f380])).

fof(f1425,plain,
    ( ~ spl5_107
    | ~ spl5_2
    | spl5_105 ),
    inference(avatar_split_clause,[],[f1418,f1406,f181,f1423])).

fof(f1423,plain,
    ( spl5_107
  <=> ~ v1_xboole_0(k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_107])])).

fof(f1418,plain,
    ( ~ v1_xboole_0(k1_tops_1(sK0,sK1))
    | ~ spl5_2
    | ~ spl5_105 ),
    inference(unit_resulting_resolution,[],[f182,f1407,f158])).

fof(f1408,plain,
    ( ~ spl5_105
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_14
    | spl5_99 ),
    inference(avatar_split_clause,[],[f1389,f1252,f225,f181,f174,f1406])).

fof(f1389,plain,
    ( k1_tops_1(sK0,sK1) != o_0_0_xboole_0
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_14
    | ~ spl5_99 ),
    inference(unit_resulting_resolution,[],[f175,f1253,f226,f235])).

fof(f1399,plain,
    ( spl5_102
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_72
    | ~ spl5_76 ),
    inference(avatar_split_clause,[],[f1390,f957,f885,f181,f174,f1397])).

fof(f885,plain,
    ( spl5_72
  <=> m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_72])])).

fof(f957,plain,
    ( spl5_76
  <=> k1_tops_1(sK0,o_0_0_xboole_0) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_76])])).

fof(f1390,plain,
    ( v2_tops_1(o_0_0_xboole_0,sK0)
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_72
    | ~ spl5_76 ),
    inference(unit_resulting_resolution,[],[f175,f886,f958,f235])).

fof(f958,plain,
    ( k1_tops_1(sK0,o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl5_76 ),
    inference(avatar_component_clause,[],[f957])).

fof(f886,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_72 ),
    inference(avatar_component_clause,[],[f885])).

fof(f1281,plain,
    ( spl5_100
    | ~ spl5_94 ),
    inference(avatar_split_clause,[],[f1264,f1218,f1279])).

fof(f1279,plain,
    ( spl5_100
  <=> r1_tarski(k2_pre_topc(sK0,o_0_0_xboole_0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_100])])).

fof(f1218,plain,
    ( spl5_94
  <=> m1_subset_1(k2_pre_topc(sK0,o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_94])])).

fof(f1264,plain,
    ( r1_tarski(k2_pre_topc(sK0,o_0_0_xboole_0),u1_struct_0(sK0))
    | ~ spl5_94 ),
    inference(unit_resulting_resolution,[],[f1219,f156])).

fof(f1219,plain,
    ( m1_subset_1(k2_pre_topc(sK0,o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_94 ),
    inference(avatar_component_clause,[],[f1218])).

fof(f1254,plain,
    ( ~ spl5_99
    | ~ spl5_0
    | ~ spl5_14
    | spl5_27
    | ~ spl5_90 ),
    inference(avatar_split_clause,[],[f1247,f1169,f293,f225,f174,f1252])).

fof(f1247,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | ~ spl5_0
    | ~ spl5_14
    | ~ spl5_27
    | ~ spl5_90 ),
    inference(forward_demodulation,[],[f1245,f1170])).

fof(f1245,plain,
    ( ~ v2_tops_1(k2_pre_topc(sK0,sK1),sK0)
    | ~ spl5_0
    | ~ spl5_14
    | ~ spl5_27 ),
    inference(unit_resulting_resolution,[],[f175,f294,f226,f134])).

fof(f134,plain,(
    ! [X0,X1] :
      ( ~ v2_tops_1(k2_pre_topc(X0,X1),X0)
      | v3_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f105])).

fof(f294,plain,
    ( ~ v3_tops_1(sK1,sK0)
    | ~ spl5_27 ),
    inference(avatar_component_clause,[],[f293])).

fof(f1244,plain,
    ( spl5_96
    | ~ spl5_92 ),
    inference(avatar_split_clause,[],[f1227,f1211,f1242])).

fof(f1242,plain,
    ( spl5_96
  <=> r1_tarski(k2_tops_1(sK0,o_0_0_xboole_0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_96])])).

fof(f1211,plain,
    ( spl5_92
  <=> m1_subset_1(k2_tops_1(sK0,o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_92])])).

fof(f1227,plain,
    ( r1_tarski(k2_tops_1(sK0,o_0_0_xboole_0),u1_struct_0(sK0))
    | ~ spl5_92 ),
    inference(unit_resulting_resolution,[],[f1212,f156])).

fof(f1212,plain,
    ( m1_subset_1(k2_tops_1(sK0,o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_92 ),
    inference(avatar_component_clause,[],[f1211])).

fof(f1220,plain,
    ( spl5_94
    | ~ spl5_0
    | ~ spl5_72 ),
    inference(avatar_split_clause,[],[f1028,f885,f174,f1218])).

fof(f1028,plain,
    ( m1_subset_1(k2_pre_topc(sK0,o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_0
    | ~ spl5_72 ),
    inference(unit_resulting_resolution,[],[f175,f886,f152])).

fof(f1213,plain,
    ( spl5_92
    | ~ spl5_0
    | ~ spl5_72 ),
    inference(avatar_split_clause,[],[f973,f885,f174,f1211])).

fof(f973,plain,
    ( m1_subset_1(k2_tops_1(sK0,o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_0
    | ~ spl5_72 ),
    inference(unit_resulting_resolution,[],[f175,f886,f151])).

fof(f1171,plain,
    ( spl5_90
    | ~ spl5_0
    | ~ spl5_8
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f1147,f225,f202,f174,f1169])).

fof(f202,plain,
    ( spl5_8
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f1147,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | ~ spl5_0
    | ~ spl5_8
    | ~ spl5_14 ),
    inference(unit_resulting_resolution,[],[f175,f203,f226,f132])).

fof(f132,plain,(
    ! [X0,X1] :
      ( ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = X1
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f65])).

fof(f65,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = X1
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => k2_pre_topc(X0,X1) = X1 ) ) ) ),
    inference(pure_predicate_removal,[],[f48])).

fof(f48,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t94_tops_1.p',t52_pre_topc)).

fof(f203,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f202])).

fof(f1146,plain,
    ( spl5_88
    | ~ spl5_78 ),
    inference(avatar_split_clause,[],[f990,f986,f1144])).

fof(f1144,plain,
    ( spl5_88
  <=> m1_subset_1(sK2(k1_zfmisc_1(sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_88])])).

fof(f986,plain,
    ( spl5_78
  <=> r1_tarski(sK2(k1_zfmisc_1(sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_78])])).

fof(f990,plain,
    ( m1_subset_1(sK2(k1_zfmisc_1(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_78 ),
    inference(unit_resulting_resolution,[],[f987,f157])).

fof(f987,plain,
    ( r1_tarski(sK2(k1_zfmisc_1(sK1)),u1_struct_0(sK0))
    | ~ spl5_78 ),
    inference(avatar_component_clause,[],[f986])).

fof(f1136,plain,
    ( spl5_86
    | ~ spl5_84 ),
    inference(avatar_split_clause,[],[f1119,f1110,f1134])).

fof(f1134,plain,
    ( spl5_86
  <=> r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_86])])).

fof(f1119,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
    | ~ spl5_84 ),
    inference(unit_resulting_resolution,[],[f1111,f156])).

fof(f1112,plain,
    ( spl5_84
    | ~ spl5_0
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f1099,f225,f174,f1110])).

fof(f1099,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_0
    | ~ spl5_14 ),
    inference(unit_resulting_resolution,[],[f175,f226,f153])).

fof(f153,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t94_tops_1.p',dt_k1_tops_1)).

fof(f1064,plain,
    ( spl5_82
    | ~ spl5_80 ),
    inference(avatar_split_clause,[],[f1047,f1039,f1062])).

fof(f1062,plain,
    ( spl5_82
  <=> r1_tarski(k2_pre_topc(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_82])])).

fof(f1039,plain,
    ( spl5_80
  <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_80])])).

fof(f1047,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK1),u1_struct_0(sK0))
    | ~ spl5_80 ),
    inference(unit_resulting_resolution,[],[f1040,f156])).

fof(f1040,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_80 ),
    inference(avatar_component_clause,[],[f1039])).

fof(f1041,plain,
    ( spl5_80
    | ~ spl5_0
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f1030,f225,f174,f1039])).

fof(f1030,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_0
    | ~ spl5_14 ),
    inference(unit_resulting_resolution,[],[f175,f226,f152])).

fof(f988,plain,
    ( spl5_78
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f870,f225,f986])).

fof(f870,plain,
    ( r1_tarski(sK2(k1_zfmisc_1(sK1)),u1_struct_0(sK0))
    | ~ spl5_14 ),
    inference(superposition,[],[f847,f328])).

fof(f847,plain,
    ( ! [X0] : r1_tarski(k3_xboole_0(X0,sK1),u1_struct_0(sK0))
    | ~ spl5_14 ),
    inference(backward_demodulation,[],[f833,f685])).

fof(f685,plain,
    ( ! [X0] : r1_tarski(k9_subset_1(u1_struct_0(sK0),X0,sK1),u1_struct_0(sK0))
    | ~ spl5_14 ),
    inference(unit_resulting_resolution,[],[f643,f156])).

fof(f643,plain,
    ( ! [X0] : m1_subset_1(k9_subset_1(u1_struct_0(sK0),X0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_14 ),
    inference(unit_resulting_resolution,[],[f226,f162])).

fof(f833,plain,
    ( ! [X0] : k3_xboole_0(X0,sK1) = k9_subset_1(u1_struct_0(sK0),X0,sK1)
    | ~ spl5_14 ),
    inference(unit_resulting_resolution,[],[f226,f164])).

fof(f959,plain,
    ( spl5_76
    | ~ spl5_2
    | ~ spl5_74 ),
    inference(avatar_split_clause,[],[f949,f941,f181,f957])).

fof(f941,plain,
    ( spl5_74
  <=> r1_tarski(k1_tops_1(sK0,o_0_0_xboole_0),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_74])])).

fof(f949,plain,
    ( k1_tops_1(sK0,o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl5_2
    | ~ spl5_74 ),
    inference(forward_demodulation,[],[f945,f231])).

fof(f945,plain,
    ( k3_xboole_0(k1_tops_1(sK0,o_0_0_xboole_0),o_0_0_xboole_0) = k1_tops_1(sK0,o_0_0_xboole_0)
    | ~ spl5_74 ),
    inference(unit_resulting_resolution,[],[f942,f144])).

fof(f942,plain,
    ( r1_tarski(k1_tops_1(sK0,o_0_0_xboole_0),o_0_0_xboole_0)
    | ~ spl5_74 ),
    inference(avatar_component_clause,[],[f941])).

fof(f943,plain,
    ( spl5_74
    | ~ spl5_0
    | ~ spl5_72 ),
    inference(avatar_split_clause,[],[f888,f885,f174,f941])).

fof(f888,plain,
    ( r1_tarski(k1_tops_1(sK0,o_0_0_xboole_0),o_0_0_xboole_0)
    | ~ spl5_0
    | ~ spl5_72 ),
    inference(unit_resulting_resolution,[],[f175,f886,f129])).

fof(f887,plain,
    ( spl5_72
    | ~ spl5_70 ),
    inference(avatar_split_clause,[],[f879,f875,f885])).

fof(f875,plain,
    ( spl5_70
  <=> r1_tarski(o_0_0_xboole_0,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_70])])).

fof(f879,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_70 ),
    inference(unit_resulting_resolution,[],[f876,f157])).

fof(f876,plain,
    ( r1_tarski(o_0_0_xboole_0,u1_struct_0(sK0))
    | ~ spl5_70 ),
    inference(avatar_component_clause,[],[f875])).

fof(f877,plain,
    ( spl5_70
    | ~ spl5_2
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f869,f225,f181,f875])).

fof(f869,plain,
    ( r1_tarski(o_0_0_xboole_0,u1_struct_0(sK0))
    | ~ spl5_2
    | ~ spl5_14 ),
    inference(superposition,[],[f847,f264])).

fof(f823,plain,
    ( spl5_68
    | ~ spl5_6
    | ~ spl5_40 ),
    inference(avatar_split_clause,[],[f696,f374,f195,f821])).

fof(f821,plain,
    ( spl5_68
  <=> r1_tarski(k1_tops_1(sK4,u1_struct_0(sK4)),u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_68])])).

fof(f374,plain,
    ( spl5_40
  <=> m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).

fof(f696,plain,
    ( r1_tarski(k1_tops_1(sK4,u1_struct_0(sK4)),u1_struct_0(sK4))
    | ~ spl5_6
    | ~ spl5_40 ),
    inference(unit_resulting_resolution,[],[f196,f375,f129])).

fof(f375,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ spl5_40 ),
    inference(avatar_component_clause,[],[f374])).

fof(f739,plain,
    ( spl5_66
    | ~ spl5_0
    | ~ spl5_34 ),
    inference(avatar_split_clause,[],[f695,f346,f174,f737])).

fof(f737,plain,
    ( spl5_66
  <=> r1_tarski(k1_tops_1(sK0,u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_66])])).

fof(f695,plain,
    ( r1_tarski(k1_tops_1(sK0,u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl5_0
    | ~ spl5_34 ),
    inference(unit_resulting_resolution,[],[f175,f347,f129])).

fof(f725,plain,
    ( spl5_64
    | ~ spl5_62 ),
    inference(avatar_split_clause,[],[f717,f713,f723])).

fof(f717,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl5_62 ),
    inference(unit_resulting_resolution,[],[f714,f157])).

fof(f715,plain,
    ( spl5_62
    | ~ spl5_0
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f704,f225,f174,f713])).

fof(f704,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl5_0
    | ~ spl5_14 ),
    inference(unit_resulting_resolution,[],[f175,f226,f129])).

fof(f577,plain,
    ( spl5_60
    | ~ spl5_30 ),
    inference(avatar_split_clause,[],[f431,f323,f575])).

fof(f575,plain,
    ( spl5_60
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK3),u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_60])])).

fof(f323,plain,
    ( spl5_30
  <=> m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f431,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK3),u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl5_30 ),
    inference(unit_resulting_resolution,[],[f324,f148])).

fof(f324,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl5_30 ),
    inference(avatar_component_clause,[],[f323])).

fof(f562,plain,
    ( spl5_58
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f549,f225,f560])).

fof(f560,plain,
    ( spl5_58
  <=> k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_58])])).

fof(f549,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = sK1
    | ~ spl5_14 ),
    inference(unit_resulting_resolution,[],[f226,f149])).

fof(f149,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t94_tops_1.p',involutiveness_k3_subset_1)).

fof(f484,plain,
    ( spl5_56
    | ~ spl5_54 ),
    inference(avatar_split_clause,[],[f477,f467,f482])).

fof(f482,plain,
    ( spl5_56
  <=> r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_56])])).

fof(f467,plain,
    ( spl5_54
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_54])])).

fof(f477,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ spl5_54 ),
    inference(unit_resulting_resolution,[],[f468,f156])).

fof(f468,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_54 ),
    inference(avatar_component_clause,[],[f467])).

fof(f469,plain,
    ( spl5_54
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f435,f225,f467])).

fof(f435,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_14 ),
    inference(unit_resulting_resolution,[],[f226,f148])).

fof(f461,plain,
    ( spl5_52
    | ~ spl5_2
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f445,f442,f181,f459])).

fof(f459,plain,
    ( spl5_52
  <=> k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_52])])).

fof(f442,plain,
    ( spl5_50
  <=> m1_subset_1(k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_50])])).

fof(f445,plain,
    ( k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl5_2
    | ~ spl5_50 ),
    inference(unit_resulting_resolution,[],[f443,f392])).

fof(f443,plain,
    ( m1_subset_1(k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_50 ),
    inference(avatar_component_clause,[],[f442])).

fof(f444,plain,
    ( spl5_50
    | ~ spl5_48 ),
    inference(avatar_split_clause,[],[f434,f421,f442])).

fof(f434,plain,
    ( m1_subset_1(k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_48 ),
    inference(unit_resulting_resolution,[],[f422,f148])).

fof(f423,plain,
    ( spl5_48
    | ~ spl5_44 ),
    inference(avatar_split_clause,[],[f402,f398,f421])).

fof(f402,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_44 ),
    inference(superposition,[],[f141,f399])).

fof(f411,plain,
    ( spl5_46
    | ~ spl5_44 ),
    inference(avatar_split_clause,[],[f401,f398,f409])).

fof(f409,plain,
    ( spl5_46
  <=> r1_tarski(o_0_0_xboole_0,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_46])])).

fof(f401,plain,
    ( r1_tarski(o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ spl5_44 ),
    inference(superposition,[],[f279,f399])).

fof(f400,plain,
    ( spl5_44
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f391,f181,f398])).

fof(f391,plain,
    ( o_0_0_xboole_0 = sK2(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f279,f380])).

fof(f387,plain,
    ( spl5_42
    | ~ spl5_40 ),
    inference(avatar_split_clause,[],[f377,f374,f385])).

fof(f385,plain,
    ( spl5_42
  <=> r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).

fof(f377,plain,
    ( r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4))
    | ~ spl5_40 ),
    inference(unit_resulting_resolution,[],[f375,f156])).

fof(f376,plain,
    ( spl5_40
    | ~ spl5_12
    | ~ spl5_22 ),
    inference(avatar_split_clause,[],[f316,f276,f218,f374])).

fof(f218,plain,
    ( spl5_12
  <=> l1_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f316,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ spl5_12
    | ~ spl5_22 ),
    inference(forward_demodulation,[],[f310,f277])).

fof(f310,plain,
    ( m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ spl5_12 ),
    inference(unit_resulting_resolution,[],[f219,f126])).

fof(f126,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t94_tops_1.p',dt_k2_struct_0)).

fof(f219,plain,
    ( l1_struct_0(sK4)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f218])).

fof(f366,plain,
    ( spl5_38
    | ~ spl5_34 ),
    inference(avatar_split_clause,[],[f356,f346,f364])).

fof(f364,plain,
    ( spl5_38
  <=> r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).

fof(f356,plain,
    ( r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl5_34 ),
    inference(unit_resulting_resolution,[],[f347,f156])).

fof(f355,plain,
    ( spl5_36
    | ~ spl5_24 ),
    inference(avatar_split_clause,[],[f327,f285,f353])).

fof(f353,plain,
    ( spl5_36
  <=> k3_xboole_0(sK1,u1_struct_0(sK0)) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).

fof(f285,plain,
    ( spl5_24
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f327,plain,
    ( k3_xboole_0(sK1,u1_struct_0(sK0)) = sK1
    | ~ spl5_24 ),
    inference(unit_resulting_resolution,[],[f286,f144])).

fof(f286,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f285])).

fof(f348,plain,
    ( spl5_34
    | ~ spl5_10
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f317,f261,f211,f346])).

fof(f211,plain,
    ( spl5_10
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f317,plain,
    ( m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_10
    | ~ spl5_20 ),
    inference(forward_demodulation,[],[f309,f262])).

fof(f309,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f212,f126])).

fof(f212,plain,
    ( l1_struct_0(sK0)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f211])).

fof(f338,plain,
    ( spl5_32
    | ~ spl5_30 ),
    inference(avatar_split_clause,[],[f326,f323,f336])).

fof(f336,plain,
    ( spl5_32
  <=> r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f326,plain,
    ( r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3))
    | ~ spl5_30 ),
    inference(unit_resulting_resolution,[],[f324,f156])).

fof(f325,plain,
    ( spl5_30
    | ~ spl5_4
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f318,f254,f188,f323])).

fof(f188,plain,
    ( spl5_4
  <=> l1_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f254,plain,
    ( spl5_18
  <=> u1_struct_0(sK3) = k2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f318,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl5_4
    | ~ spl5_18 ),
    inference(forward_demodulation,[],[f308,f255])).

fof(f255,plain,
    ( u1_struct_0(sK3) = k2_struct_0(sK3)
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f254])).

fof(f308,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl5_4 ),
    inference(unit_resulting_resolution,[],[f189,f126])).

fof(f189,plain,
    ( l1_struct_0(sK3)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f188])).

fof(f307,plain,
    ( ~ spl5_27
    | ~ spl5_28 ),
    inference(avatar_split_clause,[],[f306,f302,f293])).

fof(f306,plain,
    ( ~ v3_tops_1(sK1,sK0)
    | ~ spl5_28 ),
    inference(trivial_inequality_removal,[],[f305])).

fof(f305,plain,
    ( sK1 != sK1
    | ~ v3_tops_1(sK1,sK0)
    | ~ spl5_28 ),
    inference(backward_demodulation,[],[f303,f120])).

fof(f304,plain,
    ( spl5_26
    | spl5_28 ),
    inference(avatar_split_clause,[],[f119,f302,f296])).

fof(f119,plain,
    ( k2_tops_1(sK0,sK1) = sK1
    | v3_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f104])).

fof(f287,plain,
    ( spl5_24
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f280,f225,f285])).

fof(f280,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl5_14 ),
    inference(unit_resulting_resolution,[],[f226,f156])).

fof(f278,plain,
    ( spl5_22
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f249,f218,f276])).

fof(f249,plain,
    ( u1_struct_0(sK4) = k2_struct_0(sK4)
    | ~ spl5_12 ),
    inference(unit_resulting_resolution,[],[f219,f125])).

fof(f125,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t94_tops_1.p',d3_struct_0)).

fof(f263,plain,
    ( spl5_20
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f248,f211,f261])).

fof(f248,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f212,f125])).

fof(f256,plain,
    ( spl5_18
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f247,f188,f254])).

fof(f247,plain,
    ( u1_struct_0(sK3) = k2_struct_0(sK3)
    | ~ spl5_4 ),
    inference(unit_resulting_resolution,[],[f189,f125])).

fof(f243,plain,
    ( spl5_16
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f228,f181,f241])).

fof(f241,plain,
    ( spl5_16
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f227,plain,(
    spl5_14 ),
    inference(avatar_split_clause,[],[f117,f225])).

fof(f117,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f104])).

fof(f220,plain,
    ( spl5_12
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f206,f195,f218])).

fof(f206,plain,
    ( l1_struct_0(sK4)
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f196,f128])).

fof(f128,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t94_tops_1.p',dt_l1_pre_topc)).

fof(f213,plain,
    ( spl5_10
    | ~ spl5_0 ),
    inference(avatar_split_clause,[],[f205,f174,f211])).

fof(f205,plain,
    ( l1_struct_0(sK0)
    | ~ spl5_0 ),
    inference(unit_resulting_resolution,[],[f175,f128])).

fof(f204,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f118,f202])).

fof(f118,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f104])).

fof(f197,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f169,f195])).

fof(f169,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f115])).

fof(f115,plain,(
    l1_pre_topc(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f27,f114])).

fof(f114,plain,
    ( ? [X0] : l1_pre_topc(X0)
   => l1_pre_topc(sK4) ),
    introduced(choice_axiom,[])).

fof(f27,axiom,(
    ? [X0] : l1_pre_topc(X0) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t94_tops_1.p',existence_l1_pre_topc)).

fof(f190,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f168,f188])).

fof(f168,plain,(
    l1_struct_0(sK3) ),
    inference(cnf_transformation,[],[f113])).

fof(f113,plain,(
    l1_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f28,f112])).

fof(f112,plain,
    ( ? [X0] : l1_struct_0(X0)
   => l1_struct_0(sK3) ),
    introduced(choice_axiom,[])).

fof(f28,axiom,(
    ? [X0] : l1_struct_0(X0) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t94_tops_1.p',existence_l1_struct_0)).

fof(f183,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f121,f181])).

fof(f121,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t94_tops_1.p',dt_o_0_0_xboole_0)).

fof(f176,plain,(
    spl5_0 ),
    inference(avatar_split_clause,[],[f116,f174])).

fof(f116,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f104])).
%------------------------------------------------------------------------------
