%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:11 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  325 ( 645 expanded)
%              Number of leaves         :   78 ( 312 expanded)
%              Depth                    :    8
%              Number of atoms          : 1224 (2490 expanded)
%              Number of equality atoms :   84 ( 224 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f750,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f83,f88,f93,f98,f103,f108,f112,f116,f120,f124,f128,f132,f146,f151,f155,f159,f169,f182,f191,f196,f203,f206,f215,f223,f229,f234,f238,f253,f261,f288,f324,f335,f340,f345,f372,f378,f391,f395,f411,f415,f429,f439,f444,f541,f547,f555,f559,f601,f605,f612,f620,f624,f629,f641,f661,f709,f717,f731,f742,f749])).

fof(f749,plain,
    ( ~ spl5_10
    | spl5_29
    | ~ spl5_82 ),
    inference(avatar_contradiction_clause,[],[f748])).

fof(f748,plain,
    ( $false
    | ~ spl5_10
    | spl5_29
    | ~ spl5_82 ),
    inference(subsumption_resolution,[],[f233,f746])).

fof(f746,plain,
    ( ! [X1] : r1_xboole_0(X1,k2_pre_topc(sK0,k2_tarski(sK2,sK2)))
    | ~ spl5_10
    | ~ spl5_82 ),
    inference(resolution,[],[f640,f123])).

fof(f123,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK4(X0,X1),X1)
        | r1_xboole_0(X0,X1) )
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl5_10
  <=> ! [X1,X0] :
        ( r2_hidden(sK4(X0,X1),X1)
        | r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f640,plain,
    ( ! [X0] : ~ r2_hidden(X0,k2_pre_topc(sK0,k2_tarski(sK2,sK2)))
    | ~ spl5_82 ),
    inference(avatar_component_clause,[],[f639])).

fof(f639,plain,
    ( spl5_82
  <=> ! [X0] : ~ r2_hidden(X0,k2_pre_topc(sK0,k2_tarski(sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_82])])).

fof(f233,plain,
    ( ~ r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k2_tarski(sK2,sK2)))
    | spl5_29 ),
    inference(avatar_component_clause,[],[f231])).

fof(f231,plain,
    ( spl5_29
  <=> r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k2_tarski(sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f742,plain,
    ( ~ spl5_79
    | ~ spl5_81
    | ~ spl5_84 ),
    inference(avatar_contradiction_clause,[],[f741])).

fof(f741,plain,
    ( $false
    | ~ spl5_79
    | ~ spl5_81
    | ~ spl5_84 ),
    inference(subsumption_resolution,[],[f738,f628])).

fof(f628,plain,
    ( r2_hidden(sK2,k2_pre_topc(sK0,k2_tarski(sK2,sK2)))
    | ~ spl5_81 ),
    inference(avatar_component_clause,[],[f626])).

fof(f626,plain,
    ( spl5_81
  <=> r2_hidden(sK2,k2_pre_topc(sK0,k2_tarski(sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_81])])).

fof(f738,plain,
    ( ~ r2_hidden(sK2,k2_pre_topc(sK0,k2_tarski(sK2,sK2)))
    | ~ spl5_79
    | ~ spl5_84 ),
    inference(resolution,[],[f619,f660])).

fof(f660,plain,
    ( r2_hidden(sK2,k2_pre_topc(sK0,k2_tarski(sK1,sK1)))
    | ~ spl5_84 ),
    inference(avatar_component_clause,[],[f658])).

fof(f658,plain,
    ( spl5_84
  <=> r2_hidden(sK2,k2_pre_topc(sK0,k2_tarski(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_84])])).

fof(f619,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_pre_topc(sK0,k2_tarski(sK1,sK1)))
        | ~ r2_hidden(X0,k2_pre_topc(sK0,k2_tarski(sK2,sK2))) )
    | ~ spl5_79 ),
    inference(avatar_component_clause,[],[f618])).

fof(f618,plain,
    ( spl5_79
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k2_pre_topc(sK0,k2_tarski(sK1,sK1)))
        | ~ r2_hidden(X0,k2_pre_topc(sK0,k2_tarski(sK2,sK2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_79])])).

fof(f731,plain,
    ( ~ spl5_78
    | ~ spl5_6
    | ~ spl5_26
    | spl5_28
    | ~ spl5_89 ),
    inference(avatar_split_clause,[],[f729,f715,f226,f212,f105,f609])).

fof(f609,plain,
    ( spl5_78
  <=> r2_hidden(sK1,k2_pre_topc(sK0,k2_tarski(sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_78])])).

fof(f105,plain,
    ( spl5_6
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f212,plain,
    ( spl5_26
  <=> k6_domain_1(u1_struct_0(sK0),sK2) = k2_tarski(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f226,plain,
    ( spl5_28
  <=> k2_pre_topc(sK0,k2_tarski(sK1,sK1)) = k2_pre_topc(sK0,k2_tarski(sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f715,plain,
    ( spl5_89
  <=> ! [X0] :
        ( k2_pre_topc(sK0,k2_tarski(sK1,sK1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_89])])).

fof(f729,plain,
    ( ~ r2_hidden(sK1,k2_pre_topc(sK0,k2_tarski(sK2,sK2)))
    | ~ spl5_6
    | ~ spl5_26
    | spl5_28
    | ~ spl5_89 ),
    inference(subsumption_resolution,[],[f728,f228])).

fof(f228,plain,
    ( k2_pre_topc(sK0,k2_tarski(sK1,sK1)) != k2_pre_topc(sK0,k2_tarski(sK2,sK2))
    | spl5_28 ),
    inference(avatar_component_clause,[],[f226])).

fof(f728,plain,
    ( ~ r2_hidden(sK1,k2_pre_topc(sK0,k2_tarski(sK2,sK2)))
    | k2_pre_topc(sK0,k2_tarski(sK1,sK1)) = k2_pre_topc(sK0,k2_tarski(sK2,sK2))
    | ~ spl5_6
    | ~ spl5_26
    | ~ spl5_89 ),
    inference(subsumption_resolution,[],[f723,f107])).

fof(f107,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f105])).

fof(f723,plain,
    ( ~ r2_hidden(sK1,k2_pre_topc(sK0,k2_tarski(sK2,sK2)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | k2_pre_topc(sK0,k2_tarski(sK1,sK1)) = k2_pre_topc(sK0,k2_tarski(sK2,sK2))
    | ~ spl5_26
    | ~ spl5_89 ),
    inference(superposition,[],[f716,f214])).

fof(f214,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK2) = k2_tarski(sK2,sK2)
    | ~ spl5_26 ),
    inference(avatar_component_clause,[],[f212])).

fof(f716,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_pre_topc(sK0,k2_tarski(sK1,sK1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0)) )
    | ~ spl5_89 ),
    inference(avatar_component_clause,[],[f715])).

fof(f717,plain,
    ( spl5_89
    | ~ spl5_5
    | ~ spl5_22
    | ~ spl5_88 ),
    inference(avatar_split_clause,[],[f712,f707,f179,f100,f715])).

fof(f100,plain,
    ( spl5_5
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f179,plain,
    ( spl5_22
  <=> k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f707,plain,
    ( spl5_88
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_88])])).

fof(f712,plain,
    ( ! [X0] :
        ( k2_pre_topc(sK0,k2_tarski(sK1,sK1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0))) )
    | ~ spl5_5
    | ~ spl5_22
    | ~ spl5_88 ),
    inference(forward_demodulation,[],[f710,f181])).

fof(f181,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1)
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f179])).

fof(f710,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0)))
        | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0)) )
    | ~ spl5_5
    | ~ spl5_88 ),
    inference(resolution,[],[f708,f102])).

fof(f102,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f100])).

fof(f708,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X0,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)))
        | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0)) )
    | ~ spl5_88 ),
    inference(avatar_component_clause,[],[f707])).

fof(f709,plain,
    ( spl5_88
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_80 ),
    inference(avatar_split_clause,[],[f705,f622,f95,f90,f85,f80,f707])).

fof(f80,plain,
    ( spl5_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f85,plain,
    ( spl5_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f90,plain,
    ( spl5_3
  <=> v3_tdlat_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f95,plain,
    ( spl5_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f622,plain,
    ( spl5_80
  <=> ! [X1,X0,X2] :
        ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
        | ~ r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_pre_topc(X0)
        | ~ v3_tdlat_3(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_80])])).

fof(f705,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0)) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_80 ),
    inference(subsumption_resolution,[],[f704,f82])).

fof(f82,plain,
    ( ~ v2_struct_0(sK0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f80])).

fof(f704,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0))
        | v2_struct_0(sK0) )
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_80 ),
    inference(subsumption_resolution,[],[f703,f87])).

fof(f87,plain,
    ( v2_pre_topc(sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f85])).

fof(f703,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0))
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_80 ),
    inference(subsumption_resolution,[],[f702,f97])).

fof(f97,plain,
    ( l1_pre_topc(sK0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f95])).

fof(f702,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_pre_topc(sK0)
        | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0))
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_3
    | ~ spl5_80 ),
    inference(resolution,[],[f623,f92])).

fof(f92,plain,
    ( v3_tdlat_3(sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f90])).

fof(f623,plain,
    ( ! [X2,X0,X1] :
        ( ~ v3_tdlat_3(X0)
        | ~ r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_pre_topc(X0)
        | k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl5_80 ),
    inference(avatar_component_clause,[],[f622])).

fof(f661,plain,
    ( spl5_84
    | ~ spl5_27
    | spl5_29
    | ~ spl5_77 ),
    inference(avatar_split_clause,[],[f656,f603,f231,f220,f658])).

fof(f220,plain,
    ( spl5_27
  <=> m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f603,plain,
    ( spl5_77
  <=> ! [X1] :
        ( ~ m1_subset_1(k2_tarski(X1,X1),k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k2_tarski(X1,X1)))
        | r2_hidden(X1,k2_pre_topc(sK0,k2_tarski(sK1,sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_77])])).

fof(f656,plain,
    ( r2_hidden(sK2,k2_pre_topc(sK0,k2_tarski(sK1,sK1)))
    | ~ spl5_27
    | spl5_29
    | ~ spl5_77 ),
    inference(subsumption_resolution,[],[f655,f233])).

fof(f655,plain,
    ( r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k2_tarski(sK2,sK2)))
    | r2_hidden(sK2,k2_pre_topc(sK0,k2_tarski(sK1,sK1)))
    | ~ spl5_27
    | ~ spl5_77 ),
    inference(resolution,[],[f604,f222])).

fof(f222,plain,
    ( m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_27 ),
    inference(avatar_component_clause,[],[f220])).

fof(f604,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(k2_tarski(X1,X1),k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k2_tarski(X1,X1)))
        | r2_hidden(X1,k2_pre_topc(sK0,k2_tarski(sK1,sK1))) )
    | ~ spl5_77 ),
    inference(avatar_component_clause,[],[f603])).

fof(f641,plain,
    ( spl5_82
    | ~ spl5_12
    | ~ spl5_75 ),
    inference(avatar_split_clause,[],[f632,f590,f130,f639])).

fof(f130,plain,
    ( spl5_12
  <=> ! [X1,X0,X2] :
        ( ~ r1_xboole_0(X0,X1)
        | ~ r2_hidden(X2,X1)
        | ~ r2_hidden(X2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f590,plain,
    ( spl5_75
  <=> r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),k2_pre_topc(sK0,k2_tarski(sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_75])])).

fof(f632,plain,
    ( ! [X0] : ~ r2_hidden(X0,k2_pre_topc(sK0,k2_tarski(sK2,sK2)))
    | ~ spl5_12
    | ~ spl5_75 ),
    inference(duplicate_literal_removal,[],[f631])).

fof(f631,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_pre_topc(sK0,k2_tarski(sK2,sK2)))
        | ~ r2_hidden(X0,k2_pre_topc(sK0,k2_tarski(sK2,sK2))) )
    | ~ spl5_12
    | ~ spl5_75 ),
    inference(resolution,[],[f592,f131])).

fof(f131,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | ~ r2_hidden(X2,X1)
        | ~ r2_hidden(X2,X0) )
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f130])).

fof(f592,plain,
    ( r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),k2_pre_topc(sK0,k2_tarski(sK2,sK2)))
    | ~ spl5_75 ),
    inference(avatar_component_clause,[],[f590])).

fof(f629,plain,
    ( spl5_81
    | spl5_75
    | ~ spl5_27
    | ~ spl5_76 ),
    inference(avatar_split_clause,[],[f607,f599,f220,f590,f626])).

fof(f599,plain,
    ( spl5_76
  <=> ! [X1] :
        ( ~ m1_subset_1(k2_tarski(X1,X1),k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),k2_pre_topc(sK0,k2_tarski(X1,X1)))
        | r2_hidden(X1,k2_pre_topc(sK0,k2_tarski(sK2,sK2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_76])])).

fof(f607,plain,
    ( r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),k2_pre_topc(sK0,k2_tarski(sK2,sK2)))
    | r2_hidden(sK2,k2_pre_topc(sK0,k2_tarski(sK2,sK2)))
    | ~ spl5_27
    | ~ spl5_76 ),
    inference(resolution,[],[f600,f222])).

fof(f600,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(k2_tarski(X1,X1),k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),k2_pre_topc(sK0,k2_tarski(X1,X1)))
        | r2_hidden(X1,k2_pre_topc(sK0,k2_tarski(sK2,sK2))) )
    | ~ spl5_76 ),
    inference(avatar_component_clause,[],[f599])).

fof(f624,plain,(
    spl5_80 ),
    inference(avatar_split_clause,[],[f63,f622])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
      | ~ r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
              | ~ r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
              | ~ r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
               => k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tex_2)).

fof(f620,plain,
    ( spl5_79
    | ~ spl5_12
    | ~ spl5_73 ),
    inference(avatar_split_clause,[],[f614,f579,f130,f618])).

fof(f579,plain,
    ( spl5_73
  <=> r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),k2_pre_topc(sK0,k2_tarski(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_73])])).

fof(f614,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_pre_topc(sK0,k2_tarski(sK1,sK1)))
        | ~ r2_hidden(X0,k2_pre_topc(sK0,k2_tarski(sK2,sK2))) )
    | ~ spl5_12
    | ~ spl5_73 ),
    inference(resolution,[],[f581,f131])).

fof(f581,plain,
    ( r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),k2_pre_topc(sK0,k2_tarski(sK1,sK1)))
    | ~ spl5_73 ),
    inference(avatar_component_clause,[],[f579])).

fof(f612,plain,
    ( spl5_78
    | spl5_73
    | ~ spl5_23
    | ~ spl5_76 ),
    inference(avatar_split_clause,[],[f606,f599,f188,f579,f609])).

fof(f188,plain,
    ( spl5_23
  <=> m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f606,plain,
    ( r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),k2_pre_topc(sK0,k2_tarski(sK1,sK1)))
    | r2_hidden(sK1,k2_pre_topc(sK0,k2_tarski(sK2,sK2)))
    | ~ spl5_23
    | ~ spl5_76 ),
    inference(resolution,[],[f600,f190])).

fof(f190,plain,
    ( m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_23 ),
    inference(avatar_component_clause,[],[f188])).

fof(f605,plain,
    ( spl5_77
    | ~ spl5_38
    | ~ spl5_69 ),
    inference(avatar_split_clause,[],[f563,f557,f286,f603])).

fof(f286,plain,
    ( spl5_38
  <=> ! [X1,X0] :
        ( r2_hidden(X0,X1)
        | r1_xboole_0(X1,k2_tarski(X0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).

fof(f557,plain,
    ( spl5_69
  <=> ! [X1] :
        ( ~ r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_69])])).

fof(f563,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(k2_tarski(X1,X1),k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k2_tarski(X1,X1)))
        | r2_hidden(X1,k2_pre_topc(sK0,k2_tarski(sK1,sK1))) )
    | ~ spl5_38
    | ~ spl5_69 ),
    inference(resolution,[],[f558,f287])).

fof(f287,plain,
    ( ! [X0,X1] :
        ( r1_xboole_0(X1,k2_tarski(X0,X0))
        | r2_hidden(X0,X1) )
    | ~ spl5_38 ),
    inference(avatar_component_clause,[],[f286])).

fof(f558,plain,
    ( ! [X1] :
        ( ~ r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,X1)) )
    | ~ spl5_69 ),
    inference(avatar_component_clause,[],[f557])).

fof(f601,plain,
    ( spl5_76
    | ~ spl5_38
    | ~ spl5_68 ),
    inference(avatar_split_clause,[],[f561,f553,f286,f599])).

fof(f553,plain,
    ( spl5_68
  <=> ! [X0] :
        ( ~ r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),k2_pre_topc(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_68])])).

fof(f561,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(k2_tarski(X1,X1),k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),k2_pre_topc(sK0,k2_tarski(X1,X1)))
        | r2_hidden(X1,k2_pre_topc(sK0,k2_tarski(sK2,sK2))) )
    | ~ spl5_38
    | ~ spl5_68 ),
    inference(resolution,[],[f554,f287])).

fof(f554,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),k2_pre_topc(sK0,X0)) )
    | ~ spl5_68 ),
    inference(avatar_component_clause,[],[f553])).

fof(f559,plain,
    ( spl5_69
    | ~ spl5_54
    | ~ spl5_58
    | ~ spl5_67 ),
    inference(avatar_split_clause,[],[f551,f545,f441,f404,f557])).

fof(f404,plain,
    ( spl5_54
  <=> m1_subset_1(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_54])])).

fof(f441,plain,
    ( spl5_58
  <=> v3_pre_topc(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_58])])).

fof(f545,plain,
    ( spl5_67
  <=> ! [X1,X0] :
        ( ~ v3_pre_topc(X0,sK0)
        | ~ r1_xboole_0(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_xboole_0(X0,k2_pre_topc(sK0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_67])])).

fof(f551,plain,
    ( ! [X1] :
        ( ~ r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,X1)) )
    | ~ spl5_54
    | ~ spl5_58
    | ~ spl5_67 ),
    inference(subsumption_resolution,[],[f549,f405])).

fof(f405,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_54 ),
    inference(avatar_component_clause,[],[f404])).

fof(f549,plain,
    ( ! [X1] :
        ( ~ r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,X1)) )
    | ~ spl5_58
    | ~ spl5_67 ),
    inference(resolution,[],[f546,f443])).

fof(f443,plain,
    ( v3_pre_topc(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),sK0)
    | ~ spl5_58 ),
    inference(avatar_component_clause,[],[f441])).

fof(f546,plain,
    ( ! [X0,X1] :
        ( ~ v3_pre_topc(X0,sK0)
        | ~ r1_xboole_0(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_xboole_0(X0,k2_pre_topc(sK0,X1)) )
    | ~ spl5_67 ),
    inference(avatar_component_clause,[],[f545])).

fof(f555,plain,
    ( spl5_68
    | ~ spl5_52
    | ~ spl5_57
    | ~ spl5_67 ),
    inference(avatar_split_clause,[],[f550,f545,f436,f384,f553])).

fof(f384,plain,
    ( spl5_52
  <=> m1_subset_1(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_52])])).

fof(f436,plain,
    ( spl5_57
  <=> v3_pre_topc(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_57])])).

fof(f550,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),k2_pre_topc(sK0,X0)) )
    | ~ spl5_52
    | ~ spl5_57
    | ~ spl5_67 ),
    inference(subsumption_resolution,[],[f548,f385])).

fof(f385,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_52 ),
    inference(avatar_component_clause,[],[f384])).

fof(f548,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),k2_pre_topc(sK0,X0)) )
    | ~ spl5_57
    | ~ spl5_67 ),
    inference(resolution,[],[f546,f438])).

fof(f438,plain,
    ( v3_pre_topc(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),sK0)
    | ~ spl5_57 ),
    inference(avatar_component_clause,[],[f436])).

fof(f547,plain,
    ( spl5_67
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_66 ),
    inference(avatar_split_clause,[],[f543,f539,f95,f85,f545])).

fof(f539,plain,
    ( spl5_66
  <=> ! [X1,X0,X2] :
        ( r1_xboole_0(X1,k2_pre_topc(X0,X2))
        | ~ v3_pre_topc(X1,X0)
        | ~ r1_xboole_0(X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_66])])).

fof(f543,plain,
    ( ! [X0,X1] :
        ( ~ v3_pre_topc(X0,sK0)
        | ~ r1_xboole_0(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_xboole_0(X0,k2_pre_topc(sK0,X1)) )
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_66 ),
    inference(subsumption_resolution,[],[f542,f97])).

fof(f542,plain,
    ( ! [X0,X1] :
        ( ~ v3_pre_topc(X0,sK0)
        | ~ r1_xboole_0(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | r1_xboole_0(X0,k2_pre_topc(sK0,X1)) )
    | ~ spl5_2
    | ~ spl5_66 ),
    inference(resolution,[],[f540,f87])).

fof(f540,plain,
    ( ! [X2,X0,X1] :
        ( ~ v2_pre_topc(X0)
        | ~ v3_pre_topc(X1,X0)
        | ~ r1_xboole_0(X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | r1_xboole_0(X1,k2_pre_topc(X0,X2)) )
    | ~ spl5_66 ),
    inference(avatar_component_clause,[],[f539])).

fof(f541,plain,(
    spl5_66 ),
    inference(avatar_split_clause,[],[f68,f539])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X1,k2_pre_topc(X0,X2))
      | ~ v3_pre_topc(X1,X0)
      | ~ r1_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_xboole_0(X1,k2_pre_topc(X0,X2))
              | ~ v3_pre_topc(X1,X0)
              | ~ r1_xboole_0(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_xboole_0(X1,k2_pre_topc(X0,X2))
              | ~ v3_pre_topc(X1,X0)
              | ~ r1_xboole_0(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v3_pre_topc(X1,X0)
                  & r1_xboole_0(X1,X2) )
               => r1_xboole_0(X1,k2_pre_topc(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_tsep_1)).

fof(f444,plain,
    ( spl5_58
    | ~ spl5_54
    | ~ spl5_55
    | ~ spl5_56 ),
    inference(avatar_split_clause,[],[f434,f427,f408,f404,f441])).

fof(f408,plain,
    ( spl5_55
  <=> v4_pre_topc(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_55])])).

fof(f427,plain,
    ( spl5_56
  <=> ! [X0] :
        ( ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_56])])).

fof(f434,plain,
    ( v3_pre_topc(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),sK0)
    | ~ spl5_54
    | ~ spl5_55
    | ~ spl5_56 ),
    inference(subsumption_resolution,[],[f432,f405])).

fof(f432,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),sK0)
    | ~ spl5_55
    | ~ spl5_56 ),
    inference(resolution,[],[f428,f410])).

fof(f410,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),sK0)
    | ~ spl5_55 ),
    inference(avatar_component_clause,[],[f408])).

fof(f428,plain,
    ( ! [X0] :
        ( ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_pre_topc(X0,sK0) )
    | ~ spl5_56 ),
    inference(avatar_component_clause,[],[f427])).

fof(f439,plain,
    ( spl5_57
    | ~ spl5_52
    | ~ spl5_53
    | ~ spl5_56 ),
    inference(avatar_split_clause,[],[f433,f427,f388,f384,f436])).

fof(f388,plain,
    ( spl5_53
  <=> v4_pre_topc(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_53])])).

fof(f433,plain,
    ( v3_pre_topc(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),sK0)
    | ~ spl5_52
    | ~ spl5_53
    | ~ spl5_56 ),
    inference(subsumption_resolution,[],[f431,f385])).

fof(f431,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),sK0)
    | ~ spl5_53
    | ~ spl5_56 ),
    inference(resolution,[],[f428,f390])).

fof(f390,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),sK0)
    | ~ spl5_53 ),
    inference(avatar_component_clause,[],[f388])).

fof(f429,plain,
    ( spl5_56
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f425,f370,f95,f90,f85,f427])).

% (4295)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
fof(f370,plain,
    ( spl5_50
  <=> ! [X0,X2] :
        ( v3_pre_topc(X2,X0)
        | ~ v4_pre_topc(X2,X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v3_tdlat_3(X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_50])])).

fof(f425,plain,
    ( ! [X0] :
        ( ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_pre_topc(X0,sK0) )
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(subsumption_resolution,[],[f424,f87])).

fof(f424,plain,
    ( ! [X0] :
        ( ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_pre_topc(X0,sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(subsumption_resolution,[],[f423,f97])).

fof(f423,plain,
    ( ! [X0] :
        ( ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_pre_topc(X0,sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl5_3
    | ~ spl5_50 ),
    inference(resolution,[],[f371,f92])).

fof(f371,plain,
    ( ! [X2,X0] :
        ( ~ v3_tdlat_3(X0)
        | ~ v4_pre_topc(X2,X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | v3_pre_topc(X2,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl5_50 ),
    inference(avatar_component_clause,[],[f370])).

fof(f415,plain,
    ( ~ spl5_4
    | ~ spl5_23
    | ~ spl5_30
    | spl5_54 ),
    inference(avatar_contradiction_clause,[],[f414])).

fof(f414,plain,
    ( $false
    | ~ spl5_4
    | ~ spl5_23
    | ~ spl5_30
    | spl5_54 ),
    inference(subsumption_resolution,[],[f413,f97])).

fof(f413,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl5_23
    | ~ spl5_30
    | spl5_54 ),
    inference(subsumption_resolution,[],[f412,f190])).

fof(f412,plain,
    ( ~ m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl5_30
    | spl5_54 ),
    inference(resolution,[],[f406,f237])).

fof(f237,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl5_30 ),
    inference(avatar_component_clause,[],[f236])).

fof(f236,plain,
    ( spl5_30
  <=> ! [X1,X0] :
        ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f406,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_54 ),
    inference(avatar_component_clause,[],[f404])).

fof(f411,plain,
    ( ~ spl5_54
    | spl5_55
    | ~ spl5_46
    | ~ spl5_51 ),
    inference(avatar_split_clause,[],[f382,f376,f337,f408,f404])).

fof(f337,plain,
    ( spl5_46
  <=> k2_pre_topc(sK0,k2_tarski(sK1,sK1)) = k2_pre_topc(sK0,k2_pre_topc(sK0,k2_tarski(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_46])])).

fof(f376,plain,
    ( spl5_51
  <=> ! [X0] :
        ( k2_pre_topc(sK0,X0) != X0
        | v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_51])])).

fof(f382,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),sK0)
    | ~ m1_subset_1(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_46
    | ~ spl5_51 ),
    inference(trivial_inequality_removal,[],[f379])).

fof(f379,plain,
    ( k2_pre_topc(sK0,k2_tarski(sK1,sK1)) != k2_pre_topc(sK0,k2_tarski(sK1,sK1))
    | v4_pre_topc(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),sK0)
    | ~ m1_subset_1(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_46
    | ~ spl5_51 ),
    inference(superposition,[],[f377,f339])).

fof(f339,plain,
    ( k2_pre_topc(sK0,k2_tarski(sK1,sK1)) = k2_pre_topc(sK0,k2_pre_topc(sK0,k2_tarski(sK1,sK1)))
    | ~ spl5_46 ),
    inference(avatar_component_clause,[],[f337])).

fof(f377,plain,
    ( ! [X0] :
        ( k2_pre_topc(sK0,X0) != X0
        | v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_51 ),
    inference(avatar_component_clause,[],[f376])).

fof(f395,plain,
    ( ~ spl5_4
    | ~ spl5_27
    | ~ spl5_30
    | spl5_52 ),
    inference(avatar_contradiction_clause,[],[f394])).

fof(f394,plain,
    ( $false
    | ~ spl5_4
    | ~ spl5_27
    | ~ spl5_30
    | spl5_52 ),
    inference(subsumption_resolution,[],[f393,f97])).

fof(f393,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl5_27
    | ~ spl5_30
    | spl5_52 ),
    inference(subsumption_resolution,[],[f392,f222])).

fof(f392,plain,
    ( ~ m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl5_30
    | spl5_52 ),
    inference(resolution,[],[f386,f237])).

fof(f386,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_52 ),
    inference(avatar_component_clause,[],[f384])).

fof(f391,plain,
    ( ~ spl5_52
    | spl5_53
    | ~ spl5_47
    | ~ spl5_51 ),
    inference(avatar_split_clause,[],[f381,f376,f342,f388,f384])).

fof(f342,plain,
    ( spl5_47
  <=> k2_pre_topc(sK0,k2_tarski(sK2,sK2)) = k2_pre_topc(sK0,k2_pre_topc(sK0,k2_tarski(sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_47])])).

fof(f381,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),sK0)
    | ~ m1_subset_1(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_47
    | ~ spl5_51 ),
    inference(trivial_inequality_removal,[],[f380])).

fof(f380,plain,
    ( k2_pre_topc(sK0,k2_tarski(sK2,sK2)) != k2_pre_topc(sK0,k2_tarski(sK2,sK2))
    | v4_pre_topc(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),sK0)
    | ~ m1_subset_1(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_47
    | ~ spl5_51 ),
    inference(superposition,[],[f377,f344])).

fof(f344,plain,
    ( k2_pre_topc(sK0,k2_tarski(sK2,sK2)) = k2_pre_topc(sK0,k2_pre_topc(sK0,k2_tarski(sK2,sK2)))
    | ~ spl5_47 ),
    inference(avatar_component_clause,[],[f342])).

fof(f378,plain,
    ( spl5_51
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_45 ),
    inference(avatar_split_clause,[],[f374,f333,f95,f85,f376])).

fof(f333,plain,
    ( spl5_45
  <=> ! [X1,X0] :
        ( v4_pre_topc(X1,X0)
        | k2_pre_topc(X0,X1) != X1
        | ~ v2_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_45])])).

fof(f374,plain,
    ( ! [X0] :
        ( k2_pre_topc(sK0,X0) != X0
        | v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_45 ),
    inference(subsumption_resolution,[],[f373,f97])).

fof(f373,plain,
    ( ! [X0] :
        ( k2_pre_topc(sK0,X0) != X0
        | v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl5_2
    | ~ spl5_45 ),
    inference(resolution,[],[f334,f87])).

fof(f334,plain,
    ( ! [X0,X1] :
        ( ~ v2_pre_topc(X0)
        | k2_pre_topc(X0,X1) != X1
        | v4_pre_topc(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl5_45 ),
    inference(avatar_component_clause,[],[f333])).

fof(f372,plain,(
    spl5_50 ),
    inference(avatar_split_clause,[],[f64,f370])).

fof(f64,plain,(
    ! [X2,X0] :
      ( v3_pre_topc(X2,X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ( ( v3_tdlat_3(X0)
          | ( ~ v3_pre_topc(sK3(X0),X0)
            & v4_pre_topc(sK3(X0),X0)
            & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v3_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f45,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_pre_topc(X1,X0)
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK3(X0),X0)
        & v4_pre_topc(sK3(X0),X0)
        & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] :
      ( ( ( v3_tdlat_3(X0)
          | ? [X1] :
              ( ~ v3_pre_topc(X1,X0)
              & v4_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v3_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ( ( v3_tdlat_3(X0)
          | ? [X1] :
              ( ~ v3_pre_topc(X1,X0)
              & v4_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X1] :
              ( v3_pre_topc(X1,X0)
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v3_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
             => v3_pre_topc(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tdlat_3)).

fof(f345,plain,
    ( spl5_47
    | ~ spl5_27
    | ~ spl5_44 ),
    inference(avatar_split_clause,[],[f326,f322,f220,f342])).

fof(f322,plain,
    ( spl5_44
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,k2_pre_topc(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).

fof(f326,plain,
    ( k2_pre_topc(sK0,k2_tarski(sK2,sK2)) = k2_pre_topc(sK0,k2_pre_topc(sK0,k2_tarski(sK2,sK2)))
    | ~ spl5_27
    | ~ spl5_44 ),
    inference(resolution,[],[f323,f222])).

fof(f323,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,k2_pre_topc(sK0,X0)) )
    | ~ spl5_44 ),
    inference(avatar_component_clause,[],[f322])).

fof(f340,plain,
    ( spl5_46
    | ~ spl5_23
    | ~ spl5_44 ),
    inference(avatar_split_clause,[],[f325,f322,f188,f337])).

fof(f325,plain,
    ( k2_pre_topc(sK0,k2_tarski(sK1,sK1)) = k2_pre_topc(sK0,k2_pre_topc(sK0,k2_tarski(sK1,sK1)))
    | ~ spl5_23
    | ~ spl5_44 ),
    inference(resolution,[],[f323,f190])).

fof(f335,plain,(
    spl5_45 ),
    inference(avatar_split_clause,[],[f61,f333])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f324,plain,
    ( spl5_44
    | ~ spl5_4
    | ~ spl5_33 ),
    inference(avatar_split_clause,[],[f320,f251,f95,f322])).

fof(f251,plain,
    ( spl5_33
  <=> ! [X1,X0] :
        ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).

fof(f320,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,k2_pre_topc(sK0,X0)) )
    | ~ spl5_4
    | ~ spl5_33 ),
    inference(resolution,[],[f252,f97])).

fof(f252,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) )
    | ~ spl5_33 ),
    inference(avatar_component_clause,[],[f251])).

fof(f288,plain,
    ( spl5_38
    | ~ spl5_9
    | ~ spl5_35 ),
    inference(avatar_split_clause,[],[f284,f259,f118,f286])).

fof(f118,plain,
    ( spl5_9
  <=> ! [X1,X0] :
        ( r2_hidden(sK4(X0,X1),X0)
        | r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f259,plain,
    ( spl5_35
  <=> ! [X3,X5,X4] :
        ( ~ r2_hidden(sK4(X3,k2_tarski(X4,X4)),X5)
        | r2_hidden(X4,X5)
        | r1_xboole_0(X3,k2_tarski(X4,X4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).

fof(f284,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,X1)
        | r1_xboole_0(X1,k2_tarski(X0,X0)) )
    | ~ spl5_9
    | ~ spl5_35 ),
    inference(duplicate_literal_removal,[],[f280])).

fof(f280,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,X1)
        | r1_xboole_0(X1,k2_tarski(X0,X0))
        | r1_xboole_0(X1,k2_tarski(X0,X0)) )
    | ~ spl5_9
    | ~ spl5_35 ),
    inference(resolution,[],[f260,f119])).

fof(f119,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK4(X0,X1),X0)
        | r1_xboole_0(X0,X1) )
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f118])).

fof(f260,plain,
    ( ! [X4,X5,X3] :
        ( ~ r2_hidden(sK4(X3,k2_tarski(X4,X4)),X5)
        | r2_hidden(X4,X5)
        | r1_xboole_0(X3,k2_tarski(X4,X4)) )
    | ~ spl5_35 ),
    inference(avatar_component_clause,[],[f259])).

fof(f261,plain,
    ( spl5_35
    | ~ spl5_10
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f161,f157,f122,f259])).

fof(f157,plain,
    ( spl5_18
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k2_tarski(X2,X2))
        | r2_hidden(X2,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

% (4286)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
fof(f161,plain,
    ( ! [X4,X5,X3] :
        ( ~ r2_hidden(sK4(X3,k2_tarski(X4,X4)),X5)
        | r2_hidden(X4,X5)
        | r1_xboole_0(X3,k2_tarski(X4,X4)) )
    | ~ spl5_10
    | ~ spl5_18 ),
    inference(resolution,[],[f158,f123])).

fof(f158,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,k2_tarski(X2,X2))
        | ~ r2_hidden(X0,X1)
        | r2_hidden(X2,X1) )
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f157])).

fof(f253,plain,(
    spl5_33 ),
    inference(avatar_split_clause,[],[f76,f251])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',projectivity_k2_pre_topc)).

fof(f238,plain,(
    spl5_30 ),
    inference(avatar_split_clause,[],[f75,f236])).

fof(f75,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f234,plain,
    ( ~ spl5_29
    | ~ spl5_6
    | spl5_15
    | ~ spl5_20
    | spl5_21
    | ~ spl5_22 ),
    inference(avatar_split_clause,[],[f209,f179,f175,f167,f143,f105,f231])).

fof(f143,plain,
    ( spl5_15
  <=> r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f167,plain,
    ( spl5_20
  <=> ! [X1,X0] :
        ( k6_domain_1(X0,X1) = k2_tarski(X1,X1)
        | ~ m1_subset_1(X1,X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f175,plain,
    ( spl5_21
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

% (4288)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
fof(f209,plain,
    ( ~ r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k2_tarski(sK2,sK2)))
    | ~ spl5_6
    | spl5_15
    | ~ spl5_20
    | spl5_21
    | ~ spl5_22 ),
    inference(backward_demodulation,[],[f184,f207])).

fof(f207,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK2) = k2_tarski(sK2,sK2)
    | ~ spl5_6
    | ~ spl5_20
    | spl5_21 ),
    inference(subsumption_resolution,[],[f171,f176])).

fof(f176,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | spl5_21 ),
    inference(avatar_component_clause,[],[f175])).

fof(f171,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK2) = k2_tarski(sK2,sK2)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl5_6
    | ~ spl5_20 ),
    inference(resolution,[],[f168,f107])).

fof(f168,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,X0)
        | k6_domain_1(X0,X1) = k2_tarski(X1,X1)
        | v1_xboole_0(X0) )
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f167])).

fof(f184,plain,
    ( ~ r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
    | spl5_15
    | ~ spl5_22 ),
    inference(backward_demodulation,[],[f145,f181])).

fof(f145,plain,
    ( ~ r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
    | spl5_15 ),
    inference(avatar_component_clause,[],[f143])).

fof(f229,plain,
    ( ~ spl5_28
    | ~ spl5_6
    | ~ spl5_20
    | spl5_21
    | spl5_24 ),
    inference(avatar_split_clause,[],[f208,f193,f175,f167,f105,f226])).

fof(f193,plain,
    ( spl5_24
  <=> k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) = k2_pre_topc(sK0,k2_tarski(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f208,plain,
    ( k2_pre_topc(sK0,k2_tarski(sK1,sK1)) != k2_pre_topc(sK0,k2_tarski(sK2,sK2))
    | ~ spl5_6
    | ~ spl5_20
    | spl5_21
    | spl5_24 ),
    inference(backward_demodulation,[],[f195,f207])).

fof(f195,plain,
    ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) != k2_pre_topc(sK0,k2_tarski(sK1,sK1))
    | spl5_24 ),
    inference(avatar_component_clause,[],[f193])).

fof(f223,plain,
    ( spl5_27
    | ~ spl5_6
    | ~ spl5_17
    | spl5_21
    | ~ spl5_26 ),
    inference(avatar_split_clause,[],[f218,f212,f175,f153,f105,f220])).

fof(f153,plain,
    ( spl5_17
  <=> ! [X1,X0] :
        ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f218,plain,
    ( m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_6
    | ~ spl5_17
    | spl5_21
    | ~ spl5_26 ),
    inference(subsumption_resolution,[],[f217,f176])).

fof(f217,plain,
    ( m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl5_6
    | ~ spl5_17
    | ~ spl5_26 ),
    inference(subsumption_resolution,[],[f216,f107])).

fof(f216,plain,
    ( m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl5_17
    | ~ spl5_26 ),
    inference(superposition,[],[f154,f214])).

fof(f154,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,X0)
        | v1_xboole_0(X0) )
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f153])).

fof(f215,plain,
    ( spl5_26
    | ~ spl5_6
    | ~ spl5_20
    | spl5_21 ),
    inference(avatar_split_clause,[],[f207,f175,f167,f105,f212])).

fof(f206,plain,
    ( ~ spl5_4
    | ~ spl5_7
    | spl5_25 ),
    inference(avatar_contradiction_clause,[],[f205])).

fof(f205,plain,
    ( $false
    | ~ spl5_4
    | ~ spl5_7
    | spl5_25 ),
    inference(subsumption_resolution,[],[f204,f97])).

fof(f204,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl5_7
    | spl5_25 ),
    inference(resolution,[],[f202,f111])).

fof(f111,plain,
    ( ! [X0] :
        ( l1_struct_0(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl5_7
  <=> ! [X0] :
        ( l1_struct_0(X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f202,plain,
    ( ~ l1_struct_0(sK0)
    | spl5_25 ),
    inference(avatar_component_clause,[],[f200])).

fof(f200,plain,
    ( spl5_25
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f203,plain,
    ( ~ spl5_25
    | spl5_1
    | ~ spl5_8
    | ~ spl5_21 ),
    inference(avatar_split_clause,[],[f198,f175,f114,f80,f200])).

fof(f114,plain,
    ( spl5_8
  <=> ! [X0] :
        ( ~ v1_xboole_0(u1_struct_0(X0))
        | ~ l1_struct_0(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f198,plain,
    ( ~ l1_struct_0(sK0)
    | spl5_1
    | ~ spl5_8
    | ~ spl5_21 ),
    inference(subsumption_resolution,[],[f197,f82])).

fof(f197,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_8
    | ~ spl5_21 ),
    inference(resolution,[],[f177,f115])).

fof(f115,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(u1_struct_0(X0))
        | ~ l1_struct_0(X0)
        | v2_struct_0(X0) )
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f114])).

fof(f177,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f175])).

fof(f196,plain,
    ( ~ spl5_24
    | spl5_16
    | ~ spl5_22 ),
    inference(avatar_split_clause,[],[f183,f179,f148,f193])).

fof(f148,plain,
    ( spl5_16
  <=> k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f183,plain,
    ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) != k2_pre_topc(sK0,k2_tarski(sK1,sK1))
    | spl5_16
    | ~ spl5_22 ),
    inference(backward_demodulation,[],[f150,f181])).

fof(f150,plain,
    ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))
    | spl5_16 ),
    inference(avatar_component_clause,[],[f148])).

fof(f191,plain,
    ( spl5_21
    | spl5_23
    | ~ spl5_5
    | ~ spl5_17
    | ~ spl5_22 ),
    inference(avatar_split_clause,[],[f186,f179,f153,f100,f188,f175])).

fof(f186,plain,
    ( m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl5_5
    | ~ spl5_17
    | ~ spl5_22 ),
    inference(subsumption_resolution,[],[f185,f102])).

fof(f185,plain,
    ( m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl5_17
    | ~ spl5_22 ),
    inference(superposition,[],[f154,f181])).

fof(f182,plain,
    ( spl5_21
    | spl5_22
    | ~ spl5_5
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f170,f167,f100,f179,f175])).

fof(f170,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl5_5
    | ~ spl5_20 ),
    inference(resolution,[],[f168,f102])).

fof(f169,plain,(
    spl5_20 ),
    inference(avatar_split_clause,[],[f78,f167])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k2_tarski(X1,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f73,f58])).

fof(f58,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f73,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f159,plain,
    ( spl5_18
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f133,f130,f126,f157])).

fof(f126,plain,
    ( spl5_11
  <=> ! [X1,X0] :
        ( r1_xboole_0(k2_tarski(X0,X0),X1)
        | r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f133,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k2_tarski(X2,X2))
        | r2_hidden(X2,X1) )
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(resolution,[],[f131,f127])).

fof(f127,plain,
    ( ! [X0,X1] :
        ( r1_xboole_0(k2_tarski(X0,X0),X1)
        | r2_hidden(X0,X1) )
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f126])).

fof(f155,plain,(
    spl5_17 ),
    inference(avatar_split_clause,[],[f74,f153])).

fof(f74,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f151,plain,(
    ~ spl5_16 ),
    inference(avatar_split_clause,[],[f57,f148])).

fof(f57,plain,(
    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,
    ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))
    & ~ r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v3_tdlat_3(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f42,f41,f40])).

fof(f40,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
                & ~ r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1))
              & ~ r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_pre_topc(sK0)
      & v3_tdlat_3(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1))
            & ~ r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1))
          & ~ r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X2] :
        ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1))
        & ~ r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))
      & ~ r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
              & ~ r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
              & ~ r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v3_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
                  | r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
                | r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tex_2)).

fof(f146,plain,(
    ~ spl5_15 ),
    inference(avatar_split_clause,[],[f56,f143])).

fof(f56,plain,(
    ~ r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) ),
    inference(cnf_transformation,[],[f43])).

fof(f132,plain,(
    spl5_12 ),
    inference(avatar_split_clause,[],[f71,f130])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f30,f48])).

fof(f48,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f128,plain,(
    spl5_11 ),
    inference(avatar_split_clause,[],[f77,f126])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_tarski(X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f72,f58])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f124,plain,(
    spl5_10 ),
    inference(avatar_split_clause,[],[f70,f122])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f120,plain,(
    spl5_9 ),
    inference(avatar_split_clause,[],[f69,f118])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f116,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f62,f114])).

fof(f62,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f112,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f59,f110])).

fof(f59,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f108,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f55,f105])).

fof(f55,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f43])).

fof(f103,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f54,f100])).

fof(f54,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f43])).

fof(f98,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f53,f95])).

fof(f53,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f93,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f52,f90])).

fof(f52,plain,(
    v3_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f88,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f51,f85])).

fof(f51,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f83,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f50,f80])).

fof(f50,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f43])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:02:32 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.47  % (4292)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.47  % (4299)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.47  % (4293)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.47  % (4298)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.48  % (4290)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.48  % (4300)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.48  % (4291)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.49  % (4289)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.49  % (4293)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f750,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(avatar_sat_refutation,[],[f83,f88,f93,f98,f103,f108,f112,f116,f120,f124,f128,f132,f146,f151,f155,f159,f169,f182,f191,f196,f203,f206,f215,f223,f229,f234,f238,f253,f261,f288,f324,f335,f340,f345,f372,f378,f391,f395,f411,f415,f429,f439,f444,f541,f547,f555,f559,f601,f605,f612,f620,f624,f629,f641,f661,f709,f717,f731,f742,f749])).
% 0.22/0.49  fof(f749,plain,(
% 0.22/0.49    ~spl5_10 | spl5_29 | ~spl5_82),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f748])).
% 0.22/0.49  fof(f748,plain,(
% 0.22/0.49    $false | (~spl5_10 | spl5_29 | ~spl5_82)),
% 0.22/0.49    inference(subsumption_resolution,[],[f233,f746])).
% 0.22/0.49  fof(f746,plain,(
% 0.22/0.49    ( ! [X1] : (r1_xboole_0(X1,k2_pre_topc(sK0,k2_tarski(sK2,sK2)))) ) | (~spl5_10 | ~spl5_82)),
% 0.22/0.49    inference(resolution,[],[f640,f123])).
% 0.22/0.49  fof(f123,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | r1_xboole_0(X0,X1)) ) | ~spl5_10),
% 0.22/0.49    inference(avatar_component_clause,[],[f122])).
% 0.22/0.49  fof(f122,plain,(
% 0.22/0.49    spl5_10 <=> ! [X1,X0] : (r2_hidden(sK4(X0,X1),X1) | r1_xboole_0(X0,X1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.22/0.49  fof(f640,plain,(
% 0.22/0.49    ( ! [X0] : (~r2_hidden(X0,k2_pre_topc(sK0,k2_tarski(sK2,sK2)))) ) | ~spl5_82),
% 0.22/0.49    inference(avatar_component_clause,[],[f639])).
% 0.22/0.49  fof(f639,plain,(
% 0.22/0.49    spl5_82 <=> ! [X0] : ~r2_hidden(X0,k2_pre_topc(sK0,k2_tarski(sK2,sK2)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_82])])).
% 0.22/0.49  fof(f233,plain,(
% 0.22/0.49    ~r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k2_tarski(sK2,sK2))) | spl5_29),
% 0.22/0.49    inference(avatar_component_clause,[],[f231])).
% 0.22/0.49  fof(f231,plain,(
% 0.22/0.49    spl5_29 <=> r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k2_tarski(sK2,sK2)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).
% 0.22/0.49  fof(f742,plain,(
% 0.22/0.49    ~spl5_79 | ~spl5_81 | ~spl5_84),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f741])).
% 0.22/0.49  fof(f741,plain,(
% 0.22/0.49    $false | (~spl5_79 | ~spl5_81 | ~spl5_84)),
% 0.22/0.49    inference(subsumption_resolution,[],[f738,f628])).
% 0.22/0.49  fof(f628,plain,(
% 0.22/0.49    r2_hidden(sK2,k2_pre_topc(sK0,k2_tarski(sK2,sK2))) | ~spl5_81),
% 0.22/0.49    inference(avatar_component_clause,[],[f626])).
% 0.22/0.49  fof(f626,plain,(
% 0.22/0.49    spl5_81 <=> r2_hidden(sK2,k2_pre_topc(sK0,k2_tarski(sK2,sK2)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_81])])).
% 0.22/0.49  fof(f738,plain,(
% 0.22/0.49    ~r2_hidden(sK2,k2_pre_topc(sK0,k2_tarski(sK2,sK2))) | (~spl5_79 | ~spl5_84)),
% 0.22/0.49    inference(resolution,[],[f619,f660])).
% 0.22/0.49  fof(f660,plain,(
% 0.22/0.49    r2_hidden(sK2,k2_pre_topc(sK0,k2_tarski(sK1,sK1))) | ~spl5_84),
% 0.22/0.49    inference(avatar_component_clause,[],[f658])).
% 0.22/0.49  fof(f658,plain,(
% 0.22/0.49    spl5_84 <=> r2_hidden(sK2,k2_pre_topc(sK0,k2_tarski(sK1,sK1)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_84])])).
% 0.22/0.49  fof(f619,plain,(
% 0.22/0.49    ( ! [X0] : (~r2_hidden(X0,k2_pre_topc(sK0,k2_tarski(sK1,sK1))) | ~r2_hidden(X0,k2_pre_topc(sK0,k2_tarski(sK2,sK2)))) ) | ~spl5_79),
% 0.22/0.49    inference(avatar_component_clause,[],[f618])).
% 0.22/0.49  fof(f618,plain,(
% 0.22/0.49    spl5_79 <=> ! [X0] : (~r2_hidden(X0,k2_pre_topc(sK0,k2_tarski(sK1,sK1))) | ~r2_hidden(X0,k2_pre_topc(sK0,k2_tarski(sK2,sK2))))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_79])])).
% 0.22/0.49  fof(f731,plain,(
% 0.22/0.49    ~spl5_78 | ~spl5_6 | ~spl5_26 | spl5_28 | ~spl5_89),
% 0.22/0.49    inference(avatar_split_clause,[],[f729,f715,f226,f212,f105,f609])).
% 0.22/0.49  fof(f609,plain,(
% 0.22/0.49    spl5_78 <=> r2_hidden(sK1,k2_pre_topc(sK0,k2_tarski(sK2,sK2)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_78])])).
% 0.22/0.49  fof(f105,plain,(
% 0.22/0.49    spl5_6 <=> m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.22/0.49  fof(f212,plain,(
% 0.22/0.49    spl5_26 <=> k6_domain_1(u1_struct_0(sK0),sK2) = k2_tarski(sK2,sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 0.22/0.49  fof(f226,plain,(
% 0.22/0.49    spl5_28 <=> k2_pre_topc(sK0,k2_tarski(sK1,sK1)) = k2_pre_topc(sK0,k2_tarski(sK2,sK2))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).
% 0.22/0.49  fof(f715,plain,(
% 0.22/0.49    spl5_89 <=> ! [X0] : (k2_pre_topc(sK0,k2_tarski(sK1,sK1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0))))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_89])])).
% 0.22/0.49  fof(f729,plain,(
% 0.22/0.49    ~r2_hidden(sK1,k2_pre_topc(sK0,k2_tarski(sK2,sK2))) | (~spl5_6 | ~spl5_26 | spl5_28 | ~spl5_89)),
% 0.22/0.49    inference(subsumption_resolution,[],[f728,f228])).
% 0.22/0.49  fof(f228,plain,(
% 0.22/0.49    k2_pre_topc(sK0,k2_tarski(sK1,sK1)) != k2_pre_topc(sK0,k2_tarski(sK2,sK2)) | spl5_28),
% 0.22/0.49    inference(avatar_component_clause,[],[f226])).
% 0.22/0.49  fof(f728,plain,(
% 0.22/0.49    ~r2_hidden(sK1,k2_pre_topc(sK0,k2_tarski(sK2,sK2))) | k2_pre_topc(sK0,k2_tarski(sK1,sK1)) = k2_pre_topc(sK0,k2_tarski(sK2,sK2)) | (~spl5_6 | ~spl5_26 | ~spl5_89)),
% 0.22/0.49    inference(subsumption_resolution,[],[f723,f107])).
% 0.22/0.49  fof(f107,plain,(
% 0.22/0.49    m1_subset_1(sK2,u1_struct_0(sK0)) | ~spl5_6),
% 0.22/0.49    inference(avatar_component_clause,[],[f105])).
% 0.22/0.49  fof(f723,plain,(
% 0.22/0.49    ~r2_hidden(sK1,k2_pre_topc(sK0,k2_tarski(sK2,sK2))) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | k2_pre_topc(sK0,k2_tarski(sK1,sK1)) = k2_pre_topc(sK0,k2_tarski(sK2,sK2)) | (~spl5_26 | ~spl5_89)),
% 0.22/0.49    inference(superposition,[],[f716,f214])).
% 0.22/0.49  fof(f214,plain,(
% 0.22/0.49    k6_domain_1(u1_struct_0(sK0),sK2) = k2_tarski(sK2,sK2) | ~spl5_26),
% 0.22/0.49    inference(avatar_component_clause,[],[f212])).
% 0.22/0.49  fof(f716,plain,(
% 0.22/0.49    ( ! [X0] : (~r2_hidden(sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k2_pre_topc(sK0,k2_tarski(sK1,sK1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0))) ) | ~spl5_89),
% 0.22/0.49    inference(avatar_component_clause,[],[f715])).
% 0.22/0.49  fof(f717,plain,(
% 0.22/0.49    spl5_89 | ~spl5_5 | ~spl5_22 | ~spl5_88),
% 0.22/0.49    inference(avatar_split_clause,[],[f712,f707,f179,f100,f715])).
% 0.22/0.49  fof(f100,plain,(
% 0.22/0.49    spl5_5 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.22/0.49  fof(f179,plain,(
% 0.22/0.49    spl5_22 <=> k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 0.22/0.49  fof(f707,plain,(
% 0.22/0.49    spl5_88 <=> ! [X1,X0] : (~r2_hidden(X0,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_88])])).
% 0.22/0.49  fof(f712,plain,(
% 0.22/0.49    ( ! [X0] : (k2_pre_topc(sK0,k2_tarski(sK1,sK1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0)))) ) | (~spl5_5 | ~spl5_22 | ~spl5_88)),
% 0.22/0.49    inference(forward_demodulation,[],[f710,f181])).
% 0.22/0.49  fof(f181,plain,(
% 0.22/0.49    k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1) | ~spl5_22),
% 0.22/0.49    inference(avatar_component_clause,[],[f179])).
% 0.22/0.49  fof(f710,plain,(
% 0.22/0.49    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0))) | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0))) ) | (~spl5_5 | ~spl5_88)),
% 0.22/0.49    inference(resolution,[],[f708,f102])).
% 0.22/0.49  fof(f102,plain,(
% 0.22/0.49    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl5_5),
% 0.22/0.49    inference(avatar_component_clause,[],[f100])).
% 0.22/0.49  fof(f708,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X0,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1))) | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0))) ) | ~spl5_88),
% 0.22/0.49    inference(avatar_component_clause,[],[f707])).
% 0.22/0.49  fof(f709,plain,(
% 0.22/0.49    spl5_88 | spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_80),
% 0.22/0.49    inference(avatar_split_clause,[],[f705,f622,f95,f90,f85,f80,f707])).
% 0.22/0.49  fof(f80,plain,(
% 0.22/0.49    spl5_1 <=> v2_struct_0(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.49  fof(f85,plain,(
% 0.22/0.49    spl5_2 <=> v2_pre_topc(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.22/0.49  fof(f90,plain,(
% 0.22/0.49    spl5_3 <=> v3_tdlat_3(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.22/0.49  fof(f95,plain,(
% 0.22/0.49    spl5_4 <=> l1_pre_topc(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.22/0.49  fof(f622,plain,(
% 0.22/0.49    spl5_80 <=> ! [X1,X0,X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) | ~r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_80])])).
% 0.22/0.49  fof(f705,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r2_hidden(X0,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0))) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_80)),
% 0.22/0.49    inference(subsumption_resolution,[],[f704,f82])).
% 0.22/0.49  fof(f82,plain,(
% 0.22/0.49    ~v2_struct_0(sK0) | spl5_1),
% 0.22/0.49    inference(avatar_component_clause,[],[f80])).
% 0.22/0.49  fof(f704,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r2_hidden(X0,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0)) | v2_struct_0(sK0)) ) | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_80)),
% 0.22/0.49    inference(subsumption_resolution,[],[f703,f87])).
% 0.22/0.49  fof(f87,plain,(
% 0.22/0.49    v2_pre_topc(sK0) | ~spl5_2),
% 0.22/0.49    inference(avatar_component_clause,[],[f85])).
% 0.22/0.49  fof(f703,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r2_hidden(X0,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl5_3 | ~spl5_4 | ~spl5_80)),
% 0.22/0.49    inference(subsumption_resolution,[],[f702,f97])).
% 0.22/0.49  fof(f97,plain,(
% 0.22/0.49    l1_pre_topc(sK0) | ~spl5_4),
% 0.22/0.49    inference(avatar_component_clause,[],[f95])).
% 0.22/0.49  fof(f702,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r2_hidden(X0,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl5_3 | ~spl5_80)),
% 0.22/0.49    inference(resolution,[],[f623,f92])).
% 0.22/0.49  fof(f92,plain,(
% 0.22/0.49    v3_tdlat_3(sK0) | ~spl5_3),
% 0.22/0.49    inference(avatar_component_clause,[],[f90])).
% 0.22/0.49  fof(f623,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~v3_tdlat_3(X0) | ~r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) | ~v2_pre_topc(X0) | v2_struct_0(X0)) ) | ~spl5_80),
% 0.22/0.49    inference(avatar_component_clause,[],[f622])).
% 0.22/0.49  fof(f661,plain,(
% 0.22/0.49    spl5_84 | ~spl5_27 | spl5_29 | ~spl5_77),
% 0.22/0.49    inference(avatar_split_clause,[],[f656,f603,f231,f220,f658])).
% 0.22/0.49  fof(f220,plain,(
% 0.22/0.49    spl5_27 <=> m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 0.22/0.49  fof(f603,plain,(
% 0.22/0.49    spl5_77 <=> ! [X1] : (~m1_subset_1(k2_tarski(X1,X1),k1_zfmisc_1(u1_struct_0(sK0))) | r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k2_tarski(X1,X1))) | r2_hidden(X1,k2_pre_topc(sK0,k2_tarski(sK1,sK1))))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_77])])).
% 0.22/0.49  fof(f656,plain,(
% 0.22/0.49    r2_hidden(sK2,k2_pre_topc(sK0,k2_tarski(sK1,sK1))) | (~spl5_27 | spl5_29 | ~spl5_77)),
% 0.22/0.49    inference(subsumption_resolution,[],[f655,f233])).
% 0.22/0.49  fof(f655,plain,(
% 0.22/0.49    r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k2_tarski(sK2,sK2))) | r2_hidden(sK2,k2_pre_topc(sK0,k2_tarski(sK1,sK1))) | (~spl5_27 | ~spl5_77)),
% 0.22/0.49    inference(resolution,[],[f604,f222])).
% 0.22/0.49  fof(f222,plain,(
% 0.22/0.49    m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_27),
% 0.22/0.49    inference(avatar_component_clause,[],[f220])).
% 0.22/0.49  fof(f604,plain,(
% 0.22/0.49    ( ! [X1] : (~m1_subset_1(k2_tarski(X1,X1),k1_zfmisc_1(u1_struct_0(sK0))) | r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k2_tarski(X1,X1))) | r2_hidden(X1,k2_pre_topc(sK0,k2_tarski(sK1,sK1)))) ) | ~spl5_77),
% 0.22/0.49    inference(avatar_component_clause,[],[f603])).
% 0.22/0.49  fof(f641,plain,(
% 0.22/0.49    spl5_82 | ~spl5_12 | ~spl5_75),
% 0.22/0.49    inference(avatar_split_clause,[],[f632,f590,f130,f639])).
% 0.22/0.49  fof(f130,plain,(
% 0.22/0.49    spl5_12 <=> ! [X1,X0,X2] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.22/0.49  fof(f590,plain,(
% 0.22/0.49    spl5_75 <=> r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),k2_pre_topc(sK0,k2_tarski(sK2,sK2)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_75])])).
% 0.22/0.49  fof(f632,plain,(
% 0.22/0.49    ( ! [X0] : (~r2_hidden(X0,k2_pre_topc(sK0,k2_tarski(sK2,sK2)))) ) | (~spl5_12 | ~spl5_75)),
% 0.22/0.49    inference(duplicate_literal_removal,[],[f631])).
% 0.22/0.49  fof(f631,plain,(
% 0.22/0.49    ( ! [X0] : (~r2_hidden(X0,k2_pre_topc(sK0,k2_tarski(sK2,sK2))) | ~r2_hidden(X0,k2_pre_topc(sK0,k2_tarski(sK2,sK2)))) ) | (~spl5_12 | ~spl5_75)),
% 0.22/0.49    inference(resolution,[],[f592,f131])).
% 0.22/0.49  fof(f131,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) ) | ~spl5_12),
% 0.22/0.49    inference(avatar_component_clause,[],[f130])).
% 0.22/0.49  fof(f592,plain,(
% 0.22/0.49    r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),k2_pre_topc(sK0,k2_tarski(sK2,sK2))) | ~spl5_75),
% 0.22/0.49    inference(avatar_component_clause,[],[f590])).
% 0.22/0.49  fof(f629,plain,(
% 0.22/0.49    spl5_81 | spl5_75 | ~spl5_27 | ~spl5_76),
% 0.22/0.49    inference(avatar_split_clause,[],[f607,f599,f220,f590,f626])).
% 0.22/0.49  fof(f599,plain,(
% 0.22/0.49    spl5_76 <=> ! [X1] : (~m1_subset_1(k2_tarski(X1,X1),k1_zfmisc_1(u1_struct_0(sK0))) | r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),k2_pre_topc(sK0,k2_tarski(X1,X1))) | r2_hidden(X1,k2_pre_topc(sK0,k2_tarski(sK2,sK2))))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_76])])).
% 0.22/0.49  fof(f607,plain,(
% 0.22/0.49    r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),k2_pre_topc(sK0,k2_tarski(sK2,sK2))) | r2_hidden(sK2,k2_pre_topc(sK0,k2_tarski(sK2,sK2))) | (~spl5_27 | ~spl5_76)),
% 0.22/0.49    inference(resolution,[],[f600,f222])).
% 0.22/0.49  fof(f600,plain,(
% 0.22/0.49    ( ! [X1] : (~m1_subset_1(k2_tarski(X1,X1),k1_zfmisc_1(u1_struct_0(sK0))) | r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),k2_pre_topc(sK0,k2_tarski(X1,X1))) | r2_hidden(X1,k2_pre_topc(sK0,k2_tarski(sK2,sK2)))) ) | ~spl5_76),
% 0.22/0.49    inference(avatar_component_clause,[],[f599])).
% 0.22/0.49  fof(f624,plain,(
% 0.22/0.49    spl5_80),
% 0.22/0.49    inference(avatar_split_clause,[],[f63,f622])).
% 0.22/0.49  fof(f63,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) | ~r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f25])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) | ~r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f24])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : ((k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) | ~r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f13])).
% 0.22/0.49  fof(f13,axiom,(
% 0.22/0.49    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) => k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tex_2)).
% 0.22/0.49  fof(f620,plain,(
% 0.22/0.49    spl5_79 | ~spl5_12 | ~spl5_73),
% 0.22/0.49    inference(avatar_split_clause,[],[f614,f579,f130,f618])).
% 0.22/0.49  fof(f579,plain,(
% 0.22/0.49    spl5_73 <=> r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),k2_pre_topc(sK0,k2_tarski(sK1,sK1)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_73])])).
% 0.22/0.49  fof(f614,plain,(
% 0.22/0.49    ( ! [X0] : (~r2_hidden(X0,k2_pre_topc(sK0,k2_tarski(sK1,sK1))) | ~r2_hidden(X0,k2_pre_topc(sK0,k2_tarski(sK2,sK2)))) ) | (~spl5_12 | ~spl5_73)),
% 0.22/0.49    inference(resolution,[],[f581,f131])).
% 0.22/0.49  fof(f581,plain,(
% 0.22/0.49    r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),k2_pre_topc(sK0,k2_tarski(sK1,sK1))) | ~spl5_73),
% 0.22/0.49    inference(avatar_component_clause,[],[f579])).
% 0.22/0.49  fof(f612,plain,(
% 0.22/0.49    spl5_78 | spl5_73 | ~spl5_23 | ~spl5_76),
% 0.22/0.49    inference(avatar_split_clause,[],[f606,f599,f188,f579,f609])).
% 0.22/0.49  fof(f188,plain,(
% 0.22/0.49    spl5_23 <=> m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 0.22/0.49  fof(f606,plain,(
% 0.22/0.49    r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),k2_pre_topc(sK0,k2_tarski(sK1,sK1))) | r2_hidden(sK1,k2_pre_topc(sK0,k2_tarski(sK2,sK2))) | (~spl5_23 | ~spl5_76)),
% 0.22/0.49    inference(resolution,[],[f600,f190])).
% 0.22/0.49  fof(f190,plain,(
% 0.22/0.49    m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_23),
% 0.22/0.49    inference(avatar_component_clause,[],[f188])).
% 0.22/0.49  fof(f605,plain,(
% 0.22/0.49    spl5_77 | ~spl5_38 | ~spl5_69),
% 0.22/0.49    inference(avatar_split_clause,[],[f563,f557,f286,f603])).
% 0.22/0.49  fof(f286,plain,(
% 0.22/0.49    spl5_38 <=> ! [X1,X0] : (r2_hidden(X0,X1) | r1_xboole_0(X1,k2_tarski(X0,X0)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).
% 0.22/0.49  fof(f557,plain,(
% 0.22/0.49    spl5_69 <=> ! [X1] : (~r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,X1)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_69])])).
% 0.22/0.49  fof(f563,plain,(
% 0.22/0.49    ( ! [X1] : (~m1_subset_1(k2_tarski(X1,X1),k1_zfmisc_1(u1_struct_0(sK0))) | r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k2_tarski(X1,X1))) | r2_hidden(X1,k2_pre_topc(sK0,k2_tarski(sK1,sK1)))) ) | (~spl5_38 | ~spl5_69)),
% 0.22/0.49    inference(resolution,[],[f558,f287])).
% 0.22/0.49  fof(f287,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r1_xboole_0(X1,k2_tarski(X0,X0)) | r2_hidden(X0,X1)) ) | ~spl5_38),
% 0.22/0.49    inference(avatar_component_clause,[],[f286])).
% 0.22/0.49  fof(f558,plain,(
% 0.22/0.49    ( ! [X1] : (~r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,X1))) ) | ~spl5_69),
% 0.22/0.49    inference(avatar_component_clause,[],[f557])).
% 0.22/0.49  fof(f601,plain,(
% 0.22/0.49    spl5_76 | ~spl5_38 | ~spl5_68),
% 0.22/0.49    inference(avatar_split_clause,[],[f561,f553,f286,f599])).
% 0.22/0.49  fof(f553,plain,(
% 0.22/0.49    spl5_68 <=> ! [X0] : (~r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),k2_pre_topc(sK0,X0)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_68])])).
% 0.22/0.49  fof(f561,plain,(
% 0.22/0.49    ( ! [X1] : (~m1_subset_1(k2_tarski(X1,X1),k1_zfmisc_1(u1_struct_0(sK0))) | r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),k2_pre_topc(sK0,k2_tarski(X1,X1))) | r2_hidden(X1,k2_pre_topc(sK0,k2_tarski(sK2,sK2)))) ) | (~spl5_38 | ~spl5_68)),
% 0.22/0.49    inference(resolution,[],[f554,f287])).
% 0.22/0.49  fof(f554,plain,(
% 0.22/0.49    ( ! [X0] : (~r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),k2_pre_topc(sK0,X0))) ) | ~spl5_68),
% 0.22/0.49    inference(avatar_component_clause,[],[f553])).
% 0.22/0.49  fof(f559,plain,(
% 0.22/0.49    spl5_69 | ~spl5_54 | ~spl5_58 | ~spl5_67),
% 0.22/0.49    inference(avatar_split_clause,[],[f551,f545,f441,f404,f557])).
% 0.22/0.49  fof(f404,plain,(
% 0.22/0.49    spl5_54 <=> m1_subset_1(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_54])])).
% 0.22/0.49  fof(f441,plain,(
% 0.22/0.49    spl5_58 <=> v3_pre_topc(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_58])])).
% 0.22/0.49  fof(f545,plain,(
% 0.22/0.49    spl5_67 <=> ! [X1,X0] : (~v3_pre_topc(X0,sK0) | ~r1_xboole_0(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_xboole_0(X0,k2_pre_topc(sK0,X1)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_67])])).
% 0.22/0.49  fof(f551,plain,(
% 0.22/0.49    ( ! [X1] : (~r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,X1))) ) | (~spl5_54 | ~spl5_58 | ~spl5_67)),
% 0.22/0.49    inference(subsumption_resolution,[],[f549,f405])).
% 0.22/0.49  fof(f405,plain,(
% 0.22/0.49    m1_subset_1(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_54),
% 0.22/0.49    inference(avatar_component_clause,[],[f404])).
% 0.22/0.49  fof(f549,plain,(
% 0.22/0.49    ( ! [X1] : (~r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,X1))) ) | (~spl5_58 | ~spl5_67)),
% 0.22/0.49    inference(resolution,[],[f546,f443])).
% 0.22/0.49  fof(f443,plain,(
% 0.22/0.49    v3_pre_topc(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),sK0) | ~spl5_58),
% 0.22/0.49    inference(avatar_component_clause,[],[f441])).
% 0.22/0.49  fof(f546,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v3_pre_topc(X0,sK0) | ~r1_xboole_0(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_xboole_0(X0,k2_pre_topc(sK0,X1))) ) | ~spl5_67),
% 0.22/0.49    inference(avatar_component_clause,[],[f545])).
% 0.22/0.49  fof(f555,plain,(
% 0.22/0.49    spl5_68 | ~spl5_52 | ~spl5_57 | ~spl5_67),
% 0.22/0.49    inference(avatar_split_clause,[],[f550,f545,f436,f384,f553])).
% 0.22/0.49  fof(f384,plain,(
% 0.22/0.49    spl5_52 <=> m1_subset_1(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_52])])).
% 0.22/0.49  fof(f436,plain,(
% 0.22/0.49    spl5_57 <=> v3_pre_topc(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_57])])).
% 0.22/0.49  fof(f550,plain,(
% 0.22/0.49    ( ! [X0] : (~r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),k2_pre_topc(sK0,X0))) ) | (~spl5_52 | ~spl5_57 | ~spl5_67)),
% 0.22/0.49    inference(subsumption_resolution,[],[f548,f385])).
% 0.22/0.49  fof(f385,plain,(
% 0.22/0.49    m1_subset_1(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_52),
% 0.22/0.49    inference(avatar_component_clause,[],[f384])).
% 0.22/0.49  fof(f548,plain,(
% 0.22/0.49    ( ! [X0] : (~r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),k2_pre_topc(sK0,X0))) ) | (~spl5_57 | ~spl5_67)),
% 0.22/0.49    inference(resolution,[],[f546,f438])).
% 0.22/0.49  fof(f438,plain,(
% 0.22/0.49    v3_pre_topc(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),sK0) | ~spl5_57),
% 0.22/0.49    inference(avatar_component_clause,[],[f436])).
% 0.22/0.49  fof(f547,plain,(
% 0.22/0.49    spl5_67 | ~spl5_2 | ~spl5_4 | ~spl5_66),
% 0.22/0.49    inference(avatar_split_clause,[],[f543,f539,f95,f85,f545])).
% 0.22/0.49  fof(f539,plain,(
% 0.22/0.49    spl5_66 <=> ! [X1,X0,X2] : (r1_xboole_0(X1,k2_pre_topc(X0,X2)) | ~v3_pre_topc(X1,X0) | ~r1_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_66])])).
% 0.22/0.49  fof(f543,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v3_pre_topc(X0,sK0) | ~r1_xboole_0(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_xboole_0(X0,k2_pre_topc(sK0,X1))) ) | (~spl5_2 | ~spl5_4 | ~spl5_66)),
% 0.22/0.49    inference(subsumption_resolution,[],[f542,f97])).
% 0.22/0.49  fof(f542,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v3_pre_topc(X0,sK0) | ~r1_xboole_0(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | r1_xboole_0(X0,k2_pre_topc(sK0,X1))) ) | (~spl5_2 | ~spl5_66)),
% 0.22/0.49    inference(resolution,[],[f540,f87])).
% 0.22/0.49  fof(f540,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~v3_pre_topc(X1,X0) | ~r1_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | r1_xboole_0(X1,k2_pre_topc(X0,X2))) ) | ~spl5_66),
% 0.22/0.49    inference(avatar_component_clause,[],[f539])).
% 0.22/0.49  fof(f541,plain,(
% 0.22/0.49    spl5_66),
% 0.22/0.49    inference(avatar_split_clause,[],[f68,f539])).
% 0.22/0.49  fof(f68,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (r1_xboole_0(X1,k2_pre_topc(X0,X2)) | ~v3_pre_topc(X1,X0) | ~r1_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f29])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : (r1_xboole_0(X1,k2_pre_topc(X0,X2)) | ~v3_pre_topc(X1,X0) | ~r1_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.49    inference(flattening,[],[f28])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : ((r1_xboole_0(X1,k2_pre_topc(X0,X2)) | (~v3_pre_topc(X1,X0) | ~r1_xboole_0(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f12])).
% 0.22/0.49  fof(f12,axiom,(
% 0.22/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X1,X0) & r1_xboole_0(X1,X2)) => r1_xboole_0(X1,k2_pre_topc(X0,X2))))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_tsep_1)).
% 0.22/0.49  fof(f444,plain,(
% 0.22/0.49    spl5_58 | ~spl5_54 | ~spl5_55 | ~spl5_56),
% 0.22/0.49    inference(avatar_split_clause,[],[f434,f427,f408,f404,f441])).
% 0.22/0.49  fof(f408,plain,(
% 0.22/0.49    spl5_55 <=> v4_pre_topc(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_55])])).
% 0.22/0.49  fof(f427,plain,(
% 0.22/0.49    spl5_56 <=> ! [X0] : (~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(X0,sK0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_56])])).
% 0.22/0.49  fof(f434,plain,(
% 0.22/0.49    v3_pre_topc(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),sK0) | (~spl5_54 | ~spl5_55 | ~spl5_56)),
% 0.22/0.49    inference(subsumption_resolution,[],[f432,f405])).
% 0.22/0.49  fof(f432,plain,(
% 0.22/0.49    ~m1_subset_1(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),sK0) | (~spl5_55 | ~spl5_56)),
% 0.22/0.49    inference(resolution,[],[f428,f410])).
% 0.22/0.49  fof(f410,plain,(
% 0.22/0.49    v4_pre_topc(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),sK0) | ~spl5_55),
% 0.22/0.49    inference(avatar_component_clause,[],[f408])).
% 0.22/0.49  fof(f428,plain,(
% 0.22/0.49    ( ! [X0] : (~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(X0,sK0)) ) | ~spl5_56),
% 0.22/0.49    inference(avatar_component_clause,[],[f427])).
% 0.22/0.49  fof(f439,plain,(
% 0.22/0.49    spl5_57 | ~spl5_52 | ~spl5_53 | ~spl5_56),
% 0.22/0.49    inference(avatar_split_clause,[],[f433,f427,f388,f384,f436])).
% 0.22/0.49  fof(f388,plain,(
% 0.22/0.49    spl5_53 <=> v4_pre_topc(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_53])])).
% 0.22/0.49  fof(f433,plain,(
% 0.22/0.49    v3_pre_topc(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),sK0) | (~spl5_52 | ~spl5_53 | ~spl5_56)),
% 0.22/0.49    inference(subsumption_resolution,[],[f431,f385])).
% 0.22/0.49  fof(f431,plain,(
% 0.22/0.49    ~m1_subset_1(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),sK0) | (~spl5_53 | ~spl5_56)),
% 0.22/0.49    inference(resolution,[],[f428,f390])).
% 0.22/0.49  fof(f390,plain,(
% 0.22/0.49    v4_pre_topc(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),sK0) | ~spl5_53),
% 0.22/0.49    inference(avatar_component_clause,[],[f388])).
% 0.22/0.49  fof(f429,plain,(
% 0.22/0.49    spl5_56 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_50),
% 0.22/0.49    inference(avatar_split_clause,[],[f425,f370,f95,f90,f85,f427])).
% 0.22/0.49  % (4295)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.49  fof(f370,plain,(
% 0.22/0.49    spl5_50 <=> ! [X0,X2] : (v3_pre_topc(X2,X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tdlat_3(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_50])])).
% 0.22/0.49  fof(f425,plain,(
% 0.22/0.49    ( ! [X0] : (~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(X0,sK0)) ) | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_50)),
% 0.22/0.49    inference(subsumption_resolution,[],[f424,f87])).
% 0.22/0.49  fof(f424,plain,(
% 0.22/0.49    ( ! [X0] : (~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(X0,sK0) | ~v2_pre_topc(sK0)) ) | (~spl5_3 | ~spl5_4 | ~spl5_50)),
% 0.22/0.49    inference(subsumption_resolution,[],[f423,f97])).
% 0.22/0.49  fof(f423,plain,(
% 0.22/0.49    ( ! [X0] : (~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(X0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) ) | (~spl5_3 | ~spl5_50)),
% 0.22/0.49    inference(resolution,[],[f371,f92])).
% 0.22/0.49  fof(f371,plain,(
% 0.22/0.49    ( ! [X2,X0] : (~v3_tdlat_3(X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(X2,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl5_50),
% 0.22/0.49    inference(avatar_component_clause,[],[f370])).
% 0.22/0.49  fof(f415,plain,(
% 0.22/0.49    ~spl5_4 | ~spl5_23 | ~spl5_30 | spl5_54),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f414])).
% 0.22/0.49  fof(f414,plain,(
% 0.22/0.49    $false | (~spl5_4 | ~spl5_23 | ~spl5_30 | spl5_54)),
% 0.22/0.49    inference(subsumption_resolution,[],[f413,f97])).
% 0.22/0.49  fof(f413,plain,(
% 0.22/0.49    ~l1_pre_topc(sK0) | (~spl5_23 | ~spl5_30 | spl5_54)),
% 0.22/0.49    inference(subsumption_resolution,[],[f412,f190])).
% 0.22/0.49  fof(f412,plain,(
% 0.22/0.49    ~m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl5_30 | spl5_54)),
% 0.22/0.49    inference(resolution,[],[f406,f237])).
% 0.22/0.49  fof(f237,plain,(
% 0.22/0.49    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl5_30),
% 0.22/0.49    inference(avatar_component_clause,[],[f236])).
% 0.22/0.49  fof(f236,plain,(
% 0.22/0.49    spl5_30 <=> ! [X1,X0] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).
% 0.22/0.49  fof(f406,plain,(
% 0.22/0.49    ~m1_subset_1(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | spl5_54),
% 0.22/0.49    inference(avatar_component_clause,[],[f404])).
% 0.22/0.49  fof(f411,plain,(
% 0.22/0.49    ~spl5_54 | spl5_55 | ~spl5_46 | ~spl5_51),
% 0.22/0.49    inference(avatar_split_clause,[],[f382,f376,f337,f408,f404])).
% 0.22/0.50  fof(f337,plain,(
% 0.22/0.50    spl5_46 <=> k2_pre_topc(sK0,k2_tarski(sK1,sK1)) = k2_pre_topc(sK0,k2_pre_topc(sK0,k2_tarski(sK1,sK1)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_46])])).
% 0.22/0.50  fof(f376,plain,(
% 0.22/0.50    spl5_51 <=> ! [X0] : (k2_pre_topc(sK0,X0) != X0 | v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_51])])).
% 0.22/0.50  fof(f382,plain,(
% 0.22/0.50    v4_pre_topc(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),sK0) | ~m1_subset_1(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl5_46 | ~spl5_51)),
% 0.22/0.50    inference(trivial_inequality_removal,[],[f379])).
% 0.22/0.50  fof(f379,plain,(
% 0.22/0.50    k2_pre_topc(sK0,k2_tarski(sK1,sK1)) != k2_pre_topc(sK0,k2_tarski(sK1,sK1)) | v4_pre_topc(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),sK0) | ~m1_subset_1(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl5_46 | ~spl5_51)),
% 0.22/0.50    inference(superposition,[],[f377,f339])).
% 0.22/0.50  fof(f339,plain,(
% 0.22/0.50    k2_pre_topc(sK0,k2_tarski(sK1,sK1)) = k2_pre_topc(sK0,k2_pre_topc(sK0,k2_tarski(sK1,sK1))) | ~spl5_46),
% 0.22/0.50    inference(avatar_component_clause,[],[f337])).
% 0.22/0.50  fof(f377,plain,(
% 0.22/0.50    ( ! [X0] : (k2_pre_topc(sK0,X0) != X0 | v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl5_51),
% 0.22/0.50    inference(avatar_component_clause,[],[f376])).
% 0.22/0.50  fof(f395,plain,(
% 0.22/0.50    ~spl5_4 | ~spl5_27 | ~spl5_30 | spl5_52),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f394])).
% 0.22/0.50  fof(f394,plain,(
% 0.22/0.50    $false | (~spl5_4 | ~spl5_27 | ~spl5_30 | spl5_52)),
% 0.22/0.50    inference(subsumption_resolution,[],[f393,f97])).
% 0.22/0.50  fof(f393,plain,(
% 0.22/0.50    ~l1_pre_topc(sK0) | (~spl5_27 | ~spl5_30 | spl5_52)),
% 0.22/0.50    inference(subsumption_resolution,[],[f392,f222])).
% 0.22/0.50  fof(f392,plain,(
% 0.22/0.50    ~m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl5_30 | spl5_52)),
% 0.22/0.50    inference(resolution,[],[f386,f237])).
% 0.22/0.50  fof(f386,plain,(
% 0.22/0.50    ~m1_subset_1(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | spl5_52),
% 0.22/0.50    inference(avatar_component_clause,[],[f384])).
% 0.22/0.50  fof(f391,plain,(
% 0.22/0.50    ~spl5_52 | spl5_53 | ~spl5_47 | ~spl5_51),
% 0.22/0.50    inference(avatar_split_clause,[],[f381,f376,f342,f388,f384])).
% 0.22/0.50  fof(f342,plain,(
% 0.22/0.50    spl5_47 <=> k2_pre_topc(sK0,k2_tarski(sK2,sK2)) = k2_pre_topc(sK0,k2_pre_topc(sK0,k2_tarski(sK2,sK2)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_47])])).
% 0.22/0.50  fof(f381,plain,(
% 0.22/0.50    v4_pre_topc(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),sK0) | ~m1_subset_1(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl5_47 | ~spl5_51)),
% 0.22/0.50    inference(trivial_inequality_removal,[],[f380])).
% 0.22/0.50  fof(f380,plain,(
% 0.22/0.50    k2_pre_topc(sK0,k2_tarski(sK2,sK2)) != k2_pre_topc(sK0,k2_tarski(sK2,sK2)) | v4_pre_topc(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),sK0) | ~m1_subset_1(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl5_47 | ~spl5_51)),
% 0.22/0.50    inference(superposition,[],[f377,f344])).
% 0.22/0.50  fof(f344,plain,(
% 0.22/0.50    k2_pre_topc(sK0,k2_tarski(sK2,sK2)) = k2_pre_topc(sK0,k2_pre_topc(sK0,k2_tarski(sK2,sK2))) | ~spl5_47),
% 0.22/0.50    inference(avatar_component_clause,[],[f342])).
% 0.22/0.50  fof(f378,plain,(
% 0.22/0.50    spl5_51 | ~spl5_2 | ~spl5_4 | ~spl5_45),
% 0.22/0.50    inference(avatar_split_clause,[],[f374,f333,f95,f85,f376])).
% 0.22/0.50  fof(f333,plain,(
% 0.22/0.50    spl5_45 <=> ! [X1,X0] : (v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_45])])).
% 0.22/0.50  fof(f374,plain,(
% 0.22/0.50    ( ! [X0] : (k2_pre_topc(sK0,X0) != X0 | v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl5_2 | ~spl5_4 | ~spl5_45)),
% 0.22/0.50    inference(subsumption_resolution,[],[f373,f97])).
% 0.22/0.50  fof(f373,plain,(
% 0.22/0.50    ( ! [X0] : (k2_pre_topc(sK0,X0) != X0 | v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) ) | (~spl5_2 | ~spl5_45)),
% 0.22/0.50    inference(resolution,[],[f334,f87])).
% 0.22/0.50  fof(f334,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v2_pre_topc(X0) | k2_pre_topc(X0,X1) != X1 | v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl5_45),
% 0.22/0.50    inference(avatar_component_clause,[],[f333])).
% 0.22/0.50  fof(f372,plain,(
% 0.22/0.50    spl5_50),
% 0.22/0.50    inference(avatar_split_clause,[],[f64,f370])).
% 0.22/0.50  fof(f64,plain,(
% 0.22/0.50    ( ! [X2,X0] : (v3_pre_topc(X2,X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tdlat_3(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f47])).
% 0.22/0.50  fof(f47,plain,(
% 0.22/0.50    ! [X0] : (((v3_tdlat_3(X0) | (~v3_pre_topc(sK3(X0),X0) & v4_pre_topc(sK3(X0),X0) & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f45,f46])).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    ! [X0] : (? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK3(X0),X0) & v4_pre_topc(sK3(X0),X0) & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    ! [X0] : (((v3_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.50    inference(rectify,[],[f44])).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    ! [X0] : (((v3_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X1] : (v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.50    inference(nnf_transformation,[],[f27])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.50    inference(flattening,[],[f26])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : ((v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f11])).
% 0.22/0.50  fof(f11,axiom,(
% 0.22/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v3_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => v3_pre_topc(X1,X0)))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tdlat_3)).
% 0.22/0.50  fof(f345,plain,(
% 0.22/0.50    spl5_47 | ~spl5_27 | ~spl5_44),
% 0.22/0.50    inference(avatar_split_clause,[],[f326,f322,f220,f342])).
% 0.22/0.50  fof(f322,plain,(
% 0.22/0.50    spl5_44 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,k2_pre_topc(sK0,X0)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).
% 0.22/0.50  fof(f326,plain,(
% 0.22/0.50    k2_pre_topc(sK0,k2_tarski(sK2,sK2)) = k2_pre_topc(sK0,k2_pre_topc(sK0,k2_tarski(sK2,sK2))) | (~spl5_27 | ~spl5_44)),
% 0.22/0.50    inference(resolution,[],[f323,f222])).
% 0.22/0.50  fof(f323,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,k2_pre_topc(sK0,X0))) ) | ~spl5_44),
% 0.22/0.50    inference(avatar_component_clause,[],[f322])).
% 0.22/0.50  fof(f340,plain,(
% 0.22/0.50    spl5_46 | ~spl5_23 | ~spl5_44),
% 0.22/0.50    inference(avatar_split_clause,[],[f325,f322,f188,f337])).
% 0.22/0.50  fof(f325,plain,(
% 0.22/0.50    k2_pre_topc(sK0,k2_tarski(sK1,sK1)) = k2_pre_topc(sK0,k2_pre_topc(sK0,k2_tarski(sK1,sK1))) | (~spl5_23 | ~spl5_44)),
% 0.22/0.50    inference(resolution,[],[f323,f190])).
% 0.22/0.50  fof(f335,plain,(
% 0.22/0.50    spl5_45),
% 0.22/0.50    inference(avatar_split_clause,[],[f61,f333])).
% 0.22/0.50  fof(f61,plain,(
% 0.22/0.50    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(flattening,[],[f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f8])).
% 0.22/0.50  fof(f8,axiom,(
% 0.22/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).
% 0.22/0.50  fof(f324,plain,(
% 0.22/0.50    spl5_44 | ~spl5_4 | ~spl5_33),
% 0.22/0.50    inference(avatar_split_clause,[],[f320,f251,f95,f322])).
% 0.22/0.50  fof(f251,plain,(
% 0.22/0.50    spl5_33 <=> ! [X1,X0] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).
% 0.22/0.50  fof(f320,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,k2_pre_topc(sK0,X0))) ) | (~spl5_4 | ~spl5_33)),
% 0.22/0.50    inference(resolution,[],[f252,f97])).
% 0.22/0.50  fof(f252,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))) ) | ~spl5_33),
% 0.22/0.50    inference(avatar_component_clause,[],[f251])).
% 0.22/0.50  fof(f288,plain,(
% 0.22/0.50    spl5_38 | ~spl5_9 | ~spl5_35),
% 0.22/0.50    inference(avatar_split_clause,[],[f284,f259,f118,f286])).
% 0.22/0.50  fof(f118,plain,(
% 0.22/0.50    spl5_9 <=> ! [X1,X0] : (r2_hidden(sK4(X0,X1),X0) | r1_xboole_0(X0,X1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.22/0.50  fof(f259,plain,(
% 0.22/0.50    spl5_35 <=> ! [X3,X5,X4] : (~r2_hidden(sK4(X3,k2_tarski(X4,X4)),X5) | r2_hidden(X4,X5) | r1_xboole_0(X3,k2_tarski(X4,X4)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).
% 0.22/0.50  fof(f284,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r2_hidden(X0,X1) | r1_xboole_0(X1,k2_tarski(X0,X0))) ) | (~spl5_9 | ~spl5_35)),
% 0.22/0.50    inference(duplicate_literal_removal,[],[f280])).
% 0.22/0.50  fof(f280,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r2_hidden(X0,X1) | r1_xboole_0(X1,k2_tarski(X0,X0)) | r1_xboole_0(X1,k2_tarski(X0,X0))) ) | (~spl5_9 | ~spl5_35)),
% 0.22/0.50    inference(resolution,[],[f260,f119])).
% 0.22/0.50  fof(f119,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_xboole_0(X0,X1)) ) | ~spl5_9),
% 0.22/0.50    inference(avatar_component_clause,[],[f118])).
% 0.22/0.50  fof(f260,plain,(
% 0.22/0.50    ( ! [X4,X5,X3] : (~r2_hidden(sK4(X3,k2_tarski(X4,X4)),X5) | r2_hidden(X4,X5) | r1_xboole_0(X3,k2_tarski(X4,X4))) ) | ~spl5_35),
% 0.22/0.50    inference(avatar_component_clause,[],[f259])).
% 0.22/0.50  fof(f261,plain,(
% 0.22/0.50    spl5_35 | ~spl5_10 | ~spl5_18),
% 0.22/0.50    inference(avatar_split_clause,[],[f161,f157,f122,f259])).
% 0.22/0.50  fof(f157,plain,(
% 0.22/0.50    spl5_18 <=> ! [X1,X0,X2] : (~r2_hidden(X0,X1) | ~r2_hidden(X0,k2_tarski(X2,X2)) | r2_hidden(X2,X1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.22/0.50  % (4286)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.50  fof(f161,plain,(
% 0.22/0.50    ( ! [X4,X5,X3] : (~r2_hidden(sK4(X3,k2_tarski(X4,X4)),X5) | r2_hidden(X4,X5) | r1_xboole_0(X3,k2_tarski(X4,X4))) ) | (~spl5_10 | ~spl5_18)),
% 0.22/0.50    inference(resolution,[],[f158,f123])).
% 0.22/0.50  fof(f158,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_tarski(X2,X2)) | ~r2_hidden(X0,X1) | r2_hidden(X2,X1)) ) | ~spl5_18),
% 0.22/0.50    inference(avatar_component_clause,[],[f157])).
% 0.22/0.50  fof(f253,plain,(
% 0.22/0.50    spl5_33),
% 0.22/0.50    inference(avatar_split_clause,[],[f76,f251])).
% 0.22/0.50  fof(f76,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f39])).
% 0.22/0.50  fof(f39,plain,(
% 0.22/0.50    ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(flattening,[],[f38])).
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,axiom,(
% 0.22/0.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',projectivity_k2_pre_topc)).
% 0.22/0.50  fof(f238,plain,(
% 0.22/0.50    spl5_30),
% 0.22/0.50    inference(avatar_split_clause,[],[f75,f236])).
% 0.22/0.50  fof(f75,plain,(
% 0.22/0.50    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f37])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(flattening,[],[f36])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 0.22/0.50  fof(f234,plain,(
% 0.22/0.50    ~spl5_29 | ~spl5_6 | spl5_15 | ~spl5_20 | spl5_21 | ~spl5_22),
% 0.22/0.50    inference(avatar_split_clause,[],[f209,f179,f175,f167,f143,f105,f231])).
% 0.22/0.50  fof(f143,plain,(
% 0.22/0.50    spl5_15 <=> r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.22/0.50  fof(f167,plain,(
% 0.22/0.50    spl5_20 <=> ! [X1,X0] : (k6_domain_1(X0,X1) = k2_tarski(X1,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 0.22/0.50  fof(f175,plain,(
% 0.22/0.50    spl5_21 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 0.22/0.50  % (4288)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.50  fof(f209,plain,(
% 0.22/0.50    ~r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k2_tarski(sK2,sK2))) | (~spl5_6 | spl5_15 | ~spl5_20 | spl5_21 | ~spl5_22)),
% 0.22/0.50    inference(backward_demodulation,[],[f184,f207])).
% 0.22/0.50  fof(f207,plain,(
% 0.22/0.50    k6_domain_1(u1_struct_0(sK0),sK2) = k2_tarski(sK2,sK2) | (~spl5_6 | ~spl5_20 | spl5_21)),
% 0.22/0.50    inference(subsumption_resolution,[],[f171,f176])).
% 0.22/0.50  fof(f176,plain,(
% 0.22/0.50    ~v1_xboole_0(u1_struct_0(sK0)) | spl5_21),
% 0.22/0.50    inference(avatar_component_clause,[],[f175])).
% 0.22/0.50  fof(f171,plain,(
% 0.22/0.50    k6_domain_1(u1_struct_0(sK0),sK2) = k2_tarski(sK2,sK2) | v1_xboole_0(u1_struct_0(sK0)) | (~spl5_6 | ~spl5_20)),
% 0.22/0.50    inference(resolution,[],[f168,f107])).
% 0.22/0.50  fof(f168,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k2_tarski(X1,X1) | v1_xboole_0(X0)) ) | ~spl5_20),
% 0.22/0.50    inference(avatar_component_clause,[],[f167])).
% 0.22/0.50  fof(f184,plain,(
% 0.22/0.50    ~r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) | (spl5_15 | ~spl5_22)),
% 0.22/0.50    inference(backward_demodulation,[],[f145,f181])).
% 0.22/0.50  fof(f145,plain,(
% 0.22/0.50    ~r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) | spl5_15),
% 0.22/0.50    inference(avatar_component_clause,[],[f143])).
% 0.22/0.50  fof(f229,plain,(
% 0.22/0.50    ~spl5_28 | ~spl5_6 | ~spl5_20 | spl5_21 | spl5_24),
% 0.22/0.50    inference(avatar_split_clause,[],[f208,f193,f175,f167,f105,f226])).
% 0.22/0.50  fof(f193,plain,(
% 0.22/0.50    spl5_24 <=> k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) = k2_pre_topc(sK0,k2_tarski(sK1,sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 0.22/0.50  fof(f208,plain,(
% 0.22/0.50    k2_pre_topc(sK0,k2_tarski(sK1,sK1)) != k2_pre_topc(sK0,k2_tarski(sK2,sK2)) | (~spl5_6 | ~spl5_20 | spl5_21 | spl5_24)),
% 0.22/0.50    inference(backward_demodulation,[],[f195,f207])).
% 0.22/0.50  fof(f195,plain,(
% 0.22/0.50    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) != k2_pre_topc(sK0,k2_tarski(sK1,sK1)) | spl5_24),
% 0.22/0.50    inference(avatar_component_clause,[],[f193])).
% 0.22/0.50  fof(f223,plain,(
% 0.22/0.50    spl5_27 | ~spl5_6 | ~spl5_17 | spl5_21 | ~spl5_26),
% 0.22/0.50    inference(avatar_split_clause,[],[f218,f212,f175,f153,f105,f220])).
% 0.22/0.50  fof(f153,plain,(
% 0.22/0.50    spl5_17 <=> ! [X1,X0] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.22/0.50  fof(f218,plain,(
% 0.22/0.50    m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl5_6 | ~spl5_17 | spl5_21 | ~spl5_26)),
% 0.22/0.50    inference(subsumption_resolution,[],[f217,f176])).
% 0.22/0.50  fof(f217,plain,(
% 0.22/0.50    m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(u1_struct_0(sK0)) | (~spl5_6 | ~spl5_17 | ~spl5_26)),
% 0.22/0.50    inference(subsumption_resolution,[],[f216,f107])).
% 0.22/0.50  fof(f216,plain,(
% 0.22/0.50    m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | (~spl5_17 | ~spl5_26)),
% 0.22/0.50    inference(superposition,[],[f154,f214])).
% 0.22/0.50  fof(f154,plain,(
% 0.22/0.50    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) ) | ~spl5_17),
% 0.22/0.50    inference(avatar_component_clause,[],[f153])).
% 0.22/0.50  fof(f215,plain,(
% 0.22/0.50    spl5_26 | ~spl5_6 | ~spl5_20 | spl5_21),
% 0.22/0.50    inference(avatar_split_clause,[],[f207,f175,f167,f105,f212])).
% 0.22/0.50  fof(f206,plain,(
% 0.22/0.50    ~spl5_4 | ~spl5_7 | spl5_25),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f205])).
% 0.22/0.50  fof(f205,plain,(
% 0.22/0.50    $false | (~spl5_4 | ~spl5_7 | spl5_25)),
% 0.22/0.50    inference(subsumption_resolution,[],[f204,f97])).
% 0.22/0.50  fof(f204,plain,(
% 0.22/0.50    ~l1_pre_topc(sK0) | (~spl5_7 | spl5_25)),
% 0.22/0.50    inference(resolution,[],[f202,f111])).
% 0.22/0.50  fof(f111,plain,(
% 0.22/0.50    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) ) | ~spl5_7),
% 0.22/0.50    inference(avatar_component_clause,[],[f110])).
% 0.22/0.50  fof(f110,plain,(
% 0.22/0.50    spl5_7 <=> ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.22/0.50  fof(f202,plain,(
% 0.22/0.50    ~l1_struct_0(sK0) | spl5_25),
% 0.22/0.50    inference(avatar_component_clause,[],[f200])).
% 0.22/0.50  fof(f200,plain,(
% 0.22/0.50    spl5_25 <=> l1_struct_0(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 0.22/0.50  fof(f203,plain,(
% 0.22/0.50    ~spl5_25 | spl5_1 | ~spl5_8 | ~spl5_21),
% 0.22/0.50    inference(avatar_split_clause,[],[f198,f175,f114,f80,f200])).
% 0.22/0.50  fof(f114,plain,(
% 0.22/0.50    spl5_8 <=> ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.22/0.50  fof(f198,plain,(
% 0.22/0.50    ~l1_struct_0(sK0) | (spl5_1 | ~spl5_8 | ~spl5_21)),
% 0.22/0.50    inference(subsumption_resolution,[],[f197,f82])).
% 0.22/0.50  fof(f197,plain,(
% 0.22/0.50    ~l1_struct_0(sK0) | v2_struct_0(sK0) | (~spl5_8 | ~spl5_21)),
% 0.22/0.50    inference(resolution,[],[f177,f115])).
% 0.22/0.50  fof(f115,plain,(
% 0.22/0.50    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) ) | ~spl5_8),
% 0.22/0.50    inference(avatar_component_clause,[],[f114])).
% 0.22/0.50  fof(f177,plain,(
% 0.22/0.50    v1_xboole_0(u1_struct_0(sK0)) | ~spl5_21),
% 0.22/0.50    inference(avatar_component_clause,[],[f175])).
% 0.22/0.50  fof(f196,plain,(
% 0.22/0.50    ~spl5_24 | spl5_16 | ~spl5_22),
% 0.22/0.50    inference(avatar_split_clause,[],[f183,f179,f148,f193])).
% 0.22/0.50  fof(f148,plain,(
% 0.22/0.50    spl5_16 <=> k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.22/0.50  fof(f183,plain,(
% 0.22/0.50    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) != k2_pre_topc(sK0,k2_tarski(sK1,sK1)) | (spl5_16 | ~spl5_22)),
% 0.22/0.50    inference(backward_demodulation,[],[f150,f181])).
% 0.22/0.50  fof(f150,plain,(
% 0.22/0.50    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) | spl5_16),
% 0.22/0.50    inference(avatar_component_clause,[],[f148])).
% 0.22/0.50  fof(f191,plain,(
% 0.22/0.50    spl5_21 | spl5_23 | ~spl5_5 | ~spl5_17 | ~spl5_22),
% 0.22/0.50    inference(avatar_split_clause,[],[f186,f179,f153,f100,f188,f175])).
% 0.22/0.50  fof(f186,plain,(
% 0.22/0.50    m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(u1_struct_0(sK0)) | (~spl5_5 | ~spl5_17 | ~spl5_22)),
% 0.22/0.50    inference(subsumption_resolution,[],[f185,f102])).
% 0.22/0.50  fof(f185,plain,(
% 0.22/0.50    m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | (~spl5_17 | ~spl5_22)),
% 0.22/0.50    inference(superposition,[],[f154,f181])).
% 0.22/0.50  fof(f182,plain,(
% 0.22/0.50    spl5_21 | spl5_22 | ~spl5_5 | ~spl5_20),
% 0.22/0.50    inference(avatar_split_clause,[],[f170,f167,f100,f179,f175])).
% 0.22/0.50  fof(f170,plain,(
% 0.22/0.50    k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1) | v1_xboole_0(u1_struct_0(sK0)) | (~spl5_5 | ~spl5_20)),
% 0.22/0.50    inference(resolution,[],[f168,f102])).
% 0.22/0.50  fof(f169,plain,(
% 0.22/0.50    spl5_20),
% 0.22/0.50    inference(avatar_split_clause,[],[f78,f167])).
% 0.22/0.50  fof(f78,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k2_tarski(X1,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.22/0.50    inference(definition_unfolding,[],[f73,f58])).
% 0.22/0.50  fof(f58,plain,(
% 0.22/0.50    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.50  fof(f73,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f33])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.22/0.50    inference(flattening,[],[f32])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f10])).
% 0.22/0.50  fof(f10,axiom,(
% 0.22/0.50    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.22/0.50  fof(f159,plain,(
% 0.22/0.50    spl5_18 | ~spl5_11 | ~spl5_12),
% 0.22/0.50    inference(avatar_split_clause,[],[f133,f130,f126,f157])).
% 0.22/0.50  fof(f126,plain,(
% 0.22/0.50    spl5_11 <=> ! [X1,X0] : (r1_xboole_0(k2_tarski(X0,X0),X1) | r2_hidden(X0,X1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.22/0.50  fof(f133,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~r2_hidden(X0,k2_tarski(X2,X2)) | r2_hidden(X2,X1)) ) | (~spl5_11 | ~spl5_12)),
% 0.22/0.50    inference(resolution,[],[f131,f127])).
% 0.22/0.50  fof(f127,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_xboole_0(k2_tarski(X0,X0),X1) | r2_hidden(X0,X1)) ) | ~spl5_11),
% 0.22/0.50    inference(avatar_component_clause,[],[f126])).
% 0.22/0.50  fof(f155,plain,(
% 0.22/0.50    spl5_17),
% 0.22/0.50    inference(avatar_split_clause,[],[f74,f153])).
% 0.22/0.50  fof(f74,plain,(
% 0.22/0.50    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f35])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.22/0.50    inference(flattening,[],[f34])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f9])).
% 0.22/0.50  fof(f9,axiom,(
% 0.22/0.50    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 0.22/0.50  fof(f151,plain,(
% 0.22/0.50    ~spl5_16),
% 0.22/0.50    inference(avatar_split_clause,[],[f57,f148])).
% 0.22/0.50  fof(f57,plain,(
% 0.22/0.50    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))),
% 0.22/0.50    inference(cnf_transformation,[],[f43])).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    ((k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) & ~r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) & m1_subset_1(sK2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v3_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f42,f41,f40])).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) & ~r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v3_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f41,plain,(
% 0.22/0.50    ? [X1] : (? [X2] : (k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) & ~r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : (k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) & ~r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f42,plain,(
% 0.22/0.50    ? [X2] : (k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) & ~r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) & m1_subset_1(X2,u1_struct_0(sK0))) => (k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) & ~r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) & m1_subset_1(sK2,u1_struct_0(sK0)))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f17])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : ((k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f15])).
% 0.22/0.50  fof(f15,negated_conjecture,(
% 0.22/0.50    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) | r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))))))),
% 0.22/0.50    inference(negated_conjecture,[],[f14])).
% 0.22/0.50  fof(f14,conjecture,(
% 0.22/0.50    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) | r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tex_2)).
% 0.22/0.50  fof(f146,plain,(
% 0.22/0.50    ~spl5_15),
% 0.22/0.50    inference(avatar_split_clause,[],[f56,f143])).
% 0.22/0.50  fof(f56,plain,(
% 0.22/0.50    ~r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))),
% 0.22/0.50    inference(cnf_transformation,[],[f43])).
% 0.22/0.50  fof(f132,plain,(
% 0.22/0.50    spl5_12),
% 0.22/0.50    inference(avatar_split_clause,[],[f71,f130])).
% 0.22/0.50  fof(f71,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f49])).
% 0.22/0.50  fof(f49,plain,(
% 0.22/0.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f30,f48])).
% 0.22/0.50  fof(f48,plain,(
% 0.22/0.50    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.22/0.50    inference(ennf_transformation,[],[f16])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.50    inference(rectify,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.22/0.50  fof(f128,plain,(
% 0.22/0.50    spl5_11),
% 0.22/0.50    inference(avatar_split_clause,[],[f77,f126])).
% 0.22/0.50  fof(f77,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_xboole_0(k2_tarski(X0,X0),X1) | r2_hidden(X0,X1)) )),
% 0.22/0.50    inference(definition_unfolding,[],[f72,f58])).
% 0.22/0.50  fof(f72,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f31])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 0.22/0.50  fof(f124,plain,(
% 0.22/0.50    spl5_10),
% 0.22/0.50    inference(avatar_split_clause,[],[f70,f122])).
% 0.22/0.50  fof(f70,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f49])).
% 0.22/0.50  fof(f120,plain,(
% 0.22/0.50    spl5_9),
% 0.22/0.50    inference(avatar_split_clause,[],[f69,f118])).
% 0.22/0.50  fof(f69,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f49])).
% 0.22/0.50  fof(f116,plain,(
% 0.22/0.50    spl5_8),
% 0.22/0.50    inference(avatar_split_clause,[],[f62,f114])).
% 0.22/0.50  fof(f62,plain,(
% 0.22/0.50    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f23])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f22])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.22/0.50  fof(f112,plain,(
% 0.22/0.50    spl5_7),
% 0.22/0.50    inference(avatar_split_clause,[],[f59,f110])).
% 0.22/0.50  fof(f59,plain,(
% 0.22/0.50    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.50  fof(f108,plain,(
% 0.22/0.50    spl5_6),
% 0.22/0.50    inference(avatar_split_clause,[],[f55,f105])).
% 0.22/0.50  fof(f55,plain,(
% 0.22/0.50    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.22/0.50    inference(cnf_transformation,[],[f43])).
% 0.22/0.50  fof(f103,plain,(
% 0.22/0.50    spl5_5),
% 0.22/0.50    inference(avatar_split_clause,[],[f54,f100])).
% 0.22/0.50  fof(f54,plain,(
% 0.22/0.50    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.50    inference(cnf_transformation,[],[f43])).
% 0.22/0.50  fof(f98,plain,(
% 0.22/0.50    spl5_4),
% 0.22/0.50    inference(avatar_split_clause,[],[f53,f95])).
% 0.22/0.50  fof(f53,plain,(
% 0.22/0.50    l1_pre_topc(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f43])).
% 0.22/0.50  fof(f93,plain,(
% 0.22/0.50    spl5_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f52,f90])).
% 0.22/0.50  fof(f52,plain,(
% 0.22/0.50    v3_tdlat_3(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f43])).
% 0.22/0.50  fof(f88,plain,(
% 0.22/0.50    spl5_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f51,f85])).
% 0.22/0.50  fof(f51,plain,(
% 0.22/0.50    v2_pre_topc(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f43])).
% 0.22/0.50  fof(f83,plain,(
% 0.22/0.50    ~spl5_1),
% 0.22/0.50    inference(avatar_split_clause,[],[f50,f80])).
% 0.22/0.50  fof(f50,plain,(
% 0.22/0.50    ~v2_struct_0(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f43])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (4293)------------------------------
% 0.22/0.50  % (4293)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (4293)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (4293)Memory used [KB]: 6524
% 0.22/0.50  % (4293)Time elapsed: 0.035 s
% 0.22/0.50  % (4293)------------------------------
% 0.22/0.50  % (4293)------------------------------
% 0.22/0.50  % (4285)Success in time 0.144 s
%------------------------------------------------------------------------------
