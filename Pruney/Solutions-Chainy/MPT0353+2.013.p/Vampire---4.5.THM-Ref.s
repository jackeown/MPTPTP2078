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
% DateTime   : Thu Dec  3 12:44:22 EST 2020

% Result     : Theorem 2.56s
% Output     : Refutation 2.56s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 172 expanded)
%              Number of leaves         :   24 (  71 expanded)
%              Depth                    :    9
%              Number of atoms          :  222 ( 375 expanded)
%              Number of equality atoms :   71 ( 124 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3743,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f49,f54,f59,f87,f146,f1345,f1366,f1372,f1494,f1573,f1731,f1773,f2329,f3732])).

fof(f3732,plain,
    ( ~ spl4_24
    | spl4_76 ),
    inference(avatar_contradiction_clause,[],[f3731])).

fof(f3731,plain,
    ( $false
    | ~ spl4_24
    | spl4_76 ),
    inference(trivial_inequality_removal,[],[f3687])).

fof(f3687,plain,
    ( k6_subset_1(sK1,sK2) != k6_subset_1(sK1,sK2)
    | ~ spl4_24
    | spl4_76 ),
    inference(superposition,[],[f2328,f2269])).

fof(f2269,plain,
    ( ! [X1] : k3_xboole_0(sK1,k5_xboole_0(sK0,X1)) = k6_subset_1(sK1,X1)
    | ~ spl4_24 ),
    inference(superposition,[],[f1413,f26])).

fof(f26,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f1413,plain,
    ( ! [X0] : k6_subset_1(sK1,X0) = k3_xboole_0(k5_xboole_0(sK0,X0),sK1)
    | ~ spl4_24 ),
    inference(forward_demodulation,[],[f1374,f67])).

fof(f67,plain,(
    ! [X2,X1] : k6_subset_1(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X2,X1)) ),
    inference(superposition,[],[f39,f26])).

fof(f39,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k6_subset_1(X0,X1) ),
    inference(definition_unfolding,[],[f27,f25])).

fof(f25,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f27,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f1374,plain,
    ( ! [X0] : k3_xboole_0(k5_xboole_0(sK0,X0),sK1) = k5_xboole_0(sK1,k3_xboole_0(X0,sK1))
    | ~ spl4_24 ),
    inference(superposition,[],[f30,f1344])).

fof(f1344,plain,
    ( sK1 = k3_xboole_0(sK0,sK1)
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f1342])).

fof(f1342,plain,
    ( spl4_24
  <=> sK1 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f30,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).

fof(f2328,plain,
    ( k6_subset_1(sK1,sK2) != k3_xboole_0(sK1,k5_xboole_0(sK0,sK2))
    | spl4_76 ),
    inference(avatar_component_clause,[],[f2326])).

fof(f2326,plain,
    ( spl4_76
  <=> k6_subset_1(sK1,sK2) = k3_xboole_0(sK1,k5_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_76])])).

fof(f2329,plain,
    ( ~ spl4_76
    | ~ spl4_5
    | ~ spl4_51
    | spl4_57 ),
    inference(avatar_split_clause,[],[f2324,f1770,f1728,f84,f2326])).

fof(f84,plain,
    ( spl4_5
  <=> k3_subset_1(sK0,sK2) = k6_subset_1(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f1728,plain,
    ( spl4_51
  <=> k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_51])])).

fof(f1770,plain,
    ( spl4_57
  <=> k6_subset_1(sK1,sK2) = k9_subset_1(sK0,sK1,k5_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_57])])).

fof(f2324,plain,
    ( k6_subset_1(sK1,sK2) != k3_xboole_0(sK1,k5_xboole_0(sK0,sK2))
    | ~ spl4_5
    | ~ spl4_51
    | spl4_57 ),
    inference(superposition,[],[f1772,f2252])).

fof(f2252,plain,
    ( ! [X6] : k3_xboole_0(X6,k5_xboole_0(sK0,sK2)) = k9_subset_1(sK0,X6,k5_xboole_0(sK0,sK2))
    | ~ spl4_5
    | ~ spl4_51 ),
    inference(forward_demodulation,[],[f399,f1730])).

fof(f1730,plain,
    ( k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,sK2)
    | ~ spl4_51 ),
    inference(avatar_component_clause,[],[f1728])).

fof(f399,plain,
    ( ! [X6] : k3_xboole_0(X6,k3_subset_1(sK0,sK2)) = k9_subset_1(sK0,X6,k3_subset_1(sK0,sK2))
    | ~ spl4_5 ),
    inference(superposition,[],[f110,f86])).

fof(f86,plain,
    ( k3_subset_1(sK0,sK2) = k6_subset_1(sK0,sK2)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f84])).

fof(f110,plain,(
    ! [X4,X5,X3] : k9_subset_1(X3,X4,k6_subset_1(X3,X5)) = k3_xboole_0(X4,k6_subset_1(X3,X5)) ),
    inference(resolution,[],[f32,f24])).

fof(f24,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f1772,plain,
    ( k6_subset_1(sK1,sK2) != k9_subset_1(sK0,sK1,k5_xboole_0(sK0,sK2))
    | spl4_57 ),
    inference(avatar_component_clause,[],[f1770])).

fof(f1773,plain,
    ( ~ spl4_57
    | spl4_10
    | ~ spl4_51 ),
    inference(avatar_split_clause,[],[f1762,f1728,f143,f1770])).

fof(f143,plain,
    ( spl4_10
  <=> k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) = k6_subset_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f1762,plain,
    ( k6_subset_1(sK1,sK2) != k9_subset_1(sK0,sK1,k5_xboole_0(sK0,sK2))
    | spl4_10
    | ~ spl4_51 ),
    inference(backward_demodulation,[],[f145,f1730])).

fof(f145,plain,
    ( k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) != k6_subset_1(sK1,sK2)
    | spl4_10 ),
    inference(avatar_component_clause,[],[f143])).

fof(f1731,plain,
    ( spl4_51
    | ~ spl4_5
    | ~ spl4_37 ),
    inference(avatar_split_clause,[],[f1715,f1570,f84,f1728])).

fof(f1570,plain,
    ( spl4_37
  <=> k6_subset_1(sK0,sK2) = k5_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f1715,plain,
    ( k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,sK2)
    | ~ spl4_5
    | ~ spl4_37 ),
    inference(backward_demodulation,[],[f86,f1572])).

fof(f1572,plain,
    ( k6_subset_1(sK0,sK2) = k5_xboole_0(sK0,sK2)
    | ~ spl4_37 ),
    inference(avatar_component_clause,[],[f1570])).

fof(f1573,plain,
    ( spl4_37
    | ~ spl4_26 ),
    inference(avatar_split_clause,[],[f1528,f1363,f1570])).

fof(f1363,plain,
    ( spl4_26
  <=> sK2 = k3_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f1528,plain,
    ( k6_subset_1(sK0,sK2) = k5_xboole_0(sK0,sK2)
    | ~ spl4_26 ),
    inference(superposition,[],[f39,f1365])).

fof(f1365,plain,
    ( sK2 = k3_xboole_0(sK0,sK2)
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f1363])).

fof(f1494,plain,
    ( spl4_26
    | spl4_25 ),
    inference(avatar_split_clause,[],[f1490,f1359,f1363])).

fof(f1359,plain,
    ( spl4_25
  <=> r2_hidden(sK3(sK0,sK2,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f1490,plain,
    ( sK2 = k3_xboole_0(sK0,sK2)
    | spl4_25 ),
    inference(resolution,[],[f1361,f179])).

fof(f179,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1,X1),X1)
      | k3_xboole_0(X0,X1) = X1 ) ),
    inference(factoring,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f1361,plain,
    ( ~ r2_hidden(sK3(sK0,sK2,sK2),sK2)
    | spl4_25 ),
    inference(avatar_component_clause,[],[f1359])).

fof(f1372,plain,
    ( spl4_24
    | spl4_23 ),
    inference(avatar_split_clause,[],[f1368,f1338,f1342])).

fof(f1338,plain,
    ( spl4_23
  <=> r2_hidden(sK3(sK0,sK1,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f1368,plain,
    ( sK1 = k3_xboole_0(sK0,sK1)
    | spl4_23 ),
    inference(resolution,[],[f1340,f179])).

fof(f1340,plain,
    ( ~ r2_hidden(sK3(sK0,sK1,sK1),sK1)
    | spl4_23 ),
    inference(avatar_component_clause,[],[f1338])).

fof(f1366,plain,
    ( ~ spl4_25
    | spl4_26
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f1357,f56,f1363,f1359])).

fof(f56,plain,
    ( spl4_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f1357,plain,
    ( sK2 = k3_xboole_0(sK0,sK2)
    | ~ r2_hidden(sK3(sK0,sK2,sK2),sK2)
    | ~ spl4_3 ),
    inference(duplicate_literal_removal,[],[f1347])).

fof(f1347,plain,
    ( sK2 = k3_xboole_0(sK0,sK2)
    | ~ r2_hidden(sK3(sK0,sK2,sK2),sK2)
    | ~ r2_hidden(sK3(sK0,sK2,sK2),sK2)
    | sK2 = k3_xboole_0(sK0,sK2)
    | ~ spl4_3 ),
    inference(resolution,[],[f388,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f388,plain,
    ( ! [X25] :
        ( r2_hidden(sK3(X25,sK2,sK2),sK0)
        | sK2 = k3_xboole_0(X25,sK2) )
    | ~ spl4_3 ),
    inference(resolution,[],[f179,f71])).

fof(f71,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK2)
        | r2_hidden(X1,sK0) )
    | ~ spl4_3 ),
    inference(resolution,[],[f29,f58])).

fof(f58,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f56])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f1345,plain,
    ( ~ spl4_23
    | spl4_24
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f1336,f46,f1342,f1338])).

fof(f46,plain,
    ( spl4_1
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f1336,plain,
    ( sK1 = k3_xboole_0(sK0,sK1)
    | ~ r2_hidden(sK3(sK0,sK1,sK1),sK1)
    | ~ spl4_1 ),
    inference(duplicate_literal_removal,[],[f1326])).

fof(f1326,plain,
    ( sK1 = k3_xboole_0(sK0,sK1)
    | ~ r2_hidden(sK3(sK0,sK1,sK1),sK1)
    | ~ r2_hidden(sK3(sK0,sK1,sK1),sK1)
    | sK1 = k3_xboole_0(sK0,sK1)
    | ~ spl4_1 ),
    inference(resolution,[],[f387,f33])).

fof(f387,plain,
    ( ! [X24] :
        ( r2_hidden(sK3(X24,sK1,sK1),sK0)
        | sK1 = k3_xboole_0(X24,sK1) )
    | ~ spl4_1 ),
    inference(resolution,[],[f179,f70])).

fof(f70,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | r2_hidden(X0,sK0) )
    | ~ spl4_1 ),
    inference(resolution,[],[f29,f48])).

fof(f48,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f46])).

fof(f146,plain,
    ( ~ spl4_10
    | ~ spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f141,f51,f46,f143])).

fof(f51,plain,
    ( spl4_2
  <=> k7_subset_1(sK0,sK1,sK2) = k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f141,plain,
    ( k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) != k6_subset_1(sK1,sK2)
    | ~ spl4_1
    | spl4_2 ),
    inference(backward_demodulation,[],[f53,f120])).

fof(f120,plain,
    ( ! [X0] : k7_subset_1(sK0,sK1,X0) = k6_subset_1(sK1,X0)
    | ~ spl4_1 ),
    inference(resolution,[],[f41,f48])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k6_subset_1(X1,X2) ) ),
    inference(definition_unfolding,[],[f31,f25])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f53,plain,
    ( k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f51])).

fof(f87,plain,
    ( spl4_5
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f75,f56,f84])).

fof(f75,plain,
    ( k3_subset_1(sK0,sK2) = k6_subset_1(sK0,sK2)
    | ~ spl4_3 ),
    inference(resolution,[],[f40,f58])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k6_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f28,f25])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f59,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f20,f56])).

fof(f20,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k7_subset_1(X0,X1,X2) != k9_subset_1(X0,X1,k3_subset_1(X0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).

fof(f54,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f21,f51])).

fof(f21,plain,(
    k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f49,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f22,f46])).

fof(f22,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:55:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.51  % (19940)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.52  % (19944)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.52  % (19957)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.52  % (19937)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.52  % (19934)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  % (19958)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.52  % (19952)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.52  % (19934)Refutation not found, incomplete strategy% (19934)------------------------------
% 0.20/0.52  % (19934)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (19934)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (19934)Memory used [KB]: 1663
% 0.20/0.52  % (19934)Time elapsed: 0.116 s
% 0.20/0.52  % (19934)------------------------------
% 0.20/0.52  % (19934)------------------------------
% 0.20/0.53  % (19961)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.53  % (19959)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.53  % (19943)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.53  % (19941)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.53  % (19936)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (19935)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.53  % (19948)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.53  % (19960)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.53  % (19944)Refutation not found, incomplete strategy% (19944)------------------------------
% 0.20/0.53  % (19944)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (19943)Refutation not found, incomplete strategy% (19943)------------------------------
% 0.20/0.54  % (19943)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (19951)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.54  % (19939)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.54  % (19947)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.54  % (19938)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.54  % (19953)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.54  % (19944)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (19944)Memory used [KB]: 10618
% 0.20/0.54  % (19944)Time elapsed: 0.127 s
% 0.20/0.54  % (19944)------------------------------
% 0.20/0.54  % (19944)------------------------------
% 0.20/0.54  % (19949)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.54  % (19951)Refutation not found, incomplete strategy% (19951)------------------------------
% 0.20/0.54  % (19951)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (19951)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (19951)Memory used [KB]: 10618
% 0.20/0.54  % (19951)Time elapsed: 0.135 s
% 0.20/0.54  % (19951)------------------------------
% 0.20/0.54  % (19951)------------------------------
% 0.20/0.54  % (19962)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.54  % (19943)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (19943)Memory used [KB]: 10618
% 0.20/0.54  % (19943)Time elapsed: 0.127 s
% 0.20/0.54  % (19943)------------------------------
% 0.20/0.54  % (19943)------------------------------
% 1.41/0.55  % (19942)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.41/0.55  % (19963)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.41/0.55  % (19957)Refutation not found, incomplete strategy% (19957)------------------------------
% 1.41/0.55  % (19957)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (19957)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.55  
% 1.41/0.55  % (19957)Memory used [KB]: 10746
% 1.41/0.55  % (19957)Time elapsed: 0.140 s
% 1.41/0.55  % (19957)------------------------------
% 1.41/0.55  % (19957)------------------------------
% 1.41/0.55  % (19946)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.41/0.55  % (19945)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.41/0.55  % (19950)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.41/0.55  % (19945)Refutation not found, incomplete strategy% (19945)------------------------------
% 1.41/0.55  % (19945)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (19945)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.55  
% 1.41/0.55  % (19945)Memory used [KB]: 10618
% 1.41/0.55  % (19945)Time elapsed: 0.150 s
% 1.41/0.55  % (19945)------------------------------
% 1.41/0.55  % (19945)------------------------------
% 1.41/0.55  % (19954)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.41/0.55  % (19964)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.41/0.56  % (19954)Refutation not found, incomplete strategy% (19954)------------------------------
% 1.41/0.56  % (19954)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.56  % (19954)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.56  
% 1.41/0.56  % (19954)Memory used [KB]: 10746
% 1.41/0.56  % (19954)Time elapsed: 0.147 s
% 1.41/0.56  % (19954)------------------------------
% 1.41/0.56  % (19954)------------------------------
% 1.41/0.56  % (19956)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 2.00/0.64  % (20043)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.00/0.64  % (20043)Refutation not found, incomplete strategy% (20043)------------------------------
% 2.00/0.64  % (20043)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.00/0.64  % (20043)Termination reason: Refutation not found, incomplete strategy
% 2.00/0.64  
% 2.00/0.64  % (20043)Memory used [KB]: 6140
% 2.00/0.64  % (20043)Time elapsed: 0.054 s
% 2.00/0.64  % (20043)------------------------------
% 2.00/0.64  % (20043)------------------------------
% 2.19/0.67  % (20072)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 2.19/0.67  % (20064)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 2.19/0.67  % (20054)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.19/0.67  % (20056)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.19/0.68  % (20058)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.19/0.69  % (20062)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.56/0.75  % (19950)Refutation found. Thanks to Tanya!
% 2.56/0.75  % SZS status Theorem for theBenchmark
% 2.56/0.75  % SZS output start Proof for theBenchmark
% 2.56/0.75  fof(f3743,plain,(
% 2.56/0.75    $false),
% 2.56/0.75    inference(avatar_sat_refutation,[],[f49,f54,f59,f87,f146,f1345,f1366,f1372,f1494,f1573,f1731,f1773,f2329,f3732])).
% 2.56/0.75  fof(f3732,plain,(
% 2.56/0.75    ~spl4_24 | spl4_76),
% 2.56/0.75    inference(avatar_contradiction_clause,[],[f3731])).
% 2.56/0.75  fof(f3731,plain,(
% 2.56/0.75    $false | (~spl4_24 | spl4_76)),
% 2.56/0.75    inference(trivial_inequality_removal,[],[f3687])).
% 2.56/0.75  fof(f3687,plain,(
% 2.56/0.75    k6_subset_1(sK1,sK2) != k6_subset_1(sK1,sK2) | (~spl4_24 | spl4_76)),
% 2.56/0.75    inference(superposition,[],[f2328,f2269])).
% 2.56/0.75  fof(f2269,plain,(
% 2.56/0.75    ( ! [X1] : (k3_xboole_0(sK1,k5_xboole_0(sK0,X1)) = k6_subset_1(sK1,X1)) ) | ~spl4_24),
% 2.56/0.75    inference(superposition,[],[f1413,f26])).
% 2.56/0.75  fof(f26,plain,(
% 2.56/0.75    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.56/0.75    inference(cnf_transformation,[],[f1])).
% 2.56/0.75  fof(f1,axiom,(
% 2.56/0.75    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.56/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.56/0.75  fof(f1413,plain,(
% 2.56/0.75    ( ! [X0] : (k6_subset_1(sK1,X0) = k3_xboole_0(k5_xboole_0(sK0,X0),sK1)) ) | ~spl4_24),
% 2.56/0.75    inference(forward_demodulation,[],[f1374,f67])).
% 2.56/0.75  fof(f67,plain,(
% 2.56/0.75    ( ! [X2,X1] : (k6_subset_1(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X2,X1))) )),
% 2.56/0.75    inference(superposition,[],[f39,f26])).
% 2.56/0.75  fof(f39,plain,(
% 2.56/0.75    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k6_subset_1(X0,X1)) )),
% 2.56/0.75    inference(definition_unfolding,[],[f27,f25])).
% 2.56/0.75  fof(f25,plain,(
% 2.56/0.75    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 2.56/0.75    inference(cnf_transformation,[],[f9])).
% 2.56/0.75  fof(f9,axiom,(
% 2.56/0.75    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 2.56/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 2.56/0.75  fof(f27,plain,(
% 2.56/0.75    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.56/0.75    inference(cnf_transformation,[],[f4])).
% 2.56/0.75  fof(f4,axiom,(
% 2.56/0.75    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.56/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.56/0.75  fof(f1374,plain,(
% 2.56/0.75    ( ! [X0] : (k3_xboole_0(k5_xboole_0(sK0,X0),sK1) = k5_xboole_0(sK1,k3_xboole_0(X0,sK1))) ) | ~spl4_24),
% 2.56/0.75    inference(superposition,[],[f30,f1344])).
% 2.56/0.75  fof(f1344,plain,(
% 2.56/0.75    sK1 = k3_xboole_0(sK0,sK1) | ~spl4_24),
% 2.56/0.75    inference(avatar_component_clause,[],[f1342])).
% 2.56/0.75  fof(f1342,plain,(
% 2.56/0.75    spl4_24 <=> sK1 = k3_xboole_0(sK0,sK1)),
% 2.56/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 2.56/0.75  fof(f30,plain,(
% 2.56/0.75    ( ! [X2,X0,X1] : (k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)) )),
% 2.56/0.75    inference(cnf_transformation,[],[f5])).
% 2.56/0.75  fof(f5,axiom,(
% 2.56/0.75    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)),
% 2.56/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).
% 2.56/0.75  fof(f2328,plain,(
% 2.56/0.75    k6_subset_1(sK1,sK2) != k3_xboole_0(sK1,k5_xboole_0(sK0,sK2)) | spl4_76),
% 2.56/0.75    inference(avatar_component_clause,[],[f2326])).
% 2.56/0.75  fof(f2326,plain,(
% 2.56/0.75    spl4_76 <=> k6_subset_1(sK1,sK2) = k3_xboole_0(sK1,k5_xboole_0(sK0,sK2))),
% 2.56/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_76])])).
% 2.56/0.75  fof(f2329,plain,(
% 2.56/0.75    ~spl4_76 | ~spl4_5 | ~spl4_51 | spl4_57),
% 2.56/0.75    inference(avatar_split_clause,[],[f2324,f1770,f1728,f84,f2326])).
% 2.56/0.75  fof(f84,plain,(
% 2.56/0.75    spl4_5 <=> k3_subset_1(sK0,sK2) = k6_subset_1(sK0,sK2)),
% 2.56/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 2.56/0.75  fof(f1728,plain,(
% 2.56/0.75    spl4_51 <=> k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,sK2)),
% 2.56/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_51])])).
% 2.56/0.75  fof(f1770,plain,(
% 2.56/0.75    spl4_57 <=> k6_subset_1(sK1,sK2) = k9_subset_1(sK0,sK1,k5_xboole_0(sK0,sK2))),
% 2.56/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_57])])).
% 2.56/0.75  fof(f2324,plain,(
% 2.56/0.75    k6_subset_1(sK1,sK2) != k3_xboole_0(sK1,k5_xboole_0(sK0,sK2)) | (~spl4_5 | ~spl4_51 | spl4_57)),
% 2.56/0.75    inference(superposition,[],[f1772,f2252])).
% 2.56/0.75  fof(f2252,plain,(
% 2.56/0.75    ( ! [X6] : (k3_xboole_0(X6,k5_xboole_0(sK0,sK2)) = k9_subset_1(sK0,X6,k5_xboole_0(sK0,sK2))) ) | (~spl4_5 | ~spl4_51)),
% 2.56/0.75    inference(forward_demodulation,[],[f399,f1730])).
% 2.56/0.75  fof(f1730,plain,(
% 2.56/0.75    k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,sK2) | ~spl4_51),
% 2.56/0.75    inference(avatar_component_clause,[],[f1728])).
% 2.56/0.75  fof(f399,plain,(
% 2.56/0.75    ( ! [X6] : (k3_xboole_0(X6,k3_subset_1(sK0,sK2)) = k9_subset_1(sK0,X6,k3_subset_1(sK0,sK2))) ) | ~spl4_5),
% 2.56/0.75    inference(superposition,[],[f110,f86])).
% 2.56/0.75  fof(f86,plain,(
% 2.56/0.75    k3_subset_1(sK0,sK2) = k6_subset_1(sK0,sK2) | ~spl4_5),
% 2.56/0.75    inference(avatar_component_clause,[],[f84])).
% 2.56/0.75  fof(f110,plain,(
% 2.56/0.75    ( ! [X4,X5,X3] : (k9_subset_1(X3,X4,k6_subset_1(X3,X5)) = k3_xboole_0(X4,k6_subset_1(X3,X5))) )),
% 2.56/0.75    inference(resolution,[],[f32,f24])).
% 2.56/0.75  fof(f24,plain,(
% 2.56/0.75    ( ! [X0,X1] : (m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 2.56/0.75    inference(cnf_transformation,[],[f7])).
% 2.56/0.75  fof(f7,axiom,(
% 2.56/0.75    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))),
% 2.56/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).
% 2.56/0.75  fof(f32,plain,(
% 2.56/0.75    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 2.56/0.75    inference(cnf_transformation,[],[f19])).
% 2.56/0.75  fof(f19,plain,(
% 2.56/0.75    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 2.56/0.75    inference(ennf_transformation,[],[f11])).
% 2.56/0.75  fof(f11,axiom,(
% 2.56/0.75    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 2.56/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 2.56/0.75  fof(f1772,plain,(
% 2.56/0.75    k6_subset_1(sK1,sK2) != k9_subset_1(sK0,sK1,k5_xboole_0(sK0,sK2)) | spl4_57),
% 2.56/0.75    inference(avatar_component_clause,[],[f1770])).
% 2.56/0.75  fof(f1773,plain,(
% 2.56/0.75    ~spl4_57 | spl4_10 | ~spl4_51),
% 2.56/0.75    inference(avatar_split_clause,[],[f1762,f1728,f143,f1770])).
% 2.56/0.75  fof(f143,plain,(
% 2.56/0.75    spl4_10 <=> k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) = k6_subset_1(sK1,sK2)),
% 2.56/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 2.56/0.75  fof(f1762,plain,(
% 2.56/0.75    k6_subset_1(sK1,sK2) != k9_subset_1(sK0,sK1,k5_xboole_0(sK0,sK2)) | (spl4_10 | ~spl4_51)),
% 2.56/0.75    inference(backward_demodulation,[],[f145,f1730])).
% 2.56/0.75  fof(f145,plain,(
% 2.56/0.75    k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) != k6_subset_1(sK1,sK2) | spl4_10),
% 2.56/0.75    inference(avatar_component_clause,[],[f143])).
% 2.56/0.75  fof(f1731,plain,(
% 2.56/0.75    spl4_51 | ~spl4_5 | ~spl4_37),
% 2.56/0.75    inference(avatar_split_clause,[],[f1715,f1570,f84,f1728])).
% 2.56/0.75  fof(f1570,plain,(
% 2.56/0.75    spl4_37 <=> k6_subset_1(sK0,sK2) = k5_xboole_0(sK0,sK2)),
% 2.56/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).
% 2.56/0.75  fof(f1715,plain,(
% 2.56/0.75    k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,sK2) | (~spl4_5 | ~spl4_37)),
% 2.56/0.75    inference(backward_demodulation,[],[f86,f1572])).
% 2.56/0.75  fof(f1572,plain,(
% 2.56/0.75    k6_subset_1(sK0,sK2) = k5_xboole_0(sK0,sK2) | ~spl4_37),
% 2.56/0.75    inference(avatar_component_clause,[],[f1570])).
% 2.56/0.75  fof(f1573,plain,(
% 2.56/0.75    spl4_37 | ~spl4_26),
% 2.56/0.75    inference(avatar_split_clause,[],[f1528,f1363,f1570])).
% 2.56/0.75  fof(f1363,plain,(
% 2.56/0.75    spl4_26 <=> sK2 = k3_xboole_0(sK0,sK2)),
% 2.56/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 2.56/0.75  fof(f1528,plain,(
% 2.56/0.75    k6_subset_1(sK0,sK2) = k5_xboole_0(sK0,sK2) | ~spl4_26),
% 2.56/0.75    inference(superposition,[],[f39,f1365])).
% 2.56/0.75  fof(f1365,plain,(
% 2.56/0.75    sK2 = k3_xboole_0(sK0,sK2) | ~spl4_26),
% 2.56/0.75    inference(avatar_component_clause,[],[f1363])).
% 2.56/0.75  fof(f1494,plain,(
% 2.56/0.75    spl4_26 | spl4_25),
% 2.56/0.75    inference(avatar_split_clause,[],[f1490,f1359,f1363])).
% 2.56/0.75  fof(f1359,plain,(
% 2.56/0.75    spl4_25 <=> r2_hidden(sK3(sK0,sK2,sK2),sK2)),
% 2.56/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 2.56/0.75  fof(f1490,plain,(
% 2.56/0.75    sK2 = k3_xboole_0(sK0,sK2) | spl4_25),
% 2.56/0.75    inference(resolution,[],[f1361,f179])).
% 2.56/0.75  fof(f179,plain,(
% 2.56/0.75    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1,X1),X1) | k3_xboole_0(X0,X1) = X1) )),
% 2.56/0.75    inference(factoring,[],[f35])).
% 2.56/0.75  fof(f35,plain,(
% 2.56/0.75    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X2) | k3_xboole_0(X0,X1) = X2) )),
% 2.56/0.75    inference(cnf_transformation,[],[f2])).
% 2.56/0.75  fof(f2,axiom,(
% 2.56/0.75    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.56/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 2.56/0.75  fof(f1361,plain,(
% 2.56/0.75    ~r2_hidden(sK3(sK0,sK2,sK2),sK2) | spl4_25),
% 2.56/0.75    inference(avatar_component_clause,[],[f1359])).
% 2.56/0.75  fof(f1372,plain,(
% 2.56/0.75    spl4_24 | spl4_23),
% 2.56/0.75    inference(avatar_split_clause,[],[f1368,f1338,f1342])).
% 2.56/0.75  fof(f1338,plain,(
% 2.56/0.75    spl4_23 <=> r2_hidden(sK3(sK0,sK1,sK1),sK1)),
% 2.56/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 2.56/0.75  fof(f1368,plain,(
% 2.56/0.75    sK1 = k3_xboole_0(sK0,sK1) | spl4_23),
% 2.56/0.75    inference(resolution,[],[f1340,f179])).
% 2.56/0.75  fof(f1340,plain,(
% 2.56/0.75    ~r2_hidden(sK3(sK0,sK1,sK1),sK1) | spl4_23),
% 2.56/0.75    inference(avatar_component_clause,[],[f1338])).
% 2.56/0.75  fof(f1366,plain,(
% 2.56/0.75    ~spl4_25 | spl4_26 | ~spl4_3),
% 2.56/0.75    inference(avatar_split_clause,[],[f1357,f56,f1363,f1359])).
% 2.56/0.75  fof(f56,plain,(
% 2.56/0.75    spl4_3 <=> m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 2.56/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 2.56/0.75  fof(f1357,plain,(
% 2.56/0.75    sK2 = k3_xboole_0(sK0,sK2) | ~r2_hidden(sK3(sK0,sK2,sK2),sK2) | ~spl4_3),
% 2.56/0.75    inference(duplicate_literal_removal,[],[f1347])).
% 2.56/0.75  fof(f1347,plain,(
% 2.56/0.75    sK2 = k3_xboole_0(sK0,sK2) | ~r2_hidden(sK3(sK0,sK2,sK2),sK2) | ~r2_hidden(sK3(sK0,sK2,sK2),sK2) | sK2 = k3_xboole_0(sK0,sK2) | ~spl4_3),
% 2.56/0.75    inference(resolution,[],[f388,f33])).
% 2.56/0.75  fof(f33,plain,(
% 2.56/0.75    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X2) | k3_xboole_0(X0,X1) = X2) )),
% 2.56/0.75    inference(cnf_transformation,[],[f2])).
% 2.56/0.75  fof(f388,plain,(
% 2.56/0.75    ( ! [X25] : (r2_hidden(sK3(X25,sK2,sK2),sK0) | sK2 = k3_xboole_0(X25,sK2)) ) | ~spl4_3),
% 2.56/0.75    inference(resolution,[],[f179,f71])).
% 2.56/0.75  fof(f71,plain,(
% 2.56/0.75    ( ! [X1] : (~r2_hidden(X1,sK2) | r2_hidden(X1,sK0)) ) | ~spl4_3),
% 2.56/0.75    inference(resolution,[],[f29,f58])).
% 2.56/0.75  fof(f58,plain,(
% 2.56/0.75    m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~spl4_3),
% 2.56/0.75    inference(avatar_component_clause,[],[f56])).
% 2.56/0.75  fof(f29,plain,(
% 2.56/0.75    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 2.56/0.75    inference(cnf_transformation,[],[f17])).
% 2.56/0.75  fof(f17,plain,(
% 2.56/0.75    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.56/0.75    inference(ennf_transformation,[],[f8])).
% 2.56/0.75  fof(f8,axiom,(
% 2.56/0.75    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 2.56/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 2.56/0.75  fof(f1345,plain,(
% 2.56/0.75    ~spl4_23 | spl4_24 | ~spl4_1),
% 2.56/0.75    inference(avatar_split_clause,[],[f1336,f46,f1342,f1338])).
% 2.56/0.75  fof(f46,plain,(
% 2.56/0.75    spl4_1 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 2.56/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 2.56/0.75  fof(f1336,plain,(
% 2.56/0.75    sK1 = k3_xboole_0(sK0,sK1) | ~r2_hidden(sK3(sK0,sK1,sK1),sK1) | ~spl4_1),
% 2.56/0.75    inference(duplicate_literal_removal,[],[f1326])).
% 2.56/0.75  fof(f1326,plain,(
% 2.56/0.75    sK1 = k3_xboole_0(sK0,sK1) | ~r2_hidden(sK3(sK0,sK1,sK1),sK1) | ~r2_hidden(sK3(sK0,sK1,sK1),sK1) | sK1 = k3_xboole_0(sK0,sK1) | ~spl4_1),
% 2.56/0.75    inference(resolution,[],[f387,f33])).
% 2.56/0.75  fof(f387,plain,(
% 2.56/0.75    ( ! [X24] : (r2_hidden(sK3(X24,sK1,sK1),sK0) | sK1 = k3_xboole_0(X24,sK1)) ) | ~spl4_1),
% 2.56/0.75    inference(resolution,[],[f179,f70])).
% 2.56/0.75  fof(f70,plain,(
% 2.56/0.75    ( ! [X0] : (~r2_hidden(X0,sK1) | r2_hidden(X0,sK0)) ) | ~spl4_1),
% 2.56/0.75    inference(resolution,[],[f29,f48])).
% 2.56/0.75  fof(f48,plain,(
% 2.56/0.75    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl4_1),
% 2.56/0.75    inference(avatar_component_clause,[],[f46])).
% 2.56/0.75  fof(f146,plain,(
% 2.56/0.75    ~spl4_10 | ~spl4_1 | spl4_2),
% 2.56/0.75    inference(avatar_split_clause,[],[f141,f51,f46,f143])).
% 2.56/0.75  fof(f51,plain,(
% 2.56/0.75    spl4_2 <=> k7_subset_1(sK0,sK1,sK2) = k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2))),
% 2.56/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 2.56/0.75  fof(f141,plain,(
% 2.56/0.75    k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) != k6_subset_1(sK1,sK2) | (~spl4_1 | spl4_2)),
% 2.56/0.75    inference(backward_demodulation,[],[f53,f120])).
% 2.56/0.75  fof(f120,plain,(
% 2.56/0.75    ( ! [X0] : (k7_subset_1(sK0,sK1,X0) = k6_subset_1(sK1,X0)) ) | ~spl4_1),
% 2.56/0.75    inference(resolution,[],[f41,f48])).
% 2.56/0.75  fof(f41,plain,(
% 2.56/0.75    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k6_subset_1(X1,X2)) )),
% 2.56/0.75    inference(definition_unfolding,[],[f31,f25])).
% 2.56/0.75  fof(f31,plain,(
% 2.56/0.75    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)) )),
% 2.56/0.75    inference(cnf_transformation,[],[f18])).
% 2.56/0.75  fof(f18,plain,(
% 2.56/0.75    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.56/0.75    inference(ennf_transformation,[],[f10])).
% 2.56/0.75  fof(f10,axiom,(
% 2.56/0.75    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 2.56/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 2.56/0.75  fof(f53,plain,(
% 2.56/0.75    k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) | spl4_2),
% 2.56/0.75    inference(avatar_component_clause,[],[f51])).
% 2.56/0.75  fof(f87,plain,(
% 2.56/0.75    spl4_5 | ~spl4_3),
% 2.56/0.75    inference(avatar_split_clause,[],[f75,f56,f84])).
% 2.56/0.75  fof(f75,plain,(
% 2.56/0.75    k3_subset_1(sK0,sK2) = k6_subset_1(sK0,sK2) | ~spl4_3),
% 2.56/0.75    inference(resolution,[],[f40,f58])).
% 2.56/0.75  fof(f40,plain,(
% 2.56/0.75    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k6_subset_1(X0,X1)) )),
% 2.56/0.75    inference(definition_unfolding,[],[f28,f25])).
% 2.56/0.75  fof(f28,plain,(
% 2.56/0.75    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 2.56/0.75    inference(cnf_transformation,[],[f16])).
% 2.56/0.75  fof(f16,plain,(
% 2.56/0.75    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.56/0.75    inference(ennf_transformation,[],[f6])).
% 2.56/0.75  fof(f6,axiom,(
% 2.56/0.75    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.56/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 2.56/0.75  fof(f59,plain,(
% 2.56/0.75    spl4_3),
% 2.56/0.75    inference(avatar_split_clause,[],[f20,f56])).
% 2.56/0.75  fof(f20,plain,(
% 2.56/0.75    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 2.56/0.75    inference(cnf_transformation,[],[f15])).
% 2.56/0.75  fof(f15,plain,(
% 2.56/0.75    ? [X0,X1] : (? [X2] : (k7_subset_1(X0,X1,X2) != k9_subset_1(X0,X1,k3_subset_1(X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.56/0.75    inference(ennf_transformation,[],[f13])).
% 2.56/0.75  fof(f13,negated_conjecture,(
% 2.56/0.75    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))))),
% 2.56/0.75    inference(negated_conjecture,[],[f12])).
% 2.56/0.75  fof(f12,conjecture,(
% 2.56/0.75    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))))),
% 2.56/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).
% 2.56/0.75  fof(f54,plain,(
% 2.56/0.75    ~spl4_2),
% 2.56/0.75    inference(avatar_split_clause,[],[f21,f51])).
% 2.56/0.75  fof(f21,plain,(
% 2.56/0.75    k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2))),
% 2.56/0.75    inference(cnf_transformation,[],[f15])).
% 2.56/0.75  fof(f49,plain,(
% 2.56/0.75    spl4_1),
% 2.56/0.75    inference(avatar_split_clause,[],[f22,f46])).
% 2.56/0.75  fof(f22,plain,(
% 2.56/0.75    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 2.56/0.75    inference(cnf_transformation,[],[f15])).
% 2.56/0.75  % SZS output end Proof for theBenchmark
% 2.56/0.75  % (19950)------------------------------
% 2.56/0.75  % (19950)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.56/0.75  % (19950)Termination reason: Refutation
% 2.56/0.75  
% 2.56/0.75  % (19950)Memory used [KB]: 13560
% 2.56/0.75  % (19950)Time elapsed: 0.323 s
% 2.56/0.75  % (19950)------------------------------
% 2.56/0.75  % (19950)------------------------------
% 2.56/0.75  % (19930)Success in time 0.38 s
%------------------------------------------------------------------------------
