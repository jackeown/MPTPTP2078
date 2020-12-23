%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:13 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 200 expanded)
%              Number of leaves         :   27 (  93 expanded)
%              Depth                    :    8
%              Number of atoms          :  350 ( 667 expanded)
%              Number of equality atoms :   11 (  31 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f447,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f43,f44,f49,f54,f58,f62,f66,f70,f82,f86,f100,f105,f116,f122,f126,f130,f136,f291,f312,f332,f442])).

fof(f442,plain,
    ( spl3_2
    | ~ spl3_3
    | ~ spl3_14
    | ~ spl3_45
    | ~ spl3_47 ),
    inference(avatar_contradiction_clause,[],[f441])).

fof(f441,plain,
    ( $false
    | spl3_2
    | ~ spl3_3
    | ~ spl3_14
    | ~ spl3_45
    | ~ spl3_47 ),
    inference(subsumption_resolution,[],[f440,f42])).

fof(f42,plain,
    ( ~ r1_tarski(sK1,sK2)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl3_2
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f440,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl3_3
    | ~ spl3_14
    | ~ spl3_45
    | ~ spl3_47 ),
    inference(subsumption_resolution,[],[f439,f48])).

fof(f48,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f46])).

fof(f46,plain,
    ( spl3_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f439,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | r1_tarski(sK1,sK2)
    | ~ spl3_14
    | ~ spl3_45
    | ~ spl3_47 ),
    inference(subsumption_resolution,[],[f433,f311])).

fof(f311,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1))
    | ~ spl3_45 ),
    inference(avatar_component_clause,[],[f309])).

fof(f309,plain,
    ( spl3_45
  <=> r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).

fof(f433,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | r1_tarski(sK1,sK2)
    | ~ spl3_14
    | ~ spl3_47 ),
    inference(superposition,[],[f331,f99])).

fof(f99,plain,
    ( k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl3_14
  <=> k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f331,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k3_subset_1(sK0,X1),k4_xboole_0(sK0,sK1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(sK0))
        | r1_tarski(sK1,X1) )
    | ~ spl3_47 ),
    inference(avatar_component_clause,[],[f330])).

fof(f330,plain,
    ( spl3_47
  <=> ! [X1] :
        ( ~ r1_tarski(k3_subset_1(sK0,X1),k4_xboole_0(sK0,sK1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(sK0))
        | r1_tarski(sK1,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).

fof(f332,plain,
    ( spl3_47
    | ~ spl3_4
    | ~ spl3_8
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f328,f102,f68,f51,f330])).

fof(f51,plain,
    ( spl3_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f68,plain,
    ( spl3_8
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X1,X2)
        | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f102,plain,
    ( spl3_15
  <=> k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f328,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k3_subset_1(sK0,X1),k4_xboole_0(sK0,sK1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(sK0))
        | r1_tarski(sK1,X1) )
    | ~ spl3_4
    | ~ spl3_8
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f315,f104])).

fof(f104,plain,
    ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f102])).

fof(f315,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k3_subset_1(sK0,X1),k3_subset_1(sK0,sK1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(sK0))
        | r1_tarski(sK1,X1) )
    | ~ spl3_4
    | ~ spl3_8 ),
    inference(resolution,[],[f69,f53])).

fof(f53,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f51])).

fof(f69,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | r1_tarski(X1,X2) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f68])).

fof(f312,plain,
    ( spl3_45
    | ~ spl3_4
    | ~ spl3_15
    | ~ spl3_18
    | ~ spl3_42 ),
    inference(avatar_split_clause,[],[f307,f289,f119,f102,f51,f309])).

fof(f119,plain,
    ( spl3_18
  <=> m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f289,plain,
    ( spl3_42
  <=> ! [X8] :
        ( r1_tarski(k4_xboole_0(sK0,sK2),k3_subset_1(X8,sK1))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X8))
        | ~ m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(X8)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).

fof(f307,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1))
    | ~ spl3_4
    | ~ spl3_15
    | ~ spl3_18
    | ~ spl3_42 ),
    inference(forward_demodulation,[],[f306,f104])).

fof(f306,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK2),k3_subset_1(sK0,sK1))
    | ~ spl3_4
    | ~ spl3_18
    | ~ spl3_42 ),
    inference(subsumption_resolution,[],[f305,f121])).

fof(f121,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f119])).

fof(f305,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK2),k3_subset_1(sK0,sK1))
    | ~ m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ spl3_4
    | ~ spl3_42 ),
    inference(resolution,[],[f290,f53])).

fof(f290,plain,
    ( ! [X8] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(X8))
        | r1_tarski(k4_xboole_0(sK0,sK2),k3_subset_1(X8,sK1))
        | ~ m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(X8)) )
    | ~ spl3_42 ),
    inference(avatar_component_clause,[],[f289])).

fof(f291,plain,
    ( spl3_42
    | ~ spl3_11
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f278,f133,f80,f289])).

fof(f80,plain,
    ( spl3_11
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X1,k3_subset_1(X0,X2))
        | ~ r1_xboole_0(X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f133,plain,
    ( spl3_19
  <=> r1_xboole_0(k4_xboole_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f278,plain,
    ( ! [X8] :
        ( r1_tarski(k4_xboole_0(sK0,sK2),k3_subset_1(X8,sK1))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X8))
        | ~ m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(X8)) )
    | ~ spl3_11
    | ~ spl3_19 ),
    inference(resolution,[],[f81,f135])).

fof(f135,plain,
    ( r1_xboole_0(k4_xboole_0(sK0,sK2),sK1)
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f133])).

fof(f81,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_xboole_0(X1,X2)
        | r1_tarski(X1,k3_subset_1(X0,X2))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f80])).

fof(f136,plain,
    ( spl3_19
    | ~ spl3_5
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f131,f113,f56,f133])).

fof(f56,plain,
    ( spl3_5
  <=> ! [X1,X0] :
        ( r1_xboole_0(X1,X0)
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f113,plain,
    ( spl3_17
  <=> r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f131,plain,
    ( r1_xboole_0(k4_xboole_0(sK0,sK2),sK1)
    | ~ spl3_5
    | ~ spl3_17 ),
    inference(resolution,[],[f114,f57])).

fof(f57,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X1,X0) )
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f56])).

fof(f114,plain,
    ( r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f113])).

fof(f130,plain,
    ( spl3_17
    | ~ spl3_1
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f127,f97,f36,f113])).

fof(f36,plain,
    ( spl3_1
  <=> r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f127,plain,
    ( r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    | ~ spl3_1
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f37,f99])).

fof(f37,plain,
    ( r1_xboole_0(sK1,k3_subset_1(sK0,sK2))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f36])).

fof(f126,plain,
    ( ~ spl3_2
    | ~ spl3_12
    | spl3_17 ),
    inference(avatar_split_clause,[],[f123,f113,f84,f40])).

fof(f84,plain,
    ( spl3_12
  <=> ! [X1,X0,X2] :
        ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f123,plain,
    ( ~ r1_tarski(sK1,sK2)
    | ~ spl3_12
    | spl3_17 ),
    inference(resolution,[],[f115,f85])).

fof(f85,plain,
    ( ! [X2,X0,X1] :
        ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f84])).

fof(f115,plain,
    ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    | spl3_17 ),
    inference(avatar_component_clause,[],[f113])).

fof(f122,plain,
    ( spl3_18
    | ~ spl3_3
    | ~ spl3_6
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f117,f97,f60,f46,f119])).

fof(f60,plain,
    ( spl3_6
  <=> ! [X1,X0] :
        ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f117,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ spl3_3
    | ~ spl3_6
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f111,f48])).

fof(f111,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl3_6
    | ~ spl3_14 ),
    inference(superposition,[],[f61,f99])).

fof(f61,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f60])).

fof(f116,plain,
    ( ~ spl3_17
    | spl3_1
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f110,f97,f36,f113])).

fof(f110,plain,
    ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    | spl3_1
    | ~ spl3_14 ),
    inference(superposition,[],[f38,f99])).

fof(f38,plain,
    ( ~ r1_xboole_0(sK1,k3_subset_1(sK0,sK2))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f36])).

fof(f105,plain,
    ( spl3_15
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f94,f64,f51,f102])).

fof(f64,plain,
    ( spl3_7
  <=> ! [X1,X0] :
        ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f94,plain,
    ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(resolution,[],[f65,f53])).

fof(f65,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f64])).

fof(f100,plain,
    ( spl3_14
    | ~ spl3_3
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f93,f64,f46,f97])).

fof(f93,plain,
    ( k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)
    | ~ spl3_3
    | ~ spl3_7 ),
    inference(resolution,[],[f65,f48])).

fof(f86,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f34,f84])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

fof(f82,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f32,f80])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,k3_subset_1(X0,X2))
      | ~ r1_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_xboole_0(X1,X2)
              | ~ r1_tarski(X1,k3_subset_1(X0,X2)) )
            & ( r1_tarski(X1,k3_subset_1(X0,X2))
              | ~ r1_xboole_0(X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_xboole_0(X1,X2)
          <=> r1_tarski(X1,k3_subset_1(X0,X2)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,X2)
          <=> r1_tarski(X1,k3_subset_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_subset_1)).

fof(f70,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f31,f68])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_tarski(X1,X2)
              | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
            & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | ~ r1_tarski(X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

fof(f66,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f29,f64])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f62,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f28,f60])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f58,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f27,f56])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f54,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f23,f51])).

fof(f23,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ( ~ r1_tarski(sK1,sK2)
      | ~ r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) )
    & ( r1_tarski(sK1,sK2)
      | r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) )
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f19,f18])).

fof(f18,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ~ r1_tarski(X1,X2)
              | ~ r1_xboole_0(X1,k3_subset_1(X0,X2)) )
            & ( r1_tarski(X1,X2)
              | r1_xboole_0(X1,k3_subset_1(X0,X2)) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ( ~ r1_tarski(sK1,X2)
            | ~ r1_xboole_0(sK1,k3_subset_1(sK0,X2)) )
          & ( r1_tarski(sK1,X2)
            | r1_xboole_0(sK1,k3_subset_1(sK0,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X2] :
        ( ( ~ r1_tarski(sK1,X2)
          | ~ r1_xboole_0(sK1,k3_subset_1(sK0,X2)) )
        & ( r1_tarski(sK1,X2)
          | r1_xboole_0(sK1,k3_subset_1(sK0,X2)) )
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( ( ~ r1_tarski(sK1,sK2)
        | ~ r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) )
      & ( r1_tarski(sK1,sK2)
        | r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X1,X2)
            | ~ r1_xboole_0(X1,k3_subset_1(X0,X2)) )
          & ( r1_tarski(X1,X2)
            | r1_xboole_0(X1,k3_subset_1(X0,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X1,X2)
            | ~ r1_xboole_0(X1,k3_subset_1(X0,X2)) )
          & ( r1_tarski(X1,X2)
            | r1_xboole_0(X1,k3_subset_1(X0,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_xboole_0(X1,k3_subset_1(X0,X2))
          <~> r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_xboole_0(X1,k3_subset_1(X0,X2))
            <=> r1_tarski(X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,k3_subset_1(X0,X2))
          <=> r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_subset_1)).

fof(f49,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f24,f46])).

fof(f24,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f44,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f25,f40,f36])).

fof(f25,plain,
    ( r1_tarski(sK1,sK2)
    | r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f20])).

fof(f43,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f26,f40,f36])).

fof(f26,plain,
    ( ~ r1_tarski(sK1,sK2)
    | ~ r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:15:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.42  % (11745)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.21/0.42  % (11746)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.42  % (11746)Refutation found. Thanks to Tanya!
% 0.21/0.42  % SZS status Theorem for theBenchmark
% 0.21/0.42  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f447,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(avatar_sat_refutation,[],[f43,f44,f49,f54,f58,f62,f66,f70,f82,f86,f100,f105,f116,f122,f126,f130,f136,f291,f312,f332,f442])).
% 0.21/0.43  fof(f442,plain,(
% 0.21/0.43    spl3_2 | ~spl3_3 | ~spl3_14 | ~spl3_45 | ~spl3_47),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f441])).
% 0.21/0.43  fof(f441,plain,(
% 0.21/0.43    $false | (spl3_2 | ~spl3_3 | ~spl3_14 | ~spl3_45 | ~spl3_47)),
% 0.21/0.43    inference(subsumption_resolution,[],[f440,f42])).
% 0.21/0.43  fof(f42,plain,(
% 0.21/0.43    ~r1_tarski(sK1,sK2) | spl3_2),
% 0.21/0.43    inference(avatar_component_clause,[],[f40])).
% 0.21/0.43  fof(f40,plain,(
% 0.21/0.43    spl3_2 <=> r1_tarski(sK1,sK2)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.43  fof(f440,plain,(
% 0.21/0.43    r1_tarski(sK1,sK2) | (~spl3_3 | ~spl3_14 | ~spl3_45 | ~spl3_47)),
% 0.21/0.43    inference(subsumption_resolution,[],[f439,f48])).
% 0.21/0.43  fof(f48,plain,(
% 0.21/0.43    m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~spl3_3),
% 0.21/0.43    inference(avatar_component_clause,[],[f46])).
% 0.21/0.43  fof(f46,plain,(
% 0.21/0.43    spl3_3 <=> m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.43  fof(f439,plain,(
% 0.21/0.43    ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | r1_tarski(sK1,sK2) | (~spl3_14 | ~spl3_45 | ~spl3_47)),
% 0.21/0.43    inference(subsumption_resolution,[],[f433,f311])).
% 0.21/0.43  fof(f311,plain,(
% 0.21/0.43    r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1)) | ~spl3_45),
% 0.21/0.43    inference(avatar_component_clause,[],[f309])).
% 0.21/0.43  fof(f309,plain,(
% 0.21/0.43    spl3_45 <=> r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).
% 0.21/0.43  fof(f433,plain,(
% 0.21/0.43    ~r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | r1_tarski(sK1,sK2) | (~spl3_14 | ~spl3_47)),
% 0.21/0.43    inference(superposition,[],[f331,f99])).
% 0.21/0.43  fof(f99,plain,(
% 0.21/0.43    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) | ~spl3_14),
% 0.21/0.43    inference(avatar_component_clause,[],[f97])).
% 0.21/0.43  fof(f97,plain,(
% 0.21/0.43    spl3_14 <=> k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.43  fof(f331,plain,(
% 0.21/0.43    ( ! [X1] : (~r1_tarski(k3_subset_1(sK0,X1),k4_xboole_0(sK0,sK1)) | ~m1_subset_1(X1,k1_zfmisc_1(sK0)) | r1_tarski(sK1,X1)) ) | ~spl3_47),
% 0.21/0.43    inference(avatar_component_clause,[],[f330])).
% 0.21/0.43  fof(f330,plain,(
% 0.21/0.43    spl3_47 <=> ! [X1] : (~r1_tarski(k3_subset_1(sK0,X1),k4_xboole_0(sK0,sK1)) | ~m1_subset_1(X1,k1_zfmisc_1(sK0)) | r1_tarski(sK1,X1))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).
% 0.21/0.43  fof(f332,plain,(
% 0.21/0.43    spl3_47 | ~spl3_4 | ~spl3_8 | ~spl3_15),
% 0.21/0.43    inference(avatar_split_clause,[],[f328,f102,f68,f51,f330])).
% 0.21/0.43  fof(f51,plain,(
% 0.21/0.43    spl3_4 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.43  fof(f68,plain,(
% 0.21/0.43    spl3_8 <=> ! [X1,X0,X2] : (r1_tarski(X1,X2) | ~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.43  fof(f102,plain,(
% 0.21/0.43    spl3_15 <=> k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.43  fof(f328,plain,(
% 0.21/0.43    ( ! [X1] : (~r1_tarski(k3_subset_1(sK0,X1),k4_xboole_0(sK0,sK1)) | ~m1_subset_1(X1,k1_zfmisc_1(sK0)) | r1_tarski(sK1,X1)) ) | (~spl3_4 | ~spl3_8 | ~spl3_15)),
% 0.21/0.43    inference(forward_demodulation,[],[f315,f104])).
% 0.21/0.43  fof(f104,plain,(
% 0.21/0.43    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) | ~spl3_15),
% 0.21/0.43    inference(avatar_component_clause,[],[f102])).
% 0.21/0.43  fof(f315,plain,(
% 0.21/0.43    ( ! [X1] : (~r1_tarski(k3_subset_1(sK0,X1),k3_subset_1(sK0,sK1)) | ~m1_subset_1(X1,k1_zfmisc_1(sK0)) | r1_tarski(sK1,X1)) ) | (~spl3_4 | ~spl3_8)),
% 0.21/0.43    inference(resolution,[],[f69,f53])).
% 0.21/0.43  fof(f53,plain,(
% 0.21/0.43    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl3_4),
% 0.21/0.43    inference(avatar_component_clause,[],[f51])).
% 0.21/0.43  fof(f69,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | r1_tarski(X1,X2)) ) | ~spl3_8),
% 0.21/0.43    inference(avatar_component_clause,[],[f68])).
% 0.21/0.43  fof(f312,plain,(
% 0.21/0.43    spl3_45 | ~spl3_4 | ~spl3_15 | ~spl3_18 | ~spl3_42),
% 0.21/0.43    inference(avatar_split_clause,[],[f307,f289,f119,f102,f51,f309])).
% 0.21/0.43  fof(f119,plain,(
% 0.21/0.43    spl3_18 <=> m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.21/0.43  fof(f289,plain,(
% 0.21/0.43    spl3_42 <=> ! [X8] : (r1_tarski(k4_xboole_0(sK0,sK2),k3_subset_1(X8,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(X8)) | ~m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(X8)))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).
% 0.21/0.43  fof(f307,plain,(
% 0.21/0.43    r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1)) | (~spl3_4 | ~spl3_15 | ~spl3_18 | ~spl3_42)),
% 0.21/0.43    inference(forward_demodulation,[],[f306,f104])).
% 0.21/0.43  fof(f306,plain,(
% 0.21/0.43    r1_tarski(k4_xboole_0(sK0,sK2),k3_subset_1(sK0,sK1)) | (~spl3_4 | ~spl3_18 | ~spl3_42)),
% 0.21/0.43    inference(subsumption_resolution,[],[f305,f121])).
% 0.21/0.43  fof(f121,plain,(
% 0.21/0.43    m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0)) | ~spl3_18),
% 0.21/0.43    inference(avatar_component_clause,[],[f119])).
% 0.21/0.43  fof(f305,plain,(
% 0.21/0.43    r1_tarski(k4_xboole_0(sK0,sK2),k3_subset_1(sK0,sK1)) | ~m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0)) | (~spl3_4 | ~spl3_42)),
% 0.21/0.43    inference(resolution,[],[f290,f53])).
% 0.21/0.43  fof(f290,plain,(
% 0.21/0.43    ( ! [X8] : (~m1_subset_1(sK1,k1_zfmisc_1(X8)) | r1_tarski(k4_xboole_0(sK0,sK2),k3_subset_1(X8,sK1)) | ~m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(X8))) ) | ~spl3_42),
% 0.21/0.43    inference(avatar_component_clause,[],[f289])).
% 0.21/0.43  fof(f291,plain,(
% 0.21/0.43    spl3_42 | ~spl3_11 | ~spl3_19),
% 0.21/0.43    inference(avatar_split_clause,[],[f278,f133,f80,f289])).
% 0.21/0.43  fof(f80,plain,(
% 0.21/0.43    spl3_11 <=> ! [X1,X0,X2] : (r1_tarski(X1,k3_subset_1(X0,X2)) | ~r1_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.43  fof(f133,plain,(
% 0.21/0.43    spl3_19 <=> r1_xboole_0(k4_xboole_0(sK0,sK2),sK1)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.21/0.43  fof(f278,plain,(
% 0.21/0.43    ( ! [X8] : (r1_tarski(k4_xboole_0(sK0,sK2),k3_subset_1(X8,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(X8)) | ~m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(X8))) ) | (~spl3_11 | ~spl3_19)),
% 0.21/0.43    inference(resolution,[],[f81,f135])).
% 0.21/0.43  fof(f135,plain,(
% 0.21/0.43    r1_xboole_0(k4_xboole_0(sK0,sK2),sK1) | ~spl3_19),
% 0.21/0.43    inference(avatar_component_clause,[],[f133])).
% 0.21/0.43  fof(f81,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~r1_xboole_0(X1,X2) | r1_tarski(X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl3_11),
% 0.21/0.43    inference(avatar_component_clause,[],[f80])).
% 0.21/0.43  fof(f136,plain,(
% 0.21/0.43    spl3_19 | ~spl3_5 | ~spl3_17),
% 0.21/0.43    inference(avatar_split_clause,[],[f131,f113,f56,f133])).
% 0.21/0.43  fof(f56,plain,(
% 0.21/0.43    spl3_5 <=> ! [X1,X0] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.43  fof(f113,plain,(
% 0.21/0.43    spl3_17 <=> r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.43  fof(f131,plain,(
% 0.21/0.43    r1_xboole_0(k4_xboole_0(sK0,sK2),sK1) | (~spl3_5 | ~spl3_17)),
% 0.21/0.43    inference(resolution,[],[f114,f57])).
% 0.21/0.43  fof(f57,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) ) | ~spl3_5),
% 0.21/0.43    inference(avatar_component_clause,[],[f56])).
% 0.21/0.43  fof(f114,plain,(
% 0.21/0.43    r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) | ~spl3_17),
% 0.21/0.43    inference(avatar_component_clause,[],[f113])).
% 0.21/0.43  fof(f130,plain,(
% 0.21/0.43    spl3_17 | ~spl3_1 | ~spl3_14),
% 0.21/0.43    inference(avatar_split_clause,[],[f127,f97,f36,f113])).
% 0.21/0.43  fof(f36,plain,(
% 0.21/0.43    spl3_1 <=> r1_xboole_0(sK1,k3_subset_1(sK0,sK2))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.43  fof(f127,plain,(
% 0.21/0.43    r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) | (~spl3_1 | ~spl3_14)),
% 0.21/0.43    inference(forward_demodulation,[],[f37,f99])).
% 0.21/0.43  fof(f37,plain,(
% 0.21/0.43    r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) | ~spl3_1),
% 0.21/0.43    inference(avatar_component_clause,[],[f36])).
% 0.21/0.43  fof(f126,plain,(
% 0.21/0.43    ~spl3_2 | ~spl3_12 | spl3_17),
% 0.21/0.43    inference(avatar_split_clause,[],[f123,f113,f84,f40])).
% 0.21/0.43  fof(f84,plain,(
% 0.21/0.43    spl3_12 <=> ! [X1,X0,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.43  fof(f123,plain,(
% 0.21/0.43    ~r1_tarski(sK1,sK2) | (~spl3_12 | spl3_17)),
% 0.21/0.43    inference(resolution,[],[f115,f85])).
% 0.21/0.43  fof(f85,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) ) | ~spl3_12),
% 0.21/0.43    inference(avatar_component_clause,[],[f84])).
% 0.21/0.43  fof(f115,plain,(
% 0.21/0.43    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) | spl3_17),
% 0.21/0.43    inference(avatar_component_clause,[],[f113])).
% 0.21/0.43  fof(f122,plain,(
% 0.21/0.43    spl3_18 | ~spl3_3 | ~spl3_6 | ~spl3_14),
% 0.21/0.43    inference(avatar_split_clause,[],[f117,f97,f60,f46,f119])).
% 0.21/0.43  fof(f60,plain,(
% 0.21/0.43    spl3_6 <=> ! [X1,X0] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.43  fof(f117,plain,(
% 0.21/0.43    m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0)) | (~spl3_3 | ~spl3_6 | ~spl3_14)),
% 0.21/0.43    inference(subsumption_resolution,[],[f111,f48])).
% 0.21/0.43  fof(f111,plain,(
% 0.21/0.43    m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | (~spl3_6 | ~spl3_14)),
% 0.21/0.43    inference(superposition,[],[f61,f99])).
% 0.21/0.43  fof(f61,plain,(
% 0.21/0.43    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl3_6),
% 0.21/0.43    inference(avatar_component_clause,[],[f60])).
% 0.21/0.43  fof(f116,plain,(
% 0.21/0.43    ~spl3_17 | spl3_1 | ~spl3_14),
% 0.21/0.43    inference(avatar_split_clause,[],[f110,f97,f36,f113])).
% 0.21/0.43  fof(f110,plain,(
% 0.21/0.43    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) | (spl3_1 | ~spl3_14)),
% 0.21/0.43    inference(superposition,[],[f38,f99])).
% 0.21/0.43  fof(f38,plain,(
% 0.21/0.43    ~r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) | spl3_1),
% 0.21/0.43    inference(avatar_component_clause,[],[f36])).
% 0.21/0.43  fof(f105,plain,(
% 0.21/0.43    spl3_15 | ~spl3_4 | ~spl3_7),
% 0.21/0.43    inference(avatar_split_clause,[],[f94,f64,f51,f102])).
% 0.21/0.43  fof(f64,plain,(
% 0.21/0.43    spl3_7 <=> ! [X1,X0] : (k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.43  fof(f94,plain,(
% 0.21/0.43    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) | (~spl3_4 | ~spl3_7)),
% 0.21/0.43    inference(resolution,[],[f65,f53])).
% 0.21/0.43  fof(f65,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)) ) | ~spl3_7),
% 0.21/0.43    inference(avatar_component_clause,[],[f64])).
% 0.21/0.43  fof(f100,plain,(
% 0.21/0.43    spl3_14 | ~spl3_3 | ~spl3_7),
% 0.21/0.43    inference(avatar_split_clause,[],[f93,f64,f46,f97])).
% 0.21/0.43  fof(f93,plain,(
% 0.21/0.43    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) | (~spl3_3 | ~spl3_7)),
% 0.21/0.43    inference(resolution,[],[f65,f48])).
% 0.21/0.43  fof(f86,plain,(
% 0.21/0.43    spl3_12),
% 0.21/0.43    inference(avatar_split_clause,[],[f34,f84])).
% 0.21/0.43  fof(f34,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f15])).
% 0.21/0.43  fof(f15,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f2])).
% 0.21/0.43  fof(f2,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).
% 0.21/0.43  fof(f82,plain,(
% 0.21/0.43    spl3_11),
% 0.21/0.43    inference(avatar_split_clause,[],[f32,f80])).
% 0.21/0.43  fof(f32,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (r1_tarski(X1,k3_subset_1(X0,X2)) | ~r1_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f22])).
% 0.21/0.43  fof(f22,plain,(
% 0.21/0.43    ! [X0,X1] : (! [X2] : (((r1_xboole_0(X1,X2) | ~r1_tarski(X1,k3_subset_1(X0,X2))) & (r1_tarski(X1,k3_subset_1(X0,X2)) | ~r1_xboole_0(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.43    inference(nnf_transformation,[],[f14])).
% 0.21/0.43  fof(f14,plain,(
% 0.21/0.43    ! [X0,X1] : (! [X2] : ((r1_xboole_0(X1,X2) <=> r1_tarski(X1,k3_subset_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.43    inference(ennf_transformation,[],[f6])).
% 0.21/0.43  fof(f6,axiom,(
% 0.21/0.43    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,X2) <=> r1_tarski(X1,k3_subset_1(X0,X2)))))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_subset_1)).
% 0.21/0.43  fof(f70,plain,(
% 0.21/0.43    spl3_8),
% 0.21/0.43    inference(avatar_split_clause,[],[f31,f68])).
% 0.21/0.43  fof(f31,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f21])).
% 0.21/0.43  fof(f21,plain,(
% 0.21/0.43    ! [X0,X1] : (! [X2] : (((r1_tarski(X1,X2) | ~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.43    inference(nnf_transformation,[],[f13])).
% 0.21/0.43  fof(f13,plain,(
% 0.21/0.43    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.43    inference(ennf_transformation,[],[f5])).
% 0.21/0.43  fof(f5,axiom,(
% 0.21/0.43    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).
% 0.21/0.43  fof(f66,plain,(
% 0.21/0.43    spl3_7),
% 0.21/0.43    inference(avatar_split_clause,[],[f29,f64])).
% 0.21/0.43  fof(f29,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f12])).
% 0.21/0.43  fof(f12,plain,(
% 0.21/0.43    ! [X0,X1] : (k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.43    inference(ennf_transformation,[],[f3])).
% 0.21/0.43  fof(f3,axiom,(
% 0.21/0.43    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 0.21/0.43  fof(f62,plain,(
% 0.21/0.43    spl3_6),
% 0.21/0.43    inference(avatar_split_clause,[],[f28,f60])).
% 0.21/0.43  fof(f28,plain,(
% 0.21/0.43    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f11])).
% 0.21/0.43  fof(f11,plain,(
% 0.21/0.43    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.43    inference(ennf_transformation,[],[f4])).
% 0.21/0.43  fof(f4,axiom,(
% 0.21/0.43    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.21/0.43  fof(f58,plain,(
% 0.21/0.43    spl3_5),
% 0.21/0.43    inference(avatar_split_clause,[],[f27,f56])).
% 0.21/0.43  fof(f27,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f10])).
% 0.21/0.43  fof(f10,plain,(
% 0.21/0.43    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.21/0.43  fof(f54,plain,(
% 0.21/0.43    spl3_4),
% 0.21/0.43    inference(avatar_split_clause,[],[f23,f51])).
% 0.21/0.43  fof(f23,plain,(
% 0.21/0.43    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.43    inference(cnf_transformation,[],[f20])).
% 0.21/0.43  fof(f20,plain,(
% 0.21/0.43    ((~r1_tarski(sK1,sK2) | ~r1_xboole_0(sK1,k3_subset_1(sK0,sK2))) & (r1_tarski(sK1,sK2) | r1_xboole_0(sK1,k3_subset_1(sK0,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f19,f18])).
% 0.21/0.43  fof(f18,plain,(
% 0.21/0.43    ? [X0,X1] : (? [X2] : ((~r1_tarski(X1,X2) | ~r1_xboole_0(X1,k3_subset_1(X0,X2))) & (r1_tarski(X1,X2) | r1_xboole_0(X1,k3_subset_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : ((~r1_tarski(sK1,X2) | ~r1_xboole_0(sK1,k3_subset_1(sK0,X2))) & (r1_tarski(sK1,X2) | r1_xboole_0(sK1,k3_subset_1(sK0,X2))) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f19,plain,(
% 0.21/0.43    ? [X2] : ((~r1_tarski(sK1,X2) | ~r1_xboole_0(sK1,k3_subset_1(sK0,X2))) & (r1_tarski(sK1,X2) | r1_xboole_0(sK1,k3_subset_1(sK0,X2))) & m1_subset_1(X2,k1_zfmisc_1(sK0))) => ((~r1_tarski(sK1,sK2) | ~r1_xboole_0(sK1,k3_subset_1(sK0,sK2))) & (r1_tarski(sK1,sK2) | r1_xboole_0(sK1,k3_subset_1(sK0,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f17,plain,(
% 0.21/0.43    ? [X0,X1] : (? [X2] : ((~r1_tarski(X1,X2) | ~r1_xboole_0(X1,k3_subset_1(X0,X2))) & (r1_tarski(X1,X2) | r1_xboole_0(X1,k3_subset_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.43    inference(flattening,[],[f16])).
% 0.21/0.43  fof(f16,plain,(
% 0.21/0.43    ? [X0,X1] : (? [X2] : (((~r1_tarski(X1,X2) | ~r1_xboole_0(X1,k3_subset_1(X0,X2))) & (r1_tarski(X1,X2) | r1_xboole_0(X1,k3_subset_1(X0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.43    inference(nnf_transformation,[],[f9])).
% 0.21/0.43  fof(f9,plain,(
% 0.21/0.43    ? [X0,X1] : (? [X2] : ((r1_xboole_0(X1,k3_subset_1(X0,X2)) <~> r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.43    inference(ennf_transformation,[],[f8])).
% 0.21/0.43  fof(f8,negated_conjecture,(
% 0.21/0.43    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,k3_subset_1(X0,X2)) <=> r1_tarski(X1,X2))))),
% 0.21/0.43    inference(negated_conjecture,[],[f7])).
% 0.21/0.43  fof(f7,conjecture,(
% 0.21/0.43    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,k3_subset_1(X0,X2)) <=> r1_tarski(X1,X2))))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_subset_1)).
% 0.21/0.43  fof(f49,plain,(
% 0.21/0.43    spl3_3),
% 0.21/0.43    inference(avatar_split_clause,[],[f24,f46])).
% 0.21/0.43  fof(f24,plain,(
% 0.21/0.43    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.21/0.43    inference(cnf_transformation,[],[f20])).
% 0.21/0.43  fof(f44,plain,(
% 0.21/0.43    spl3_1 | spl3_2),
% 0.21/0.43    inference(avatar_split_clause,[],[f25,f40,f36])).
% 0.21/0.43  fof(f25,plain,(
% 0.21/0.43    r1_tarski(sK1,sK2) | r1_xboole_0(sK1,k3_subset_1(sK0,sK2))),
% 0.21/0.43    inference(cnf_transformation,[],[f20])).
% 0.21/0.43  fof(f43,plain,(
% 0.21/0.43    ~spl3_1 | ~spl3_2),
% 0.21/0.43    inference(avatar_split_clause,[],[f26,f40,f36])).
% 0.21/0.43  fof(f26,plain,(
% 0.21/0.43    ~r1_tarski(sK1,sK2) | ~r1_xboole_0(sK1,k3_subset_1(sK0,sK2))),
% 0.21/0.43    inference(cnf_transformation,[],[f20])).
% 0.21/0.43  % SZS output end Proof for theBenchmark
% 0.21/0.43  % (11746)------------------------------
% 0.21/0.43  % (11746)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (11746)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (11746)Memory used [KB]: 10746
% 0.21/0.43  % (11746)Time elapsed: 0.012 s
% 0.21/0.43  % (11746)------------------------------
% 0.21/0.43  % (11746)------------------------------
% 0.21/0.43  % (11740)Success in time 0.069 s
%------------------------------------------------------------------------------
