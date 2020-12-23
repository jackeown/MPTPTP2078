%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : subset_1__t28_subset_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:22 EDT 2019

% Result     : Theorem 0.12s
% Output     : Refutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   58 (  77 expanded)
%              Number of leaves         :   15 (  29 expanded)
%              Depth                    :    9
%              Number of atoms          :  123 ( 157 expanded)
%              Number of equality atoms :   31 (  41 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f166,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f72,f83,f87,f95,f120,f162,f165])).

fof(f165,plain,
    ( spl4_5
    | ~ spl4_12
    | ~ spl4_20 ),
    inference(avatar_contradiction_clause,[],[f164])).

fof(f164,plain,
    ( $false
    | ~ spl4_5
    | ~ spl4_12
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f163,f86])).

fof(f86,plain,
    ( k4_subset_1(sK0,sK1,sK0) != sK0
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl4_5
  <=> k4_subset_1(sK0,sK1,sK0) != sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f163,plain,
    ( k4_subset_1(sK0,sK1,sK0) = sK0
    | ~ spl4_12
    | ~ spl4_20 ),
    inference(forward_demodulation,[],[f161,f127])).

fof(f127,plain,
    ( k2_xboole_0(sK0,sK1) = sK0
    | ~ spl4_12 ),
    inference(superposition,[],[f119,f57])).

fof(f57,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t28_subset_1.p',commutativity_k2_xboole_0)).

fof(f119,plain,
    ( k2_xboole_0(sK1,sK0) = sK0
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl4_12
  <=> k2_xboole_0(sK1,sK0) = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f161,plain,
    ( k4_subset_1(sK0,sK1,sK0) = k2_xboole_0(sK0,sK1)
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f160])).

fof(f160,plain,
    ( spl4_20
  <=> k4_subset_1(sK0,sK1,sK0) = k2_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f162,plain,
    ( spl4_20
    | ~ spl4_0 ),
    inference(avatar_split_clause,[],[f115,f70,f160])).

fof(f70,plain,
    ( spl4_0
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_0])])).

fof(f115,plain,
    ( k4_subset_1(sK0,sK1,sK0) = k2_xboole_0(sK0,sK1)
    | ~ spl4_0 ),
    inference(forward_demodulation,[],[f114,f57])).

fof(f114,plain,
    ( k4_subset_1(sK0,sK1,sK0) = k2_xboole_0(sK1,sK0)
    | ~ spl4_0 ),
    inference(forward_demodulation,[],[f111,f49])).

fof(f49,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/subset_1__t28_subset_1.p',d4_subset_1)).

fof(f111,plain,
    ( k4_subset_1(sK0,sK1,k2_subset_1(sK0)) = k2_xboole_0(sK1,k2_subset_1(sK0))
    | ~ spl4_0 ),
    inference(resolution,[],[f75,f48])).

fof(f48,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t28_subset_1.p',dt_k2_subset_1)).

fof(f75,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(sK0))
        | k4_subset_1(sK0,sK1,X1) = k2_xboole_0(sK1,X1) )
    | ~ spl4_0 ),
    inference(resolution,[],[f71,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t28_subset_1.p',redefinition_k4_subset_1)).

fof(f71,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl4_0 ),
    inference(avatar_component_clause,[],[f70])).

fof(f120,plain,
    ( spl4_12
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f100,f93,f118])).

fof(f93,plain,
    ( spl4_6
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f100,plain,
    ( k2_xboole_0(sK1,sK0) = sK0
    | ~ spl4_6 ),
    inference(resolution,[],[f94,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t28_subset_1.p',t12_xboole_1)).

fof(f94,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f93])).

fof(f95,plain,
    ( spl4_6
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f88,f81,f93])).

fof(f81,plain,
    ( spl4_2
  <=> r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f88,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl4_2 ),
    inference(resolution,[],[f82,f65])).

fof(f65,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t28_subset_1.p',d1_zfmisc_1)).

fof(f82,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f81])).

fof(f87,plain,(
    ~ spl4_5 ),
    inference(avatar_split_clause,[],[f68,f85])).

fof(f68,plain,(
    k4_subset_1(sK0,sK1,sK0) != sK0 ),
    inference(forward_demodulation,[],[f42,f49])).

fof(f42,plain,(
    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0)) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t28_subset_1.p',t28_subset_1)).

fof(f83,plain,
    ( spl4_2
    | ~ spl4_0 ),
    inference(avatar_split_clause,[],[f79,f70,f81])).

fof(f79,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl4_0 ),
    inference(subsumption_resolution,[],[f78,f55])).

fof(f55,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t28_subset_1.p',fc1_subset_1)).

fof(f78,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl4_0 ),
    inference(resolution,[],[f71,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t28_subset_1.p',d2_subset_1)).

fof(f72,plain,(
    spl4_0 ),
    inference(avatar_split_clause,[],[f41,f70])).

fof(f41,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
