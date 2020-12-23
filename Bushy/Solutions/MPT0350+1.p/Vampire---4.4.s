%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : subset_1__t25_subset_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:22 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   57 (  74 expanded)
%              Number of leaves         :   14 (  26 expanded)
%              Depth                    :    9
%              Number of atoms          :  130 ( 164 expanded)
%              Number of equality atoms :   27 (  31 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f186,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f89,f103,f107,f115,f119,f182])).

fof(f182,plain,
    ( ~ spl4_0
    | spl4_5
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(avatar_contradiction_clause,[],[f181])).

fof(f181,plain,
    ( $false
    | ~ spl4_0
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f180,f106])).

fof(f106,plain,
    ( k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) != sK0
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl4_5
  <=> k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) != sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f180,plain,
    ( k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) = sK0
    | ~ spl4_0
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(forward_demodulation,[],[f176,f122])).

fof(f122,plain,
    ( k2_xboole_0(sK1,k3_subset_1(sK0,sK1)) = sK0
    | ~ spl4_0
    | ~ spl4_6 ),
    inference(forward_demodulation,[],[f121,f93])).

fof(f93,plain,
    ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)
    | ~ spl4_0 ),
    inference(resolution,[],[f88,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t25_subset_1.p',d5_subset_1)).

fof(f88,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl4_0 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl4_0
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_0])])).

fof(f121,plain,
    ( k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)) = sK0
    | ~ spl4_6 ),
    inference(resolution,[],[f114,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t25_subset_1.p',t45_xboole_1)).

fof(f114,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl4_6
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f176,plain,
    ( k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) = k2_xboole_0(sK1,k3_subset_1(sK0,sK1))
    | ~ spl4_0
    | ~ spl4_8 ),
    inference(resolution,[],[f91,f118])).

fof(f118,plain,
    ( m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl4_8
  <=> m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f91,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(sK0))
        | k4_subset_1(sK0,sK1,X1) = k2_xboole_0(sK1,X1) )
    | ~ spl4_0 ),
    inference(resolution,[],[f88,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t25_subset_1.p',redefinition_k4_subset_1)).

fof(f119,plain,
    ( spl4_8
    | ~ spl4_0 ),
    inference(avatar_split_clause,[],[f95,f87,f117])).

fof(f95,plain,
    ( m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl4_0 ),
    inference(resolution,[],[f88,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t25_subset_1.p',dt_k3_subset_1)).

fof(f115,plain,
    ( spl4_6
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f108,f101,f113])).

fof(f101,plain,
    ( spl4_2
  <=> r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f108,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl4_2 ),
    inference(resolution,[],[f102,f82])).

fof(f82,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
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
    file('/export/starexec/sandbox/benchmark/subset_1__t25_subset_1.p',d1_zfmisc_1)).

fof(f102,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f101])).

fof(f107,plain,(
    ~ spl4_5 ),
    inference(avatar_split_clause,[],[f85,f105])).

fof(f85,plain,(
    k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) != sK0 ),
    inference(forward_demodulation,[],[f52,f54])).

fof(f54,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/subset_1__t25_subset_1.p',d4_subset_1)).

fof(f52,plain,(
    k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) != k2_subset_1(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ? [X0,X1] :
      ( k4_subset_1(X0,X1,k3_subset_1(X0,X1)) != k2_subset_1(X0)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = k2_subset_1(X0) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = k2_subset_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t25_subset_1.p',t25_subset_1)).

fof(f103,plain,
    ( spl4_2
    | ~ spl4_0 ),
    inference(avatar_split_clause,[],[f99,f87,f101])).

fof(f99,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl4_0 ),
    inference(subsumption_resolution,[],[f98,f63])).

fof(f63,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t25_subset_1.p',fc1_subset_1)).

fof(f98,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl4_0 ),
    inference(resolution,[],[f88,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
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
    file('/export/starexec/sandbox/benchmark/subset_1__t25_subset_1.p',d2_subset_1)).

fof(f89,plain,(
    spl4_0 ),
    inference(avatar_split_clause,[],[f51,f87])).

fof(f51,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
